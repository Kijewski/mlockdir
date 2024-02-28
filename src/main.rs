// SPDX-License-Identifier: Apache-2.0
//
// Copyright 2024 René Kijewski <crates.io@k6i.de>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![allow(unused_attributes)]
#![warn(absolute_paths_not_starting_with_crate)]
#![warn(elided_lifetimes_in_paths)]
#![warn(explicit_outlives_requirements)]
#![warn(meta_variable_misuse)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(non_ascii_idents)]
#![warn(noop_method_call)]
#![warn(single_use_lifetimes)]
#![warn(trivial_casts)]
#![warn(unreachable_pub)]
#![warn(unused_crate_dependencies)]
#![warn(unused_extern_crates)]
#![warn(unused_lifetimes)]
#![warn(unused_results)]

use std::env::args_os;
use std::ffi::CStr;
use std::fmt::Arguments;
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::process::exit;
use std::ptr::null_mut;
use std::time::Instant;

use ahash::{AHashMap, AHashSet};
use compact_str::ToCompactString;
use cstr::cstr;
use humansize::{SizeFormatter, BINARY};
use libc::{c_void, mode_t, S_IFMT, S_IFREG};
use rustix::fd::{self, AsFd as _};
use rustix::{event, fs, io, mm, param, process, stdio, termios};

fn main() {
    if let Err(err) = run() {
        write(format_args!("{err:?}\n"));
        exit(1);
    }
}

fn run() -> Result<(), Error> {
    let dfds = collect_directory_fds()?;
    process::chdir(cstr!("/")).map_err(Error::ChdirRoot)?;

    let mut file_count = 0;
    let mut total_len = 0;
    let mut inos = InosMap::with_capacity(64);
    let mut readdir_buf = Vec::with_capacity(1 << 16);

    enumerate_all_files(&dfds, &mut inos, &mut readdir_buf, &mut total_len)?;
    match () {
        _ if inos.is_empty() => return Err(Error::NoFiles),
        _ if inos.is_empty() => return Err(Error::NoData),
        _ => (),
    }

    let (map_start, mut map_end) = allocate_empty_map(total_len)?;

    map_all_files(
        &dfds,
        map_start,
        &mut map_end,
        &mut readdir_buf,
        &mut inos,
        &mut file_count,
    )?;
    drop(inos);
    drop(readdir_buf);
    drop(dfds);

    lock_files(file_count, map_start, map_end)?;
    pause()?;
    release_memory(map_end, map_start)?;

    Ok(())
}

#[derive(thiserror::Error, pretty_error_debug::Debug)]
enum Error {
    #[error("Nothing to do. The folder is empty ...")]
    NoFiles,
    #[error("Nothing to do. All files in the folder are empty ...")]
    NoData,
    #[error("Could not open current working directory")]
    OpenCwd(#[source] io::Errno),
    #[error("Could not open directory {}", .1.display())]
    OpenDir(#[source] io::Errno, PathBuf),
    #[error("Could not statx directory {}", .1.display())]
    StatDir(Option<io::Errno>, PathBuf),
    #[error("Could not change directory")]
    ChdirRoot(#[source] io::Errno),
    #[error("Could not read directory")]
    ReadDir(#[source] io::Errno),
    #[error("Total size too big")]
    TooBig,
    #[error("Could not map empty range")]
    MmapEmpty(#[source] io::Errno),
    #[error("Could not rewind directory index")]
    Rewind(#[source] io::Errno),
    #[error("Could not unmap memory range")]
    Munmap(#[source] io::Errno),
    #[error("Could not lock memory range")]
    Mlock(#[source] io::Errno),
    #[error("Could not advise memory map")]
    Madvise(#[source] io::Errno),
    #[error("Could not populate locked memory")]
    Populate(#[source] io::Errno),
    #[error("Too many files to lock")]
    TooManyFiles,
    #[error("Did not lock any files")]
    NothingReserved,
    #[error("Could not get file status for STDIN")]
    StdinGetFl(#[source] io::Errno),
    #[error("Could not set file status for STDIN")]
    StdinSetFl(#[source] io::Errno),
    #[error("Could not set terminal attributes for STDIN")]
    StdinSetAttrs(#[source] io::Errno),
    #[error("Could not read from STDIN")]
    StdinRead(#[source] io::Errno),
    #[error("`mmap(..MAP_FIXED..)` returned an unexpected address")]
    MmapUnexpectedAddress,
    #[error("Could not unlock and unmap memory")]
    Unmap(#[source] io::Errno),
}

fn map_all_files(
    dfds: &[Dfd],
    map_start: *mut c_void,
    map_end: &mut *mut c_void,
    readdir_buf: &mut Vec<u8>,
    inos: &mut InosMap,
    file_count: &mut usize,
) -> Result<(), Error> {
    let len = *map_end as usize - map_start as usize;
    write(format_args!(
        "Mapping {} files with {} in memory ...",
        inos.len(),
        SizeFormatter::new(len, BINARY),
    ));
    let start = Instant::now();

    let page_size = param::page_size();
    let mut map_pos = map_start;
    for dfd in dfds.iter() {
        map_files(dfd, page_size, &mut map_pos, readdir_buf, inos, file_count)?;
    }
    if map_pos.cast() == map_start {
        return Err(Error::NothingReserved);
    }

    if map_pos != (*map_end).cast() {
        let trailing_len = *map_end as usize - map_pos as usize;
        unsafe { mm::munmap(map_pos.cast(), trailing_len).map_err(Error::Munmap)? };
        *map_end = map_pos;
    }

    write(format_args!(" {:.2?}\n", start.elapsed()));
    Ok(())
}

fn collect_directory_fds() -> Result<Vec<Dfd>, Error> {
    let cwd = open_cwd()?;

    let mut paths = args_os().fuse();
    let _ = paths.next();
    let mut dfds = Vec::with_capacity(paths.size_hint().0.max(1));

    let mut seen_dirs = AHashSet::with_capacity(paths.size_hint().0);
    for path in paths {
        let oflags = fs::OFlags::RDONLY | fs::OFlags::DIRECTORY | fs::OFlags::CLOEXEC;
        let mode = fs::Mode::empty();
        let resolve = fs::ResolveFlags::NO_MAGICLINKS;
        let dfd = match fs::openat2(&cwd, &path, oflags, mode, resolve) {
            Ok(dfd) => dfd,
            Err(err) => return Err(Error::OpenDir(err, path.into())),
        };

        let key = match dir_ino(dfd.as_fd()) {
            Ok(key) => key,
            Err(err) => return Err(Error::StatDir(err, path.into())),
        };
        if seen_dirs.insert(key) {
            dfds.push(((key.0, key.1), dfd));
        }
    }

    if dfds.is_empty() {
        let key = match dir_ino(cwd.as_fd()) {
            Ok(key) => key,
            Err(err) => return Err(Error::StatDir(err, ".".into())),
        };
        dfds.push(((key.0, key.1), cwd));
    }

    Ok(dfds)
}

fn dir_ino(dfd: fd::BorrowedFd<'_>) -> Result<(u32, u32, u64), Option<io::Errno>> {
    let flags =
        fs::AtFlags::NO_AUTOMOUNT | fs::AtFlags::STATX_SYNC_AS_STAT | fs::AtFlags::EMPTY_PATH;
    let mask = fs::StatxFlags::INO;
    let stats = fs::statx(dfd, cstr!(""), flags, mask).map_err(Some)?;
    if stats.stx_mask & mask.bits() != mask.bits() {
        return Err(None);
    }

    Ok((stats.stx_dev_major, stats.stx_dev_minor, stats.stx_ino))
}

fn open_cwd() -> Result<fd::OwnedFd, Error> {
    let oflags = fs::OFlags::RDONLY | fs::OFlags::DIRECTORY | fs::OFlags::CLOEXEC;
    let mode = fs::Mode::empty();
    let resolve = fs::ResolveFlags::NO_XDEV
        | fs::ResolveFlags::NO_MAGICLINKS
        | fs::ResolveFlags::NO_SYMLINKS
        | fs::ResolveFlags::BENEATH;
    fs::openat2(fs::CWD, cstr!("."), oflags, mode, resolve).map_err(Error::OpenCwd)
}

fn allocate_empty_map(total_len: usize) -> Result<(*mut c_void, *mut c_void), Error> {
    write(format_args!(
        "Allocating empty memory map with {} ...",
        SizeFormatter::new(total_len, BINARY),
    ));
    let start = Instant::now();

    let ptr = null_mut();
    let prot = mm::ProtFlags::empty();
    let flags = mm::MapFlags::PRIVATE | mm::MapFlags::NORESERVE;
    let map_start = unsafe { mm::mmap_anonymous(ptr, total_len, prot, flags) };
    let map_start = match map_start {
        Ok(map_start) => map_start,
        Err(err) => return Err(Error::MmapEmpty(err)),
    };
    unsafe { madvise_range(map_start, total_len)? };

    write(format_args!(" {:.2?}\n", start.elapsed()));
    Ok((
        map_start,
        map_start.cast::<u8>().wrapping_add(total_len).cast(),
    ))
}

fn enumerate_all_files(
    dfds: &[Dfd],
    inos: &mut InosMap,
    readdir_buf: &mut Vec<u8>,
    total_len: &mut usize,
) -> Result<(), Error> {
    write(format_args!(
        "Enumerating files in {} folder(s) ...",
        dfds.len()
    ));
    let start = Instant::now();

    let page_size = param::page_size();
    for dfd in dfds.iter() {
        enumerate_files(dfd, page_size, inos, readdir_buf, total_len)?;
        let _ = fs::seek(&dfd.1, fs::SeekFrom::Start(0)).map_err(Error::Rewind)?;
    }

    write(format_args!(" {:.2?}\n", start.elapsed()));
    Ok(())
}

fn enumerate_files(
    dfd: &Dfd,
    page_size: usize,
    inos: &mut InosMap,
    readdir_buf: &mut Vec<u8>,
    total_len: &mut usize,
) -> Result<(), Error> {
    let &(device, ref dfd) = dfd;
    let dfd = dfd.as_fd();

    next_entry(dfd, readdir_buf, &mut |entry| {
        // no already handled INOs
        let key = (device, entry.ino());
        if inos.contains_key(&key) {
            return Ok(());
        }

        // only readable files
        let path = entry.file_name();
        let access = fs::Access::READ_OK;
        let flags = fs::AtFlags::empty();
        if fs::accessat(dfd, path, access, flags).is_err() {
            return Ok(());
        }

        if let Some(size) = next_entry_statx(dfd, path, &entry, page_size)? {
            let size = size.get();
            *total_len = total_len.checked_add(size).ok_or(Error::TooBig)?;
            let _ = inos.insert(key, size);
        }
        Ok(())
    })
}

fn map_files(
    dfd: &Dfd,
    page_size: usize,
    map_start: &mut *mut c_void,
    readdir_buf: &mut Vec<u8>,
    inos: &mut InosMap,
    file_count: &mut usize,
) -> Result<(), Error> {
    let &(device, ref dfd) = dfd;
    let dfd = dfd.as_fd();
    let mut map_pos = map_start.cast::<u8>();

    next_entry(dfd, readdir_buf, &mut |entry| {
        // only seen INOs
        let key = (device, entry.ino());
        let Some(reserved_size) = inos.remove(&key) else {
            return Ok(());
        };

        let oflags = fs::OFlags::RDONLY | fs::OFlags::NOCTTY | fs::OFlags::CLOEXEC;
        let mode = fs::Mode::empty();
        let resolve = fs::ResolveFlags::NO_XDEV
            | fs::ResolveFlags::NO_MAGICLINKS
            | fs::ResolveFlags::NO_SYMLINKS
            | fs::ResolveFlags::BENEATH;
        let Ok(fd) = fs::openat2(dfd, entry.file_name(), oflags, mode, resolve) else {
            return Ok(());
        };

        let Some(cur_size) = next_entry_statx(fd.as_fd(), cstr!(""), &entry, page_size)? else {
            return Ok(());
        };
        let cur_size = cur_size.get();
        if cur_size > reserved_size {
            return Ok(());
        }

        let ptr = map_pos.cast();
        let prot = mm::ProtFlags::READ;
        let flags = mm::MapFlags::SHARED | mm::MapFlags::NORESERVE | mm::MapFlags::FIXED;
        if let Ok(new_ptr) = unsafe { mm::mmap(ptr, cur_size, prot, flags, fd, 0) } {
            if ptr != new_ptr {
                return Err(Error::MmapUnexpectedAddress);
            }
            map_pos = map_pos.wrapping_add(cur_size);
            *file_count = file_count.checked_add(1).ok_or(Error::TooManyFiles)?;
        }

        Ok(())
    })?;

    *map_start = map_pos.cast();
    Ok(())
}

fn lock_files(
    file_count: usize,
    map_start: *mut c_void,
    map_end: *mut c_void,
) -> Result<(), Error> {
    let start = Instant::now();
    let total_len = map_end as usize - map_start as usize;
    write(format_args!(
        "Locking {file_count} files with {} in memory ...",
        SizeFormatter::new(total_len, BINARY),
    ));

    unsafe {
        madvise_range(map_start, total_len)?;
        mm::mlock_with(map_start, total_len, mm::MlockFlags::ONFAULT).map_err(Error::Mlock)?;
        mm::madvise(map_start, total_len, mm::Advice::LinuxPopulateRead)
            .map_err(Error::Populate)?;
    }

    write(format_args!(" {:.2?}\n", start.elapsed()));
    Ok(())
}

unsafe fn madvise_range(map_start: *mut c_void, total_len: usize) -> Result<(), Error> {
    for adv in [
        mm::Advice::LinuxNoHugepage,
        mm::Advice::LinuxDontDump,
        mm::Advice::Random,
    ] {
        mm::madvise(map_start, total_len, adv).map_err(Error::Madvise)?;
    }
    Ok(())
}

fn next_entry(
    dfd: fd::BorrowedFd<'_>,
    readdir_buf: &mut Vec<u8>,
    per_entry: &mut dyn FnMut(fs::RawDirEntry<'_>) -> Result<(), Error>,
) -> Result<(), Error> {
    'readdir: loop {
        let mut iter = fs::RawDir::new(&dfd, readdir_buf.spare_capacity_mut());
        while let Some(entry) = iter.next() {
            match entry {
                Ok(entry) => {
                    // no hidden files, ".", or ".."
                    let file_name = entry.file_name().to_bytes();
                    if file_name.is_empty() || file_name[0] == b'.' {
                        continue;
                    }

                    // only regular files
                    if entry.file_type() != fs::FileType::RegularFile {
                        continue;
                    }

                    per_entry(entry)?;
                },
                Err(io::Errno::INVAL) => {
                    readdir_buf.reserve_exact(readdir_buf.capacity().checked_mul(3).unwrap() / 2);
                    continue 'readdir;
                },
                Err(err) => return Err(Error::ReadDir(err)),
            }
        }
        break;
    }
    Ok(())
}

fn next_entry_statx(
    dfd: fd::BorrowedFd<'_>,
    path: &CStr,
    entry: &fs::RawDirEntry<'_>,
    page_size: usize,
) -> Result<Option<NonZeroUsize>, Error> {
    let flags =
        fs::AtFlags::NO_AUTOMOUNT | fs::AtFlags::STATX_SYNC_AS_STAT | fs::AtFlags::EMPTY_PATH;
    let mask = fs::StatxFlags::TYPE | fs::StatxFlags::SIZE | fs::StatxFlags::INO;
    let Ok(stats) = fs::statx(dfd, path, flags, mask) else {
        return Ok(None);
    };
    if (stats.stx_mask & mask.bits() != mask.bits())
        || (stats.stx_mode as mode_t & S_IFMT != S_IFREG)
        || (stats.stx_ino != entry.ino())
        || (stats.stx_size == 0)
    {
        return Ok(None);
    }

    let size: usize = stats.stx_size.try_into().map_err(|_| Error::TooBig)?;
    let size = size
        .checked_next_multiple_of(page_size)
        .ok_or(Error::TooBig)?;
    Ok(NonZeroUsize::new(size))
}

fn pause() -> Result<(), Error> {
    let fd = stdio::stdin();
    if let Ok(attrs) = termios::tcgetattr(fd) {
        write(format_args!(
            "Files locked ... Press any key to terminate.\n",
        ));

        // set STDIN to trap ctrl+c, etc., disable line mode, don't echo input
        let mut new_attrs = attrs.clone();
        for idx in [
            termios::SpecialCodeIndex::VINTR,
            termios::SpecialCodeIndex::VQUIT,
            termios::SpecialCodeIndex::VKILL,
            termios::SpecialCodeIndex::VEOF,
        ] {
            new_attrs.special_codes[idx] = 0;
        }
        new_attrs.local_modes = new_attrs.local_modes
            & !(termios::LocalModes::ECHO | termios::LocalModes::ICANON)
            | (termios::LocalModes::ISIG | termios::LocalModes::NOFLSH);
        termios::tcsetattr(fd, termios::OptionalActions::Now, &new_attrs)
            .map_err(Error::StdinSetAttrs)?;

        let reset_terminal = scopeguard::guard(attrs, |attrs| {
            let _ = termios::tcsetattr(fd, termios::OptionalActions::Now, &attrs);
        });

        // set STDIN to non blocking
        let fl = fs::fcntl_getfl(fd).map_err(Error::StdinGetFl)?;
        if !fl.contains(fs::OFlags::NONBLOCK) {
            fs::fcntl_setfl(fd, fl | fs::OFlags::NONBLOCK).map_err(Error::StdinSetFl)?;
        }

        // await input
        let events = event::PollFlags::IN
            | event::PollFlags::PRI
            | event::PollFlags::RDBAND
            | event::PollFlags::RDNORM
            | event::PollFlags::RDHUP
            | event::PollFlags::ERR
            | event::PollFlags::HUP
            | event::PollFlags::NVAL;
        match event::poll(&mut [event::PollFd::new(&fd, events)], -1) {
            Ok(_) | Err(io::Errno::WOULDBLOCK) | Err(io::Errno::INTR) => (),
            Err(err) => return Err(Error::StdinRead(err)),
        }

        // set STDIN to blocking, again
        if !fl.contains(fs::OFlags::NONBLOCK) {
            let _ = fs::fcntl_setfl(fd, fl);
        }

        // reset changes to terminal
        drop(reset_terminal);

        // clear any input on STDIN
        let _ = termios::tcflush(fd, termios::QueueSelector::IFlush);
    } else {
        // TODO: set sigaction for ctrl+c, etc.
        event::pause();
    }
    Ok(())
}

fn release_memory(map_end: *mut c_void, map_start: *mut c_void) -> Result<(), Error> {
    let len = map_end as usize - map_start as usize;
    write(format_args!("Releasing memory ..."));
    let start = Instant::now();
    unsafe { mm::munmap(map_start, len).map_err(Error::Unmap)? };
    write(format_args!(" {:.2?}\n", start.elapsed()));
    Ok(())
}

fn write(content: Arguments<'_>) {
    const HAD_ZERO: u32 = 1 << 0;
    const HAD_INTR: u32 = 1 << 1;
    const HAD_WOULDBLOCK: u32 = 1 << 2;

    let string_content;
    let content = if let Some(s) = content.as_str() {
        s
    } else {
        string_content = content.to_compact_string();
        &string_content
    };
    let mut content = content.as_bytes();

    let fd = stdio::stderr();
    let mut flags = 0;
    while !content.is_empty() {
        match io::write(fd, content) {
            Ok(0) if flags & HAD_ZERO == 0 => flags |= HAD_ZERO,
            Err(io::Errno::INTR) if flags & HAD_INTR == 0 => flags |= HAD_INTR,
            Err(io::Errno::WOULDBLOCK) if flags & HAD_WOULDBLOCK == 0 => flags |= HAD_WOULDBLOCK,
            Ok(0) | Err(_) => break,
            Ok(amount) => {
                content = &content[amount.min(content.len())..];
                flags = 0;
            },
        }
    }
    let _ = termios::tcdrain(fd);
}

type InosMap = AHashMap<(Device, u64), usize>; // (Device, ino) -> file size
type Dfd = (Device, fd::OwnedFd); // (Device, fd)
type Device = (u32, u32); // (dev major, dev minor)
