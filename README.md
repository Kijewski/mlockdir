# mlockdir

Lock a directory / directories in memory.

```sh
$ mlockdir
Enumerating files in 1 folder(s) ... 30.98µs
Allocating empty memory map with 24 KiB ... 6.77µs
Mapping 4 files with 24 KiB in memory ... 48.92µs
Locking 4 files with 24 KiB in memory ... 25.97µs
Files locked ... Press any key to terminate.
Releasing memory ... 25.08µs
```

If no argument is given, then the current working directory is locked.
Otherwise you can specify multiple directories as arguments.
