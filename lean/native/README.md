# Native bindings

These small C adapters are still used by the component experiments and their Linux fixtures:

- [`fsync.c`](fsync.c) exposes checked file synchronization.
- [`read_dir_checked.c`](read_dir_checked.c) reports directory enumeration errors to the segmented WAL adapter.
- [`sstable.c`](sstable.c) supports the retained native SSTable reader.

The packed benchmark helper was retired with the old benchmark stack. Run the retained adapters through [`scripts/reproduce.sh`](../../scripts/reproduce.sh).
