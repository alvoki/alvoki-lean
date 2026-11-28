import Init.System.IO
@[extern "alvoki_wal_read_chunk"]
opaque checked (h : @& IO.FS.Handle) (count : USize) : IO ByteArray

