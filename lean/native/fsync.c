#include <errno.h>
#include <lean/lean.h>
#include <stdio.h>
#include <unistd.h>

lean_object *alvoki_fsync(b_lean_obj_arg handle) {
    // Lean 4.36's IO.FS.Handle external object owns this FILE pointer.
    int fd = fileno(lean_get_external_data(handle));
    if (fd == -1)
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));

    int result;
    do {
        result = fsync(fd);
    } while (result == -1 && errno == EINTR);
    if (result == -1)
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));

    return lean_io_result_mk_ok(lean_box(0));
}

/* Call immediately after opening an experimental WAL stream. A failed write
   must not leave pending stdio output that a later finalizer could publish. */
lean_object *alvoki_wal_unbuffered(b_lean_obj_arg handle) {
    if (setvbuf(lean_get_external_data(handle), NULL, _IONBF, 0) != 0)
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("cannot disable WAL stream buffering")));
    return lean_io_result_mk_ok(lean_box(0));
}

/* Recovery supplies a nonnegative length bounded by the bytes it scanned.
   This adapter targets Linux x86-64, where every scalar Nat fits in off_t. */
lean_object *alvoki_wal_truncate_at(b_lean_obj_arg handle, b_lean_obj_arg count) {
    if (!lean_is_scalar(count))
        return lean_io_result_mk_error(lean_decode_io_error(EOVERFLOW, NULL));

    int fd = fileno(lean_get_external_data(handle));
    if (fd == -1)
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));

    int result;
    do {
        result = ftruncate(fd, (off_t)lean_unbox(count));
    } while (result == -1 && errno == EINTR);
    if (result == -1)
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));

    return lean_io_result_mk_ok(lean_box(0));
}

/* Unlike Lean 4.36 Handle.read, inspect ferror even after positive fread.
   A successful short result certifies EOF on this same description. */
lean_object *alvoki_wal_read_chunk(b_lean_obj_arg handle, size_t count) {
    FILE *stream = lean_get_external_data(handle);
    if (count == 0 || count > 65536)
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));

    lean_object *bytes = lean_alloc_sarray(1, 0, count);
    errno = 0;
    size_t actual = fread(lean_sarray_cptr(bytes), 1, count, stream);
    int error = errno;
    if (ferror(stream) || (actual < count && !feof(stream))) {
        lean_dec(bytes);
        return lean_io_result_mk_error(lean_decode_io_error(error ? error : EIO, NULL));
    }
    lean_sarray_set_size(bytes, actual);
    return lean_io_result_mk_ok(bytes);
}
