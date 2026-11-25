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

// Positional write to the inactive experimental WAL marker slot. The
// caller owns the database lock and opens this descriptor without O_APPEND.
lean_object *alvoki_write_wal_marker_slot(b_lean_obj_arg handle, uint64_t offset,
                                        b_lean_obj_arg bytes) {
    size_t remaining = lean_sarray_size(bytes);
    if ((offset != 0 && offset != 4096) || remaining != 40)
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
    int fd = fileno(lean_get_external_data(handle));
    if (fd == -1)
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));

    const uint8_t *data = lean_sarray_cptr(bytes);
    while (remaining > 0) {
        ssize_t written = pwrite(fd, data, remaining, (off_t)offset);
        if (written < 0) {
            if (errno == EINTR)
                continue;
            return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
        }
        if (written == 0)
            return lean_io_result_mk_error(lean_decode_io_error(EIO, NULL));
        data += written;
        offset += (uint64_t)written;
        remaining -= (size_t)written;
    }
    return lean_io_result_mk_ok(lean_box(0));
}
