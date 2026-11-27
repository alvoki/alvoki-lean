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
