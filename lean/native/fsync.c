#include <errno.h>
#include <lean/lean.h>
#include <stdio.h>
#include <unistd.h>

lean_object *alvoki_fsync(b_lean_obj_arg handle, b_lean_obj_arg path) {
    // Lean 4.36's IO.FS.Handle external object owns this FILE pointer.
    int fd = fileno(lean_get_external_data(handle));
    if (fd == -1)
        return lean_io_result_mk_error(lean_decode_io_error(errno, path));

    int result;
    do {
        result = fsync(fd);
    } while (result == -1 && errno == EINTR);
    if (result == -1)
        return lean_io_result_mk_error(lean_decode_io_error(errno, path));

    return lean_io_result_mk_ok(lean_box(0));
}
