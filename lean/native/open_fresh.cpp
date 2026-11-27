#include <cerrno>
#include <cstdio>
#include <cstring>
#include <fcntl.h>
#include <lean/lean.h>
#include <unistd.h>

namespace lean {
// Lean 4.36's exported runtime constructor transfers FILE* to FS.Handle.
lean_object *io_wrap_handle(FILE *file);
}

extern "C" LEAN_EXPORT lean_obj_res alvoki_open_fresh_output(b_lean_obj_arg path) {
    const char *name = lean_string_cstr(path);
    if (std::strlen(name) != lean_string_size(path) - 1) {
        lean_inc(path);
        return lean_io_result_mk_error(lean_mk_io_error_invalid_argument_file(
            path, EINVAL, lean_mk_string("string contains NUL bytes")));
    }

    int fd = open(name, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0666);
    if (fd == -1)
        return lean_io_result_mk_error(lean_decode_io_error(errno, nullptr));

    FILE *file = fdopen(fd, "w");
    if (file == nullptr) {
        int error = errno;
        close(fd);
        // Exclusive creation and the caller's stable namespace establish
        // ownership of this name. Unlink is best effort.
        unlink(name);
        return lean_io_result_mk_error(lean_decode_io_error(error, nullptr));
    }

    return lean_io_result_mk_ok(lean::io_wrap_handle(file));
}
