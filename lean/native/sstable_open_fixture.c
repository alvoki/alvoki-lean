#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <stdio.h>

static int inject_fdopen_failure;
static int failed_fd = -1;

lean_object *alvoki_test_fail_output_fdopen(b_lean_obj_arg unit) {
    (void)unit;
    inject_fdopen_failure = 1;
    failed_fd = -1;
    return lean_io_result_mk_ok(lean_box(0));
}

lean_object *alvoki_test_failed_output_fd_closed(b_lean_obj_arg unit) {
    (void)unit;
    int closed = failed_fd >= 0 && fcntl(failed_fd, F_GETFD) == -1 && errno == EBADF;
    return lean_io_result_mk_ok(lean_box(closed));
}

FILE *__real_fdopen(int fd, const char *mode);

FILE *__wrap_fdopen(int fd, const char *mode) {
    if (inject_fdopen_failure) {
        inject_fdopen_failure = 0;
        failed_fd = fd;
        errno = ENOMEM;
        return NULL;
    }
    return __real_fdopen(fd, mode);
}
