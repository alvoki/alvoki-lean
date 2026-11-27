#include <lean/lean.h>
#include <stdio.h>
#include <sys/stat.h>

static int fail_directory_sync;

lean_object *alvoki_test_fail_directory_sync(b_lean_obj_arg unit) {
    (void)unit;
    fail_directory_sync = 1;
    return lean_io_result_mk_ok(lean_box(0));
}

lean_object *__real_alvoki_fsync(b_lean_obj_arg handle);

lean_object *__wrap_alvoki_fsync(b_lean_obj_arg handle) {
    if (fail_directory_sync) {
        struct stat info;
        int fd = fileno(lean_get_external_data(handle));
        if (fstat(fd, &info) == 0 && S_ISDIR(info.st_mode)) {
            fail_directory_sync = 0;
            return lean_io_result_mk_error(lean_mk_io_user_error(
                lean_mk_string("injected directory fsync failure")));
        }
    }
    return __real_alvoki_fsync(handle);
}
