#include <lean/lean.h>
#include <stdio.h>
#include <sys/stat.h>

static int fail_directory_sync;
static unsigned syncs_until_lost_reply;
static struct stat expected_marker;

lean_object *alvoki_test_fail_directory_sync(b_lean_obj_arg unit) {
    (void)unit;
    fail_directory_sync = 1;
    return lean_io_result_mk_ok(lean_box(0));
}

lean_object *alvoki_test_lose_marker_sync_reply(b_lean_obj_arg path) {
    if (stat(lean_string_cstr(path), &expected_marker) != 0)
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("cannot identify the expected marker inode")));
    // A boundary append syncs data first, then its selected marker.
    syncs_until_lost_reply = 2;
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
    int lose_reply = syncs_until_lost_reply && --syncs_until_lost_reply == 0;
    if (lose_reply) {
        struct stat actual;
        int fd = fileno(lean_get_external_data(handle));
        if (fstat(fd, &actual) != 0 || actual.st_dev != expected_marker.st_dev ||
            actual.st_ino != expected_marker.st_ino)
            return lean_io_result_mk_error(lean_mk_io_user_error(
                lean_mk_string("append synced a different inode than the expected marker")));
    }
    lean_object *result = __real_alvoki_fsync(handle);
    if (lose_reply && lean_io_result_is_ok(result)) {
        lean_dec(result);
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("injected marker fsync reply loss")));
    }
    return result;
}
