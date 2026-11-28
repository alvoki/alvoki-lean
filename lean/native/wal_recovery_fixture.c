#include <dirent.h>
#include <errno.h>
#include <lean/lean.h>
#include <stdio.h>
#include <string.h>
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

static unsigned listing_failure_countdown;

lean_object *alvoki_test_fail_directory_listing(uint8_t after_entry) {
    listing_failure_countdown = after_entry ? 2 : 1;
    return lean_io_result_mk_ok(lean_box(0));
}

struct dirent *__real_readdir(DIR *directory);

struct dirent *__wrap_readdir(DIR *directory) {
    if (listing_failure_countdown == 1) {
        listing_failure_countdown = 0;
        errno = EIO;
        return NULL;
    }
    struct dirent *entry = __real_readdir(directory);
    // Count only entries the checked enumerator adds to its partial result.
    if (listing_failure_countdown == 2 && entry != NULL &&
        strcmp(entry->d_name, ".") != 0 && strcmp(entry->d_name, "..") != 0)
        listing_failure_countdown = 1;
    return entry;
}

/* Inject only on the second chunk of the chosen segment inode. The first
   mode returns a real positive final chunk with both EOF and error set.
   The second returns an interior short chunk with neither flag set. */
static struct stat read_target;
static unsigned chunks_until_short;
static int error_at_eof;
static FILE *read_error_stream;

lean_object *alvoki_test_short_segment_read(b_lean_obj_arg path, uint8_t error_on_eof) {
    if (stat(lean_string_cstr(path), &read_target) != 0)
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    chunks_until_short = 2;
    error_at_eof = error_on_eof;
    return lean_io_result_mk_ok(lean_box(0));
}

size_t __real_fread(void *bytes, size_t size, size_t count, FILE *stream);
int __real_ferror(FILE *stream);

size_t __wrap_fread(void *bytes, size_t size, size_t count, FILE *stream) {
    if (chunks_until_short && size == 1 && count == 1024) {
        struct stat info;
        if (fstat(fileno(stream), &info) == 0 && info.st_dev == read_target.st_dev &&
            info.st_ino == read_target.st_ino && --chunks_until_short == 0) {
            size_t n = __real_fread(bytes, 1, error_at_eof ? count : 19, stream);
            if (error_at_eof) {
                read_error_stream = stream;
                errno = EIO;
            }
            return n;
        }
    }
    return __real_fread(bytes, size, count, stream);
}

int __wrap_ferror(FILE *stream) {
    if (stream == read_error_stream) {
        read_error_stream = NULL;
        return 1;
    }
    return __real_ferror(stream);
}
