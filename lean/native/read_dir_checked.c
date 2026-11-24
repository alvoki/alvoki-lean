#include <dirent.h>
#include <errno.h>
#include <lean/lean.h>
#include <string.h>

lean_object *alvoki_read_dir_checked(b_lean_obj_arg path) {
    const char *name = lean_string_cstr(path);
    if (strlen(name) != lean_string_size(path) - 1) {
        lean_inc(path);
        return lean_io_result_mk_error(
            lean_mk_io_error_invalid_argument_file(path, EINVAL, lean_mk_string("string contains NUL bytes")));
    }

    DIR *directory = opendir(name);
    if (directory == NULL)
        return lean_io_result_mk_error(lean_decode_io_error(errno, path));

    lean_object *entries = lean_mk_empty_array();
    int error;
    for (;;) {
        errno = 0;
        struct dirent *entry = readdir(directory);
        if (entry == NULL) {
            error = errno;
            break;
        }
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0)
            continue;

        // Match the pinned Lean runtime's FilePath and IO.FS.DirEntry layout.
        lean_object *reported = lean_alloc_ctor(0, 2, 0);
        lean_inc(path);
        lean_ctor_set(reported, 0, path);
        lean_ctor_set(reported, 1, lean_mk_string(entry->d_name));
        entries = lean_array_push(entries, reported);
    }

    if (closedir(directory) != 0 && error == 0)
        error = errno;
    if (error != 0) {
        lean_dec(entries);
        // These errors arise from the already opened directory descriptor.
        return lean_io_result_mk_error(lean_decode_io_error(error, NULL));
    }
    return lean_io_result_mk_ok(entries);
}
