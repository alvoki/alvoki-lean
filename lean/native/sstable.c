#define _POSIX_C_SOURCE 200809L
#define _FILE_OFFSET_BITS 64
#include <errno.h>
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>

_Static_assert(sizeof(off_t) >= 8, "SSTable requires 64-bit file offsets");

/* Lean 4.36 FS.Handle owns a FILE*. Both operations borrow that same handle. */
LEAN_EXPORT lean_obj_res alvoki_sstable_size(b_lean_obj_arg handle) {
    struct stat st;
    int fd = fileno(lean_get_external_data(handle));
    if (fd < 0 || fstat(fd, &st) < 0)
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    if (!S_ISREG(st.st_mode) || st.st_size < 0)
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("SSTable requires a regular file")));
    return lean_io_result_mk_ok(lean_uint64_to_nat((uint64_t)st.st_size));
}

LEAN_EXPORT lean_obj_res alvoki_sstable_pread(b_lean_obj_arg handle,
                                               uint64_t offset, size_t size) {
    /* Keep the allocation bound in sync with Lean's maxRowSize. */
    if (size > 16 * 1024 * 1024 || offset > (uint64_t)INT64_MAX - size)
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("SSTable read outside positional I/O bounds")));
    int fd = fileno(lean_get_external_data(handle));
    if (fd < 0)
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    lean_object *out = lean_alloc_sarray(1, 0, size);
    size_t done = 0;
    while (done < size) {
        ssize_t n = pread(fd, lean_sarray_cptr(out) + done, size - done,
                          (off_t)(offset + done));
        if (n < 0) {
            if (errno == EINTR) continue;
            int err = errno;
            lean_dec(out);
            return lean_io_result_mk_error(lean_decode_io_error(err, NULL));
        }
        if (n == 0) break;
        done += (size_t)n;
    }
    lean_sarray_set_size(out, done);
    return lean_io_result_mk_ok(out);
}
