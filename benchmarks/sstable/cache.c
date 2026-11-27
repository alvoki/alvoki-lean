#define _POSIX_C_SOURCE 200809L
#include <fcntl.h>
#include <lean/lean.h>
#include <stdio.h>

/* Advisory only. A successful call does not certify physical storage reads. */
lean_obj_res alvoki_sstable_bench_drop_cache(b_lean_obj_arg handle) {
    int fd = fileno(lean_get_external_data(handle));
    if (fd < 0 || posix_fadvise(fd, 0, 0, POSIX_FADV_DONTNEED) != 0)
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("could not advise eviction of benchmark file")));
    return lean_io_result_mk_ok(lean_box(0));
}
