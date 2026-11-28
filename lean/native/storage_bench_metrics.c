#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include <sys/resource.h>
#include <lean/lean.h>

LEAN_EXPORT lean_obj_res alvoki_bench_cpu_ns(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_THREAD_CPUTIME_ID, &now) != 0)
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("clock_gettime failed")));
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)now.tv_sec * 1000000000 + now.tv_nsec));
}

LEAN_EXPORT lean_obj_res alvoki_bench_peak_rss(void) {
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) != 0)
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("getrusage failed")));
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)usage.ru_maxrss));
}

extern void alvoki_bench_sync_begin(void) __attribute__((weak));
extern void alvoki_bench_sync_end(void) __attribute__((weak));

LEAN_EXPORT lean_obj_res alvoki_bench_begin_sync_timing(void) {
    if (!alvoki_bench_sync_begin)
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("sync profiler not loaded")));
    alvoki_bench_sync_begin();
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res alvoki_bench_end_sync_timing(void) {
    alvoki_bench_sync_end();
    return lean_io_result_mk_ok(lean_box(0));
}

/* Read the process's current RSS before the benchmark's checking pass. */
LEAN_EXPORT lean_obj_res alvoki_bench_resident_rss(void) {
    FILE *file = fopen("/proc/self/smaps_rollup", "r");
    if (file) {
        char line[128];
        unsigned long long kib;
        while (fgets(line, sizeof(line), file)) {
            if (sscanf(line, "Rss: %llu kB", &kib) == 1) {
                fclose(file);
                return lean_io_result_mk_ok(lean_box_uint64((uint64_t)kib));
            }
        }
        fclose(file);
    }
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("cannot read current RSS from /proc/self/smaps_rollup")));
}
