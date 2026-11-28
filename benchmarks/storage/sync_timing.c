#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef int (*sync_fn)(int);
static sync_fn real_fsync;
static sync_fn real_fdatasync;

struct sample {
    uint64_t ns;
    int result;
    const char *operation;
};

static _Thread_local struct sample samples[8192];
static _Thread_local size_t count;
static _Thread_local int recording;

__attribute__((constructor)) static void init(void) {
    real_fsync = (sync_fn)dlsym(RTLD_NEXT, "fsync");
    real_fdatasync = (sync_fn)dlsym(RTLD_NEXT, "fdatasync");
    if (!real_fsync || !real_fdatasync) abort();
}

void alvoki_bench_sync_begin(void) {
    count = 0;
    recording = 1;
}

void alvoki_bench_sync_end(void) {
    recording = 0;
    const char *path = getenv("ALVOKI_BENCH_SYNC_FILE");
    if (!path) abort();
    FILE *out = fopen(path, "w");
    if (!out) abort();
    for (size_t i = 0; i < count; ++i) {
        if (fprintf(out, "%zu,%s,%" PRIu64 ",%d\n",
                    i, samples[i].operation, samples[i].ns, samples[i].result) < 0) abort();
    }
    if (fclose(out) != 0) abort();
}

static uint64_t mono_ns(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) abort();
    return (uint64_t)now.tv_sec * 1000000000 + now.tv_nsec;
}

static int timed_sync(sync_fn sync, int fd, const char *operation) {
    if (!recording) return sync(fd);
    if (count == sizeof(samples) / sizeof(samples[0])) abort();
    uint64_t start = mono_ns();
    int result = sync(fd);
    int saved_errno = errno;
    uint64_t elapsed = mono_ns() - start;
    samples[count++] = (struct sample){elapsed, result, operation};
    errno = saved_errno;
    return result;
}

int fsync(int fd) { return timed_sync(real_fsync, fd, "fsync"); }
int fdatasync(int fd) { return timed_sync(real_fdatasync, fd, "fdatasync"); }
