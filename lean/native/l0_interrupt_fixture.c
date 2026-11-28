/* Test-only syscall faults and process cuts for the native L0 fixture. */
#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64
#include <dlfcn.h>
#include <errno.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static atomic_bool published_successor;

static bool matches_fd(int fd, const char *target) {
    if (!target)
        return false;
    char link[64], path[4096];
    snprintf(link, sizeof(link), "/proc/self/fd/%d", fd);
    ssize_t n = readlink(link, path, sizeof(path));
    return n >= 0 && (size_t)n == strlen(target) && memcmp(path, target, n) == 0;
}

int fsync(int fd) {
    int (*real_fsync)(int) = dlsym(RTLD_NEXT, "fsync");
    static atomic_bool failed_wal;
    const char *target = getenv("ALVOKI_L0_FAIL_WAL_SYNC");
    if ((!getenv("ALVOKI_L0_AFTER_CONTROL") || atomic_load(&published_successor)) &&
        matches_fd(fd, target) && !atomic_exchange(&failed_wal, true)) {
        errno = EIO;
        return -1;
    }
    static atomic_bool failed_flush;
    if (matches_fd(fd, getenv("ALVOKI_L0_FAIL_FLUSH_SYNC")) &&
        !atomic_exchange(&failed_flush, true)) {
        errno = EIO;
        return -1;
    }
    int result = real_fsync(fd);
    const char *cut = getenv("ALVOKI_L0_CUT");
    if (result == 0 && cut && (!getenv("ALVOKI_L0_AFTER_CONTROL") || atomic_load(&published_successor))) {
        char link[64], path[4096];
        snprintf(link, sizeof(link), "/proc/self/fd/%d", fd);
        ssize_t length = readlink(link, path, sizeof(path) - 1);
        if (length >= 0) {
            path[length] = '\0';
            const char *name = strrchr(path, '/');
            if (name && ((strcmp(cut, "table") == 0 && strcmp(name, "/tables") == 0) ||
                         (strcmp(cut, "data") == 0 && strcmp(name, "/segment") == 0) ||
                         (strcmp(cut, "marker") == 0 &&
                          (strcmp(name, "/commit.0") == 0 || strcmp(name, "/commit.1") == 0))))
                _exit(73);
        }
    }
    return result;
}

int rename(const char *from, const char *to) {
    int (*real_rename)(const char *, const char *) = dlsym(RTLD_NEXT, "rename");
    int result = real_rename(from, to);
    const char *cut = getenv("ALVOKI_L0_CUT");
    const char *name = strrchr(to, '/');
    if (result == 0 && getenv("ALVOKI_L0_AFTER_CONTROL") && name && strcmp(name, "/CONTROL") == 0)
        atomic_store(&published_successor, true);
    if (result == 0 && cut && strcmp(cut, "control") == 0 && name && strcmp(name, "/CONTROL") == 0)
        _exit(73);
    if (result == 0 && cut && strcmp(cut, "rename") == 0 && name && strcmp(name, "/BLOB") == 0)
        _exit(73);
    return result;
}

/* Fail the checked reader's size call once on the requested open inode. */
int fstat(int fd, struct stat *st) {
    static atomic_bool fired;
    const char *target = getenv("ALVOKI_L0_FAIL_TABLE_SIZE");
    if (matches_fd(fd, target) && !atomic_exchange(&fired, true)) {
        errno = EIO;
        return -1;
    }
    int (*real_fstat)(int, struct stat *) = dlsym(RTLD_NEXT, "fstat64");
    return real_fstat(fd, st);
}
