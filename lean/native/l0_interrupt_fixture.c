/* Test-only cuts after a completed syscall, before the caller can continue. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int fsync(int fd) {
    int (*real_fsync)(int) = dlsym(RTLD_NEXT, "fsync");
    int result = real_fsync(fd);
    const char *cut = getenv("ALVOKI_L0_CUT");
    if (result == 0 && cut && strcmp(cut, "table") == 0) {
        char link[64], path[4096];
        snprintf(link, sizeof(link), "/proc/self/fd/%d", fd);
        ssize_t length = readlink(link, path, sizeof(path) - 1);
        if (length >= 0) {
            path[length] = '\0';
            const char *name = strrchr(path, '/');
            if (name && strcmp(name, "/tables") == 0)
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
    if (result == 0 && cut && strcmp(cut, "rename") == 0 && name && strcmp(name, "/BLOB") == 0)
        _exit(73);
    return result;
}
