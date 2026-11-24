#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

typedef int (*SyncFn)(int);

static bool same(const char *left, const char *right) {
    return left != NULL && right != NULL && strcmp(left, right) == 0;
}

static void log_sync(const char *log, const char *prefix, const char *path) {
    if (log == NULL) return;
    FILE *file = fopen(log, "a");
    if (file == NULL) _exit(125);
    if (fprintf(file, "%s%s\n", prefix, path) < 0 || fclose(file) != 0) _exit(125);
}

static int fail_sync(void) {
    errno = EIO;
    return -1;
}

static void wait_for_release(const char *ready, const char *release, const char *pid, size_t length) {
    int file = open(ready, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
    if (file < 0 || write(file, pid, length) != (ssize_t)length || close(file) < 0) _exit(125);
    struct timespec delay = { .tv_nsec = 10000000L };
    for (int attempt = 0; attempt < 3000; ++attempt) {
        if (access(release, F_OK) == 0) return;
        nanosleep(&delay, NULL);
    }
    _exit(125);
}

static int hold_sync(SyncFn real_sync, int fd) {
    const char *ready = getenv("ALVOKI_CHECK_SYNC_PID");
    const char *release = getenv("ALVOKI_CHECK_SYNC_RELEASE");
    if (ready == NULL || release == NULL) return fail_sync();

    if (!same(getenv("ALVOKI_CHECK_SYNC_HOLD_MODE"), "detached")) {
        char pid[32];
        int length = snprintf(pid, sizeof(pid), "%ld\n", (long)getpid());
        wait_for_release(ready, release, pid, (size_t)length);
        return real_sync(fd);
    }

    // Keep the selected inode alive after the owner is killed. The fixture
    // child must drop the writer lock and every other inherited descriptor.
    int report[2];
    if (pipe2(report, O_CLOEXEC) < 0) return -1;
    pid_t child = fork();
    if (child < 0) {
        int error = errno;
        close(report[0]);
        close(report[1]);
        errno = error;
        return -1;
    }
    if (child == 0) {
        if (dup2(fd, STDIN_FILENO) < 0 || dup2(report[0], STDOUT_FILENO) < 0 ||
            close_range(STDERR_FILENO, UINT_MAX, 0) < 0) _exit(125);
        char pid[32];
        ssize_t length = read(STDOUT_FILENO, pid, sizeof(pid));
        if (length <= 0 || close(STDOUT_FILENO) < 0) _exit(125);
        wait_for_release(ready, release, pid, (size_t)length);
        _exit(real_sync(STDIN_FILENO) == 0 ? 0 : 125);
    }

    close(report[0]);
    char pid[32];
    int length = snprintf(pid, sizeof(pid), "%ld\n", (long)child);
    ssize_t sent = write(report[1], pid, (size_t)length);
    close(report[1]);
    int status;
    pid_t reaped;
    do {
        reaped = waitpid(child, &status, 0);
    } while (reaped < 0 && errno == EINTR);
    if (sent != length || reaped < 0 || !WIFEXITED(status) || WEXITSTATUS(status) != 0) return fail_sync();
    return 0;
}

static bool is_wal_sibling(const char *path, const char *marker) {
    const char *name = strrchr(path, '/');
    const char *marker_name = strrchr(marker, '/');
    return name != NULL && marker_name != NULL && name - path == marker_name - marker &&
        strncmp(path, marker, (size_t)(name - path)) == 0 &&
        strncmp(name + 1, "WAL-segment-", strlen("WAL-segment-")) == 0;
}

int fsync(int fd) {
    SyncFn real_sync = (SyncFn)dlsym(RTLD_NEXT, "fsync");
    if (real_sync == NULL) return fail_sync();

    const char *log = getenv("ALVOKI_CHECK_SYNC_LOG");
    const char *failure = getenv("ALVOKI_CHECK_SYNC_FAIL");
    const char *hold = getenv("ALVOKI_CHECK_SYNC_HOLD");
    if (log == NULL && failure == NULL && hold == NULL) return real_sync(fd);

    char link[64], path[PATH_MAX];
    snprintf(link, sizeof(link), "/proc/self/fd/%d", fd);
    ssize_t length = readlink(link, path, sizeof(path) - 1);
    if (length < 0 || (size_t)length == sizeof(path) - 1) return fail_sync();
    path[length] = '\0';
    log_sync(log, "", path);

    static unsigned hold_hits;
    // Both test targets are synced once during open, before the write barrier.
    if (same(path, hold) && ++hold_hits == 2) return hold_sync(real_sync, fd);

    const char *mode = getenv("ALVOKI_CHECK_SYNC_FAIL_MODE");
    if (same(mode, "second-only")) {
        // The open has already synced the WAL once. Leave the intervening
        // append unsynced and complete only the staged marker's fsync.
        if (failure != NULL && is_wal_sibling(path, failure) && access(failure, F_OK) == 0) return 0;
        if (same(path, failure)) {
            if (real_sync(fd) < 0) return -1;
            log_sync(log, "synced second target before error: ", path);
            return fail_sync();
        }
        return real_sync(fd);
    }

    static unsigned failure_hits;
    if (!same(path, failure)) return real_sync(fd);
    const char *skip_text = getenv("ALVOKI_CHECK_SYNC_SKIP");
    unsigned long skip = skip_text == NULL ? 0 : strtoul(skip_text, NULL, 10);
    if (++failure_hits <= skip || (same(mode, "before-once") && failure_hits != skip + 1))
        return real_sync(fd);
    if (same(mode, "after")) {
        if (real_sync(fd) < 0) return -1;
        log_sync(log, "synced before error: ", path);
    }
    return fail_sync();
}
