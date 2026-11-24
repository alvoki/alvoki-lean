#define _GNU_SOURCE
#include <dirent.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
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

int open(const char *path, int flags, ...) {
    int (*real_open)(const char *, int, ...) = dlsym(RTLD_NEXT, "open");
    if (real_open == NULL) return fail_sync();
    if ((flags & O_ACCMODE) == O_RDONLY && same(path, getenv("ALVOKI_CHECK_READ_OPEN_FAIL"))) {
        errno = EACCES;
        return -1;
    }
    if ((flags & O_CREAT) || (flags & O_TMPFILE) == O_TMPFILE) {
        va_list args;
        va_start(args, flags);
        mode_t mode = va_arg(args, mode_t);
        va_end(args);
        return real_open(path, flags, mode);
    }
    return real_open(path, flags);
}

static _Noreturn void exit_with_inherited_lock(int fd) {
    int flags = fcntl(fd, F_GETFD);
    if (fd <= STDERR_FILENO || flags < 0 || !(flags & FD_CLOEXEC)) _exit(125);

    pid_t child = fork();
    if (child < 0) _exit(125);
    if (child == 0) {
        // Lean may have other threads. Only async-signal-safe operations
        // run here, and the inherited lock descriptor is left untouched.
        char signal;
        ssize_t count;
        do count = read(STDIN_FILENO, &signal, 1); while (count < 0 && errno == EINTR);
        if (count != 1 || signal != 'E') _exit(125);
        // The first echo proves exec reached its new image. The command pipe
        // stays open so the test can reopen while this image is still alive.
        char *const args[] = {"cat", NULL};
        char *const env[] = {NULL};
        execve("/bin/cat", args, env);
        _exit(125);
    }

    int32_t notice[] = {child, fd};
    const char *bytes = (const char *)notice;
    size_t left = sizeof(notice);
    while (left > 0) {
        ssize_t sent = write(STDOUT_FILENO, bytes, left);
        if (sent < 0 && errno == EINTR) continue;
        if (sent <= 0) _exit(125);
        bytes += sent;
        left -= (size_t)sent;
    }
    // Skip explicit LOCK_UN. Process exit drops only the parent's reference.
    _exit(0);
}

int flock(int fd, int operation) {
    int (*real_flock)(int, int) = dlsym(RTLD_NEXT, "flock");
    if (real_flock == NULL) return fail_sync();
    const char *target = getenv("ALVOKI_CHECK_FORK_LOCK");
    if (target != NULL && operation == LOCK_UN) {
        struct stat lock, held;
        if (stat(target, &lock) < 0 || fstat(fd, &held) < 0) _exit(125);
        if (held.st_dev == lock.st_dev && held.st_ino == lock.st_ino) exit_with_inherited_lock(fd);
    }
    return real_flock(fd, operation);
}

static DIR *partial_directory;
static bool partial_delivered;

DIR *opendir(const char *path) {
    DIR *(*real_open)(const char *) = dlsym(RTLD_NEXT, "opendir");
    if (real_open == NULL) {
        errno = EIO;
        return NULL;
    }
    DIR *directory = real_open(path);
    if (directory != NULL && same(path, getenv("ALVOKI_CHECK_READDIR_DIR"))) {
        static unsigned long matched;
        const char *skip = getenv("ALVOKI_CHECK_READDIR_SKIP");
        if (matched++ == (skip == NULL ? 0 : strtoul(skip, NULL, 10))) {
            partial_directory = directory;
            partial_delivered = false;
        }
    }
    return directory;
}

struct dirent *readdir(DIR *directory) {
    int incoming = errno;
    struct dirent *(*real_read)(DIR *) = dlsym(RTLD_NEXT, "readdir");
    if (real_read == NULL) {
        errno = EIO;
        return NULL;
    }
    errno = incoming;
    if (directory != partial_directory) return real_read(directory);

    const char *log = getenv("ALVOKI_CHECK_READDIR_LOG");
    const char *partial = getenv("ALVOKI_CHECK_READDIR_PARTIAL");
    if (!partial_delivered) {
        // Directory order is unspecified. Deliver the requested entry first
        // so the interrupted scan deterministically hides the other names.
        struct dirent *entry;
        while ((entry = real_read(directory)) != NULL) {
            if (same(entry->d_name, partial)) {
                partial_delivered = true;
                log_sync(log, "listed before error: ", entry->d_name);
                return entry;
            }
        }
    }
    partial_directory = NULL;
    log_sync(log, "readdir error: ", partial == NULL ? "" : partial);
    errno = EIO;
    return NULL;
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

static _Noreturn void detached_sync(SyncFn real_sync, int fd, const char *identity) {
    struct stat status;
    if ((identity != NULL && fstat(fd, &status) < 0) || real_sync(fd) < 0) _exit(125);
    if (identity != NULL) {
        // Record the object of the descriptor passed to the successful fsync.
        uint64_t object[] = {(uint64_t)status.st_dev, (uint64_t)status.st_ino};
        int file = open(identity, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
        if (file < 0 || write(file, object, sizeof(object)) != (ssize_t)sizeof(object) ||
            close(file) < 0) _exit(125);
    }
    _exit(0);
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
    const char *identity = getenv("ALVOKI_CHECK_SYNC_OBJECT");
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
        detached_sync(real_sync, STDIN_FILENO, identity);
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
