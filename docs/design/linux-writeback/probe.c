#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <linux/fiemap.h>
#include <linux/fs.h>
#include <linux/kernel-page-flags.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <unistd.h>

enum { block_size = 4096, sector_size = 512 };

static void die(const char *where) {
    perror(where);
    exit(2);
}

static int openf(const char *path, int flags) {
    int fd = open(path, flags, 0600);
    if (fd < 0) die(path);
    return fd;
}

static void rw4(int fd, void *data, off_t offset, int writing) {
    ssize_t n = writing ? pwrite(fd, data, block_size, offset) : pread(fd, data, block_size, offset);
    if (n != block_size) {
        if (n >= 0) errno = EIO;
        die(writing ? "pwrite" : "pread");
    }
}

static void set_fault(uint64_t start, uint64_t sectors, int fault) {
    char cmd[1024];
    if (system("dmsetup suspend --noflush guestdisk")) exit(3);
    if (fault)
        snprintf(cmd, sizeof cmd,
            "dmsetup reload guestdisk --table '0 %" PRIu64 " linear /dev/vda 0\n%" PRIu64 " 8 error\n%" PRIu64 " %" PRIu64 " linear /dev/vda %" PRIu64 "'",
            start, start, start + 8, sectors - (start + 8), start + 8);
    else
        snprintf(cmd, sizeof cmd, "dmsetup reload guestdisk --table '0 %" PRIu64 " linear /dev/vda 0'", sectors);
    if (system(cmd) || system("dmsetup resume guestdisk")) exit(3);
}

static int result(const char *what, int ret) {
    int error = ret < 0 ? errno : 0;
    printf("%s: ret=%d errno=%d\n", what, ret, error);
    return error;
}

static void observe(const char *what, int fd, void *data, off_t offset) {
    rw4(fd, data, offset, 0);
    size_t a = 0, b = 0;
    for (int i = 0; i < block_size; i++) {
        a += ((const char *)data)[i] == 'A';
        b += ((const char *)data)[i] == 'B';
    }
    printf("%s: A=%zu B=%zu other=%zu\n", what, a, b, (size_t)block_size - a - b);
}

static void page_flags(int file) {
    void *address = mmap(NULL, block_size, PROT_READ, MAP_SHARED, file, 0);
    if (address == MAP_FAILED) die("mmap");
    unsigned first = *(volatile unsigned char *)address;
    int pages = openf("/proc/self/pagemap", O_RDONLY);
    int flags = openf("/proc/kpageflags", O_RDONLY);
    uint64_t entry = 0, bits = 0;
    off_t entry_offset = ((uintptr_t)address / block_size) * sizeof(entry);
    if (pread(pages, &entry, sizeof(entry), entry_offset) != sizeof(entry))
        die("pagemap read");
    uint64_t pfn = entry & ((UINT64_C(1) << 55) - 1);
    if (!pfn || pread(flags, &bits, sizeof(bits), pfn * sizeof(bits)) != sizeof(bits))
        die("kpageflags read");
    printf("page after failed I/O: dirty=%" PRIu64 " writeback=%" PRIu64 " first=%c\n",
        (bits >> KPF_DIRTY) & 1, (bits >> KPF_WRITEBACK) & 1, first);
    munmap(address, block_size);
    close(pages);
    close(flags);
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    int direct = strstr(argv[1], "direct") != NULL;
    int dsync = strstr(argv[1], "dsync") != NULL;
    setvbuf(stdout, NULL, _IONBF, 0);
    printf("IO_MODE=%s\n", argv[1]);
    void *data = NULL;
    if (posix_memalign(&data, block_size, block_size)) return 2;
    int backing = openf("/dev/vda", O_RDONLY | O_DIRECT);
    uint64_t size;
    if (ioctl(backing, BLKGETSIZE64, &size)) die("BLKGETSIZE64");
    uint64_t sectors = size / sector_size;
    int file = openf("/mnt/payload", O_CREAT | O_EXCL | O_RDWR);
    memset(data, 'A', block_size);
    rw4(file, data, 0, 1);
    if (fsync(file)) die("initial file fsync");
    int parent = openf("/mnt", O_RDONLY | O_DIRECTORY);
    if (fsync(parent)) die("initial directory fsync");
    struct { struct fiemap map; struct fiemap_extent extent; } ext = {0};
    ext.map.fm_length = block_size;
    ext.map.fm_extent_count = 1;
    ext.map.fm_flags = FIEMAP_FLAG_SYNC;
    if (ioctl(file, FS_IOC_FIEMAP, &ext.map)) die("fiemap");
    uint64_t physical = ext.extent.fe_physical;
    if (ext.map.fm_mapped_extents != 1 || ext.extent.fe_logical || ext.extent.fe_length < block_size ||
        physical % block_size || physical < block_size || physical > size - block_size ||
        (ext.extent.fe_flags & (FIEMAP_EXTENT_UNKNOWN | FIEMAP_EXTENT_DELALLOC |
                                FIEMAP_EXTENT_UNWRITTEN | FIEMAP_EXTENT_SHARED)))
        return 4;
    printf("TARGET_PHYSICAL=%" PRIu64 " extent_flags=%x\n", physical, ext.extent.fe_flags);
    observe("baseline backing", backing, data, physical);
    close(file);
    file = openf("/mnt/payload", O_RDWR | (direct ? O_DIRECT : 0) | (dsync ? O_DSYNC : 0));
    int buffered_reader = openf("/mnt/payload", O_RDONLY);
    int peer = openf("/mnt/payload", O_RDWR);
    set_fault(physical / sector_size, sectors, 1);
    memset(data, 'B', block_size);
    int write_err = result("writer pwrite", pwrite(file, data, block_size, 0));
    int err = result("writer first fsync", fsync(file));
    if (write_err != EIO && err != EIO) return 5;
    set_fault(physical / sector_size, sectors, 0);
    observe("cached after failure", buffered_reader, data, 0);
    if (getenv("MEASURE_PAGE_FLAGS")) page_flags(buffered_reader);
    observe("backing after failure", backing, data, physical);
    int fresh = openf("/mnt/payload", O_RDWR);
    result("writer retry fsync", fsync(file));
    result("fresh description fsync", fsync(fresh));
    result("peer opened before fault fsync", fsync(peer));
    observe("cached after retry", fresh, data, 0);
    observe("backing after retry", backing, data, physical);
    if (posix_fadvise(file, 0, block_size, POSIX_FADV_DONTNEED)) return 6;
    observe("after page eviction", fresh, data, 0);
    memset(data, 'B', block_size);
    rw4(fresh, data, 0, 1);
    if (fsync(fresh)) die("explicit rewrite fsync");
    observe("backing after rewrite", backing, data, physical);
    puts("PROBE_COMPLETE");
    return 0;
}
