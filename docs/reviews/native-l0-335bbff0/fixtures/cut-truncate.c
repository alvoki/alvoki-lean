#define _GNU_SOURCE
#include <unistd.h>
#include <dlfcn.h>
int ftruncate(int fd, off_t size) {
  int (*next)(int,off_t) = dlsym(RTLD_NEXT, "ftruncate");
  int res = next(fd,size);
  if (res == 0) _exit(75);
  return res;
}
int ftruncate64(int fd, off64_t size) {
  int (*next)(int,off64_t) = dlsym(RTLD_NEXT, "ftruncate64");
  int res = next(fd,size);
  if (res == 0) _exit(75);
  return res;
}
