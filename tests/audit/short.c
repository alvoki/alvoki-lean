#define _GNU_SOURCE
#include <stdio.h>
#include <errno.h>
#include <sys/stat.h>
#include <string.h>
#include <stdlib.h>
#include <dlfcn.h>
static FILE *errored;
static int calls=0;
size_t fread(void *buf,size_t sz,size_t n,FILE *fp) {
  size_t (*real)(void*,size_t,size_t,FILE*)=dlsym(RTLD_NEXT,"fread");
  struct stat a,b;
  const char *path=getenv("AUDIT_INODE");
  if(path && sz==1 && n==1024 && !stat(path,&a) && !fstat(fileno(fp),&b) &&
      a.st_dev==b.st_dev && a.st_ino==b.st_ino && ++calls==2) {
    size_t k=real(buf,1,19,fp); errored=fp; errno=EIO;
    fprintf(stderr,"injected positive short read (%zu) + EIO\n",k); return k;
  }
  return real(buf,sz,n,fp);
}
int ferror(FILE *fp) {
  int (*real)(FILE*)=dlsym(RTLD_NEXT,"ferror");
  if(errored && fp==errored) {errored=NULL;return 1;} return real(fp);
}
