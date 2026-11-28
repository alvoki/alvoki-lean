#define _GNU_SOURCE
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <dlfcn.h>
#include <unistd.h>
#include <sys/stat.h>
#include <string.h>
struct input { int fd; int failed; };
static ssize_t take(void *p, char *buf, size_t n) {
    struct input *s=p;
    off_t pos=lseek(s->fd,0,SEEK_CUR);
    if(pos==1043 && !s->failed && getenv("AUDIT_EIO")) {
        s->failed=1; errno=EIO; fputs("cookie: EIO after 1043 bytes\n",stderr); return -1;
    }
    if (pos<1024 && n>1024-pos) n=1024-pos;
    return read(s->fd,buf,n);
}
static int done(void *p) {struct input *s=p; int r=close(s->fd); free(s); return r;}
FILE *fdopen(int fd,const char *mode) {
    struct stat a,b;
    if (!fstat(fd,&a) && !stat("/workspace/work/cookie-input",&b) && a.st_dev==b.st_dev && a.st_ino==b.st_ino) {
        struct input *s=calloc(1,sizeof *s); s->fd=fd;
        return fopencookie(s,"r",(cookie_io_functions_t){.read=take,.close=done});
    }
    FILE *(*real)(int,const char*)=dlsym(RTLD_NEXT,"fdopen"); return real(fd,mode);
}
