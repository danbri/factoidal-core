/* wasi-port/uv.h — the libuv declarations that Lean v4.33.1's runtime/io.cpp
   uses, for a WASI build. Not libuv: libuv has no WASI port, and its real
   header needs <netdb.h> (absent in wasip1) and <termios.h> (absent in
   wasip1 and wasip2). The functions are realised in uv_stubs.c, each one
   answering UV_ENOSYS, so IO.FS.metadata, hard links and temporary files
   fail with "function not implemented" under this build. The error codes
   are libuv's Unix values (uv/errno.h: UV__E* = -E*). */
#pragma once
#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
#define UV_VERSION_HEX 0x013000  /* the declarations follow libuv 1.48 */
#define UV_E2BIG (-E2BIG)
#define UV_EACCES (-EACCES)
#define UV_EADDRINUSE (-EADDRINUSE)
#define UV_EADDRNOTAVAIL (-EADDRNOTAVAIL)
#define UV_EAFNOSUPPORT (-EAFNOSUPPORT)
#define UV_EAGAIN (-EAGAIN)
#define UV_EBADF (-EBADF)
#define UV_EBUSY (-EBUSY)
#define UV_ECONNABORTED (-ECONNABORTED)
#define UV_ECONNREFUSED (-ECONNREFUSED)
#define UV_ECONNRESET (-ECONNRESET)
#define UV_EDESTADDRREQ (-EDESTADDRREQ)
#define UV_EEXIST (-EEXIST)
#define UV_EFAULT (-EFAULT)
#define UV_EFBIG (-EFBIG)
#define UV_EHOSTUNREACH (-EHOSTUNREACH)
#define UV_EILSEQ (-EILSEQ)
#define UV_EINTR (-EINTR)
#define UV_EINVAL (-EINVAL)
#define UV_EIO (-EIO)
#define UV_EISCONN (-EISCONN)
#define UV_EISDIR (-EISDIR)
#define UV_ELOOP (-ELOOP)
#define UV_EMFILE (-EMFILE)
#define UV_EMLINK (-EMLINK)
#define UV_EMSGSIZE (-EMSGSIZE)
#define UV_ENAMETOOLONG (-ENAMETOOLONG)
#define UV_ENETDOWN (-ENETDOWN)
#define UV_ENETUNREACH (-ENETUNREACH)
#define UV_ENFILE (-ENFILE)
#define UV_ENOBUFS (-ENOBUFS)
#define UV_ENODATA (-ENODATA)
#define UV_ENODEV (-ENODEV)
#define UV_ENOENT (-ENOENT)
#define UV_ENOMEM (-ENOMEM)
#define UV_ENOPROTOOPT (-ENOPROTOOPT)
#define UV_ENOSPC (-ENOSPC)
#define UV_ENOSYS (-ENOSYS)
#define UV_ENOTCONN (-ENOTCONN)
#define UV_ENOTDIR (-ENOTDIR)
#define UV_ENOTEMPTY (-ENOTEMPTY)
#define UV_ENOTSOCK (-ENOTSOCK)
#define UV_ENOTSUP (-ENOTSUP)
#define UV_ENOTTY (-ENOTTY)
#define UV_ENXIO (-ENXIO)
#define UV_EPERM (-EPERM)
#define UV_EPIPE (-EPIPE)
#define UV_EPROTO (-EPROTO)
#define UV_EPROTONOSUPPORT (-EPROTONOSUPPORT)
#define UV_EPROTOTYPE (-EPROTOTYPE)
#define UV_ERANGE (-ERANGE)
#define UV_EROFS (-EROFS)
#define UV_ESPIPE (-ESPIPE)
#define UV_ESRCH (-ESRCH)
#define UV_ETIMEDOUT (-ETIMEDOUT)
#define UV_ETXTBSY (-ETXTBSY)
#define UV_EXDEV (-EXDEV)
typedef struct { long tv_sec; long tv_nsec; } uv_timespec_t;
typedef struct {
  uint64_t st_dev, st_mode, st_nlink, st_uid, st_gid, st_rdev, st_ino, st_size,
           st_blksize, st_blocks, st_flags, st_gen;
  uv_timespec_t st_atim, st_mtim, st_ctim, st_birthtim;
} uv_stat_t;
typedef struct uv_loop_s uv_loop_t;
typedef struct uv_fs_s uv_fs_t;
typedef void (*uv_fs_cb)(uv_fs_t *req);
struct uv_fs_s { ptrdiff_t result; const char *path; uv_stat_t statbuf; void *ptr; };
const char *uv_strerror(int err);
int uv_fs_stat(uv_loop_t *, uv_fs_t *, const char *, uv_fs_cb);
int uv_fs_lstat(uv_loop_t *, uv_fs_t *, const char *, uv_fs_cb);
int uv_fs_link(uv_loop_t *, uv_fs_t *, const char *, const char *, uv_fs_cb);
int uv_fs_unlink(uv_loop_t *, uv_fs_t *, const char *, uv_fs_cb);
int uv_fs_mkstemp(uv_loop_t *, uv_fs_t *, const char *, uv_fs_cb);
int uv_fs_mkdtemp(uv_loop_t *, uv_fs_t *, const char *, uv_fs_cb);
void uv_fs_req_cleanup(uv_fs_t *);
int uv_os_tmpdir(char *buffer, size_t *size);
#ifdef __cplusplus
}
#endif
