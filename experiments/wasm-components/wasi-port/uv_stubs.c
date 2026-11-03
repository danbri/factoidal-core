/* wasi-port/uv_stubs.c — the libuv functions of wasi-port/uv.h, each one
   failing with UV_ENOSYS. See the header for why. */
#include "uvonly/uv.h"
#include <string.h>
const char *uv_strerror(int err) { return strerror(-err); }
int uv_fs_stat(uv_loop_t *l, uv_fs_t *r, const char *p, uv_fs_cb cb) { (void)l; (void)p; (void)cb; memset(r, 0, sizeof *r); return UV_ENOSYS; }
int uv_fs_lstat(uv_loop_t *l, uv_fs_t *r, const char *p, uv_fs_cb cb) { return uv_fs_stat(l, r, p, cb); }
int uv_fs_link(uv_loop_t *l, uv_fs_t *r, const char *a, const char *b, uv_fs_cb cb) { (void)b; return uv_fs_stat(l, r, a, cb); }
int uv_fs_unlink(uv_loop_t *l, uv_fs_t *r, const char *p, uv_fs_cb cb) { return uv_fs_stat(l, r, p, cb); }
int uv_fs_mkstemp(uv_loop_t *l, uv_fs_t *r, const char *p, uv_fs_cb cb) { return uv_fs_stat(l, r, p, cb); }
int uv_fs_mkdtemp(uv_loop_t *l, uv_fs_t *r, const char *p, uv_fs_cb cb) { return uv_fs_stat(l, r, p, cb); }
void uv_fs_req_cleanup(uv_fs_t *r) { (void)r; }
int uv_os_tmpdir(char *b, size_t *n) { (void)b; (void)n; return UV_ENOSYS; }
