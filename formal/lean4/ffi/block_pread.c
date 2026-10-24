/* POSIX positioned-read adapter for the native IBK2 executable probe.
 * It owns no RDF/SPARQL logic: Lean supplies checked offset/length plans and
 * rejects an empty/short result.  This module is intentionally not linked by
 * the WASM build. */
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

static lean_obj_res l4_empty_bytes(void) { return lean_alloc_sarray(1, 0, 0); }

LEAN_EXPORT lean_obj_res l4_block_pread(b_lean_obj_arg path, uint64_t offset,
                                        uint64_t length, lean_obj_arg world) {
  (void)world;
  if (length > SIZE_MAX || offset > INT64_MAX ||
      length > (uint64_t)INT64_MAX - offset + 1)
    return lean_io_result_mk_ok(l4_empty_bytes());
  int fd = open(lean_string_cstr(path), O_RDONLY);
  if (fd < 0) return lean_io_result_mk_ok(l4_empty_bytes());
  struct stat st;
  if (fstat(fd, &st) != 0 || st.st_size < 0 ||
      offset > (uint64_t)st.st_size || length > (uint64_t)st.st_size - offset) {
    close(fd);
    return lean_io_result_mk_ok(l4_empty_bytes());
  }
  lean_obj_res out = lean_alloc_sarray(1, (size_t)length, (size_t)length);
  size_t done = 0;
  while (done < (size_t)length) {
    ssize_t n = pread(fd, lean_sarray_cptr(out) + done, (size_t)length - done,
                      (off_t)offset + (off_t)done);
    if (n > 0) { done += (size_t)n; continue; }
    if (n < 0 && errno == EINTR) continue;
    close(fd); lean_dec(out); return lean_io_result_mk_ok(l4_empty_bytes());
  }
  close(fd);
  return lean_io_result_mk_ok(out);
}

/* An open file for positioned reads (issue 961, stage 1n of
 * docs/designissues/2026-10-12-parallel-block-scans.md). `l4_block_pread`
 * opens, stats and closes the file on every read; a session that reads many
 * blocks of one file keeps one of these per file instead. The descriptor and
 * the file length are read once, at open; the files of an SBM11 generation do
 * not change after activation. `pread` does not move a shared file offset, so
 * several threads may read through one object. The descriptor is closed when
 * Lean frees the object (the finalizer). A file that does not open gives an
 * object with fd -1, whose reads give an empty array, as a failed
 * `l4_block_pread` does. */
#include <pthread.h>
typedef struct {
  int fd;
  uint64_t size;
} l4_block_file;

static void l4_block_file_finalize(void *p) {
  l4_block_file *f = (l4_block_file *)p;
  if (f->fd >= 0) close(f->fd);
  free(f);
}

static void l4_block_file_foreach(void *p, b_lean_obj_arg fn) {
  (void)p;
  (void)fn;
}

static lean_external_class *l4_block_file_class = NULL;
static pthread_once_t l4_block_file_once = PTHREAD_ONCE_INIT;
static void l4_block_file_register(void) {
  l4_block_file_class =
      lean_register_external_class(l4_block_file_finalize, l4_block_file_foreach);
}

LEAN_EXPORT lean_obj_res l4_block_file_open(b_lean_obj_arg path,
                                            lean_obj_arg world) {
  (void)world;
  pthread_once(&l4_block_file_once, l4_block_file_register);
  l4_block_file *f = (l4_block_file *)malloc(sizeof(l4_block_file));
  if (!f) return lean_io_result_mk_error(lean_mk_io_user_error(
      lean_mk_string("l4_block_file_open: out of memory")));
  f->fd = open(lean_string_cstr(path), O_RDONLY | O_CLOEXEC);
  f->size = 0;
  struct stat st;
  if (f->fd >= 0 && (fstat(f->fd, &st) != 0 || st.st_size < 0)) {
    close(f->fd);
    f->fd = -1;
  }
  if (f->fd >= 0) f->size = (uint64_t)st.st_size;
  return lean_io_result_mk_ok(lean_alloc_external(l4_block_file_class, f));
}

/* Bytes [offset, offset + length) of an open file, or an empty array when
 * the file did not open, the range is past its length at open, or a read
 * fails or is short (the contract of `l4_block_pread`). */
LEAN_EXPORT lean_obj_res l4_block_file_pread(b_lean_obj_arg file,
                                             uint64_t offset, uint64_t length,
                                             lean_obj_arg world) {
  (void)world;
  l4_block_file *f = (l4_block_file *)lean_get_external_data(file);
  if (f->fd < 0 || length > SIZE_MAX || offset > INT64_MAX ||
      length > (uint64_t)INT64_MAX - offset + 1 || offset > f->size ||
      length > f->size - offset)
    return lean_io_result_mk_ok(l4_empty_bytes());
  lean_obj_res out = lean_alloc_sarray(1, (size_t)length, (size_t)length);
  size_t done = 0;
  while (done < (size_t)length) {
    ssize_t n = pread(f->fd, lean_sarray_cptr(out) + done,
                      (size_t)length - done, (off_t)offset + (off_t)done);
    if (n > 0) { done += (size_t)n; continue; }
    if (n < 0 && errno == EINTR) continue;
    lean_dec(out);
    return lean_io_result_mk_ok(l4_empty_bytes());
  }
  return lean_io_result_mk_ok(out);
}

/* Compare-and-append is the multi-writer form used by the DLOG host. The
 * caller parsed a particular complete byte sequence and supplies its length;
 * under an exclusive advisory lock we append only if the file still has that
 * length. A concurrent winner makes this return false, so Lean reloads the
 * committed sequence, allocates a fresh sequence number, and retries. */
LEAN_EXPORT lean_obj_res l4_delta_log_append_sync_at_size(
    b_lean_obj_arg path, uint64_t expected_size, b_lean_obj_arg bytes,
    lean_obj_arg world) {
  (void)world;
  int ok = 0;
  int fd = open(lean_string_cstr(path), O_WRONLY | O_CREAT | O_APPEND, 0644);
  if (fd < 0) return lean_io_result_mk_ok(lean_box(0));
  if (flock(fd, LOCK_EX) != 0) { close(fd); return lean_io_result_mk_ok(lean_box(0)); }
  struct stat st;
  if (fstat(fd, &st) == 0 && st.st_size >= 0 &&
      (uint64_t)st.st_size == expected_size) {
    size_t total = lean_sarray_size(bytes);
    size_t done = 0;
    ok = 1;
    while (done < total) {
      ssize_t n = write(fd, lean_sarray_cptr(bytes) + done, total - done);
      if (n > 0) { done += (size_t)n; continue; }
      if (n < 0 && errno == EINTR) continue;
      ok = 0;
      break;
    }
    if (ok && fsync(fd) != 0) ok = 0;
  }
  flock(fd, LOCK_UN);
  if (close(fd) != 0) ok = 0;
  return lean_io_result_mk_ok(lean_box(ok));
}

/* In-place counterpart of the compare-and-append: overwrite `bytes` at
 * `offset`, inside the file, only if the file still has `expected_size`
 * bytes, under the same exclusive advisory lock, then fsync. The DLOG writer
 * uses it to set the header version to 2 (four bytes at offset 4) before it
 * appends the first batch that holds an RDF 1.2 term
 * (https://github.com/danbri/factoidal/issues/792 item 1). The file size
 * does not change, so a concurrent compare-and-append is not affected. */
LEAN_EXPORT lean_obj_res l4_delta_log_write_at_size(
    b_lean_obj_arg path, uint64_t expected_size, uint64_t offset,
    b_lean_obj_arg bytes, lean_obj_arg world) {
  (void)world;
  int ok = 0;
  size_t total = lean_sarray_size(bytes);
  if (offset > (uint64_t)INT64_MAX || (uint64_t)total > expected_size ||
      offset > expected_size - (uint64_t)total)
    return lean_io_result_mk_ok(lean_box(0));
  int fd = open(lean_string_cstr(path), O_WRONLY);
  if (fd < 0) return lean_io_result_mk_ok(lean_box(0));
  if (flock(fd, LOCK_EX) != 0) { close(fd); return lean_io_result_mk_ok(lean_box(0)); }
  struct stat st;
  if (fstat(fd, &st) == 0 && st.st_size >= 0 &&
      (uint64_t)st.st_size == expected_size) {
    size_t done = 0;
    ok = 1;
    while (done < total) {
      ssize_t n = pwrite(fd, lean_sarray_cptr(bytes) + done, total - done,
                         (off_t)offset + (off_t)done);
      if (n > 0) { done += (size_t)n; continue; }
      if (n < 0 && errno == EINTR) continue;
      ok = 0;
      break;
    }
    if (ok && fsync(fd) != 0) ok = 0;
  }
  flock(fd, LOCK_UN);
  if (close(fd) != 0) ok = 0;
  return lean_io_result_mk_ok(lean_box(ok));
}

/* Sync the directory entry changed by rename.  Without this second sync a
 * successful activation is atomic for concurrent readers, but can still be
 * lost after a power failure before the filesystem persists the rename. */
static int l4_fsync_parent_dir(const char *path) {
  char *parent = strdup(path);
  if (!parent) return -1;
  char *slash = strrchr(parent, '/');
  if (slash == NULL) {
    free(parent);
    parent = strdup(".");
    if (!parent) return -1;
  } else if (slash == parent) {
    slash[1] = '\0'; /* filesystem root */
  } else {
    *slash = '\0';
  }
  int fd = open(parent, O_RDONLY);
  free(parent);
  if (fd < 0) return -1;
  int result = fsync(fd);
  int close_result = close(fd);
  return result == 0 && close_result == 0 ? 0 : -1;
}

/* Atomically replace a small control file. The new bytes and the parent
 * directory entry are fsynced around rename, so a successful result means
 * readers see a whole pointer and the activation survives normal crash
 * recovery. */
LEAN_EXPORT lean_obj_res l4_atomic_replace_file_sync(b_lean_obj_arg path,
                                                      b_lean_obj_arg bytes,
                                                      lean_obj_arg world) {
  (void)world;
  const char *dst = lean_string_cstr(path);
  size_t name_len = strlen(dst);
  const char suffix[] = ".tmp.XXXXXX";
  char *tmp = (char *)malloc(name_len + sizeof(suffix));
  if (!tmp) return lean_io_result_mk_ok(lean_box(0));
  memcpy(tmp, dst, name_len);
  memcpy(tmp + name_len, suffix, sizeof(suffix));
  int fd = mkstemp(tmp);
  int ok = fd >= 0;
  if (ok) {
    size_t total = lean_sarray_size(bytes);
    size_t done = 0;
    while (done < total) {
      ssize_t n = write(fd, lean_sarray_cptr(bytes) + done, total - done);
      if (n > 0) { done += (size_t)n; continue; }
      if (n < 0 && errno == EINTR) continue;
      ok = 0;
      break;
    }
    if (ok && fsync(fd) != 0) ok = 0;
    if (close(fd) != 0) ok = 0;
    if (ok && rename(tmp, dst) != 0) ok = 0;
    if (ok && l4_fsync_parent_dir(dst) != 0) ok = 0;
    if (!ok) unlink(tmp);
  }
  free(tmp);
  return lean_io_result_mk_ok(lean_box(ok));
}

/* Not for main without the owner's approval (issue 961, stage 1i of
 * docs/designissues/2026-10-12-parallel-block-scans.md): transparent huge
 * pages off for this process. mimalloc calls madvise(MADV_HUGEPAGE) on its
 * memory; without huge pages each thread's heap grows in 4 KB pages, and the
 * peak RSS of `l4sbm11 query --threads 4` is 17 to 31 MB smaller. Returns 0
 * on success, -1 otherwise (and on a system without the call). */
#if defined(__linux__)
#include <sys/prctl.h>
#endif
LEAN_EXPORT lean_obj_res l4_thp_disable(lean_obj_arg world) {
  (void)world;
#if defined(__linux__) && defined(PR_SET_THP_DISABLE)
  int r = prctl(PR_SET_THP_DISABLE, 1, 0, 0, 0);
#else
  int r = -1;
#endif
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)(int32_t)r));
}
