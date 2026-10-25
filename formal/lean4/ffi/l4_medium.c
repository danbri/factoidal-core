/* Host reads of the storage-medium interface (Wasm/MediumHost.lean,
 * L4Factoidal/Storage/Medium.lean; https://github.com/danbri/factoidal/issues/1010
 * KR1).  It owns no format: Lean builds every object name and decodes and
 * checks every byte.  This file only moves bytes.
 *
 *   l4_medium_read(root, name, off, len) : IO ByteArray   (empty: no such bytes)
 *   l4_medium_size(root, name)           : IO UInt64      (UINT64_MAX: absent)
 *
 * Under Emscripten the bodies are EM_JS thunks onto
 * globalThis.__factoidalMediumRead(root, name, off, len) -> Uint8Array | null
 * and globalThis.__factoidalMediumSize(root, name) -> number (-1: absent),
 * installed by the JavaScript host (npm/factoidal/lib/sbm11-hosts.mjs).  The
 * read is two steps: the first thunk asks the host and keeps the answer, the
 * second copies it into the Lean byte array that C allocated for it, so the
 * bytes cross once and no JavaScript code holds a heap pointer across an
 * allocation (ALLOW_MEMORY_GROWTH replaces the heap buffer).
 *
 * On every other target the store root is a directory and the object is the
 * file root/name, read with open, fstat and pread (no shared file cursor).
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static lean_obj_res l4_medium_empty(void) { return lean_alloc_sarray(1, 0, 0); }

#ifdef __EMSCRIPTEN__
#include <emscripten.h>

EM_JS(double, l4_medium_read_ask_js, (const char *root, const char *name, double off, double len), {
  var host = globalThis.__factoidalMediumRead;
  globalThis.__factoidalMediumLast = null;
  if (typeof host !== 'function') return -1;
  var out;
  try {
    out = host(UTF8ToString(root), UTF8ToString(name), off, len);
  } catch (e) {
    return -1;
  }
  if (!out || typeof out.length !== 'number') return -1;
  globalThis.__factoidalMediumLast = out;
  return out.length;
});

EM_JS(void, l4_medium_read_take_js, (uint8_t *dst), {
  var out = globalThis.__factoidalMediumLast;
  globalThis.__factoidalMediumLast = null;
  if (out && dst) HEAPU8.set(out, dst);
});

EM_JS(double, l4_medium_size_js, (const char *root, const char *name), {
  var host = globalThis.__factoidalMediumSize;
  if (typeof host !== 'function') return -1;
  var n;
  try {
    n = host(UTF8ToString(root), UTF8ToString(name));
  } catch (e) {
    return -1;
  }
  if (typeof n !== 'number' || !(n >= 0)) return -1;
  return n;
});

LEAN_EXPORT lean_obj_res l4_medium_read(b_lean_obj_arg root, b_lean_obj_arg name, uint64_t off,
                                        uint64_t len, lean_obj_arg world) {
  (void)world;
  double n = l4_medium_read_ask_js(lean_string_cstr(root), lean_string_cstr(name), (double)off, (double)len);
  if (n < 0 || n != (double)len || len > SIZE_MAX) {
    l4_medium_read_take_js(0);
    return lean_io_result_mk_ok(l4_medium_empty());
  }
  lean_obj_res out = lean_alloc_sarray(1, (size_t)len, (size_t)len);
  if (len > 0) l4_medium_read_take_js(lean_sarray_cptr(out));
  else l4_medium_read_take_js(0);
  return lean_io_result_mk_ok(out);
}

LEAN_EXPORT lean_obj_res l4_medium_size(b_lean_obj_arg root, b_lean_obj_arg name, lean_obj_arg world) {
  (void)world;
  double n = l4_medium_size_js(lean_string_cstr(root), lean_string_cstr(name));
  uint64_t r = (n < 0 || n >= 18446744073709551615.0) ? UINT64_MAX : (uint64_t)n;
  return lean_io_result_mk_ok(lean_box_uint64(r));
}

#else
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

/* root + "/" + name, or NULL when it does not fit. */
static char *l4_medium_path(b_lean_obj_arg root, b_lean_obj_arg name) {
  const char *r = lean_string_cstr(root);
  const char *n = lean_string_cstr(name);
  size_t lr = strlen(r), ln = strlen(n);
  char *p = malloc(lr + ln + 2);
  if (!p) return 0;
  memcpy(p, r, lr);
  p[lr] = '/';
  memcpy(p + lr + 1, n, ln);
  p[lr + 1 + ln] = 0;
  return p;
}

LEAN_EXPORT lean_obj_res l4_medium_read(b_lean_obj_arg root, b_lean_obj_arg name, uint64_t off,
                                        uint64_t len, lean_obj_arg world) {
  (void)world;
  if (len > SIZE_MAX || off > INT64_MAX || len > (uint64_t)INT64_MAX - off)
    return lean_io_result_mk_ok(l4_medium_empty());
  char *path = l4_medium_path(root, name);
  if (!path) return lean_io_result_mk_ok(l4_medium_empty());
  int fd = open(path, O_RDONLY);
  free(path);
  if (fd < 0) return lean_io_result_mk_ok(l4_medium_empty());
  struct stat st;
  if (fstat(fd, &st) != 0 || st.st_size < 0 || off > (uint64_t)st.st_size ||
      len > (uint64_t)st.st_size - off) {
    close(fd);
    return lean_io_result_mk_ok(l4_medium_empty());
  }
  lean_obj_res out = lean_alloc_sarray(1, (size_t)len, (size_t)len);
  size_t done = 0;
  while (done < (size_t)len) {
    ssize_t k = pread(fd, lean_sarray_cptr(out) + done, (size_t)len - done, (off_t)off + (off_t)done);
    if (k > 0) { done += (size_t)k; continue; }
    if (k < 0 && errno == EINTR) continue;
    close(fd);
    lean_dec(out);
    return lean_io_result_mk_ok(l4_medium_empty());
  }
  close(fd);
  return lean_io_result_mk_ok(out);
}

LEAN_EXPORT lean_obj_res l4_medium_size(b_lean_obj_arg root, b_lean_obj_arg name, lean_obj_arg world) {
  (void)world;
  char *path = l4_medium_path(root, name);
  if (!path) return lean_io_result_mk_ok(lean_box_uint64(UINT64_MAX));
  struct stat st;
  int rc = stat(path, &st);
  free(path);
  if (rc != 0 || !S_ISREG(st.st_mode) || st.st_size < 0)
    return lean_io_result_mk_ok(lean_box_uint64(UINT64_MAX));
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)st.st_size));
}
#endif
