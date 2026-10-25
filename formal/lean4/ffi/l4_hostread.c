/* Positioned reads of a store whose bytes a host supplies: the SBM11 session
 * of the wasm module (Wasm/HostRead.lean, L4Factoidal/Storage/Sbm11/
 * HostSession.lean; https://github.com/danbri/factoidal/issues/1009 KR1).
 * It owns no RDF, SPARQL or format logic: Lean names the file of the
 * generation, the offset and the length, and checks every answer against
 * the manifest.  This file only moves bytes.
 *
 *   l4_host_read_at(source, file, off, len) : IO ByteArray  -- len bytes or an IO error
 *   l4_host_size(source, file)               : IO UInt64     -- UINT64_MAX: no such file
 *
 * `source` is a string the caller chose when it opened the store.
 *
 * No world argument: the Lean 4.33 code generator erases the IO world
 * token, so the generated call is l4_host_read_at(source, file, off, len)
 * and l4_host_size(source, file).  A C definition with one more parameter
 * links natively and runs, but wasm-ld replaces a call whose signature
 * differs from the definition with an `unreachable` stub: sbm11Open
 * trapped on its first host call (https://github.com/danbri/factoidal/issues/1009).
 * build-wasm.sh now fails the link on such a mismatch.
 *
 * Under Emscripten the bodies are EM_JS thunks onto
 * globalThis.__factoidalReadAt(source, file, off, len) -> Uint8Array and
 * globalThis.__factoidalFileSize(source, file) -> number | null, which the
 * JavaScript host installs (npm/factoidal/lib/sbm11.mjs, Node reader lib/sbm11-node.mjs; a
 * browser worker over OPFS FileSystemSyncAccessHandle).  On every other
 * target `source` is a directory and the read is one pread of
 * source/file.
 */
#include <lean/lean.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static lean_obj_res l4_hr_error(const char *msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

#ifdef __EMSCRIPTEN__
#include <emscripten.h>

/* 1: `len` bytes written at `dst`; 0: no host, an exception, or a short answer. */
EM_JS(int, l4_host_read_js, (const char *src, const char *file, double off, double len, uint8_t *dst), {
  var bridge = globalThis.__factoidalReadAt;
  if (typeof bridge !== 'function') return 0;
  var out;
  try {
    out = bridge(UTF8ToString(src), UTF8ToString(file), off, len);
  } catch (e) {
    return 0;
  }
  if (!(out instanceof Uint8Array) || out.length !== len) return 0;
  HEAPU8.set(out, dst);
  return 1;
});

/* The size, or -1: no host, an exception, or no such file. */
EM_JS(double, l4_host_size_js, (const char *src, const char *file), {
  var bridge = globalThis.__factoidalFileSize;
  if (typeof bridge !== 'function') return -1;
  var n;
  try {
    n = bridge(UTF8ToString(src), UTF8ToString(file));
  } catch (e) {
    return -1;
  }
  if (typeof n !== 'number' || !(n >= 0)) return -1;
  return n;
});

LEAN_EXPORT lean_obj_res l4_host_read_at(b_lean_obj_arg source, b_lean_obj_arg file,
                                         uint64_t off, uint64_t len) {
  if (len > (uint64_t)SIZE_MAX) return l4_hr_error("host read: length too large");
  lean_obj_res out = lean_alloc_sarray(1, (size_t)len, (size_t)len);
  if (len > 0 &&
      !l4_host_read_js(lean_string_cstr(source), lean_string_cstr(file), (double)off, (double)len,
                       lean_sarray_cptr(out))) {
    lean_dec(out);
    return l4_hr_error("host read: the host gave no bytes (is globalThis.__factoidalReadAt installed?)");
  }
  return lean_io_result_mk_ok(out);
}

LEAN_EXPORT lean_obj_res l4_host_size(b_lean_obj_arg source, b_lean_obj_arg file) {
  double n = l4_host_size_js(lean_string_cstr(source), lean_string_cstr(file));
  uint64_t r = n < 0 ? UINT64_MAX : (uint64_t)n;
  return lean_io_result_mk_ok(lean_box_uint64(r));
}

#else
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

static char *l4_hr_path(b_lean_obj_arg source, b_lean_obj_arg file) {
  const char *s = lean_string_cstr(source);
  const char *f = lean_string_cstr(file);
  size_t n = strlen(s) + strlen(f) + 2;
  char *p = malloc(n);
  if (p) snprintf(p, n, "%s/%s", s, f);
  return p;
}

LEAN_EXPORT lean_obj_res l4_host_read_at(b_lean_obj_arg source, b_lean_obj_arg file,
                                         uint64_t off, uint64_t len) {
  if (len > (uint64_t)SIZE_MAX || off > (uint64_t)INT64_MAX) return l4_hr_error("host read: offset or length too large");
  char *path = l4_hr_path(source, file);
  if (!path) return l4_hr_error("host read: out of memory");
  int fd = open(path, O_RDONLY);
  free(path);
  if (fd < 0) return l4_hr_error("host read: cannot open the file");
  lean_obj_res out = lean_alloc_sarray(1, (size_t)len, (size_t)len);
  size_t done = 0;
  while (done < (size_t)len) {
    ssize_t n = pread(fd, lean_sarray_cptr(out) + done, (size_t)len - done, (off_t)off + (off_t)done);
    if (n > 0) { done += (size_t)n; continue; }
    if (n < 0 && errno == EINTR) continue;
    close(fd);
    lean_dec(out);
    return l4_hr_error("host read: short read");
  }
  close(fd);
  return lean_io_result_mk_ok(out);
}

LEAN_EXPORT lean_obj_res l4_host_size(b_lean_obj_arg source, b_lean_obj_arg file) {
  char *path = l4_hr_path(source, file);
  uint64_t r = UINT64_MAX;
  struct stat st;
  if (path && stat(path, &st) == 0 && S_ISREG(st.st_mode) && st.st_size >= 0) r = (uint64_t)st.st_size;
  free(path);
  return lean_io_result_mk_ok(lean_box_uint64(r));
}
#endif
