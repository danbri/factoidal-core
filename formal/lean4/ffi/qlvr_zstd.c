/* Optional libzstd call-out for the QLever reader's measurements
 * (Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).
 *
 * The reference zstd decoder is the pure Lean one (L4Factoidal.Codec.Zstd).
 * This file lets the `l4qlvr` harness run the same column frames through
 * libzstd, so that the cost of the Lean decoder can be measured against the
 * C library on the same data and in the same process. It owns no format
 * logic: Lean gives a frame and the expected output size, and checks the
 * size of what comes back.
 *
 * libzstd is loaded with dlopen at the first call, so the build needs no zstd
 * headers or link flags, and a host without libzstd still builds and runs:
 * `l4_zstd_available` then answers false and the harness keeps the Lean
 * decoder. Not linked by the WASM build. */
#include <lean/lean.h>
#include <dlfcn.h>
#include <stddef.h>
#include <stdint.h>

typedef size_t (*l4_zstd_dec_fn)(void *, size_t, const void *, size_t);
typedef unsigned (*l4_zstd_iserr_fn)(size_t);

static l4_zstd_dec_fn l4_zstd_dec;
static l4_zstd_iserr_fn l4_zstd_iserr;
static int l4_zstd_tried;

static int l4_zstd_load(void) {
  if (!l4_zstd_tried) {
    l4_zstd_tried = 1;
    void *h = dlopen("libzstd.so.1", RTLD_NOW | RTLD_LOCAL);
    if (!h) h = dlopen("libzstd.so", RTLD_NOW | RTLD_LOCAL);
    if (h) {
      l4_zstd_dec = (l4_zstd_dec_fn)dlsym(h, "ZSTD_decompress");
      l4_zstd_iserr = (l4_zstd_iserr_fn)dlsym(h, "ZSTD_isError");
    }
  }
  return l4_zstd_dec != NULL && l4_zstd_iserr != NULL;
}

LEAN_EXPORT lean_obj_res l4_zstd_available(lean_obj_arg world) {
  (void)world;
  return lean_io_result_mk_ok(lean_box(l4_zstd_load() ? 1 : 0));
}

/* Decompress `src` (one or more frames) into exactly `size` bytes. Any
 * failure (no libzstd, a libzstd error, a different output size) gives an
 * empty array; Lean compares the size and reports the failure. */
LEAN_EXPORT lean_obj_res l4_zstd_decompress(b_lean_obj_arg src, uint64_t size,
                                            lean_obj_arg world) {
  (void)world;
  if (!l4_zstd_load() || size > (uint64_t)SIZE_MAX || size == 0)
    return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
  lean_obj_res out = lean_alloc_sarray(1, (size_t)size, (size_t)size);
  size_t r = l4_zstd_dec(lean_sarray_cptr(out), (size_t)size,
                         lean_sarray_cptr(src), lean_sarray_size(src));
  if (l4_zstd_iserr(r) || r != (size_t)size) {
    lean_dec(out);
    return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
  }
  return lean_io_result_mk_ok(out);
}
