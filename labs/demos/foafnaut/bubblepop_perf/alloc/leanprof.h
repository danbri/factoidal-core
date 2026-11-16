/* leanprof.h: count allocations, reference-count operations and copied bytes of Lean-generated C,
   per C function and call site. Force-include it (clang -include leanprof.h) when compiling the
   generated .c files of the modules to measure; link leanprof.c. Counts only code compiled this way:
   allocations inside the Lean runtime and the precompiled Init/Std libraries are seen only through
   the wrapped entry points below. Not thread safe (one interpreter thread). */
#ifndef LEANPROF_H
#define LEANPROF_H
#include <lean/lean.h>
typedef struct lp_site { const char * fn; const char * kind; int tag, nobj, ssz; uint64_t n, bytes; struct lp_site * next; int reg; int line; } lp_site;
void lp_register(lp_site * s);
#define LP_S(kind_) ({ static lp_site s_ = { __func__, kind_, -1, -1, -1, 0, 0, 0, 0, __LINE__ }; &s_; })
static inline void lp_hit(lp_site * s, uint64_t bytes) { if (!s->reg) lp_register(s); s->n++; s->bytes += bytes; }
static inline uint64_t lp_al8(uint64_t x) { return (x + 7) & ~(uint64_t)7; }

/* number classes: what doubles are stored in boxed values (ctor float fields, boxed floats) and in float arrays */
extern uint64_t lp_numclass[2][8];
static inline void lp_num(int where, double v) {
  int c;
  if (v != v) c = 6;                                   /* NaN */
  else if (v == 0.0) c = (1.0 / v < 0) ? 5 : 0;        /* -0 : +0 */
  else if (v == (double)(int32_t)v) { int32_t i = (int32_t)v; c = (i >= -(1 << 28) && i < (1 << 28)) ? ((i >= 0 && i < 256) ? 1 : 2) : 3; }  /* small 0..255, int29, int32 */
  else if (v - v != 0.0) c = 6;                        /* infinity: counted with NaN */
  else if (v == __builtin_floor(v) && v > -9007199254740992.0 && v < 9007199254740992.0) c = 4;  /* integer beyond int32 */
  else c = 7;                                          /* fraction */
  lp_numclass[where][c]++;
}
static inline void lp_ctor_set_float(lean_object * o, unsigned off, double v) { lp_num(0, v); lean_ctor_set_float(o, off, v); }
static inline lean_object * lp_alloc_ctor(unsigned tag, unsigned n, unsigned ssz, lp_site * s) {
  if (!s->reg) { s->tag = tag; s->nobj = n; s->ssz = ssz; }
  lp_hit(s, lp_al8(8 + 8 * (uint64_t)n + ssz)); return lean_alloc_ctor(tag, n, ssz); }
static inline lean_object * lp_alloc_closure(void * f, unsigned arity, unsigned nfixed, lp_site * s) {
  if (!s->reg) { s->nobj = nfixed; }
  lp_hit(s, 24 + 8 * (uint64_t)nfixed); return lean_alloc_closure(f, arity, nfixed); }
static inline lean_object * lp_box_float(double v, lp_site * s) { lp_num(0, v); lp_hit(s, 16); return lean_box_float(v); }
static inline lean_object * lp_box_uint64(uint64_t v, lp_site * s) { lp_hit(s, 16); return lean_box_uint64(v); }
static inline void lp_inc(lean_object * o, lp_site * s) { if (!lean_is_scalar(o)) { lp_hit(s, 0); lean_inc_ref(o); } }
static inline void lp_inc_n(lean_object * o, size_t n, lp_site * s) { if (!lean_is_scalar(o)) { lp_hit(s, 0); lean_inc_ref_n(o, n); } }
static inline void lp_dec(lean_object * o, lp_site * s) { if (!lean_is_scalar(o)) { lp_hit(s, 0); lean_dec_ref(o); } }

/* arrays of objects */
static inline lean_object * lp_alloc_array(size_t size, size_t cap, lp_site * s) { lp_hit(s, 24 + 8 * (uint64_t)cap); return lean_alloc_array(size, cap); }
static inline lean_object * lp_mk_empty_array_with_capacity(b_lean_obj_arg cap, lp_site * s) {
  lp_hit(s, 24 + 8 * (uint64_t)(lean_is_scalar(cap) ? lean_unbox(cap) : 0)); return lean_mk_empty_array_with_capacity(cap); }
static inline lean_object * lp_mk_array(lean_obj_arg n, lean_obj_arg v, lp_site * s) {
  lp_hit(s, 24 + 8 * (uint64_t)(lean_is_scalar(n) ? lean_unbox(n) : 0)); return lean_mk_array(n, v); }
static inline void lp_arr_excl(lean_object * a, lp_site * s) { if (!lean_is_exclusive(a)) lp_hit(s, 24 + 8 * (uint64_t)lean_array_size(a)); }
static inline lean_object * lp_array_uset(lean_obj_arg a, size_t i, lean_obj_arg v, lp_site * s) { lp_arr_excl(a, s); return lean_array_uset(a, i, v); }
static inline lean_object * lp_array_fset(lean_obj_arg a, b_lean_obj_arg i, lean_obj_arg v, lp_site * s) { lp_arr_excl(a, s); return lean_array_fset(a, i, v); }
static inline lean_object * lp_array_set(lean_obj_arg a, b_lean_obj_arg i, lean_obj_arg v, lp_site * s) { lp_arr_excl(a, s); return lean_array_set(a, i, v); }
static inline lean_object * lp_array_pop(lean_obj_arg a, lp_site * s) { lp_arr_excl(a, s); return lean_array_pop(a); }
static inline lean_object * lp_array_fswap(lean_obj_arg a, b_lean_obj_arg i, b_lean_obj_arg j, lp_site * s) { lp_arr_excl(a, s); return lean_array_fswap(a, i, j); }
static inline lean_object * lp_array_swap(lean_obj_arg a, b_lean_obj_arg i, b_lean_obj_arg j, lp_site * s) { lp_arr_excl(a, s); return lean_array_swap(a, i, j); }
static inline lean_object * lp_array_push(lean_obj_arg a, lean_obj_arg v, lp_site * sc, lp_site * sg) {
  if (!lean_is_exclusive(a)) lp_hit(sc, 24 + 8 * (uint64_t)lean_array_size(a));
  else if (lean_array_size(a) == lean_array_capacity(a)) lp_hit(sg, 24 + 8 * (uint64_t)lean_array_size(a));
  return lean_array_push(a, v); }
static inline lean_object * lp_copy_expand_array(lean_obj_arg a, bool e, lp_site * s) { lp_hit(s, 24 + 8 * (uint64_t)lean_array_size(a)); return lean_copy_expand_array(a, e); }
/* float arrays */
static inline lean_object * lp_float_array_uset(lean_obj_arg a, size_t i, double d, lp_site * s) { lp_num(1, d); if (!lean_is_exclusive(a)) lp_hit(s, 24 + 8 * (uint64_t)lean_sarray_size(a)); return lean_float_array_uset(a, i, d); }
static inline lean_object * lp_float_array_fset(lean_obj_arg a, b_lean_obj_arg i, double d, lp_site * s) { lp_num(1, d); if (!lean_is_exclusive(a)) lp_hit(s, 24 + 8 * (uint64_t)lean_sarray_size(a)); return lean_float_array_fset(a, i, d); }
static inline lean_object * lp_float_array_set(lean_obj_arg a, b_lean_obj_arg i, double d, lp_site * s) { lp_num(1, d); if (!lean_is_exclusive(a)) lp_hit(s, 24 + 8 * (uint64_t)lean_sarray_size(a)); return lean_float_array_set(a, i, d); }
static inline lean_object * lp_float_array_push(lean_obj_arg a, double d, lp_site * sc, lp_site * sg) {
  if (!lean_is_exclusive(a)) lp_hit(sc, 24 + 8 * (uint64_t)lean_sarray_size(a));
  else if (lean_sarray_size(a) == lean_sarray_capacity(a)) lp_hit(sg, 24 + 8 * (uint64_t)lean_sarray_size(a));
  return lean_float_array_push(a, d); }
/* strings */
static inline lean_object * lp_string_append(lean_obj_arg a, b_lean_obj_arg b, lp_site * sc, lp_site * sg, lp_site * si) {
  uint64_t need = lean_string_size(a) + lean_string_size(b) - 1;
  if (!lean_is_exclusive(a)) lp_hit(sc, 24 + need);
  else if (need > lean_string_capacity(a)) lp_hit(sg, 24 + need);
  else lp_hit(si, 0);
  return lean_string_append(a, b); }
static inline lean_object * lp_string_push(lean_obj_arg a, uint32_t c, lp_site * sc, lp_site * si) {
  if (!lean_is_exclusive(a)) lp_hit(sc, 24 + lean_string_size(a) + 4); else lp_hit(si, 0);
  return lean_string_push(a, c); }
static inline lean_object * lp_string_utf8_extract(b_lean_obj_arg s0, b_lean_obj_arg b, b_lean_obj_arg e, lp_site * s) {
  uint64_t n = (lean_is_scalar(b) && lean_is_scalar(e) && lean_unbox(e) > lean_unbox(b)) ? lean_unbox(e) - lean_unbox(b) : 0;
  lp_hit(s, 24 + n + 1); return lean_string_utf8_extract(s0, b, e); }
static inline lean_object * lp_mk_string_unchecked(char const * p, size_t sz, size_t len, lp_site * s) { lp_hit(s, 24 + sz + 1); return lean_mk_string_unchecked(p, sz, len); }

#define lean_ctor_set_float(o, off, v) lp_ctor_set_float(o, off, v)
#define lean_alloc_ctor(t, n, z) lp_alloc_ctor(t, n, z, LP_S("ctor"))
#define lean_alloc_closure(f, a, n) lp_alloc_closure(f, a, n, LP_S("closure"))
#define lean_box_float(v) lp_box_float(v, LP_S("box-float"))
#define lean_box_uint64(v) lp_box_uint64(v, LP_S("box-uint64"))
#define lean_inc(o) lp_inc(o, LP_S("rc-inc"))
#define lean_inc_ref(o) lp_inc(o, LP_S("rc-inc"))
#define lean_inc_n(o, n) lp_inc_n(o, n, LP_S("rc-inc"))
#define lean_inc_ref_n(o, n) lp_inc_n(o, n, LP_S("rc-inc"))
#define lean_dec(o) lp_dec(o, LP_S("rc-dec"))
#define lean_dec_ref(o) lp_dec(o, LP_S("rc-dec"))
#define lean_alloc_array(sz, cap) lp_alloc_array(sz, cap, LP_S("array-new"))
#define lean_mk_empty_array_with_capacity(c) lp_mk_empty_array_with_capacity(c, LP_S("array-new"))
#define lean_mk_array(n, v) lp_mk_array(n, v, LP_S("array-new"))
#define lean_array_uset(a, i, v) lp_array_uset(a, i, v, LP_S("array-copy"))
#define lean_array_fset(a, i, v) lp_array_fset(a, i, v, LP_S("array-copy"))
#define lean_array_set(a, i, v) lp_array_set(a, i, v, LP_S("array-copy"))
#define lean_array_pop(a) lp_array_pop(a, LP_S("array-copy"))
#define lean_array_fswap(a, i, j) lp_array_fswap(a, i, j, LP_S("array-copy"))
#define lean_array_swap(a, i, j) lp_array_swap(a, i, j, LP_S("array-copy"))
#define lean_array_push(a, v) lp_array_push(a, v, LP_S("array-copy"), LP_S("array-grow"))
#define lean_copy_expand_array(a, e) lp_copy_expand_array(a, e, LP_S("array-copy"))
#define lean_float_array_uset(a, i, d) lp_float_array_uset(a, i, d, LP_S("floatarray-copy"))
#define lean_float_array_fset(a, i, d) lp_float_array_fset(a, i, d, LP_S("floatarray-copy"))
#define lean_float_array_set(a, i, d) lp_float_array_set(a, i, d, LP_S("floatarray-copy"))
#define lean_float_array_push(a, d) lp_float_array_push(a, d, LP_S("floatarray-copy"), LP_S("floatarray-grow"))
#define lean_string_append(a, b) lp_string_append(a, b, LP_S("string-copy"), LP_S("string-grow"), LP_S("string-inplace"))
#define lean_string_push(a, c) lp_string_push(a, c, LP_S("string-copy"), LP_S("string-inplace"))
#define lean_string_utf8_extract(s, b, e) lp_string_utf8_extract(s, b, e, LP_S("string-new"))
#define lean_mk_string_unchecked(p, sz, len) lp_mk_string_unchecked(p, sz, len, LP_S("string-new"))
#endif
