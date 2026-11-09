/*
 * qjs_wasmvm_entry.c: the entry point of the QuickJS-NG build that runs inside the
 * Lean WasmVM engine (https://github.com/danbri/factoidal/issues/1244; record:
 * docs/designissues/2026-11-07-wasmvm-engine.md, "QuickJS in WasmVM").
 *
 * Built by tools/wasmvm/build-quickjs.sh into a standalone Wasm module. It imports
 * WASI Preview 1 (from the C library; the Lean host grants nothing by default) and
 * the module `foafnaut_dom`, below. It exports:
 *
 *   qjs_new() -> 0 | negative      make the runtime and context and run the prelude
 *                                  (prelude.js): `document`, `window`, nodes, events,
 *                                  `console`, timers, animation frames, `queueMicrotask`
 *   qjs_alloc(n) -> ptr, qjs_free(ptr)
 *   qjs_eval(src_ptr, src_len) -> result ptr
 *                                  run a classic script (global scope, so `let` and
 *                                  `class` bindings are shared between scripts)
 *   qjs_call(callback_id, target, arg) -> result ptr
 *                                  run one callback the host registered earlier: a
 *                                  timer (target -1) or an animation frame callback
 *                                  (target -2, arg the frame time in ms)
 *   qjs_dispatch(target, type_ptr, type_len, flags) -> result ptr
 *                                  dispatch an event of the user agent; the host gives
 *                                  the listener order (import dispatch_plan)
 *   qjs_run_job() -> 1 | 0 | -1    run one pending promise job (a microtask)
 *   qjs_page_mode(on)              on: the host runs the microtask checkpoint (no
 *                                  checkpoint at the end of an export) and script
 *                                  exceptions are reported as an ErrorEvent
 *   qjs_page(op, ptr, len)         0: the document URL; 1: the current script node;
 *                                  2: a page starts (content event handler attributes)
 *   qjs_release(callback_id)       forget a callback (a timer that has fired)
 *
 * Without page mode, each of qjs_eval and qjs_call ends with a microtask checkpoint: it
 * runs pending promise jobs until none is left. A result is a block the host frees with
 * qjs_free:
 *
 *   u32 status   0 normal, 1 an exception was thrown (the text is its message and stack)
 *   u32 length   bytes of text
 *   text         UTF-8: the completion value as a string (qjs_eval), or
 *                "prevented" / "" (qjs_dispatch)
 *
 * The DOM is not in this module. Each DOM operation is one import of `foafnaut_dom`;
 * the Lean host turns it into a typed command on its DOM arena
 * (formal/lean4/L4Factoidal/WasmVM/Hosts/Dom.lean). Node handles are the arena's node
 * ids. Strings cross as (pointer, length) in UTF-8. An import that returns a string
 * writes into a buffer (pointer, capacity) given by this module, never more than the
 * capacity, and returns the full length; when that is larger, this module asks again
 * with a large enough buffer. Negative results are errors:
 *
 *   -1 none (no such element, no such attribute)    -2 not a node of the right type
 *   -3 InvalidCharacterError    -4 HierarchyRequestError    -5 over a budget
 *   -6 denied    -9 NotFoundError    -10 NotSupportedError    -11 NamespaceError
 *
 * Timers, listeners and animation frames only record a request: the host keeps the
 * callback id, and its event loop decides when (and whether) to run it, with qjs_call.
 * The functions stay in the prelude, by number.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "quickjs.h"

#ifdef QJS_NATIVE
/* A native build for comparison (tools/wasmvm/quickjs/README.md): no DOM, a main()
 * that runs prepared Test262 files. */
#define DOM_IMPORT(n)
#else
#define DOM_IMPORT(n) __attribute__((import_module("foafnaut_dom"), import_name(#n)))
#endif

DOM_IMPORT(get_element_by_id) int32_t dom_get_element_by_id(const char *id, int32_t len);
DOM_IMPORT(text_content_set) int32_t dom_text_content_set(int32_t node, const char *s, int32_t len);
DOM_IMPORT(get_attribute) int32_t dom_get_attribute(int32_t node, const char *name, int32_t nlen,
                                                    char *buf, int32_t cap);
DOM_IMPORT(set_attribute) int32_t dom_set_attribute(int32_t node, const char *name, int32_t nlen,
                                                    const char *value, int32_t vlen);
DOM_IMPORT(set_timer) int32_t dom_set_timer(int32_t callback, int32_t delay_ms, int32_t repeat);
DOM_IMPORT(clear_timer) int32_t dom_clear_timer(int32_t timer);
DOM_IMPORT(console_log) int32_t dom_console_log(const char *s, int32_t len);
/* Added 2026-11-08 for page scripts in the engine (docs/designissues/2026-11-08-page-scripts.md). */
DOM_IMPORT(node_info) int32_t dom_node_info(int32_t node, int32_t which);
DOM_IMPORT(node_string) int32_t dom_node_string(int32_t node, int32_t which, char *buf, int32_t cap);
DOM_IMPORT(node_children) int32_t dom_node_children(int32_t node, int32_t unused, char *buf, int32_t cap);
DOM_IMPORT(create_node) int32_t dom_create_node(int32_t kind, const char *s, int32_t len);
DOM_IMPORT(insert_before) int32_t dom_insert_before(int32_t parent, int32_t node, int32_t child);
DOM_IMPORT(remove_child) int32_t dom_remove_child(int32_t parent, int32_t child);
DOM_IMPORT(replace_child) int32_t dom_replace_child(int32_t parent, int32_t node, int32_t child);
DOM_IMPORT(remove_attribute) int32_t dom_remove_attribute(int32_t node, const char *name, int32_t nlen);
DOM_IMPORT(clone_node) int32_t dom_clone_node(int32_t node, int32_t deep);
DOM_IMPORT(tree_op) int32_t dom_tree_op(int32_t a, int32_t b, int32_t which);
DOM_IMPORT(listen) int32_t dom_listen(int32_t target, const char *type, int32_t tlen, int32_t callback, int32_t capture);
DOM_IMPORT(unlisten) int32_t dom_unlisten(int32_t callback);
DOM_IMPORT(dispatch_plan) int32_t dom_dispatch_plan(int32_t target, const char *type, int32_t tlen, int32_t bubbles,
                                                    char *buf, int32_t cap);
DOM_IMPORT(request_frame) int32_t dom_request_frame(int32_t callback);
DOM_IMPORT(cancel_frame) int32_t dom_cancel_frame(int32_t id);
DOM_IMPORT(node_query) int32_t dom_node_query(int32_t node, int32_t op, const char *s, int32_t slen,
                                              char *buf, int32_t cap);
/* gpu_command(op, unused, bytes, len, out, cap): one page GPU command (header line, '\n',
 * payload), which Lean decodes, validates and turns into host commands
 * (L4Factoidal.PageGpu; docs/designissues/2026-11-08-page-gpu.md). The answer is the
 * length of Lean's refusal message, 0 when accepted. */
DOM_IMPORT(gpu_command) int32_t dom_gpu_command(int32_t op, int32_t unused, const char *s, int32_t slen,
                                                char *buf, int32_t cap);
/* web_api(op, flags, args, len, out, cap): one operation of the web APIs that Lean serves
 * (Encoding, URL, base64, crypto; L4Factoidal.WasmVM.Hosts.WebApi). `args` is a u32 count
 * and each argument as a u32 length and its bytes. The answer is the length of the result
 * bytes, written at `out` when they fit in `cap`; otherwise Lean keeps them and op 0 takes
 * them, so an operation runs once. Negative: an error code. */
/* Zero a buffer that held key bytes or derived secrets. A memset just before free() is a
 * dead store the compiler may remove; a call through a volatile function pointer is not
 * (record docs/designissues/2026-11-09-crypto-boundary-security.md, finding F11). */
static void *(*const volatile memset_v)(void *, int, size_t) = memset;
static void zero_secret(void *p, size_t n) { if (n) memset_v(p, 0, n); }

/* Appended to the pinned quickjs.c by tools/wasmvm/build-quickjs.sh
 * (quickjs/random-seed.c.inc): set the context's Math.random state. */
void JS_SetRandomSeed(JSContext *ctx, uint64_t seed);
DOM_IMPORT(web_api) int32_t dom_web_api(int32_t op, int32_t flags, const char *s, int32_t slen,
                                        char *buf, int32_t cap);
/* wasm_call(op, handle, bytes, len, out, cap, view, view_len): the WebAssembly JavaScript API
 * of the page (L4Factoidal.WasmVM.Hosts.PageWasm; docs/designissues/2026-11-08-page-wasm.md).
 * Lean holds the page's modules in a WasmVM store of their own. `view` is the data of a
 * Memory.buffer ArrayBuffer (or 0): Lean copies the chunks that changed between it and the
 * module's memory. The answer is its length; a longer answer than `cap` is kept by Lean
 * and written by op 31. */
DOM_IMPORT(wasm_call) int32_t dom_wasm_call(int32_t op, int32_t handle, const uint8_t *s, int32_t slen,
                                            uint8_t *buf, int32_t cap, uint8_t *view, int32_t view_len);

static JSRuntime *rt;
static JSContext *ctx;
static JSValue dispatch_fn; /* the object the prelude returns: call, dispatch, report, script, url, release */
/* Page mode (qjs_page_mode(1)): no microtask checkpoint at the end of qjs_eval, qjs_call and
 * qjs_dispatch (the host runs the jobs with qjs_run_job, when its event loop says), and an
 * exception that a script throws is reported (an ErrorEvent at the window). */
static int page_mode;

__attribute__((export_name("qjs_alloc")))
void *qjs_alloc(int32_t n) { return malloc((size_t) n); }

__attribute__((export_name("qjs_free")))
void qjs_free(void *p) { free(p); }

/* ---- helpers ---------------------------------------------------------------- */

static int arg_i32(JSContext *c, JSValueConst v, int32_t *out) { return JS_ToInt32(c, out, v); }

/* An import that writes bytes into a buffer (pointer, capacity) and answers the full
 * length, or a negative code: ask with a small buffer, then with one of the full size.
 * `unit` is 1 for a UTF-8 string and 4 for a list of i32 (the answer counts units). */
typedef int32_t (*reader)(int32_t a, int32_t b, const char *s, int32_t slen, char *buf, int32_t cap);

static int32_t read_bytes(reader f, int32_t a, int32_t b, const char *s, int32_t slen, int unit, char **out) {
  static char small[1024];
  int32_t n = f(a, b, s, slen, small, (int32_t) sizeof small);
  if (n < 0) return n;
  if ((int64_t) n * unit <= (int64_t) sizeof small) { *out = small; return n; }
  if ((int64_t) n * unit > (1 << 26)) return -5;
  char *big = malloc((size_t) n * unit);
  if (!big) return -5;
  int32_t m = f(a, b, s, slen, big, n * unit);
  if (m < 0 || m > n) { free(big); return m < 0 ? m : -5; }
  *out = big;
  return m;
}

static JSValue string_result(JSContext *c, reader f, int32_t a, int32_t b, const char *s, int32_t slen) {
  char *p = 0;
  int32_t n = read_bytes(f, a, b, s, slen, 1, &p);
  if (n < 0) return JS_NewInt32(c, n);
  JSValue r = JS_NewStringLen(c, p, (size_t) n);
  if (n > 1024) free(p);
  return r;
}

static JSValue list_result(JSContext *c, reader f, int32_t a, int32_t b, const char *s, int32_t slen) {
  char *p = 0;
  int32_t n = read_bytes(f, a, b, s, slen, 4, &p);
  if (n < 0) return JS_NewInt32(c, n);
  JSValue arr = JS_NewArray(c);
  for (int32_t i = 0; i < n; i++) {
    int32_t v; memcpy(&v, p + 4 * i, 4);
    JS_SetPropertyUint32(c, arr, (uint32_t) i, JS_NewInt32(c, v));
  }
  if ((int64_t) n * 4 > 1024) free(p);
  return arr;
}

static int32_t rd_string(int32_t node, int32_t which, const char *s, int32_t slen, char *buf, int32_t cap) {
  (void) s; (void) slen; return dom_node_string(node, which, buf, cap);
}
static int32_t rd_attr(int32_t node, int32_t which, const char *s, int32_t slen, char *buf, int32_t cap) {
  (void) which; return dom_get_attribute(node, s, slen, buf, cap);
}
static int32_t rd_kids(int32_t node, int32_t which, const char *s, int32_t slen, char *buf, int32_t cap) {
  (void) s; (void) slen; return dom_node_children(node, which, buf, cap);
}
static int32_t rd_query(int32_t node, int32_t op, const char *s, int32_t slen, char *buf, int32_t cap) {
  return dom_node_query(node, op, s, slen, buf, cap);
}
static int32_t rd_gpu(int32_t op, int32_t unused, const char *s, int32_t slen, char *buf, int32_t cap) {
  return dom_gpu_command(op, unused, s, slen, buf, cap);
}
static int32_t rd_plan(int32_t node, int32_t bubbles, const char *s, int32_t slen, char *buf, int32_t cap) {
  return dom_dispatch_plan(node, s, slen, bubbles, buf, cap);
}

/* ---- the native object the prelude receives (never a global) ---------------- */

#define I32(k, v) int32_t v; if (arg_i32(c, argv[k], &v)) return JS_EXCEPTION
#define STR(k, v, l) size_t l; const char *v = JS_ToCStringLen(c, &l, argv[k]); if (!v) return JS_EXCEPTION

static JSValue n_by_id(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  STR(0, s, len);
  int32_t r = dom_get_element_by_id(s, (int32_t) len);
  JS_FreeCString(c, s);
  return JS_NewInt32(c, r);
}
static JSValue n_info(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, node); I32(1, which);
  return JS_NewInt32(c, dom_node_info(node, which));
}
static JSValue n_str(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, node); I32(1, which);
  return string_result(c, rd_string, node, which, 0, 0);
}
static JSValue n_kids(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, node);
  JSValue r = list_result(c, rd_kids, node, 0, 0, 0);
  return JS_IsNumber(r) ? JS_NewArray(c) : r;
}
static JSValue n_attr(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, node); STR(1, s, len);
  JSValue r = string_result(c, rd_attr, node, 0, s, (int32_t) len);
  JS_FreeCString(c, s);
  if (JS_IsNumber(r)) { int32_t code; JS_ToInt32(c, &code, r); if (code == -1) return JS_NULL; }
  return r;
}
/* query(node, op, s): a string answer, null for none, or a negative error code. */
static JSValue n_query(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, node); I32(1, op); STR(2, s, len);
  JSValue r = string_result(c, rd_query, node, op, s, (int32_t) len);
  JS_FreeCString(c, s);
  if (JS_IsNumber(r)) { int32_t code; JS_ToInt32(c, &code, r); if (code == -1) return JS_NULL; }
  return r;
}
/* gpu(op, header, payload): payload a string or an ArrayBuffer. Answers "" when Lean
 * accepted the command, else Lean's refusal; a negative number for a memory error. */
static JSValue n_gpu(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, op); STR(1, h, hl);
  size_t pl = 0; const char *ps = 0; uint8_t *pb = 0;
  if (JS_IsString(argv[2])) ps = JS_ToCStringLen(c, &pl, argv[2]);
  else pb = JS_GetArrayBuffer(c, &pl, argv[2]);
  if (!ps && !pb) pl = 0;
  if (hl + 1 + pl > (size_t) (1 << 26)) { JS_FreeCString(c, h); if (ps) JS_FreeCString(c, ps); return JS_NewInt32(c, -5); }
  char *buf = malloc(hl + 1 + pl + 1);
  if (!buf) { JS_FreeCString(c, h); if (ps) JS_FreeCString(c, ps); return JS_NewInt32(c, -5); }
  memcpy(buf, h, hl); buf[hl] = '\n';
  if (pl) memcpy(buf + hl + 1, ps ? (const void *) ps : (const void *) pb, pl);
  JS_FreeCString(c, h); if (ps) JS_FreeCString(c, ps);
  JSValue r = string_result(c, rd_gpu, op, 0, buf, (int32_t) (hl + 1 + pl));
  free(buf);
  return r;
}
/* api(op, flags, bytes, ...args): one web API operation. Each argument is a string or a
 * number (sent in UTF-8), an ArrayBuffer or a Uint8Array (its bytes, nothing copied in
 * JavaScript). The answer: a string (the result's UTF-8), or an ArrayBuffer when `bytes`
 * is true, or a negative error code. */
static void put_u32(uint8_t *p, uint32_t v) { p[0] = v; p[1] = v >> 8; p[2] = v >> 16; p[3] = v >> 24; }
static JSValue n_api(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, op); I32(1, flags);
  int bytes = argc > 2 && JS_ToBool(c, argv[2]);
  int k = argc > 3 ? argc - 3 : 0;
  if (k > 64) return JS_NewInt32(c, -5);
  const uint8_t *ptrs[64]; size_t lens[64]; const char *strs[64]; JSValue vals[64];
  size_t total = 4;
  int ok = 1;
  for (int i = 0; i < k; i++) {
    vals[i] = JS_DupValue(c, argv[3 + i]);
    strs[i] = 0; ptrs[i] = 0; lens[i] = 0;
    if (!ok) continue;
    if (JS_IsString(vals[i]) || JS_IsNumber(vals[i])) {
      strs[i] = JS_ToCStringLen(c, &lens[i], vals[i]);
      if (!strs[i]) { ok = 0; continue; }
      ptrs[i] = (const uint8_t *) strs[i];
    } else {
      size_t n = 0;
      uint8_t *p = JS_GetUint8Array(c, &n, vals[i]);
      if (!p) { JS_FreeValue(c, JS_GetException(c)); p = JS_GetArrayBuffer(c, &n, vals[i]); }
      if (!p) { JS_FreeValue(c, JS_GetException(c)); n = 0; } /* a detached buffer is empty */
      ptrs[i] = p; lens[i] = n;
    }
    total += 4 + lens[i];
  }
  JSValue r = JS_UNDEFINED;
  uint8_t *block = 0;
  if (!ok) r = JS_EXCEPTION;
  else if (total > (size_t) (1 << 26)) r = JS_NewInt32(c, -5);
  else if (!(block = malloc(total))) r = JS_NewInt32(c, -5);
  else {
    put_u32(block, (uint32_t) k);
    size_t at = 4;
    for (int i = 0; i < k; i++) {
      put_u32(block + at, (uint32_t) lens[i]); at += 4;
      if (lens[i]) memcpy(block + at, ptrs[i], lens[i]);
      at += lens[i];
    }
  }
  for (int i = 0; i < k; i++) { if (strs[i]) JS_FreeCString(c, strs[i]); JS_FreeValue(c, vals[i]); }
  if (!block) return r;
  static char small[4096];
  int32_t n = dom_web_api(op, flags, (const char *) block, (int32_t) total, small, (int32_t) sizeof small);
  /* Crypto operations (ops 30-49) carry key bytes, derived secrets and random bytes:
   * the guest's own copies are zeroed once Lean has them (record
   * docs/designissues/2026-11-09-hacl-web-crypto.md, "Secret lifetime"). */
  int secret = op >= 30 && op < 50;
  if (secret) zero_secret(block, total);
  free(block);
  if (n < 0) return JS_NewInt32(c, n);
  char *out = small;
  if (n > (int32_t) sizeof small) {
    out = malloc((size_t) n);
    if (!out) return JS_NewInt32(c, -5);
    int32_t m = dom_web_api(0, 0, 0, 0, out, n);
    if (m != n) { free(out); return JS_NewInt32(c, m < 0 ? m : -5); }
  }
  r = bytes ? JS_NewArrayBufferCopy(c, (const uint8_t *) out, (size_t) n) : JS_NewStringLen(c, out, (size_t) n);
  if (secret) zero_secret(out, (size_t) n);
  if (out != small) free(out);
  return r;
}
/* wasm(op, handle, payload, view, text, out): payload an ArrayBuffer, a string (sent as UTF-8) or
 * undefined; view an ArrayBuffer or undefined. The answer: an ArrayBuffer, or a string when
 * `text` is true, or a negative number. With `out` (an ArrayBuffer), Lean writes the answer
 * straight into it and the native answers its length; an answer longer than `out` comes
 * back as a new ArrayBuffer. */
static JSValue n_wasm(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, op); I32(1, handle);
  size_t pl = 0, vl = 0;
  const char *ps = argc > 2 && JS_IsString(argv[2]) ? JS_ToCStringLen(c, &pl, argv[2]) : 0;
  uint8_t *pb = ps ? (uint8_t *) ps : argc > 2 && JS_IsObject(argv[2]) ? JS_GetArrayBuffer(c, &pl, argv[2]) : 0;
  uint8_t *vb = argc > 3 && JS_IsObject(argv[3]) ? JS_GetArrayBuffer(c, &vl, argv[3]) : 0;
  int text = argc > 4 && JS_ToBool(c, argv[4]);
  size_t ol = 0;
  uint8_t *ob = argc > 5 && JS_IsObject(argv[5]) ? JS_GetArrayBuffer(c, &ol, argv[5]) : 0;
  if (!pb) pl = 0;
  if (!vb) vl = 0;
  static uint8_t small[2048];
  int32_t n = ob ? dom_wasm_call(op, handle, pb, (int32_t) pl, ob, (int32_t) ol, vb, (int32_t) vl)
                 : dom_wasm_call(op, handle, pb, (int32_t) pl, small, (int32_t) sizeof small, vb, (int32_t) vl);
  if (ps) JS_FreeCString(c, ps);
  if (n < 0) return JS_NewInt32(c, n);
  if (ob && n <= (int32_t) ol) return JS_NewInt32(c, n);
  uint8_t *p = small;
  if (ob || n > (int32_t) sizeof small) {
    p = malloc((size_t) n);
    if (!p) return JS_NewInt32(c, -5);
    int32_t m = dom_wasm_call(31, 0, 0, 0, p, n, 0, 0);
    if (m != n) { free(p); return JS_NewInt32(c, m < 0 ? m : -5); }
  }
  JSValue r = text ? JS_NewStringLen(c, (const char *) p, (size_t) n) : JS_NewArrayBufferCopy(c, p, (size_t) n);
  if (p != small) free(p);
  return r;
}
/* wasmGlue(): the function of webassembly.js (bytecode in wasm_glue.h, made by
 * build-quickjs.sh), which the prelude runs on the first read of `WebAssembly`. */
static JSValue n_wasm_glue(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv);
/* detach(buffer): a Memory.buffer whose memory grew (WebAssembly JS API, "refresh the
 * memory buffer"). */
static JSValue n_detach(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  if (argc > 0 && JS_IsObject(argv[0])) JS_DetachArrayBuffer(c, argv[0]);
  return JS_UNDEFINED;
}
/* gpuBytes(op, header, payload): gpu_command answered as bytes, an ArrayBuffer (Canvas 2D
 * getImageData, op 202: the pixels as straight RGBA). */
static JSValue n_gpu_bytes(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, op); STR(1, h, hl);
  size_t pl = 0; const char *ps = 0; uint8_t *pb = 0;
  if (JS_IsString(argv[2])) ps = JS_ToCStringLen(c, &pl, argv[2]);
  else pb = JS_GetArrayBuffer(c, &pl, argv[2]);
  if (!ps && !pb) pl = 0;
  if (hl + 1 + pl > (size_t) (1 << 26)) { JS_FreeCString(c, h); if (ps) JS_FreeCString(c, ps); return JS_NewInt32(c, -5); }
  char *buf = malloc(hl + 1 + pl + 1);
  if (!buf) { JS_FreeCString(c, h); if (ps) JS_FreeCString(c, ps); return JS_NewInt32(c, -5); }
  memcpy(buf, h, hl); buf[hl] = '\n';
  if (pl) memcpy(buf + hl + 1, ps ? (const void *) ps : (const void *) pb, pl);
  JS_FreeCString(c, h); if (ps) JS_FreeCString(c, ps);
  char *p = 0;
  int32_t n = read_bytes(rd_gpu, op, 0, buf, (int32_t) (hl + 1 + pl), 1, &p);
  free(buf);
  if (n < 0) return JS_NewInt32(c, n);
  JSValue r = JS_NewArrayBufferCopy(c, (const uint8_t *) p, (size_t) n);
  if (n > 1024) free(p);
  return r;
}
static JSValue n_set_attr(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, node); STR(1, nm, nl);
  size_t vl; const char *v = JS_ToCStringLen(c, &vl, argv[2]);
  if (!v) { JS_FreeCString(c, nm); return JS_EXCEPTION; }
  int32_t r = dom_set_attribute(node, nm, (int32_t) nl, v, (int32_t) vl);
  JS_FreeCString(c, nm); JS_FreeCString(c, v);
  return JS_NewInt32(c, r);
}
static JSValue n_remove_attr(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, node); STR(1, nm, nl);
  int32_t r = dom_remove_attribute(node, nm, (int32_t) nl);
  JS_FreeCString(c, nm);
  return JS_NewInt32(c, r);
}
static JSValue n_set_text(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, node); STR(1, s, len);
  int32_t r = dom_text_content_set(node, s, (int32_t) len);
  JS_FreeCString(c, s);
  return JS_NewInt32(c, r);
}
static JSValue n_create(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, kind); STR(1, s, len);
  int32_t r = dom_create_node(kind, s, (int32_t) len);
  JS_FreeCString(c, s);
  return JS_NewInt32(c, r);
}
static JSValue n_insert(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, p); I32(1, k); I32(2, before);
  return JS_NewInt32(c, dom_insert_before(p, k, before));
}
static JSValue n_remove(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, p); I32(1, k);
  return JS_NewInt32(c, dom_remove_child(p, k));
}
static JSValue n_replace(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, p); I32(1, k); I32(2, old);
  return JS_NewInt32(c, dom_replace_child(p, k, old));
}
static JSValue n_clone(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, k); I32(1, deep);
  return JS_NewInt32(c, dom_clone_node(k, deep));
}
static JSValue n_tree_op(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, a); I32(1, b); I32(2, which);
  return JS_NewInt32(c, dom_tree_op(a, b, which));
}
static JSValue n_listen(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, target); I32(2, cb); I32(3, capture); STR(1, t, len);
  int32_t r = dom_listen(target, t, (int32_t) len, cb, capture);
  JS_FreeCString(c, t);
  return JS_NewInt32(c, r);
}
static JSValue n_unlisten(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, cb);
  return JS_NewInt32(c, dom_unlisten(cb));
}
static JSValue n_plan(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, target); I32(2, bubbles); STR(1, t, len);
  JSValue r = list_result(c, rd_plan, target, bubbles, t, (int32_t) len);
  JS_FreeCString(c, t);
  return r;
}
static JSValue n_timer(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, cb); I32(1, delay); I32(2, rep);
  return JS_NewInt32(c, dom_set_timer(cb, delay < 0 ? 0 : delay, rep ? 1 : 0));
}
static JSValue n_clear_timer(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, t);
  dom_clear_timer(t);
  return JS_UNDEFINED;
}
static JSValue n_frame(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, cb);
  return JS_NewInt32(c, dom_request_frame(cb));
}
static JSValue n_cancel_frame(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  I32(0, id);
  dom_cancel_frame(id);
  return JS_UNDEFINED;
}
static JSValue n_log(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  STR(0, s, len);
  dom_console_log(s, (int32_t) len);
  JS_FreeCString(c, s);
  return JS_UNDEFINED;
}

/* ---- the prelude: tools/wasmvm/quickjs/prelude.js as QuickJS-NG bytecode (prelude.h is
 * made by build-quickjs.sh with prelude_bytecode.c), so loading the guest parses nothing -- */

#include "prelude.h"

#include "wasm_glue.h"

/* The glue's bytecode is a script whose value is its function (webassembly.js). */
static JSValue n_wasm_glue(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  JSValue fn = JS_ReadObject(c, wasm_glue_bc, wasm_glue_bc_len, JS_READ_OBJ_BYTECODE);
  if (JS_IsException(fn)) return fn;
  return JS_EvalFunction(c, fn);
}

/* ---- results ---------------------------------------------------------------- */

static uint8_t *result(uint32_t status, const char *s, size_t len) {
  uint8_t *r = malloc(8 + len);
  if (!r) return 0;
  memcpy(r, &status, 4);
  uint32_t l = (uint32_t) len;
  memcpy(r + 4, &l, 4);
  if (len) memcpy(r + 8, s, len);
  return r;
}

static uint8_t *result_of_value(JSValue v, uint32_t status) {
  size_t len; const char *s = JS_ToCStringLen(ctx, &len, v);
  uint8_t *r = s ? result(status, s, len) : result(1, "<unprintable>", 13);
  if (s) JS_FreeCString(ctx, s);
  return r;
}

static uint8_t *result_of_exception(void) {
  JSValue e = JS_GetException(ctx);
  JSValue stack = JS_GetPropertyStr(ctx, e, "stack");
  JSValue msg = JS_ToString(ctx, e);
  size_t ml = 0, sl = 0;
  const char *m = JS_ToCStringLen(ctx, &ml, msg);
  const char *st = JS_IsString(stack) ? JS_ToCStringLen(ctx, &sl, stack) : 0;
  size_t len = ml + (st ? 1 + sl : 0);
  char *buf = malloc(len + 1);
  uint8_t *r;
  if (buf) {
    if (m) memcpy(buf, m, ml);
    if (st) { buf[ml] = '\n'; memcpy(buf + ml + 1, st, sl); }
    r = result(1, buf, len);
    free(buf);
  } else r = result(1, "", 0);
  if (m) JS_FreeCString(ctx, m);
  if (st) JS_FreeCString(ctx, st);
  JS_FreeValue(ctx, msg); JS_FreeValue(ctx, stack); JS_FreeValue(ctx, e);
  return r;
}

/* Page mode: report the exception (an ErrorEvent at the window, HTML "report an
 * exception"), and answer it as status 1 too. */
static uint8_t *report_exception(void) {
  JSValue e = JS_GetException(ctx);
  JSValue f = JS_GetPropertyStr(ctx, dispatch_fn, "report");
  JSValue v = JS_Call(ctx, f, dispatch_fn, 1, (JSValueConst *) &e);
  JS_FreeValue(ctx, f); JS_FreeValue(ctx, v);
  JS_Throw(ctx, e);
  return result_of_exception();
}

/* The microtask checkpoint: run promise jobs until none is left. */
static void checkpoint(void) {
  JSContext *c1;
  for (int i = 0; i < 1000000; i++) {
    int r = JS_ExecutePendingJob(rt, &c1);
    if (r <= 0) break; /* 0: none left; < 0: a job threw (dropped, as an unhandled rejection) */
  }
}

/* ---- exports ---------------------------------------------------------------- */

static const JSCFunctionListEntry native_fns[] = {
  JS_CFUNC_DEF("byId", 1, n_by_id),
  JS_CFUNC_DEF("info", 2, n_info),
  JS_CFUNC_DEF("str", 2, n_str),
  JS_CFUNC_DEF("kids", 1, n_kids),
  JS_CFUNC_DEF("attr", 2, n_attr),
  JS_CFUNC_DEF("query", 3, n_query),
  JS_CFUNC_DEF("setAttr", 3, n_set_attr),
  JS_CFUNC_DEF("removeAttr", 2, n_remove_attr),
  JS_CFUNC_DEF("setText", 2, n_set_text),
  JS_CFUNC_DEF("create", 2, n_create),
  JS_CFUNC_DEF("insert", 3, n_insert),
  JS_CFUNC_DEF("remove", 2, n_remove),
  JS_CFUNC_DEF("replace", 3, n_replace),
  JS_CFUNC_DEF("clone", 2, n_clone),
  JS_CFUNC_DEF("treeOp", 3, n_tree_op),
  JS_CFUNC_DEF("listen", 4, n_listen),
  JS_CFUNC_DEF("unlisten", 1, n_unlisten),
  JS_CFUNC_DEF("plan", 3, n_plan),
  JS_CFUNC_DEF("timer", 3, n_timer),
  JS_CFUNC_DEF("clearTimer", 1, n_clear_timer),
  JS_CFUNC_DEF("frame", 1, n_frame),
  JS_CFUNC_DEF("cancelFrame", 1, n_cancel_frame),
  JS_CFUNC_DEF("log", 1, n_log),
  JS_CFUNC_DEF("gpu", 3, n_gpu),
  JS_CFUNC_DEF("api", 3, n_api),
  JS_CFUNC_DEF("wasm", 6, n_wasm),
  JS_CFUNC_DEF("detach", 1, n_detach),
  JS_CFUNC_DEF("wasmGlue", 0, n_wasm_glue),
  JS_CFUNC_DEF("gpuBytes", 3, n_gpu_bytes),
};

__attribute__((export_name("qjs_new")))
int32_t qjs_new(void) {
  if (rt) return -1;
  rt = JS_NewRuntime();
  if (!rt) return -2;
  JS_SetMemoryLimit(rt, 64 * 1024 * 1024);
  JS_SetMaxStackSize(rt, 768 * 1024);
  ctx = JS_NewContext(rt);
  if (!ctx) return -3;
  JSValue native = JS_NewObject(ctx);
  JS_SetPropertyFunctionList(ctx, native, native_fns, sizeof native_fns / sizeof native_fns[0]);
  JSValue fn = JS_ReadObject(ctx, prelude_bc, prelude_bc_len, JS_READ_OBJ_BYTECODE);
  if (JS_IsException(fn)) { JS_FreeValue(ctx, native); return -4; }
  JSValue f = JS_EvalFunction(ctx, fn); /* the script's value: the prelude's function */
  if (JS_IsException(f)) { JS_FreeValue(ctx, native); return -4; }
  JSValue api = JS_Call(ctx, f, JS_UNDEFINED, 1, (JSValueConst *) &native);
  JS_FreeValue(ctx, f); JS_FreeValue(ctx, native);
  if (JS_IsException(api)) return -5;
  dispatch_fn = api;
  return 0;
}

__attribute__((export_name("qjs_eval")))
uint8_t *qjs_eval(const char *src, int32_t len) {
  if (!ctx) return result(1, "qjs_new was not called", 22);
  /* JS_Eval needs a NUL after the source. */
  char *copy = malloc((size_t) len + 1);
  if (!copy) return result(1, "out of memory", 13);
  memcpy(copy, src, (size_t) len); copy[len] = 0;
  JSValue v = JS_Eval(ctx, copy, (size_t) len, "<page-script>", JS_EVAL_TYPE_GLOBAL);
  free(copy);
  uint8_t *r = JS_IsException(v) ? (page_mode ? report_exception() : result_of_exception()) : result_of_value(v, 0);
  JS_FreeValue(ctx, v);
  if (!page_mode) checkpoint();
  return r;
}

__attribute__((export_name("qjs_call")))
uint8_t *qjs_call(int32_t callback, int32_t target, int32_t event) {
  if (!ctx) return result(1, "qjs_new was not called", 22);
  JSValue call = JS_GetPropertyStr(ctx, dispatch_fn, "call");
  JSValue args[3] = { JS_NewInt32(ctx, callback), JS_NewInt32(ctx, target), JS_NewInt32(ctx, event) };
  JSValue v = JS_Call(ctx, call, dispatch_fn, 3, args);
  JS_FreeValue(ctx, call);
  uint8_t *r = JS_IsException(v) ? result_of_exception() : result_of_value(v, 0);
  JS_FreeValue(ctx, v);
  if (!page_mode) checkpoint();
  return r;
}

/* qjs_dispatch(target, type_ptr, type_len, flags): an event of the user agent (trusted) at
 * node `target` (0 the document, 0x0FFFFFFF the window); flags 1 bubbles, 2 cancelable,
 * 4 composed. The listener order comes from the host (foafnaut_dom.dispatch_plan). Text:
 * "prevented" when a listener canceled it. */
__attribute__((export_name("qjs_dispatch")))
uint8_t *qjs_dispatch(int32_t target, const char *type, int32_t tlen, int32_t flags) {
  if (!ctx) return result(1, "qjs_new was not called", 22);
  JSValue f = JS_GetPropertyStr(ctx, dispatch_fn, "dispatch");
  JSValue args[3] = { JS_NewInt32(ctx, target), JS_NewStringLen(ctx, type, (size_t) tlen), JS_NewInt32(ctx, flags) };
  JSValue v = JS_Call(ctx, f, dispatch_fn, 3, args);
  JS_FreeValue(ctx, f); JS_FreeValue(ctx, args[1]);
  uint8_t *r = JS_IsException(v) ? result_of_exception() : result_of_value(v, 0);
  JS_FreeValue(ctx, v);
  if (!page_mode) checkpoint();
  return r;
}

/* qjs_run_job() -> 1 a job ran, 0 none was pending, -1 a job threw (the host's event loop
 * runs the microtask checkpoint, one job at a time). */
__attribute__((export_name("qjs_run_job")))
int32_t qjs_run_job(void) {
  if (!rt) return 0;
  JSContext *c1;
  int r = JS_ExecutePendingJob(rt, &c1);
  return r > 0 ? 1 : (r == 0 ? 0 : -1);
}

__attribute__((export_name("qjs_page_mode")))
void qjs_page_mode(int32_t on) { page_mode = on != 0; }

/* qjs_page(op, ptr, len): 0 the document URL is the string; 1 the current script is node
 * `len` (-1 none); 2 a page starts on the host's arena (content event handler attributes). */
__attribute__((export_name("qjs_page")))
void qjs_page(int32_t op, const char *s, int32_t len) {
  if (!ctx) return;
  if (op == 2) {
    /* Math.random: this session's own seed (web_api op 33, Hosts.WebApi.mathRandomSeed).
     * The guest's memory is prepared once and copied for every session, so the seed
     * QuickJS-NG took when the context was made would repeat in every page (record
     * docs/designissues/2026-11-09-crypto-boundary-security.md, finding F2). An engine
     * without op 33 answers a negative number and the seed stays. */
    static const char no_args[4] = {0, 0, 0, 0};
    unsigned char seed[8];
    if (dom_web_api(33, 0, no_args, 4, (char *) seed, 8) == 8) {
      uint64_t x = 0;
      for (int i = 0; i < 8; i++) x |= (uint64_t) seed[i] << (8 * i);
      JS_SetRandomSeed(ctx, x);
    }
  }
  JSValue f = JS_GetPropertyStr(ctx, dispatch_fn, op == 0 ? "url" : op == 1 ? "script" : "start");
  JSValue arg = op == 0 ? JS_NewStringLen(ctx, s, (size_t) len) : JS_NewInt32(ctx, len);
  JSValue v = JS_Call(ctx, f, dispatch_fn, 1, &arg);
  JS_FreeValue(ctx, f); JS_FreeValue(ctx, arg); JS_FreeValue(ctx, v);
}

__attribute__((export_name("qjs_release")))
void qjs_release(int32_t callback) {
  if (!ctx) return;
  JSValue rel = JS_GetPropertyStr(ctx, dispatch_fn, "release");
  JSValue arg = JS_NewInt32(ctx, callback);
  JSValue v = JS_Call(ctx, rel, dispatch_fn, 1, &arg);
  JS_FreeValue(ctx, rel); JS_FreeValue(ctx, v);
}

/* ---- Test262 ------------------------------------------------------------------
 * qjs_test262(src_ptr, src_len) -> result ptr
 *   Run one prepared Test262 case (harness files and test, already joined) in a
 *   fresh context of the same runtime, with the `print` and `$262` helpers of
 *   QuickJS-NG's run-test262.c (createRealm, detachArrayBuffer, evalScript, gc,
 *   global, IsHTMLDDA; no agent). Then the microtask checkpoint. Result status 1 and
 *   the exception text when the script threw; otherwise status 0 and the lines it
 *   printed (async tests print Test262:AsyncTestComplete). Not used by pages.
 */
static char *printed;
static size_t printed_len;

static JSValue t_print(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  for (int i = 0; i < argc; i++) {
    size_t len; const char *s = JS_ToCStringLen(c, &len, argv[i]);
    if (!s) return JS_EXCEPTION;
    if (printed_len + len + 1 < (1 << 20)) {
      char *p = realloc(printed, printed_len + len + 2);
      if (p) { printed = p; memcpy(printed + printed_len, s, len); printed_len += len; printed[printed_len++] = '\n'; }
    }
    JS_FreeCString(c, s);
  }
  return JS_UNDEFINED;
}
static JSValue t_detach(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  JS_DetachArrayBuffer(c, argv[0]); return JS_UNDEFINED;
}
static JSValue t_eval_script(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  size_t len; const char *s = JS_ToCStringLen(c, &len, argv[0]);
  if (!s) return JS_EXCEPTION;
  JSValue r = JS_Eval(c, s, len, "<evalScript>", JS_EVAL_TYPE_GLOBAL);
  JS_FreeCString(c, s);
  return r;
}
static JSValue t_gc(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  JS_RunGC(JS_GetRuntime(c)); return JS_UNDEFINED;
}
static JSValue t_html_dda(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) { return JS_NULL; }
static JSValue t_helpers(JSContext *c);
static JSValue t_create_realm(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  JSContext *c1 = JS_NewContext(JS_GetRuntime(c));
  if (!c1) return JS_ThrowOutOfMemory(c);
  JSValue r = t_helpers(c1);
  JS_FreeContext(c1);
  return r;
}
static JSValue t_helpers(JSContext *c) {
  static const JSCFunctionListEntry props[] = {
    JS_CFUNC_DEF("createRealm", 0, t_create_realm),
    JS_CFUNC_DEF("detachArrayBuffer", 1, t_detach),
    JS_CFUNC_DEF("evalScript", 1, t_eval_script),
    JS_CFUNC_DEF("gc", 0, t_gc),
  };
  JSValue g = JS_GetGlobalObject(c);
  JS_SetPropertyStr(c, g, "print", JS_NewCFunction(c, t_print, "print", 1));
  JSValue dda = JS_NewCFunction(c, t_html_dda, "IsHTMLDDA", 0);
  JS_SetIsHTMLDDA(c, dda);
  JSValue o = JS_NewObject(c);
  JS_SetPropertyFunctionList(c, o, props, sizeof props / sizeof props[0]);
  JS_SetPropertyStr(c, o, "IsHTMLDDA", dda);
  JS_SetPropertyStr(c, o, "global", JS_DupValue(c, g));
  JS_SetPropertyStr(c, g, "$262", JS_DupValue(c, o));
  JS_FreeValue(c, g);
  return o;
}

__attribute__((export_name("qjs_test262")))
uint8_t *qjs_test262(const char *src, int32_t len) {
  if (!rt) return result(1, "qjs_new was not called", 22);
  JSContext *saved = ctx;
  JSContext *c = JS_NewContext(rt);
  if (!c) return result(1, "no context", 10);
  JS_FreeValue(c, t_helpers(c));
  free(printed); printed = 0; printed_len = 0;
  char *copy = malloc((size_t) len + 1);
  if (!copy) { JS_FreeContext(c); return result(1, "out of memory", 13); }
  memcpy(copy, src, (size_t) len); copy[len] = 0;
  ctx = c;
  JSValue v = JS_Eval(c, copy, (size_t) len, "<test262>", JS_EVAL_TYPE_GLOBAL);
  free(copy);
  uint8_t *r = 0;
  if (JS_IsException(v)) r = result_of_exception();
  JS_FreeValue(c, v);
  checkpoint();
  if (!r) r = result(0, printed ? printed : "", printed_len);
  ctx = saved;
  JS_FreeContext(c);
  return r;
}

#ifdef QJS_NATIVE
#include <stdio.h>
int32_t dom_get_element_by_id(const char *id, int32_t len) { return -6; }
int32_t dom_text_content_set(int32_t node, const char *s, int32_t len) { return -6; }
int32_t dom_get_attribute(int32_t node, const char *name, int32_t nlen, char *buf, int32_t cap) { return -6; }
int32_t dom_set_attribute(int32_t node, const char *name, int32_t nlen, const char *value, int32_t vlen) { return -6; }
int32_t dom_set_timer(int32_t callback, int32_t delay_ms, int32_t repeat) { return -6; }
int32_t dom_clear_timer(int32_t timer) { return -6; }
int32_t dom_console_log(const char *s, int32_t len) { return -6; }
int32_t dom_node_info(int32_t node, int32_t which) { return -2; }
int32_t dom_node_string(int32_t node, int32_t which, char *buf, int32_t cap) { return -2; }
int32_t dom_node_children(int32_t node, int32_t unused, char *buf, int32_t cap) { return 0; }
int32_t dom_create_node(int32_t kind, const char *s, int32_t len) { return -6; }
int32_t dom_insert_before(int32_t parent, int32_t node, int32_t child) { return -6; }
int32_t dom_remove_child(int32_t parent, int32_t child) { return -6; }
int32_t dom_replace_child(int32_t parent, int32_t node, int32_t child) { return -6; }
int32_t dom_remove_attribute(int32_t node, const char *name, int32_t nlen) { return -6; }
int32_t dom_clone_node(int32_t node, int32_t deep) { return -6; }
int32_t dom_tree_op(int32_t a, int32_t b, int32_t which) { return -6; }
int32_t dom_listen(int32_t target, const char *type, int32_t tlen, int32_t callback, int32_t capture) { return -6; }
int32_t dom_unlisten(int32_t callback) { return -6; }
int32_t dom_dispatch_plan(int32_t target, const char *type, int32_t tlen, int32_t bubbles, char *buf, int32_t cap) { return -6; }
int32_t dom_request_frame(int32_t callback) { return -6; }
int32_t dom_cancel_frame(int32_t id) { return -6; }
int32_t dom_node_query(int32_t node, int32_t op, const char *s, int32_t slen, char *buf, int32_t cap) { return -6; }
int32_t dom_gpu_command(int32_t op, int32_t unused, const char *s, int32_t slen, char *buf, int32_t cap) { return -6; }
int32_t dom_wasm_call(int32_t op, int32_t handle, const uint8_t *s, int32_t slen, uint8_t *buf, int32_t cap,
                      uint8_t *view, int32_t view_len) { return -6; }

/* qjs-native FILE...: for each file, one line: FILE <tab> status <tab> text (400 bytes, one line) */
int main(int argc, char **argv) {
  if (qjs_new() != 0) return 2;
  for (int i = 1; i < argc; i++) {
    FILE *f = fopen(argv[i], "rb");
    if (!f) { printf("%s\t9\tunreadable\n", argv[i]); continue; }
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    char *b = malloc((size_t) n + 1);
    if (fread(b, 1, (size_t) n, f) != (size_t) n) n = 0;
    fclose(f);
    uint8_t *r = qjs_test262(b, (int32_t) n);
    free(b);
    uint32_t status, len; memcpy(&status, r, 4); memcpy(&len, r + 4, 4);
    printf("%s\t%u\t", argv[i], status);
    for (uint32_t j = 0; j < len && j < 400; j++) putchar(r[8 + j] == '\n' || r[8 + j] == '\t' ? ' ' : r[8 + j]);
    putchar('\n');
    free(r);
  }
  return 0;
}
#endif
