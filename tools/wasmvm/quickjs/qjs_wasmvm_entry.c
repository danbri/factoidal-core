/*
 * qjs_wasmvm_entry.c: the entry point of the QuickJS-NG build that runs inside the
 * Lean WasmVM engine (https://github.com/danbri/factoidal/issues/1244; record:
 * docs/designissues/2026-11-07-wasmvm-engine.md, "QuickJS in WasmVM").
 *
 * Built by tools/wasmvm/build-quickjs.sh into a standalone Wasm module. It imports
 * WASI Preview 1 (from the C library; the Lean host grants nothing by default) and
 * the module `foafnaut_dom`, below. It exports:
 *
 *   qjs_new() -> 0 | negative      make the runtime and context, install `document`,
 *                                  `console`, the timer functions and `queueMicrotask`
 *   qjs_alloc(n) -> ptr, qjs_free(ptr)
 *   qjs_eval(src_ptr, src_len) -> result ptr
 *                                  run a classic script (global scope, so `let` and
 *                                  `class` bindings are shared between scripts)
 *   qjs_call(callback_id, target_node, event) -> result ptr
 *                                  run one callback the host registered earlier:
 *                                  an event listener with the click event's target
 *                                  node, or a timer with target -1. The host runs
 *                                  the listeners of one dispatch in its own order;
 *                                  calls with the same event number share one event
 *                                  object, so preventDefault is seen by later listeners
 *   qjs_release(callback_id)       forget a callback (a timer that has fired)
 *
 * Each of qjs_eval and qjs_call ends with a microtask checkpoint: it runs pending
 * promise jobs until none is left. A result is a block the host frees with qjs_free:
 *
 *   u32 status   0 normal, 1 an exception was thrown (the text is its message and stack)
 *   u32 length   bytes of text
 *   text         UTF-8: the completion value as a string (qjs_eval), or
 *                "prevented" / "" (qjs_call of an event listener)
 *
 * The DOM is not in this module. Each DOM operation is one import of `foafnaut_dom`;
 * the Lean host turns it into a typed command on its DOM arena
 * (formal/lean4/L4Factoidal/WasmVM/Hosts/Dom.lean). Node handles are the arena's node
 * ids. Strings cross as (pointer, length) in UTF-8. An import that returns a string
 * writes into a buffer (pointer, capacity) given by this module, never more than the
 * capacity, and returns the full length; when that is larger, this module asks again
 * with a large enough buffer. Negative results are errors:
 *
 *   -1 none (no such element, no such attribute)    -2 not an element node
 *   -3 InvalidCharacterError    -4 HierarchyRequestError    -5 over a budget
 *   -6 denied
 *
 * Timers and listeners only record a request: the host keeps the callback id, and its
 * event loop decides when (and whether) to run it, with qjs_call.
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
DOM_IMPORT(document_element) int32_t dom_document_element(int32_t which);
DOM_IMPORT(tag_name) int32_t dom_tag_name(int32_t node, char *buf, int32_t cap);
DOM_IMPORT(text_content_get) int32_t dom_text_content_get(int32_t node, char *buf, int32_t cap);
DOM_IMPORT(text_content_set) int32_t dom_text_content_set(int32_t node, const char *s, int32_t len);
DOM_IMPORT(get_attribute) int32_t dom_get_attribute(int32_t node, const char *name, int32_t nlen,
                                                    char *buf, int32_t cap);
DOM_IMPORT(set_attribute) int32_t dom_set_attribute(int32_t node, const char *name, int32_t nlen,
                                                    const char *value, int32_t vlen);
DOM_IMPORT(create_element) int32_t dom_create_element(const char *name, int32_t len);
DOM_IMPORT(append_child) int32_t dom_append_child(int32_t parent, int32_t child);
DOM_IMPORT(add_event_listener) int32_t dom_add_event_listener(int32_t node, const char *type,
                                                              int32_t tlen, int32_t callback);
DOM_IMPORT(set_timer) int32_t dom_set_timer(int32_t callback, int32_t delay_ms, int32_t repeat);
DOM_IMPORT(clear_timer) int32_t dom_clear_timer(int32_t timer);
DOM_IMPORT(console_log) int32_t dom_console_log(const char *s, int32_t len);

static JSRuntime *rt;
static JSContext *ctx;
static JSValue dispatch_fn; /* the prelude's dispatcher: (callback id, target node) */

__attribute__((export_name("qjs_alloc")))
void *qjs_alloc(int32_t n) { return malloc((size_t) n); }

__attribute__((export_name("qjs_free")))
void qjs_free(void *p) { free(p); }

/* ---- helpers ---------------------------------------------------------------- */

static JSValue dom_error(JSContext *c, int32_t code) {
  switch (code) {
  case -2: return JS_ThrowTypeError(c, "not an element node");
  case -3: {
    JSValue e = JS_NewError(c);
    JS_SetPropertyStr(c, e, "name", JS_NewString(c, "InvalidCharacterError"));
    JS_SetPropertyStr(c, e, "message", JS_NewString(c, "InvalidCharacterError"));
    return JS_Throw(c, e);
  }
  case -4: {
    JSValue e = JS_NewError(c);
    JS_SetPropertyStr(c, e, "name", JS_NewString(c, "HierarchyRequestError"));
    JS_SetPropertyStr(c, e, "message", JS_NewString(c, "HierarchyRequestError"));
    return JS_Throw(c, e);
  }
  case -5: return JS_ThrowRangeError(c, "DOM budget exceeded");
  case -6: return JS_ThrowTypeError(c, "denied by the host");
  default: return JS_ThrowTypeError(c, "DOM error %d", (int) code);
  }
}

static int arg_i32(JSContext *c, JSValueConst v, int32_t *out) { return JS_ToInt32(c, out, v); }

/* A string an import writes: ask with a small buffer, then with one of the full size. */
typedef int32_t (*reader)(int32_t node, const char *a, int32_t alen, char *buf, int32_t cap);

static JSValue read_string(JSContext *c, reader f, int32_t node, const char *a, int32_t alen,
                           int null_on_minus_one) {
  char small[256];
  int32_t n = f(node, a, alen, small, (int32_t) sizeof small);
  if (n == -1 && null_on_minus_one) return JS_NULL;
  if (n < 0) return dom_error(c, n);
  if (n <= (int32_t) sizeof small) return JS_NewStringLen(c, small, (size_t) n);
  if (n > (1 << 24)) return dom_error(c, -5);
  char *big = malloc((size_t) n);
  if (!big) return JS_ThrowOutOfMemory(c);
  int32_t m = f(node, a, alen, big, n);
  JSValue r = (m >= 0 && m <= n) ? JS_NewStringLen(c, big, (size_t) m) : dom_error(c, m < 0 ? m : -5);
  free(big);
  return r;
}

static int32_t rd_tag(int32_t node, const char *a, int32_t alen, char *buf, int32_t cap) {
  (void) a; (void) alen; return dom_tag_name(node, buf, cap);
}
static int32_t rd_text(int32_t node, const char *a, int32_t alen, char *buf, int32_t cap) {
  (void) a; (void) alen; return dom_text_content_get(node, buf, cap);
}
static int32_t rd_attr(int32_t node, const char *a, int32_t alen, char *buf, int32_t cap) {
  return dom_get_attribute(node, a, alen, buf, cap);
}

/* ---- the native object the prelude receives (never a global) ---------------- */

static JSValue n_by_id(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  size_t len; const char *s = JS_ToCStringLen(c, &len, argv[0]);
  if (!s) return JS_EXCEPTION;
  int32_t r = dom_get_element_by_id(s, (int32_t) len);
  JS_FreeCString(c, s);
  return JS_NewInt32(c, r);
}

static JSValue n_root(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t which; if (arg_i32(c, argv[0], &which)) return JS_EXCEPTION;
  return JS_NewInt32(c, dom_document_element(which));
}

static JSValue n_tag(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t node; if (arg_i32(c, argv[0], &node)) return JS_EXCEPTION;
  return read_string(c, rd_tag, node, 0, 0, 0);
}

static JSValue n_get_text(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t node; if (arg_i32(c, argv[0], &node)) return JS_EXCEPTION;
  return read_string(c, rd_text, node, 0, 0, 1);
}

static JSValue n_set_text(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t node; if (arg_i32(c, argv[0], &node)) return JS_EXCEPTION;
  size_t len; const char *s = JS_ToCStringLen(c, &len, argv[1]);
  if (!s) return JS_EXCEPTION;
  int32_t r = dom_text_content_set(node, s, (int32_t) len);
  JS_FreeCString(c, s);
  return r < 0 ? dom_error(c, r) : JS_UNDEFINED;
}

static JSValue n_get_attr(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t node; if (arg_i32(c, argv[0], &node)) return JS_EXCEPTION;
  size_t len; const char *s = JS_ToCStringLen(c, &len, argv[1]);
  if (!s) return JS_EXCEPTION;
  JSValue r = read_string(c, rd_attr, node, s, (int32_t) len, 1);
  JS_FreeCString(c, s);
  return r;
}

static JSValue n_set_attr(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t node; if (arg_i32(c, argv[0], &node)) return JS_EXCEPTION;
  size_t nl, vl;
  const char *nm = JS_ToCStringLen(c, &nl, argv[1]);
  if (!nm) return JS_EXCEPTION;
  const char *v = JS_ToCStringLen(c, &vl, argv[2]);
  if (!v) { JS_FreeCString(c, nm); return JS_EXCEPTION; }
  int32_t r = dom_set_attribute(node, nm, (int32_t) nl, v, (int32_t) vl);
  JS_FreeCString(c, nm); JS_FreeCString(c, v);
  return r < 0 ? dom_error(c, r) : JS_UNDEFINED;
}

static JSValue n_create(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  size_t len; const char *s = JS_ToCStringLen(c, &len, argv[0]);
  if (!s) return JS_EXCEPTION;
  int32_t r = dom_create_element(s, (int32_t) len);
  JS_FreeCString(c, s);
  return r < 0 ? dom_error(c, r) : JS_NewInt32(c, r);
}

static JSValue n_append(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t p, k;
  if (arg_i32(c, argv[0], &p) || arg_i32(c, argv[1], &k)) return JS_EXCEPTION;
  int32_t r = dom_append_child(p, k);
  return r < 0 ? dom_error(c, r) : JS_UNDEFINED;
}

static JSValue n_listen(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t node, cb;
  if (arg_i32(c, argv[0], &node) || arg_i32(c, argv[2], &cb)) return JS_EXCEPTION;
  size_t len; const char *t = JS_ToCStringLen(c, &len, argv[1]);
  if (!t) return JS_EXCEPTION;
  int32_t r = dom_add_event_listener(node, t, (int32_t) len, cb);
  JS_FreeCString(c, t);
  return r < 0 ? dom_error(c, r) : JS_UNDEFINED;
}

static JSValue n_timer(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t cb, delay, rep;
  if (arg_i32(c, argv[0], &cb) || arg_i32(c, argv[1], &delay) || arg_i32(c, argv[2], &rep))
    return JS_EXCEPTION;
  int32_t r = dom_set_timer(cb, delay < 0 ? 0 : delay, rep ? 1 : 0);
  return r < 0 ? dom_error(c, r) : JS_NewInt32(c, r);
}

static JSValue n_clear_timer(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  int32_t t; if (arg_i32(c, argv[0], &t)) return JS_EXCEPTION;
  dom_clear_timer(t);
  return JS_UNDEFINED;
}

static JSValue n_log(JSContext *c, JSValueConst this_val, int argc, JSValueConst *argv) {
  size_t len; const char *s = JS_ToCStringLen(c, &len, argv[0]);
  if (!s) return JS_EXCEPTION;
  dom_console_log(s, (int32_t) len);
  JS_FreeCString(c, s);
  return JS_UNDEFINED;
}

/* ---- the prelude: the DOM objects page scripts see, in JavaScript ----------- */

static const char prelude[] =
"(function (n) {\n"
"  'use strict';\n"
"  const callbacks = new Map(); let nextCallback = 1;\n"
"  const register = f => { const id = nextCallback++; callbacks.set(id, f); return id; };\n"
"  const elements = new Map();\n"
"  const wrap = id => id < 0 ? null : (elements.get(id) ?? make(id));\n"
"  const ids = new WeakMap();\n"
"  const idOf = e => { const id = ids.get(e); if (id === undefined) throw new TypeError('not a node'); return id; };\n"
"  const listeners = new Map();\n"
"  class Element {\n"
"    get nodeId() { return idOf(this); }\n"
"    get tagName() { return n.tag(idOf(this)).toUpperCase(); }\n"
"    get localName() { return n.tag(idOf(this)); }\n"
"    get id() { return n.getAttr(idOf(this), 'id') ?? ''; }\n"
"    set id(v) { n.setAttr(idOf(this), 'id', String(v)); }\n"
"    get textContent() { return n.getText(idOf(this)); }\n"
"    set textContent(v) { n.setText(idOf(this), v === null ? '' : String(v)); }\n"
"    getAttribute(name) { return n.getAttr(idOf(this), String(name)); }\n"
"    hasAttribute(name) { return n.getAttr(idOf(this), String(name)) !== null; }\n"
"    setAttribute(name, value) { n.setAttr(idOf(this), String(name), String(value)); }\n"
"    appendChild(child) { n.append(idOf(this), idOf(child)); return child; }\n"
"    append(...xs) { for (const x of xs) n.append(idOf(this), idOf(x)); }\n"
"    addEventListener(type, callback) {\n"
"      if (typeof callback !== 'function') return;\n"
"      const id = idOf(this), key = id + ' ' + type;\n"
"      let list = listeners.get(key); if (!list) listeners.set(key, list = []);\n"
"      if (list.includes(callback)) return;\n"
"      list.push(callback);\n"
"      const self = this;\n"
"      n.listen(id, String(type), register(event => callback.call(self, event)));\n"
"    }\n"
"    get onclick() { return handlers.get(this) ?? null; }\n"
"    set onclick(f) {\n"
"      if (!handlers.has(this)) { const self = this; n.listen(idOf(this), 'click', register(event => { const h = handlers.get(self); if (typeof h === 'function' && h.call(self, event) === false) event.preventDefault(); })); }\n"
"      handlers.set(this, typeof f === 'function' ? f : null);\n"
"    }\n"
"  }\n"
"  const handlers = new WeakMap();\n"
"  const make = id => { const e = Object.create(Element.prototype); ids.set(e, id); elements.set(id, e); return e; };\n"
"  const document = Object.freeze({\n"
"    getElementById: id => wrap(n.byId(String(id))),\n"
"    querySelector(sel) {\n"
"      sel = String(sel);\n"
"      if (/^#[A-Za-z_][A-Za-z0-9_-]*$/.test(sel)) return wrap(n.byId(sel.slice(1)));\n"
"      if (sel === 'body') return wrap(n.root(1));\n"
"      if (sel === 'html') return wrap(n.root(0));\n"
"      throw new SyntaxError('only #id, body and html selectors are supported');\n"
"    },\n"
"    createElement: name => wrap(n.create(String(name))),\n"
"    get documentElement() { return wrap(n.root(0)); },\n"
"    get body() { return wrap(n.root(1)); },\n"
"    get head() { return wrap(n.root(2)); },\n"
"  });\n"
"  const timer = (repeat, f, delay, args) => {\n"
"    const run = typeof f === 'function' ? () => f(...args) : () => (0, eval)(String(f));\n"
"    return n.timer(register(run), Number(delay) || 0, repeat);\n"
"  };\n"
"  const def = (name, value) => Object.defineProperty(globalThis, name, { value, writable: true, configurable: true });\n"
"  def('document', document);\n"
"  def('window', globalThis);\n"
"  def('self', globalThis);\n"
"  def('console', Object.freeze({ log: (...xs) => n.log(xs.map(String).join(' ')),\n"
"    error: (...xs) => n.log(xs.map(String).join(' ')), warn: (...xs) => n.log(xs.map(String).join(' ')) }));\n"
"  def('setTimeout', (f, delay, ...args) => timer(0, f, delay, args));\n"
"  def('setInterval', (f, delay, ...args) => timer(1, f, delay, args));\n"
"  def('clearTimeout', id => n.clearTimer(Number(id) | 0));\n"
"  def('clearInterval', id => n.clearTimer(Number(id) | 0));\n"
"  def('queueMicrotask', f => { if (typeof f !== 'function') throw new TypeError('queueMicrotask needs a function'); Promise.resolve().then(() => f()); });\n"
"  def('Element', Element);\n"
"  let current = null;\n"
"  return {\n"
"    call(id, target, seq) {\n"
"      const f = callbacks.get(id); if (!f) throw new TypeError('unknown callback ' + id);\n"
"      if (target < 0) { f(); return ''; }\n"
"      if (!current || current.seq !== seq) {\n"
"        let prevented = false;\n"
"        const node = wrap(target);\n"
"        current = { seq, event: Object.freeze({ type: 'click', target: node, currentTarget: node, cancelable: true,\n"
"          get defaultPrevented() { return prevented; }, preventDefault() { prevented = true; } }) };\n"
"      }\n"
"      f(current.event);\n"
"      return current.event.defaultPrevented ? 'prevented' : '';\n"
"    },\n"
"    release(id) { callbacks.delete(id); }\n"
"  };\n"
"})";

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
  JS_CFUNC_DEF("root", 1, n_root),
  JS_CFUNC_DEF("tag", 1, n_tag),
  JS_CFUNC_DEF("getText", 1, n_get_text),
  JS_CFUNC_DEF("setText", 2, n_set_text),
  JS_CFUNC_DEF("getAttr", 2, n_get_attr),
  JS_CFUNC_DEF("setAttr", 3, n_set_attr),
  JS_CFUNC_DEF("create", 1, n_create),
  JS_CFUNC_DEF("append", 2, n_append),
  JS_CFUNC_DEF("listen", 3, n_listen),
  JS_CFUNC_DEF("timer", 3, n_timer),
  JS_CFUNC_DEF("clearTimer", 1, n_clear_timer),
  JS_CFUNC_DEF("log", 1, n_log),
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
  JSValue f = JS_Eval(ctx, prelude, sizeof prelude - 1, "<foafnaut-prelude>", JS_EVAL_TYPE_GLOBAL);
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
  uint8_t *r = JS_IsException(v) ? result_of_exception() : result_of_value(v, 0);
  JS_FreeValue(ctx, v);
  checkpoint();
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
  checkpoint();
  return r;
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
int32_t dom_document_element(int32_t which) { return -6; }
int32_t dom_tag_name(int32_t node, char *buf, int32_t cap) { return -6; }
int32_t dom_text_content_get(int32_t node, char *buf, int32_t cap) { return -6; }
int32_t dom_text_content_set(int32_t node, const char *s, int32_t len) { return -6; }
int32_t dom_get_attribute(int32_t node, const char *name, int32_t nlen, char *buf, int32_t cap) { return -6; }
int32_t dom_set_attribute(int32_t node, const char *name, int32_t nlen, const char *value, int32_t vlen) { return -6; }
int32_t dom_create_element(const char *name, int32_t len) { return -6; }
int32_t dom_append_child(int32_t parent, int32_t child) { return -6; }
int32_t dom_add_event_listener(int32_t node, const char *type, int32_t tlen, int32_t callback) { return -6; }
int32_t dom_set_timer(int32_t callback, int32_t delay_ms, int32_t repeat) { return -6; }
int32_t dom_clear_timer(int32_t timer) { return -6; }
int32_t dom_console_log(const char *s, int32_t len) { return -6; }

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
