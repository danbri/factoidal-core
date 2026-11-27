/* dladdr and Dl_info (glibc declares them only with _GNU_SOURCE). */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_WebRenderRDF(uint8_t builtin);
extern lean_object *initialize_WebRenderFont(uint8_t builtin);
extern lean_object *initialize_WebDocument(uint8_t builtin);
extern lean_object *web_render_compile(lean_object *,uint32_t,uint32_t);
extern lean_object *web_document_engine_new(lean_object *);
/* WebDocument.engineEnd: the session's real-time audio runs end before its state is freed. */
extern lean_object *web_document_end(lean_object *);
#ifndef __EMSCRIPTEN__
#include <dlfcn.h>
#include <pthread.h>
#endif
/* An engine session: the engine's state between calls (WebDocument.Engine; issue 390), an
   ordinary Lean value, for one tab. Each call passes it (owned, so Lean holds the only
   reference and changes it in place) and gets the next state back. One library holds any
   number of sessions; nothing else in this file or in the engine is per tab
   (docs/designissues/2026-11-26-foafnaut-engine-sessions.md). A session's calls run one at a
   time (`lock`); calls on two sessions may run at the same time on two threads. The calls
   with no session argument use `default_session`, made at start: the Wasm build and hosts
   from before sessions use only that one. */
typedef struct web_session {
  lean_object *engine;
  /* A session on its own Lean task (WebSession.Handle; web_session_new_task), or NULL: then
     `engine` is the state and the caller's thread runs the calls. */
  lean_object *task;
#ifndef __EMSCRIPTEN__
  pthread_mutex_t lock;
#endif
} web_session;
#ifndef __EMSCRIPTEN__
/* WebSession.lean: the session's task and its calls. Each call waits on the calling thread
   for the task's answer; the arguments are made here, on the calling thread. The handle is an
   owned argument of each (a Lean export can not borrow), so a caller adds a reference first;
   the handle's counts are atomic (lean_mark_mt in web_session_new_task). */
extern lean_object *web_session_task_start(lean_object *);
extern lean_object *web_session_task_call(lean_object *,lean_object *,lean_object *,uint32_t,uint32_t);
extern lean_object *web_session_task_call_bin(lean_object *,lean_object *,lean_object *,uint32_t,uint32_t);
extern lean_object *web_session_task_font(lean_object *,lean_object *,lean_object *,lean_object *,uint32_t);
extern lean_object *web_session_task_image(lean_object *,lean_object *,lean_object *,lean_object *);
extern lean_object *web_session_task_hit(lean_object *,lean_object *,uint32_t,uint32_t,double,double);
extern lean_object *web_session_task_close(lean_object *,uint8_t);
extern lean_object *web_session_task_cancel(lean_object *,uint8_t);
#endif
static web_session *default_session;
static void session_lock(web_session *s) {
#ifndef __EMSCRIPTEN__
  pthread_mutex_lock(&s->lock);
#else
  (void)s;
#endif
}
static void session_unlock(web_session *s) {
#ifndef __EMSCRIPTEN__
  pthread_mutex_unlock(&s->lock);
#else
  (void)s;
#endif
}
/* Take the state and the answer out of a pair (Engine × answer); the pair is freed. The
   caller holds the session's lock. */
static lean_object *next_state(web_session *s,lean_object *pair) {
  s->engine=lean_ctor_get(pair,0); lean_inc(s->engine);
  lean_object *answer=lean_ctor_get(pair,1); lean_inc(answer);
  lean_dec(pair);
  return answer;
}
static web_session *session_make(void) {
  web_session *s=calloc(1,sizeof *s);
  if (!s) return NULL;
#ifndef __EMSCRIPTEN__
  if (pthread_mutex_init(&s->lock,NULL)!=0) { free(s); return NULL; }
#endif
  s->engine=web_document_engine_new(lean_box(0));
  return s;
}
/* The exports that read the clock or random bytes are BaseIO; this Lean passes no world
   argument to them and returns the value itself, as for a pure export. */
#ifdef __EMSCRIPTEN__
// Wasm has no libuv; the native runtime has its own.
void initialize_libuv(void) {}
#endif
#ifndef __EMSCRIPTEN__
#include <unistd.h>
/* Lean's task manager: the pool that runs the engine's `Task.spawn` work (L4Factoidal/Par;
   issue 398). Which work is split, and into how many chunks, is decided in Lean, and the
   result does not depend on the pool (Par.mapChunks_eq). The host only sizes the pool: one
   thread fewer than the online CPUs (the calling thread works too), at most LEAN_POOL_CAP;
   FOAFNAUT_LEAN_THREADS=N sets it (0: no task manager, so every task runs at once on the
   calling thread, as in the Wasm build). */
#define LEAN_POOL_CAP 6
static unsigned pool_size(void) {
  const char *set=getenv("FOAFNAUT_LEAN_THREADS");
  if (set && *set) { long n=strtol(set,NULL,10); return n<0 ? 0 : (n>LEAN_POOL_CAP ? LEAN_POOL_CAP : (unsigned)n); }
  long cpus=sysconf(_SC_NPROCESSORS_ONLN);
  if (cpus<=1) return 0;
  return cpus-1>LEAN_POOL_CAP ? LEAN_POOL_CAP : (unsigned)(cpus-1);
}
static unsigned pool_threads;
#endif
/* The runtime, the task manager and the module initialisers, once for the process: the
first call from any thread starts them, and a call from another thread at the same time
waits for that start (pthread_once). 1 when they started, 0 when a module failed. */
static int started;
static void start_once(void) {
  lean_initialize_runtime_module();
#ifndef __EMSCRIPTEN__
  pool_threads=pool_size();
  if (pool_threads>0) lean_init_task_manager_using(pool_threads);
#endif
  lean_object *result=initialize_WebRenderRDF(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return; }
  lean_dec(result);
  result=initialize_WebRenderFont(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return; }
  lean_dec(result);
  result=initialize_WebDocument(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return; }
  lean_dec(result); lean_io_mark_end_initialization();
  default_session=session_make();
  started=default_session!=NULL;
}
static int ready(void) {
#ifndef __EMSCRIPTEN__
  static pthread_once_t once=PTHREAD_ONCE_INIT;
  pthread_once(&once,start_once);
#else
  static int tried;
  if (!tried) { tried=1; start_once(); }
#endif
  return started;
}
/* A new engine session with nothing held (no font, no page): NULL when the runtime did not
   start or memory ran out. End it with web_session_free. */
web_session *web_session_new(void) {
  if (!ready()) return NULL;
  return session_make();
}
#ifndef __EMSCRIPTEN__
/* Keep this library loaded until the process ends (RTLD_NODELETE), from the first task session
   on. A session's task runs on a thread of its own, which the host can not stop or wait for, so
   a dlclose of the last handle would unload code that the thread still runs. Deno closes its
   handles when its runtime ends (`deno test` does so after the last test, before it exits).
   Seen 2026-11-26: engine_sessions_test.ts ended with a segmentation fault on every run, a
   session task thread in lean_dec_ref_cold (freeing its engine state at the end of
   WebSession.serve) while Deno's runtime teardown was in dlclose. 1 when pinned. */
static int pinned;
web_session *web_session_new_task(void);
static void pin_once(void) {
  Dl_info info;
  if (!dladdr((void *)&web_session_new_task,&info) || !info.dli_fname) return;
  /* RTLD_NOLOAD: this library is loaded already; the handle is never closed. */
  pinned=dlopen(info.dli_fname,RTLD_LAZY|RTLD_NOLOAD|RTLD_NODELETE)!=NULL;
}
#endif
/* A new engine session on its own Lean task (Task.Priority.dedicated: a thread of its own;
   WebSession.lean): its calls run there, one at a time, in arrival order, and a caller waits
   on its own thread for its answer, so a host calls them from a thread that may wait (Deno:
   nonblocking FFI). NULL when the runtime did not start, when this library could not be kept
   loaded (pin_once), in the Wasm build, or with no task manager (FOAFNAUT_LEAN_THREADS=0), where
   a task would run on the calling thread. */
web_session *web_session_new_task(void) {
#ifdef __EMSCRIPTEN__
  return NULL;
#else
  if (!ready() || pool_threads==0) return NULL;
  static pthread_once_t pin=PTHREAD_ONCE_INIT;
  pthread_once(&pin,pin_once);
  /* No task session in a library that could be unloaded under its thread. */
  if (!pinned) return NULL;
  web_session *s=calloc(1,sizeof *s);
  if (!s) return NULL;
  if (pthread_mutex_init(&s->lock,NULL)!=0) { free(s); return NULL; }
  s->task=web_session_task_start(lean_box(0));
  /* Calls on two threads may read the handle at once: its counts are atomic from here on. */
  lean_mark_mt(s->task);
  return s;
#endif
}
/* Stop a session taking calls (task sessions): the calls it has are answered, a later call is
   answered with an error, and its task then ends. Does not wait. Nothing for other sessions. */
void web_session_close(web_session *s) {
#ifndef __EMSCRIPTEN__
  if (s && s->task) { lean_inc(s->task); lean_dec(web_session_task_close(s->task,0)); }
#else
  (void)s;
#endif
}
/* Stop a session (task sessions): close it and cancel its task (IO.cancel), so the call in
   progress stops at the engine's next check (WebWasm.Machine.canceled: before a render's layout
   and before its paint) and the calls not started are refused; a layout in progress runs to its
   end. Does not wait. Nothing for other sessions. */
void web_session_cancel(web_session *s) {
#ifndef __EMSCRIPTEN__
  if (s && s->task) { lean_inc(s->task); lean_dec(web_session_task_cancel(s->task,0)); }
#else
  (void)s;
#endif
}
/* End a session: its engine state is freed (a task session is closed first; its task frees
   the state when it ends). No call on it may run or come after this: a host frees a session
   only after every call it made on it has returned. The default session is never freed. Before
   the state is freed its real-time audio runs end (WebDocument.engineEnd, which takes the state);
   a task session's task does the same when it ends (WebSession.serve). */
void web_session_free(web_session *s) {
  if (!s || s==default_session) return;
#ifndef __EMSCRIPTEN__
  if (s->task) {
    /* The close takes the session's own reference to the handle: the handle is freed when the
       task ends (the task's closure holds the session, not the handle). */
    lean_dec(web_session_task_close(s->task,0));
    s->task=NULL;
  }
#endif
  session_lock(s);
  lean_object *e=s->engine; s->engine=NULL;
  session_unlock(s);
  if (e) lean_dec(web_document_end(e));
#ifndef __EMSCRIPTEN__
  pthread_mutex_destroy(&s->lock);
#endif
  free(s);
}
char *web_render_call(const char *html,uint32_t width,uint32_t height) {
  if (!ready()) return NULL;
  lean_object *value=web_render_compile(lean_mk_string(html),width,height);
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
extern lean_object *web_render_rdf_compile(lean_object *,uint32_t,uint32_t);
char *web_render_rdf_call(const char *source,uint32_t width,uint32_t height) {
  if (!ready()) return NULL;
  lean_object *value=web_render_rdf_compile(lean_mk_string(source),width,height);
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
extern lean_object *web_render_font_compile(lean_object *,lean_object *,uint32_t,uint32_t);
char *web_render_font_call(const char *html,const char *font_data,uint32_t width,uint32_t height) {
  if (!ready()) return NULL;
  lean_object *value=web_render_font_compile(lean_mk_string(html),lean_mk_string(font_data),width,height);
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
void web_render_free(char *value) { free(value); }
extern lean_object *web_document_compile(lean_object *,lean_object *,lean_object *,uint32_t,uint32_t);
/* A document request on session `s` (WebDocument.compile); the answer is JSON text. */
char *web_session_call(web_session *s,const char *html,const char *request,uint32_t width,uint32_t height) {
  if (!ready() || !s) return NULL;
  lean_object *h=lean_mk_string(html),*r=lean_mk_string(request),*value;
#ifndef __EMSCRIPTEN__
  if (s->task) { lean_inc(s->task); value=web_session_task_call(s->task,h,r,width,height); } else
#endif
  {
    session_lock(s);
    value=next_state(s,web_document_compile(s->engine,h,r,width,height));
    session_unlock(s);
  }
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
char *web_document_call(const char *html,const char *request,uint32_t width,uint32_t height) {
  if (!ready()) return NULL;
  return web_session_call(default_session,html,request,width,height);
}
extern lean_object *web_document_compile_bin(lean_object *,lean_object *,lean_object *,uint32_t,uint32_t);
/* The same request as web_document_call; the answer is bytes (WebDocument.packAnswer):
   a JSON head and the storage floats and tile words as raw sections, with no Base64.
   The first uint32 is the total length; out_len, if not NULL, gets it too. */
uint8_t *web_session_call_bin(web_session *s,const char *html,const char *request,uint32_t width,uint32_t height,uint32_t *out_len) {
  if (!ready() || !s) return NULL;
  lean_object *h=lean_mk_string(html),*r=lean_mk_string(request),*value;
#ifndef __EMSCRIPTEN__
  if (s->task) { lean_inc(s->task); value=web_session_task_call_bin(s->task,h,r,width,height); } else
#endif
  {
    session_lock(s);
    value=next_state(s,web_document_compile_bin(s->engine,h,r,width,height));
    session_unlock(s);
  }
  size_t size=lean_sarray_size(value);
  uint8_t *copy=malloc(size ? size : 1);
  if (copy) memcpy(copy,lean_sarray_cptr(value),size);
  lean_dec(value);
  if (out_len) *out_len=(uint32_t)size;
  return copy;
}
uint8_t *web_document_call_bin(const char *html,const char *request,uint32_t width,uint32_t height,uint32_t *out_len) {
  if (!ready()) return NULL;
  return web_session_call_bin(default_session,html,request,width,height,out_len);
}
extern lean_object *web_document_font_load_bin(lean_object *,lean_object *,lean_object *,lean_object *,uint32_t);
/* The fontLoad op with the font file as bytes (WebDocument.fontLoadBin): no Base64 and no
   JSON, so the file is not copied onto the call stack. The engine copies the bytes into
   a Lean ByteArray; the caller keeps and frees its own buffer. The answer is the
   fontLoad JSON answer, freed with web_render_free. fallback is 1 to add the font
   to the engine's list of fonts, 0 to replace the list. */
char *web_session_font_call_bin(web_session *s,const uint8_t *bytes,uint32_t length,const char *family,const char *sha256,uint32_t fallback) {
  if (!ready() || !s) return NULL;
  lean_object *array=lean_alloc_sarray(1,length,length);
  if (length) memcpy(lean_sarray_cptr(array),bytes,length);
  lean_object *f=lean_mk_string(family),*h=lean_mk_string(sha256),*value;
#ifndef __EMSCRIPTEN__
  if (s->task) { lean_inc(s->task); value=web_session_task_font(s->task,array,f,h,fallback); } else
#endif
  {
    session_lock(s);
    value=next_state(s,web_document_font_load_bin(s->engine,array,f,h,fallback));
    session_unlock(s);
  }
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
char *web_document_font_call_bin(const uint8_t *bytes,uint32_t length,const char *family,const char *sha256,uint32_t fallback) {
  if (!ready()) return NULL;
  return web_session_font_call_bin(default_session,bytes,length,family,sha256,fallback);
}
extern lean_object *web_document_image_load_bin(lean_object *,lean_object *,lean_object *,lean_object *);
/* The imageLoad op with the image as bytes (WebDocument.imageLoadBin): the engine holds
   the image by key and SHA-256, and render requests name it in heldImages, so its
   bytes cross once, not with every frame. The caller keeps and frees its own buffer.
   The answer is the imageLoad JSON answer, freed with web_render_free. A host calls
   this only after imageInfo says the engine has it (issue 1274). */
char *web_session_image_call_bin(web_session *s,const uint8_t *bytes,uint32_t length,const char *key,const char *sha256) {
  if (!ready() || !s) return NULL;
  lean_object *array=lean_alloc_sarray(1,length,length);
  if (length) memcpy(lean_sarray_cptr(array),bytes,length);
  lean_object *k=lean_mk_string(key),*h=lean_mk_string(sha256),*value;
#ifndef __EMSCRIPTEN__
  if (s->task) { lean_inc(s->task); value=web_session_task_image(s->task,array,k,h); } else
#endif
  {
    session_lock(s);
    value=next_state(s,web_document_image_load_bin(s->engine,array,k,h));
    session_unlock(s);
  }
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
char *web_document_image_call_bin(const uint8_t *bytes,uint32_t length,const char *key,const char *sha256) {
  if (!ready()) return NULL;
  return web_session_image_call_bin(default_session,bytes,length,key,sha256);
}
/* A page's bytes as text, decoded by Lean (WebDocument.decodeBin): the encoding's name, a
   line feed, the text. `charset` is the HTTP charset label, "" for none. */
extern lean_object *web_document_decode_bin(lean_object *,lean_object *);
char *web_document_decode_call_bin(const uint8_t *bytes,uint32_t length,const char *charset) {
  if (!ready()) return NULL;
  lean_object *array=lean_alloc_sarray(1,length,length);
  if (length) memcpy(lean_sarray_cptr(array),bytes,length);
  lean_object *value=web_document_decode_bin(array,lean_mk_string(charset));
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
/* The same with the user's default for undeclared pages ("" detect, "locale", or an
   encoding's name) and the system's language (WebDocument.decodeBinWith). */
extern lean_object *web_document_decode2_bin(lean_object *,lean_object *,lean_object *,lean_object *);
char *web_document_decode2_call_bin(const uint8_t *bytes,uint32_t length,const char *contentType,const char *fallback,const char *locale) {
  if (!ready()) return NULL;
  lean_object *array=lean_alloc_sarray(1,length,length);
  if (length) memcpy(lean_sarray_cptr(array),bytes,length);
  lean_object *value=web_document_decode2_bin(array,lean_mk_string(contentType),lean_mk_string(fallback),lean_mk_string(locale));
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
extern lean_object *web_render_font_requests(lean_object *);
char *web_render_font_requests_call(const char *html) {
  if (!ready()) return NULL;
  lean_object *value=web_render_font_requests(lean_mk_string(html));
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
extern lean_object *web_render_pick_link_kept(lean_object *,lean_object *,uint32_t,uint32_t,double,double);
char *web_session_hit(web_session *s,const char *regions,uint32_t width,uint32_t height,double x,double y) {
  if (!ready() || !s) return NULL;
  lean_object *r=lean_mk_string(regions),*value;
#ifndef __EMSCRIPTEN__
  if (s->task) { lean_inc(s->task); value=web_session_task_hit(s->task,r,width,height,x,y); } else
#endif
  {
    session_lock(s);
    value=next_state(s,web_render_pick_link_kept(s->engine,r,width,height,x,y));
    session_unlock(s);
  }
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
char *web_render_hit(const char *regions,uint32_t width,uint32_t height,double x,double y) {
  if (!ready()) return NULL;
  return web_session_hit(default_session,regions,width,height,x,y);
}
