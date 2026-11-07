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
#ifdef __EMSCRIPTEN__
// Wasm has no libuv; the native runtime has its own.
void initialize_libuv(void) {}
#endif
static int ready(void) {
  static int initialized;
  if (initialized) return 1;
  lean_initialize_runtime_module();
  lean_object *result=initialize_WebRenderRDF(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return 0; }
  lean_dec(result);
  result=initialize_WebRenderFont(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return 0; }
  lean_dec(result);
  result=initialize_WebDocument(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return 0; }
  lean_dec(result); lean_io_mark_end_initialization(); initialized=1; return 1;
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
extern lean_object *web_document_compile(lean_object *,lean_object *,uint32_t,uint32_t);
char *web_document_call(const char *html,const char *request,uint32_t width,uint32_t height) {
  if (!ready()) return NULL;
  lean_object *value=web_document_compile(lean_mk_string(html),lean_mk_string(request),width,height);
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
extern lean_object *web_document_compile_bin(lean_object *,lean_object *,uint32_t,uint32_t);
/* The same request as web_document_call; the answer is bytes (WebDocument.packAnswer):
   a JSON head and the storage floats and tile words as raw sections, with no Base64.
   The first uint32 is the total length; out_len, if not NULL, gets it too. */
uint8_t *web_document_call_bin(const char *html,const char *request,uint32_t width,uint32_t height,uint32_t *out_len) {
  if (!ready()) return NULL;
  lean_object *value=web_document_compile_bin(lean_mk_string(html),lean_mk_string(request),width,height);
  size_t size=lean_sarray_size(value);
  uint8_t *copy=malloc(size ? size : 1);
  if (copy) memcpy(copy,lean_sarray_cptr(value),size);
  lean_dec(value);
  if (out_len) *out_len=(uint32_t)size;
  return copy;
}
extern lean_object *web_document_font_load_bin(lean_object *,lean_object *,lean_object *,uint32_t);
/* The fontLoad op with the font file as bytes (WebDocument.fontLoadBin): no Base64 and no
   JSON, so the file is not copied onto the call stack. The engine copies the bytes into
   a Lean ByteArray; the caller keeps and frees its own buffer. The answer is the
   fontLoad JSON answer, freed with web_render_free. fallback is 1 to add the font
   to the engine's list of fonts, 0 to replace the list. */
char *web_document_font_call_bin(const uint8_t *bytes,uint32_t length,const char *family,const char *sha256,uint32_t fallback) {
  if (!ready()) return NULL;
  lean_object *array=lean_alloc_sarray(1,length,length);
  if (length) memcpy(lean_sarray_cptr(array),bytes,length);
  lean_object *value=web_document_font_load_bin(array,lean_mk_string(family),lean_mk_string(sha256),fallback);
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
extern lean_object *web_render_font_requests(lean_object *);
char *web_render_font_requests_call(const char *html) {
  if (!ready()) return NULL;
  lean_object *value=web_render_font_requests(lean_mk_string(html));
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
extern lean_object *web_render_pick_link(lean_object *,uint32_t,uint32_t,double,double);
char *web_render_hit(const char *regions,uint32_t width,uint32_t height,double x,double y) {
  if (!ready()) return NULL;
  lean_object *value=web_render_pick_link(lean_mk_string(regions),width,height,x,y);
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
