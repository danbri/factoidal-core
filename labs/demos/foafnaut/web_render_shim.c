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
