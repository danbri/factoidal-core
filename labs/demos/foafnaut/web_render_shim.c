#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_WebRender(uint8_t builtin);
extern lean_object *web_render_compile(lean_object *,uint32_t,uint32_t);
void initialize_libuv(void) {}
static int ready(void) {
  static int initialized;
  if (initialized) return 1;
  lean_initialize_runtime_module();
  lean_object *result=initialize_WebRender(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return 0; }
  lean_dec(result); lean_io_mark_end_initialization(); initialized=1; return 1;
}
char *web_render_call(const char *html,uint32_t width,uint32_t height) {
  if (!ready()) return NULL;
  lean_object *value=web_render_compile(lean_mk_string(html),width,height);
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
void web_render_free(char *value) { free(value); }
extern lean_object *web_render_pick_link(lean_object *,uint32_t,uint32_t,double,double);
char *web_render_hit(const char *regions,uint32_t width,uint32_t height,double x,double y) {
  if (!ready()) return NULL;
  lean_object *value=web_render_pick_link(lean_mk_string(regions),width,height,x,y);
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
