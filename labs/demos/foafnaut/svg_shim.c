#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_SVG(uint8_t builtin);
extern lean_object *svg_compile(lean_object *xml,uint32_t width,uint32_t height);
extern lean_object *svg_sample(lean_object *xml,uint32_t width,uint32_t height,uint32_t x,uint32_t y);
void initialize_libuv(void) {}
static int ready(void) {
  static int initialized;
  if(initialized)return 1;
  lean_initialize_runtime_module();lean_object *result=initialize_SVG(1);
  if(!lean_io_result_is_ok(result)){lean_dec(result);return 0;}
  lean_dec(result);lean_io_mark_end_initialization();initialized=1;return 1;
}
static char *copy_result(lean_object *value){char *copy=strdup(lean_string_cstr(value));lean_dec(value);return copy;}
char *svg_call(const char *xml,uint32_t width,uint32_t height){return ready()?copy_result(svg_compile(lean_mk_string(xml),width,height)):NULL;}
char *svg_pixel(const char *xml,uint32_t width,uint32_t height,uint32_t x,uint32_t y){return ready()?copy_result(svg_sample(lean_mk_string(xml),width,height,x,y)):NULL;}
void svg_free(char *value){free(value);}
