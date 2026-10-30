#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_RenderPlan(uint8_t builtin);
extern lean_object *render_plan_request(lean_object *, lean_object *, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t);
void initialize_libuv(void) {}
char *render_plan(const char *mode, const char *format, uint32_t width, uint32_t height,
                  uint32_t floats, uint32_t maxUniformBytes, uint32_t maxDimension) {
  static int initialized;
  if (!initialized) {
    lean_initialize_runtime_module();
    lean_object *init=initialize_RenderPlan(1);
    if (!lean_io_result_is_ok(init)) { lean_dec(init); return NULL; }
    lean_dec(init); lean_io_mark_end_initialization(); initialized=1;
  }
  lean_object *value=render_plan_request(lean_mk_string(mode),lean_mk_string(format),
    width,height,floats,maxUniformBytes,maxDimension);
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
void render_plan_free(char *value) { free(value); }
