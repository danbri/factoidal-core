#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_Demos(uint8_t builtin);
extern lean_object *demos_initialize(uint32_t width,uint32_t height,uint32_t kind);
extern lean_object *demos_transition(lean_object *wire,uint32_t kind,int32_t a,int32_t b);
void initialize_libuv(void) {}
static int ensure_init(void) {
  static int initialized;
  if (initialized) return 1;
  lean_initialize_runtime_module();
  lean_object *result=initialize_Demos(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return 0; }
  lean_dec(result); lean_io_mark_end_initialization(); initialized=1; return 1;
}
static char *copy_result(lean_object *value) {
  char *copy=strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
char *demos_init(uint32_t width,uint32_t height,uint32_t kind) {
  return ensure_init() ? copy_result(demos_initialize(width,height,kind)) : NULL;
}
char *demos_step(const char *wire,uint32_t kind,int32_t a,int32_t b) {
  return ensure_init() ? copy_result(demos_transition(lean_mk_string(wire),kind,a,b)) : NULL;
}
void demos_free(char *value) { free(value); }
