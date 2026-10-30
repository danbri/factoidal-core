#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_FoafNaut(uint8_t builtin);
extern lean_object *foafnaut_initialize(lean_object *rdf, uint32_t width, uint32_t height);
extern lean_object *foafnaut_transition(lean_object *wire, uint32_t kind, int32_t a, int32_t b);
extern lean_object *foafnaut_snapshot(lean_object *wire);
extern lean_object *foafnaut_insert_text(lean_object *wire, lean_object *text);
void initialize_libuv(void) {}
static int ensure_init(void) {
  static int initialized;
  if (initialized) return 1;
  lean_initialize_runtime_module();
  lean_object *result = initialize_FoafNaut(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return 0; }
  lean_dec(result); lean_io_mark_end_initialization(); initialized = 1; return 1;
}
static char *copy_result(lean_object *value) {
  char *copy = strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
char *foafnaut_init(const char *rdf, uint32_t width, uint32_t height) {
  return ensure_init() ? copy_result(foafnaut_initialize(lean_mk_string(rdf), width, height)) : NULL;
}
char *foafnaut_step(const char *wire, uint32_t kind, int32_t a, int32_t b) {
  return ensure_init() ? copy_result(foafnaut_transition(lean_mk_string(wire), kind, a, b)) : NULL;
}
char *foafnaut_picture(const char *wire) {
  return ensure_init() ? copy_result(foafnaut_snapshot(lean_mk_string(wire))) : NULL;
}
char *foafnaut_text(const char *wire, const char *text) {
  return ensure_init() ? copy_result(foafnaut_insert_text(lean_mk_string(wire), lean_mk_string(text))) : NULL;
}
void foafnaut_free(char *value) { free(value); }
