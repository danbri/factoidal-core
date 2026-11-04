/* Pure string ABI only: initialize, call Lean, copy owned result, free result. */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_Graphics(uint8_t builtin);
extern lean_object *graphics_generate(uint32_t width, uint32_t height, uint32_t variant);
void initialize_libuv(void) {}

char *graphics_call(uint32_t width, uint32_t height, uint32_t variant) {
  static int initialized = 0;
  if (!initialized) {
    lean_initialize_runtime_module();
    lean_object *result = initialize_Graphics(1);
    if (!lean_io_result_is_ok(result)) { lean_dec(result); return NULL; }
    lean_dec(result);
    lean_io_mark_end_initialization();
    initialized = 1;
  }
  lean_object *value = graphics_generate(width, height, variant);
  char *copy = strdup(lean_string_cstr(value));
  lean_dec(value);
  return copy;
}
void graphics_free(char *value) { free(value); }
