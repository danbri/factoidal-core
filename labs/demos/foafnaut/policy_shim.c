#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_PolicyBridge(uint8_t builtin);
extern lean_object *layout_policy_request(lean_object *input);
void initialize_libuv(void) {}
char *layout_policy(const char *input) {
  static int initialized;
  if (!initialized) {
    lean_initialize_runtime_module();
    lean_object *init = initialize_PolicyBridge(1);
    if (!lean_io_result_is_ok(init)) { lean_dec(init); return NULL; }
    lean_dec(init); lean_io_mark_end_initialization(); initialized = 1;
  }
  lean_object *value = layout_policy_request(lean_mk_string(input));
  char *copy = strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
void layout_policy_free(char *value) { free(value); }
