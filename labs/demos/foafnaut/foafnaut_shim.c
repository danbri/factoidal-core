#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_FoafLiveBridge(uint8_t builtin);
extern lean_object *foafnaut_initialize(lean_object *rdf, uint32_t width, uint32_t height);
extern lean_object *foafnaut_initialize_policy(lean_object *rdf, uint32_t width, uint32_t height, lean_object *policy);
extern lean_object *foafnaut_transition(lean_object *wire, uint32_t kind, int32_t a, int32_t b);
extern lean_object *foafnaut_snapshot(lean_object *wire);
extern lean_object *foafnaut_insert_text(lean_object *wire, lean_object *text);
extern lean_object *foafnaut_svg(lean_object *wire, lean_object *policy);
extern lean_object *foafnaut_checked_picture(lean_object *wire, lean_object *policy);
extern lean_object *foafnaut_live_create(lean_object *rdf, uint32_t width, uint32_t height, lean_object *policy, lean_object *time);
extern lean_object *foafnaut_live_transition(lean_object *state, uint32_t kind, int32_t a, int32_t b, lean_object *time);
extern lean_object *foafnaut_live_insert(lean_object *state, lean_object *text, lean_object *time);
extern lean_object *foafnaut_live_present(lean_object *state, lean_object *time);
extern lean_object *foafnaut_live_ack(lean_object *state, lean_object *token);
extern lean_object *foafnaut_live_frame(lean_object *state, uint8_t shader);
extern lean_object *foafnaut_live_svg(lean_object *state);
extern lean_object *foafnaut_live_commit(lean_object *previous, lean_object *proposed);
/* One holder per WASM module instance. No state pointer or serialized candidate
   crosses the public ABI. Lean owns every transition and admission decision. */
static lean_object *live_state;
/* A fresh WASM instance is required for another session. In particular, old
   render tokens can never acknowledge a restarted session in this holder. */
static int live_started;
void initialize_libuv(void) {}
static int ensure_init(void) {
  static int initialized;
  if (initialized) return 1;
  lean_initialize_runtime_module();
  lean_object *result = initialize_FoafLiveBridge(1);
  if (!lean_io_result_is_ok(result)) { lean_dec(result); return 0; }
  lean_dec(result); lean_io_mark_end_initialization(); initialized = 1; return 1;
}
static char *copy_result(lean_object *value) {
  char *copy = strdup(lean_string_cstr(value)); lean_dec(value); return copy;
}
char *foafnaut_init(const char *rdf, uint32_t width, uint32_t height) {
  return ensure_init() ? copy_result(foafnaut_initialize(lean_mk_string(rdf), width, height)) : NULL;
}
char *foafnaut_init_policy(const char *rdf, uint32_t width, uint32_t height, const char *policy) {
  return ensure_init() ? copy_result(foafnaut_initialize_policy(lean_mk_string(rdf), width, height, lean_mk_string(policy))) : NULL;
}
char *foafnaut_export_svg(const char *wire, const char *policy) {
  return ensure_init() ? copy_result(foafnaut_svg(lean_mk_string(wire), lean_mk_string(policy))) : NULL;
}
char *foafnaut_picture_checked(const char *wire, const char *policy) {
  return ensure_init() ? copy_result(foafnaut_checked_picture(lean_mk_string(wire), lean_mk_string(policy))) : NULL;
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
static char *live_commit(lean_object *next) {
  lean_inc(next);
  char *result = copy_result(foafnaut_live_frame(next, 0));
  live_state = foafnaut_live_commit(live_state, next);
  return result;
}
char *foafnaut_live_start(const char *rdf, uint32_t width, uint32_t height, const char *policy, const char *time) {
  if (!ensure_init()) return NULL;
  if (live_started) return strdup("{\"error\":\"live session already initialized; create a new WASM instance\"}");
  live_started = 1;
  live_state = foafnaut_live_create(lean_mk_string(rdf), width, height, lean_mk_string(policy), lean_mk_string(time));
  lean_inc(live_state);
  return copy_result(foafnaut_live_frame(live_state, 1));
}
char *foafnaut_live_event(uint32_t kind, int32_t a, int32_t b, const char *time) {
  if (!live_state) return strdup("{\"error\":\"live session is not initialized\"}");
  lean_inc(live_state);
  return live_commit(foafnaut_live_transition(live_state, kind, a, b, lean_mk_string(time)));
}
char *foafnaut_live_text(const char *text, const char *time) {
  if (!live_state) return strdup("{\"error\":\"live session is not initialized\"}");
  lean_inc(live_state);
  return live_commit(foafnaut_live_insert(live_state, lean_mk_string(text), lean_mk_string(time)));
}
char *foafnaut_live_tick(const char *time) {
  if (!live_state) return strdup("{\"error\":\"live session is not initialized\"}");
  lean_inc(live_state);
  return live_commit(foafnaut_live_present(live_state, lean_mk_string(time)));
}
char *foafnaut_live_acknowledge(const char *token) {
  if (!live_state) return strdup("{\"error\":\"live session is not initialized\"}");
  lean_inc(live_state);
  return live_commit(foafnaut_live_ack(live_state, lean_mk_string(token)));
}
char *foafnaut_live_export_svg(void) {
  if (!live_state) return strdup("{\"error\":\"live session is not initialized\"}");
  lean_inc(live_state);
  return copy_result(foafnaut_live_svg(live_state));
}
char *foafnaut_live_dispose(void) {
  if (live_state) { lean_dec(live_state); live_state = NULL; }
  return strdup("{\"closed\":true}");
}
void foafnaut_free(char *value) { free(value); }
