#include <lean/lean.h>
void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
lean_object* initialize_Repro(uint8_t);
lean_object* repro_run(lean_object*);
void initialize_libuv(void) {}
int main(void) {
  lean_initialize_runtime_module();
  lean_object* r = initialize_Repro(1);
  if (!lean_io_result_is_ok(r)) return 2;
  lean_dec_ref(r);
  lean_io_mark_end_initialization();
  r = repro_run(lean_box(0));
  return lean_io_result_is_ok(r) ? 0 : 3;
}
