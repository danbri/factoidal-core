// wasi-port/process_stubs.cpp — the two initialisers that Lean v4.33.1's
// runtime/init_module.cpp calls unconditionally, for builds that leave out
// runtime/process.cpp (fork, waitpid, pipes: no WASI equivalent; blocker B8)
// and runtime/libuv.cpp (no libuv for wasm32; the shipped Emscripten build
// stubs initialize_libuv the same way, formal/lean4/Wasm/l4_stubs.c).
// IO.Process.spawn and the other process primitives are then absent: a call
// would be an undefined symbol at link time, and none is reached.
namespace lean {
void initialize_process() {}
void finalize_process() {}
}
extern "C" void initialize_libuv(void) {}
