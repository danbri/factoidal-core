// wasi-port/cxa_trap.cpp — the C++ ABI throw entry points for the
// "no exception handling" build (WC_EH=trap): the runtime is compiled with
// -fexceptions but without -fwasm-exceptions, so LLVM drops every catch
// block and a throw reaches __cxa_throw, which prints the exception type and
// traps. Why this build exists: jco 1.38 (and its wasmparser) rejects a
// component that uses the wasm exception-handling proposal (blocker B12), so
// the browser path through jco needs a module without it. Lean-compiled C
// does not throw; only the C++ runtime does, on conditions that end the
// computation anyway (out of memory, stack size query failure, internal
// errors), so a trap changes the error report, not an answer.
#include <cstdio>
#include <cstdlib>
#include <typeinfo>

extern "C" {
void *__cxa_allocate_exception(size_t n) noexcept { return std::malloc(n); }
void __cxa_free_exception(void *p) noexcept { std::free(p); }
[[noreturn]] void __cxa_throw(void *, std::type_info *t, void (*)(void *)) {
    std::fprintf(stderr, "uncaught C++ exception %s (build without exception handling)\n",
                 t ? t->name() : "?");
    std::abort();
}
void *__cxa_begin_catch(void *p) noexcept { return p; }
void __cxa_end_catch() {}
[[noreturn]] void __cxa_rethrow() { std::abort(); }
}
