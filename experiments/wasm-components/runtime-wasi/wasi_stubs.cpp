/*
wasi_stubs.cpp — the definitions that the wasi-sdk build of the Lean v4.33.1
runtime needs and that WASI cannot give. experiments/wasm-components only.

1. process.cpp is not compiled (no processes under WASI); init_module.cpp
   still calls its initialiser and finaliser, defined empty below.
   stack_overflow.cpp is not compiled: WASI has no signals and no alternate
   signal stack. A stack overflow is a wasm trap, as in the Emscripten build.
2. C++ exceptions. wasi-sdk 27 and 30 build libc++abi with -fno-exceptions,
   so __cxa_throw is not defined (wasi-sdk README, "Notable Limitations").
   The runtime throws only for conditions it does not recover from in the
   code that this experiment links (out of memory, internal errors). These
   definitions print the exception and abort: a trap, never a silent
   continuation. Pure Lean code reports errors as values, not exceptions.
3. initialize_libuv: the same single stub as formal/lean4/Wasm/l4_stubs.c.
*/
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <typeinfo>

namespace lean {
class stack_guard { public: stack_guard(); ~stack_guard(); };
stack_guard::stack_guard() {}
stack_guard::~stack_guard() {}
void initialize_stack_overflow() {}
void finalize_stack_overflow() {}
void initialize_process() {}
void finalize_process() {}
}

extern "C" {
void *__cxa_allocate_exception(size_t size) noexcept {
    void *p = std::calloc(1, size);
    if (!p) std::abort();
    return p;
}
void __cxa_free_exception(void *p) noexcept { std::free(p); }
[[noreturn]] void __cxa_throw(void *obj, std::type_info *tinfo, void (*)(void *)) {
    std::fprintf(stderr, "factoidal wasi build: C++ exception of type %s thrown; "
                 "this build has no exception support, aborting\n",
                 tinfo ? tinfo->name() : "?");
    (void)obj;
    std::abort();
}
#ifdef __wasm_exception_handling__
/* Only with -fwasm-exceptions (variant p2-eh): the catch sites of
   runtime/exception.cpp need these two. __cxa_throw above aborts, so no
   catch block is ever entered; the variant measures the code size and speed
   of a build that carries wasm exception-handling instructions. */
void *__cxa_begin_catch(void *exc) noexcept { return exc; }
void __cxa_end_catch() {}
#endif
void initialize_libuv(void) {}
const char *uv_strerror(int err) { return std::strerror(err < 0 ? -err : err); }
}
