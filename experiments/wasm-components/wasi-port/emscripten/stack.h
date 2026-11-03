/* wasi-port/emscripten/stack.h — the two stack queries stackinfo.cpp asks
   under LEAN_EMSCRIPTEN, answered from the symbols wasm-ld defines
   (__stack_low, __stack_high: the bounds of the linear-memory stack). */
#pragma once
#include <stdint.h>
extern unsigned char __stack_low;
extern unsigned char __stack_high;
static inline uintptr_t emscripten_stack_get_base(void) { return (uintptr_t)&__stack_high; }
static inline uintptr_t emscripten_stack_get_end(void)  { return (uintptr_t)&__stack_low; }
