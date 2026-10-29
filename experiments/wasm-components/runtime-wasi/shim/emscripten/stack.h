/* Shim: stack bounds from the symbols wasm-ld defines. */
#pragma once
#include <stdint.h>
extern unsigned char __stack_low;
extern unsigned char __stack_high;
static inline uintptr_t emscripten_stack_get_base(void) { return (uintptr_t)&__stack_high; }
static inline uintptr_t emscripten_stack_get_end(void) { return (uintptr_t)&__stack_low; }
