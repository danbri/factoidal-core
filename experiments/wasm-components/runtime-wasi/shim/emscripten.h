/* Shim for building the Lean runtime with wasi-sdk under -DLEAN_EMSCRIPTEN.
   The runtime uses EM_ASM only for a debugger break and for reading
   process.env / the app path from JavaScript; under WASI neither exists. */
#pragma once
#define EM_ASM(...) ((void)0)
#define EM_ASM_INT(...) 0
#define EMSCRIPTEN_KEEPALIVE __attribute__((used))
