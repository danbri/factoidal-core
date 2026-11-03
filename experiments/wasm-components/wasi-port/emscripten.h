/* wasi-port/emscripten.h — NOT Emscripten. A stand-in so that Lean's runtime
   (v4.33.1) can be compiled by wasi-sdk with -DLEAN_EMSCRIPTEN.

   Why: upstream keys every wasm32 decision on LEAN_EMSCRIPTEN, not on the
   target. lean.h's LEAN_SCALAR_PTR_LITERAL (the layout of closed scalar
   terms in the generated C) uses 32-bit words only under that macro, and
   object.cpp, io.cpp, thread.cpp and stackinfo.cpp take their single-thread,
   no-signal, no-getenv paths only under it. Claiming the macro reuses those
   paths; the JavaScript escapes (EM_ASM) become "no answer".

   Effects under wasi: IO.getEnv answers none (io.cpp asks JavaScript),
   IO.appPath fails, invoke_debugger exits. None is reached by the
   experiment's exports. */
#pragma once
#include <stdlib.h>
#define EMSCRIPTEN_KEEPALIVE __attribute__((used))
#define EM_ASM(...) ((void)0)
#define EM_ASM_INT(...) 0
