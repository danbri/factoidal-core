/* Forced include (-include) for the wasi-sdk build of the Lean runtime.
   wasi-libc has no stdio stream locks in its single-threaded build. */
#pragma once
#ifdef __wasi__
#include <stdio.h>
#define flockfile(f) ((void)(f))
#define funlockfile(f) ((void)(f))
#endif
