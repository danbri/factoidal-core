#!/usr/bin/env python3
"""Patch Lean v4.33.1's runtime sources so that wasi-sdk can compile them.

Usage: patch-runtime-wasi.py <lean4-src/src>

Each patch is one blocker of the Lean runtime under WASI, recorded in
experiments/wasm-components/RESULTS.md section "Lean runtime blockers".
Every patch is anchored on upstream text and guarded by __wasi__, so the
native and Emscripten builds of the same file are unchanged. The script is
idempotent and exits 1 if an anchor is missing (upstream changed).
"""
import sys, pathlib

root = pathlib.Path(sys.argv[1])
MARK = "/* wasi-port patch */"

PATCHES = [
  # B3: stack_overflow.h keeps a sigaltstack (stack_t). WASI has no signals.
  ("runtime/stack_overflow.h",
   "#ifndef LEAN_WINDOWS\n#include <csignal>\n#endif",
   "#if !defined(LEAN_WINDOWS) && !defined(__wasi__) " + MARK + "\n#include <csignal>\n#endif"),
  ("runtime/stack_overflow.h",
   "#ifndef LEAN_WINDOWS\n    // We need a separate signal stack",
   "#if !defined(LEAN_WINDOWS) && !defined(__wasi__) " + MARK + "\n    // We need a separate signal stack"),
  ("runtime/stack_overflow.cpp",
   "#ifdef LEAN_WINDOWS\n#include <windows.h>",
   "#if defined(__wasi__) " + MARK + "\n#elif defined(LEAN_WINDOWS)\n#include <windows.h>"),
  ("runtime/stack_overflow.cpp",
   "#ifdef LEAN_WINDOWS\n// https://github.com/rust-lang/rust/blob/master/src/libstd/sys/windows",
   "#if defined(__wasi__) " + MARK + "\n// A wasm stack overflow traps the instance; there is no handler to install.\n"
   "stack_guard::stack_guard() {}\nstack_guard::~stack_guard() {}\n"
   "#elif defined(LEAN_WINDOWS)\n// https://github.com/rust-lang/rust/blob/master/src/libstd/sys/windows"),
  ("runtime/stack_overflow.cpp",
   "#ifdef LEAN_WINDOWS\n    AddVectoredExceptionHandler",
   "#if defined(__wasi__) " + MARK + "\n#elif defined(LEAN_WINDOWS)\n    AddVectoredExceptionHandler"),
  # B4: get_peak_rss reads rusage.ru_maxrss; wasi-libc's emulated rusage has no such field.
  ("runtime/memory.cpp",
   "#if defined(__APPLE__)\n    return static_cast<size_t>(rusage.ru_maxrss);",
   "#if defined(__wasi__) " + MARK + "\n    (void)rusage; return 0;\n#elif defined(__APPLE__)\n    return static_cast<size_t>(rusage.ru_maxrss);"),
  # B5: the compactor lists loaded libraries with dl_iterate_phdr (<link.h>). WASI has no dynamic loader.
  ("runtime/compact.cpp",
   "#elif !defined(LEAN_WINDOWS)\n#include <link.h>",
   "#elif !defined(LEAN_WINDOWS) && !defined(__wasi__) " + MARK + "\n#include <link.h>"),
  ("runtime/compact.cpp",
   "#else\n    // Linux: use dl_iterate_phdr",
   "#elif defined(__wasi__) " + MARK + "\n    (void)libs;\n#else\n    // Linux: use dl_iterate_phdr"),

  # B1 (all wasm32 targets, the same defect Wasm/build-wasm.sh step 1b patches
  # for Emscripten): string_to_list_core ends List Char with lean_box_uint32(0),
  # which heap-allocates on 32-bit targets, so lean_string_mk never meets a
  # scalar List.nil. Not guarded by __wasi__: it is a 32-bit defect.
  ("runtime/object.cpp",
   "obj_res  r = lean_box_uint32(0);",
   "obj_res  r = lean_box(0); " + MARK),
  # B6: Handle.getLine locks the FILE with flockfile; single-threaded wasi-libc has none.
  ("runtime/io.cpp",
   "#if defined(LEAN_WINDOWS)\n\n#define LEAN_IO_LOCK_FILE(fp) _lock_file(fp)",
   "#if defined(__wasi__) " + MARK + "\n\n#define LEAN_IO_LOCK_FILE(fp) ((void)0)\n"
   "#define LEAN_IO_UNLOCK_FILE(fp) ((void)0)\n#define LEAN_IO_GETC_UNLOCKED(fp) getc(fp)\n\n"
   "#elif defined(LEAN_WINDOWS)\n\n#define LEAN_IO_LOCK_FILE(fp) _lock_file(fp)"),
  # B9: thread.h's single-thread lock types name std::adopt_lock_t without
  # including <mutex>; libc++ 23 (wasi-sdk 34) no longer brings it in
  # transitively through <chrono>/<functional>.
  ("runtime/thread.h",
   "#include <iostream>\n#include <chrono>",
   "#include <iostream>\n#if defined(__wasi__) " + MARK + "\n#include <mutex>\n#endif\n#include <chrono>"),
  # B10: IO.getRandomBytes opens /dev/urandom; a WASI host has no such file
  # (Emscripten emulates it in its JS file system). Lean's initialisers call it
  # (the first run under wasmtime stopped with "no such file or directory:
  # /dev/urandom"). WASI's random_get, through wasi-libc's getentropy, which
  # gives at most 256 bytes per call.
  ("runtime/io.cpp",
   "    if (nbytes == 0) return io_result_mk_ok(lean_alloc_sarray(1, 0, 0));\n\n#if !defined(LEAN_WINDOWS)\n    int fd_urandom",
   "    if (nbytes == 0) return io_result_mk_ok(lean_alloc_sarray(1, 0, 0));\n\n"
   "#if defined(__wasi__) " + MARK + "\n"
   "    {\n        obj_res res = lean_alloc_sarray(1, nbytes, nbytes);\n"
   "        uint8_t * dst = lean_sarray_cptr(res);\n"
   "        for (size_t off = 0; off < nbytes; off += 256) {\n"
   "            size_t n = std::min(nbytes - off, static_cast<size_t>(256));\n"
   "            if (getentropy(dst + off, n) != 0) {\n"
   "                dec_ref(res);\n                return io_result_mk_error(decode_io_error(errno, nullptr));\n            }\n        }\n"
   "        return io_result_mk_ok(res);\n    }\n#endif\n"
   "#if !defined(LEAN_WINDOWS)\n    int fd_urandom"),
]
PATCHES = PATCHES

rc = 0
for rel, old, new in PATCHES:
    p = root / rel
    s = p.read_text()
    if new in s:
        continue
    if s.count(old) != 1:
        print(f"ANCHOR NOT FOUND ONCE: {rel}: {old.splitlines()[0]!r}")
        rc = 1
        continue
    p.write_text(s.replace(old, new))
    print(f"patched {rel}")
sys.exit(rc)
