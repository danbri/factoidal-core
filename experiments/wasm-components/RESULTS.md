# Results: the Lean engine as a WebAssembly component

Milestone 1 of https://github.com/danbri/factoidal/issues/1167 (track C),
measured 2026-10-28 on the 4-vCPU cloud VM. Design record and recommendation:
[`docs/designissues/2026-10-29-wasm-components.md`](../../docs/designissues/2026-10-29-wasm-components.md).

## Result

1. Lean's C output and Lean's runtime (v4.33.1) build with wasi-sdk 34 for
   `wasm32-wasip1` and `wasm32-wasip2`, single-threaded, with eleven small
   source patches and four stand-in files (section "Lean runtime blockers").
2. The build exports the WIT interface `factoidal:core/rdf` through
   wit-bindgen's C bindings. It is a real component: `wasm-tools component
   wit` shows the export, `wac plug` composes it with a Rust component, and
   the composition runs in wasmtime 49.
3. jco 1.38 transpiles the component and it runs in Node 22 and in headless
   Chromium, but only the build without wasm exception handling
   (`WC_EH=trap`, blocker B12).
4. The static-link variant (Lean objects, Lean runtime and a Rust static
   library, linked by wasm-ld into one core module) runs in wasmtime.
5. All 13 builds give byte-identical answers on both inputs (same SHA-256
   of the N-Quads and of the query answer as the Emscripten baseline).
6. Speed: the same Lean code is as fast under wasi-sdk as under Emscripten,
   within the noise of this VM. Size: the stripped wasi core module is 5.5 %
   larger than the Emscripten module at `-O3` and 4.1 % larger at `-Oz`.

## Inputs and method

- Subset: `lean/WcCore.lean`, the Turtle reader and the shipped `queryDataset`
  evaluation path; import closure 334 repository and 811 toolchain modules,
  1,146 C files.
- Inputs: `bench/gen-data.py 1000` (6,000 triples, 120 KB of Turtle) and
  `bench/gen-data.py 10000` (60,000 triples, 1.24 MB); query `bench/q1.rq`
  (a join of three patterns, FILTER, GROUP BY, COUNT, ORDER BY, LIMIT).
- Each number is the median of 5 runs in one process ("first parse" is the
  first run; in wasmtime the median includes it, in Node it is a sixth run). "Start" is, for wasmtime, the wall time of
  a whole `wasmtime run` of the built-in sample with a precompiled `.cwasm`
  (process start, instantiation, Lean initialisation, two small calls); for
  Node, the time to import and instantiate the module and run the Lean
  module initialisers. The two "Start" columns measure different things and
  are not compared with each other.
- "Small call" is the mean time of 2,000 calls of the sample query (2 triples)
  from Rust: across the component boundary (`composed`) or by a direct call
  (`static`).
- Noise: three repeats of two builds gave spreads of 5 to 10 % on the 60k
  inputs (Emscripten query 506 to 541 ms; wasip1 query 568 to 624 ms). A
  difference below 10 % in the table is not a result.
- Raw data: `bench/results-2026-10-28.jsonl`. Command:
  `bench/measure.py /opt/wc/out /opt/wc <artifacts>` (see README.md).

Toolchains: Lean 4.33.1; Emscripten 6.0.8; wasi-sdk 34 (clang 23.1.0);
wasm-tools 1.239.0; wit-bindgen 0.45.0; wac 0.8.0; wasmtime 49.0.0; jco
1.38.0 with preview2-shim 0.29.0; Node 22.22.0 (V8 12.4); Binaryen 132 (from
emsdk); Rust 1.x stable with `wasm32-wasip1` and `wasm32-wasip2`.
`tools/install.sh` pins them.

## Measurements

| Build | Run in | Bytes (MB) | gzip -9 (MB) | Start (ms) | 6k triples parse / query (ms) | 60k triples parse / query (ms) | 60k first parse (ms) | Small call (µs) |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `emcc-o3` (baseline) | Node 22 | 5.95 | 1.17 | 118 | 22.8 / 47 | 261.5 / 548.3 | 338.4 | – |
| `emcc-oz` | Node 22 | 3.57 | 0.89 | 116 | 36.4 / 74 | 424.1 / 856.3 | 448.5 | – |
| `wasip1-o3-trap` through jco | Node 22 | 6.28 | 1.16 | 242.5 | 29.5 / 60.8 | 303 / 621 | 386.5 | – |
| `wasip1-o3-trap-wo` through jco | Node 22 | 6.25 | 1.15 | 265.3 | 31.1 / 69.3 | 326.5 / 654.6 | 384.1 | – |
| `wasip1-o3` composed | wasmtime 49 | 6.44 | 1.23 | 17.0 | 22.2 / 47.8 | 295.2 / 606.8 | 295.2 | 36.3 |
| `wasip1-o3-wo` composed | wasmtime 49 | 6.41 | 1.21 | 14.5 | 26.4 / 56.2 | 265.1 / 569.7 | 318.1 | 33.7 |
| `wasip2-o3` composed | wasmtime 49 | 6.79 | 1.23 | 15.0 | 22.5 / 50.3 | 267.1 / 596.6 | 273.9 | 31.3 |
| `wasip1-o3-trap` composed | wasmtime 49 | 6.42 | 1.22 | 18.5 | 23.2 / 51.9 | 287.8 / 708.2 | 312.3 | 32.8 |
| `wasip1-oz-wo` composed | wasmtime 49 | 3.88 | 0.94 | 18.3 | 37.1 / 78.4 | 419.2 / 886.6 | 419.2 | 54.3 |
| `wasip1-o3-tail-wo` composed | wasmtime 49 | 6.41 | 1.21 | 18.3 | 30.9 / 64.5 | 259.6 / 609.6 | 296.4 | 38.6 |
| `wasip1-o3-simd-wo` composed | wasmtime 49 | 6.41 | 1.21 | 16.1 | 24.0 / 48.4 | 268.1 / 629.0 | 307.7 | 32.2 |
| `wasip1-o3` static link | wasmtime 49 | 6.36 | 1.20 | 14.2 | 25.3 / 54.6 | 274.7 / 684.9 | 311.5 | 42.8 |
| `wasip1-o3-tail` static link | wasmtime 49 | 6.33 | 1.19 | 14.2 | 21.9 / 48.3 | 251.1 / 588.9 | 275.3 | 30.4 |

Name parts: `o3`/`oz` the clang level; `wo` Binaryen `wasm-opt` at the same
level after the link (Emscripten always runs it); `trap` no wasm exception
handling (B12); `tail` `-mtail-call`; `simd` `-msimd128`. Composed bytes
include the Rust client (123 KB). jco bytes are the two core modules jco
writes; its JavaScript glue `engine.js` is 388 KB more (50 KB gzip), against
63 KB (18 KB gzip) for Emscripten's `.mjs`.

Same page in headless Chromium (Playwright's Chromium,
`bench/browser/browser.mjs`, 6k triples, median of 5):

| Build | Instantiate + init (ms) | Parse (ms) | Query (ms) |
| --- | ---: | ---: | ---: |
| `emcc-o3` | 301.9 | 32.8 | 52.7 |
| `wasip1-o3-trap` through jco | 455.9 | 41.1 | 73.6 |

Wasmtime ahead-of-time compile (`wasmtime compile`, Cranelift) of a 6.4 MB
composition: 1.6 to 2.2 s; the `.cwasm` is 25 MB.

### What the numbers show

- **Compiler**: wasi-sdk's clang 23 and Emscripten's clang give the same
  parse and query times for the same Lean C (60k parse: 247 to 276 ms against
  249 to 262 ms over the repeats).
- **Engine**: the 60k query is about 10 % slower in wasmtime 49 than in V8
  12.4 (568 to 624 ms against 506 to 541 ms). This is the engine, not the
  build: the same component in Node through jco gives 621 ms, and the
  Emscripten module has no wasmtime run to compare.
- **Size**: `-Oz` saves 40 % of bytes (24 % gzip) and costs 55 to 65 % more
  time, in both toolchains. `wasm-opt` after a wasi-sdk link saves 0.5 %.
  The wasip2 core module is 0.38 MB larger than wasip1: wasi-libc's
  generated WASI 0.2 bindings (`wasip2.c`, `wasip2_component_type.o`) against
  the 52 KB preview1 adapter.
- **Tail calls and SIMD**: `-mtail-call` makes clang emit 3,916
  `return_call` instructions; neither flag changes a time beyond noise.
  Lean already compiles self tail calls to loops.
- **Component boundary**: 2,000 small calls cost 31 to 39 µs each composed
  and 30 to 43 µs each static. The boundary cost is below the noise at this
  call size, where the Lean work (parse, plan, evaluate, serialise) is most of
  the time. Large strings: the 1.24 MB input is copied into the engine's
  memory on every composed call and the 60k parse shows no measured
  difference from the static link.
- **jco start-up**: 243 to 265 ms in Node against 118 ms for Emscripten. A
  CPU profile of the first call puts the extra time in jco's generated glue
  (`_debugLog`, `AsyncTask`, `_lowerImportBackwardsCompat`), around the WASI
  calls that Lean's module initialisers make. Steady-state calls are 15 to
  30 % slower through jco than through Emscripten's glue in Node and in
  Chromium.

### Stack depth (`bench/deep.py`)

The deepest nested blank-node property list (`ex:s ex:p [ ex:p [ ... ] ]`)
each build parses, on a ladder with steps of 25 %:

| Build | Engine stack | Deepest nesting parsed |
| --- | --- | ---: |
| `emcc-o3` | Node 22 default | 2,328 |
| `wasip1-o3-trap` through jco | Node 22 default | 2,328 |
| `wasip1-o3-wo` composed, and `-tail` | wasmtime default (512 KiB) | 762 |
| `wasip1-o3` static, and `-tail` | wasmtime default (512 KiB) | 762 |
| `wasip1-o3-wo` composed, and `-tail` | `-W max-wasm-stack=8388608` | 13,877 |

The limit met first is the engine's own call stack, not the 8 MiB stack in
linear memory. The depth grows in proportion to the engine stack (about
600 bytes of engine stack per nesting level). Tail calls do not change it:
this recursion is not in tail position. The rule of CLAUDE.md for decoders
over input-proportional data (a loop or a tail call with an accumulator)
is the remedy, not a build flag.

## Lean runtime blockers under WASI

Lean v4.33.1, `src/runtime`. Each patch is in `tools/patch-runtime-wasi.py`,
guarded by `__wasi__` (except B1), so native and Emscripten builds of the
same sources do not change. Line numbers are of the upstream file.

| Id | Where | What fails | What the experiment does |
| --- | --- | --- | --- |
| B0 | `include/lean/lean.h:3360` and `runtime/{object,io,thread,stackinfo,platform,debug}.cpp` | Every wasm32 decision is keyed on `LEAN_EMSCRIPTEN`, not on the target. Without it, `LEAN_SCALAR_PTR_LITERAL` writes 64-bit words into the closed terms of the generated C on a 32-bit target. | Compile with `-DLEAN_EMSCRIPTEN` and a stand-in `wasi-port/emscripten.h` (EM_ASM gives no answer: `IO.getEnv` is `none`, `IO.appPath` fails) and `wasi-port/emscripten/stack.h` (stack bounds from wasm-ld's `__stack_low`/`__stack_high`). Upstream fix: key the 32-bit layout on `UINTPTR_MAX` or `__wasm32__`. |
| B1 | `runtime/object.cpp:2191`, `string_to_list_core` | `lean_box_uint32(0)` heap-allocates on 32-bit targets, so `String.mk` never meets a scalar `List.nil`. All wasm32 targets. | The same one-line patch as `formal/lean4/Wasm/build-wasm.sh` step 1b. |
| B2 | `runtime/{memory,stackinfo,io,init_module}.cpp` | wasi-libc refuses `<signal.h>`, `<sys/resource.h>`, `<sys/mman.h>` without emulation macros. | `-D_WASI_EMULATED_{SIGNAL,PROCESS_CLOCKS,MMAN,GETPID}` and the four `libwasi-emulated-*` libraries. |
| B3 | `runtime/stack_overflow.{h,cpp}` | `sigaltstack`, `sigaction`, `siginfo_t`, `SIGSTKSZ`: WASI has no signals. | The stack guard is empty under WASI: a wasm stack overflow traps the instance. |
| B4 | `runtime/memory.cpp:80`, `get_peak_rss` | wasi-libc's emulated `rusage` has no `ru_maxrss`. | Returns 0. |
| B5 | `runtime/compact.cpp:28,103` | `<link.h>`, `dl_iterate_phdr`: no dynamic loader. | No loaded libraries are listed (the compactor writes `.olean` files; not used at run time). |
| B6 | `runtime/io.cpp:621` | `flockfile`/`funlockfile` are absent from single-threaded wasi-libc. | No-op locks, `getc` for `getc_unlocked`. |
| B7 | wasi-sdk 27 and 32 | No `libunwind` and a libc++abi without `__cxa_throw`: Lean's C++ runtime throws and cannot link. | wasi-sdk 34 (2026-08-24) ships `lib/<target>/eh/` with libunwind and an exception-enabled libc++; link with `-fwasm-exceptions -lunwind`. |
| B8 | `runtime/process.cpp:25` | `<sys/wait.h>`, `fork`, `waitpid`, pipes. | The file is left out; `wasi-port/process_stubs.cpp` gives empty `initialize_process`/`finalize_process` (`init_module.cpp` calls them). `IO.Process.*` is absent. |
| B9 | `runtime/thread.h:184` | The single-thread `unique_lock` names `std::adopt_lock_t`; libc++ 23 no longer brings it in through `<chrono>`. | `#include <mutex>` under `__wasi__`. |
| B10 | `runtime/io.cpp:867`, `lean_io_get_random_bytes` | Opens `/dev/urandom`; a WASI host has no such file (Emscripten emulates it). Lean's module initialisers call it: the first wasmtime run stopped with "no such file or directory: /dev/urandom". | `getentropy` (WASI `random_get`) in blocks of 256 bytes. |
| B11 | clang 23 `-fwasm-exceptions` | Emits the legacy exception instructions (`try`/`catch`); wasmtime 37 and 49 accept only the standard form with `exnref` (`try_table`). | Binaryen `wasm-opt --translate-to-exnref` after the link. |
| B12 | jco 1.38 | Its component parser has no exception-handling feature: "exceptions proposal not enabled". | `WC_EH=trap`: compile with `-fexceptions` and without `-fwasm-exceptions` (LLVM drops the catch blocks), `wasi-port/cxa_trap.cpp` makes a throw print its type and trap. |
| B13 | libuv | `runtime/io.cpp:44` includes `<uv.h>`, which needs `<netdb.h>` (absent in wasip1) and `<termios.h>` (absent in wasip1 and wasip2); libuv has no WASI port. | `wasi-port/uvonly/uv.h` declares the 9 libuv functions and the error codes `io.cpp` uses; `wasi-port/uv_stubs.c` answers `UV_ENOSYS` (`IO.FS.metadata`, hard links, temporary files fail). `initialize_libuv` is empty, as in the shipped `Wasm/l4_stubs.c`. |
| B14 | wasi-sdk 34 and wasmtime 37 | wasi-libc of wasi-sdk 34 imports WASI 0.2.12 (`wasi:cli/exit@0.2.12` `exit-with-code`); wasmtime 37 does not supply it. | wasmtime 49. |

Not attempted: threads (the Component Model has no shared memory yet, and
the shipped build is single-threaded too), memory64 (wasi-sdk 34 has no
`wasm64` sysroot), WASI 0.3 (`wasm32-wasip3`; wasi-sdk 34 ships a sysroot for
it).

## Reproduce

`README.md` has the commands. Every build writes to `/opt/wc/out` and keeps
its objects in `/opt/wc/work/obj-<target>-<variant>`.
