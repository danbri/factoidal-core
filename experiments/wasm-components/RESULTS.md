# Wasm component experiments: results (2026-10-29)

Plan: https://github.com/danbri/factoidal/issues/1167 (milestone 1). Method and
layout: [README.md](README.md). Recommendation:
[`docs/designissues/2026-10-29-wasm-components.md`](../../docs/designissues/2026-10-29-wasm-components.md).
Raw data: [`bench/results-2026-10-29.jsonl`](bench/results-2026-10-29.jsonl)
(`bench/run-all.sh` output; `bench/summarize.py` makes the tables below).

## Summary

* ✅ Lean's C output (337 modules of `formal/lean4` plus the core library) and
  the Lean v4.33.1 runtime build with wasi-sdk 30 for `wasm32-wasip1` and
  `wasm32-wasip2`, single-threaded, with 5 small runtime patches and 3 shim
  headers. The result is a real component: it exports the WIT interface
  `factoidal:subset/rdf@0.1.0` (`wit/factoidal.wit`) through wit-bindgen's C
  bindings.
* ✅ `wac plug` composes it with a Rust component (`driver-rs`, 103 KB). The
  composed component runs in wasmtime 37 and in Node 22 through `jco run`. The
  Lean component alone runs in Node through `jco transpile`.
* ✅ Same answers: every build gives the same SPARQL JSON envelope on each
  document (SHA-256 prefix `63ff5cf8ae8adbac` for `people-2000`,
  `aa2f07bb552ee7a2` for `people-10000`).
* 📊 With `wasm-opt -O3` (which Emscripten runs at `-O3`), the component has
  the throughput of the Emscripten build: on 60,000 triples, parse 442 ms
  against 458 ms and query 902 ms against 934 ms in Node (medians of 3 runs of
  5 calls). The component is 3.9% larger raw and 2.4% smaller after gzip. The
  jco glue is 5.3 times the Emscripten glue (317 KB against 60 KB), and the
  module load in Node takes 62 to 67 ms against 30 to 35 ms.
* ⚠️ No C++ exceptions: wasi-sdk 27 and 30 ship libc++abi without
  `__cxa_throw`. The experiment aborts on a throw (`runtime-wasi/wasi_stubs.cpp`).
  A build with `-fwasm-exceptions` links (variant `p2-eh`), but jco 1.40 refuses
  it ("exceptions proposal not enabled"), and wasmtime 37 runs it only after
  `wasm-opt --translate-to-exnref` (variant `p2-ehx`).
* No measured gain from wasm tail calls (`-mtail-call`) or SIMD (`-msimd128`),
  nor from static linking (one module) against composition at this boundary.

## Environment

Linux x86_64 container, 4 vCPU (Intel Xeon 2.10 GHz), 15 GB RAM. Lean 4.33.1
(the repository's `lean-toolchain`); wasi-sdk 30.0 (clang 21.1.4, wasi-libc
`ec0effd769df`); Emscripten 6.0.13 (the baseline); wasm-opt (Binaryen) 121;
wit-bindgen 0.46.0; wasm-tools 1.240.0; wac 0.8.0; wasmtime 37.0.0;
jco 1.40.0 with preview2-shim 0.31.0; Node 22.22.0; rustc 1.97.0. Repository
base: `origin/main` at `8e4bf6a3a`. No other job ran during the measurements
(the builds finished first).

## Inputs and method

* Documents (`bench/gen-data.py`): `people-2000.ttl` (275 KB, 2,000 people,
  12,000 triples) and `people-10000.ttl` (1.39 MB, 60,000 triples): prefixes,
  `;` and `,` lists, language-tagged and typed literals, decimals.
* Query `q1.rq`: a two-hop join with `FILTER(?age > 70)`, `ORDER BY` and
  `LIMIT 20`.
* Each timing is the median of 5 calls in one process; the tables give the
  median of 3 processes. Node: `bench/node-bench.mjs` (`importMs` = load,
  compile and instantiate; `initMs` = the first call, on a one-triple document,
  which runs Lean's module initialisers). wasmtime: the variant composed with
  `driver-rs`, precompiled with `wasmtime compile`; `one` is the wall time of a
  whole `wasmtime run` on a one-triple document (process start, instantiation,
  Lean initialisation, one parse and one query). `node-composed`: the same
  composed component under `jco run`.
* The parse call returns the canonical N-Quads (1.17 MB and 5.89 MB); the query
  call takes them back. So each call pair copies the document across the
  component boundary twice.

## Variants

| Variant | Build |
| --- | --- |
| emcc | baseline: Emscripten, the flags of `formal/lean4/Wasm/build-wasm.sh` (`-O3 -fwasm-exceptions`, mimalloc, no pthreads); char\* entry points; Node only |
| p2 | wasi-sdk `wasm32-wasip2`, `-O3`, no `wasm-opt` |
| p2-opt | p2 plus `wasm-opt -O3 --strip-debug` |
| p1-opt | `wasm32-wasip1` core module plus `wasm-opt -O3`, adapted to Preview 2 with the wasmtime 37 reactor adapter |
| p2-oz | p2-opt at `-Oz` (clang and wasm-opt) |
| p2-tail | p2-opt with `-mtail-call` |
| p2-simd | p2-opt with `-msimd128` |
| p2-eh | p2-opt with `-fwasm-exceptions` (legacy exception instructions) |
| p2-ehx | p2-eh after `wasm-opt --translate-to-exnref` |
| static | strategy 3: `wasm-ld` links the Rust driver (a static library), the Lean subset and the runtime into one `wasm32-wasip1` module, plus `wasm-opt -O3`; wasmtime only |

## Sizes

| Variant | Artifact | Bytes | gzip -9 bytes |
| --- | --- | ---: | ---: |
| emcc | wasm | 5,967,670 | 1,149,729 |
| emcc | JS glue | 60,295 | 17,133 |
| p2 | component | 8,209,236 | 1,267,631 |
| p2 | jco JS glue | 324,446 | 49,574 |
| p2-opt | component | 6,201,671 | 1,122,302 |
| p2-opt | jco core module | 6,188,845 | 1,118,920 |
| p2-opt | jco JS glue | 317,043 | 49,270 |
| p1-opt | component | 6,204,783 | 1,120,710 |
| p1-opt | jco JS glue | 339,558 | 50,725 |
| p2-oz | component | 3,708,045 | 853,695 |
| p2-tail | component | 6,202,923 | 1,124,624 |
| p2-simd | component | 6,201,737 | 1,122,939 |
| p2-eh | component | 6,206,568 | 1,123,250 |
| p2-ehx | component | 6,207,997 | 1,123,550 |
| static | core module | 6,227,808 | 1,135,682 |
| driver-rs | component | 103,429 | |

## Node 22 (Lean component through jco; emcc through its glue)

Times in ms.

| Variant | Document | import | init | parse | query |
| --- | --- | ---: | ---: | ---: | ---: |
| emcc | people-2000 | 35.4 | 106 | 82.3 | 165 |
| emcc | people-10000 | 30.1 | 96.7 | 458 | 934 |
| p2 | people-2000 | 71.5 | 97.4 | 87.5 | 162 |
| p2 | people-10000 | 77.2 | 102 | 513 | 1,039 |
| p2-opt | people-2000 | 67.3 | 89.8 | 77.7 | 146 |
| p2-opt | people-10000 | 62.3 | 89.4 | 442 | 902 |
| p1-opt | people-2000 | 71.7 | 91.8 | 76.6 | 136 |
| p1-opt | people-10000 | 67.4 | 87.9 | 449 | 918 |
| p2-oz | people-2000 | 60.8 | 78.7 | 129 | 208 |
| p2-oz | people-10000 | 57.2 | 77.0 | 744 | 1,219 |
| p2-tail | people-2000 | 72.0 | 94.1 | 81.4 | 148 |
| p2-tail | people-10000 | 65.8 | 97.7 | 481 | 968 |
| p2-simd | people-2000 | 68.4 | 102 | 76.4 | 150 |
| p2-simd | people-10000 | 61.9 | 89.8 | 472 | 954 |

p2-eh: jco 1.40 refuses to transpile it (`exceptions proposal not enabled`).

## Composed with the Rust driver (`wac plug`)

Times in ms. `compile` is `wasmtime compile` of the composed component
(Cranelift, 4 threads), paid once per build when the result is cached.

| Variant | Host | compile | one (wall) | parse 2000 | query 2000 | parse 10000 | query 10000 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| p2 | wasmtime | 2,444 | 21 | 86.6 | 164 | 528 | 1,028 |
| p2-opt | wasmtime | 2,013 | 18 | 81.5 | 151 | 479 | 953 |
| p1-opt | wasmtime | 1,838 | 20 | 106 | 172 | 518 | 1,018 |
| p2-oz | wasmtime | 1,462 | 28 | 130 | 218 | 735 | 1,423 |
| p2-tail | wasmtime | 1,992 | 24 | 87.3 | 166 | 520 | 1,008 |
| p2-simd | wasmtime | 2,102 | 20 | 96.1 | 184 | 502 | 1,018 |
| p2-ehx | wasmtime | 1,959 | 20 | 94.4 | 166 | 525 | 1,007 |
| static | wasmtime | | 18 | 87.5 | 168 | 493 | 975 |
| p2 | Node (`jco run`) | | | 94.2 | 181 | 507 | 999 |
| p2-opt | Node (`jco run`) | | | 77.9 | 144 | 447 | 873 |
| p1-opt | Node (`jco run`) | | | 82.2 | 144 | 432 | 956 |
| p2-oz | Node (`jco run`) | | | 135 | 202 | 715 | 1,213 |
| p2-tail | Node (`jco run`) | | | 78.4 | 157 | 440 | 923 |
| p2-simd | Node (`jco run`) | | | 79.1 | 147 | 455 | 924 |

The spread between processes was up to about 10% (raw data), so differences
below that are not results.

## Findings

1. **wasm-opt is required.** Without it (p2 against p2-opt) the component is
   32% larger, and parse and query on 60,000 triples are 16% and 15% slower
   in Node. The Emscripten link runs `wasm-opt` at `-O3`; wasi-sdk does not.
2. **Allocator clock reads (fixed).** Two sources of
   `wasi:clocks/monotonic-clock.now` calls, each one a JavaScript call under
   jco, measured by counting the shim calls (`bench/count-imports.mjs`):
   * mimalloc's delayed purge reads the clock on free. `fx_component.c` sets
     `mi_option_purge_delay` to -1 (no purge; wasm cannot give memory back).
     Before, in one sequential session: parse 87 to 94 ms and query 183 to
     209 ms on `people-2000` (p2-opt); after: 77 to 88 ms and 148 to 161 ms.
   * `lean_obj_once_cold` takes a spin lock whose `std::atomic::wait` reads
     `steady_clock` in single-threaded libc++ (runtime patch 5). Lean
     initialisation made 5,963 clock calls before the patch and 4 after;
     `init` fell from 181 to 216 ms to the 88 to 102 ms in the table.
3. **Throughput parity.** p2-opt and emcc run the same Lean code at the same
   speed in Node (differences inside the 10% spread). wasmtime is not faster
   than V8 for this code (p2-opt 479 and 953 ms against 442 and 902 ms).
4. **Load cost is the jco glue.** `import` is 62 to 77 ms for the components
   against 30 to 35 ms for emcc. The jco glue is 317 KB (49 KB gzip) against
   60 KB (17 KB gzip). It carries jco 1.40's generic async task code
   (classes such as `Waitable`), which this synchronous interface does not
   call.
5. **Composition costs nothing measurable here.** The coarse interface copies
   the document across the boundary twice per call pair (7 MB on
   `people-10000`); static linking (one memory, direct calls) gave 493 and
   975 ms against 479 and 953 ms for the composed p2-opt.
6. **Tail calls, SIMD: no gain.** Within the 10% spread, with a size change
   below 0.03%. Lean's C code generator already turns self tail calls into
   loops, and clang finds little to vectorise in it.
7. **`-Oz`** gives 40% fewer bytes (24% after gzip) for 40% to 68% more time.
8. **Exception handling:** see the blockers below. Size cost of
   `-fwasm-exceptions`: 0.08%.

## Blockers and gaps in the Lean runtime under WASI

Each item names the file of Lean v4.33.1 `src/runtime` and what the experiment
does. All are in `runtime-wasi/`.

| # | Where | Gap | What the experiment does |
| --- | --- | --- | --- |
| 1 | `exception.cpp`, every `throw` | wasi-sdk 27 and 30: libc++abi without `__cxa_throw`, `__cxa_begin_catch`, `__cxa_end_catch` (README: "C++ code is supported only with -fno-exceptions") | `wasi_stubs.cpp`: `__cxa_throw` prints the type and aborts. Throw sites that this code reaches: memory exhaustion (`memory.cpp`), `unreachable_reached` (`debug.cpp`), stack checks of the kernel (`stackinfo.cpp`, `interrupt.cpp`); none is a recoverable Lean error |
| 2 | `stack_overflow.cpp`, `stack_overflow.h` | no signals, no `sigaltstack` | not compiled; `stack_guard` and the initialiser are empty (patch 1, stubs); a stack overflow is a wasm trap, as under Emscripten |
| 3 | `process.cpp` | no `fork`, `execvp`, `waitpid`, `sys/wait.h` | not compiled; `initialize_process` and `finalize_process` empty; no process function is reachable from the subset (the link has no undefined process symbol) |
| 4 | `compact.cpp` | no `link.h`, `dl_iterate_phdr` (`.olean` compaction) | not compiled; not reachable |
| 5 | `memory.cpp` | `struct rusage` has no `ru_maxrss` | patch 2: peak RSS reads 0 |
| 6 | `io.cpp` | `IO.getRandomBytes` opens `/dev/urandom`; a module initialiser of the subset calls it | patch 4: `getentropy` (wasi `random_get`) |
| 7 | `io.cpp` | `flockfile`, `funlockfile` absent | forced include `wasi_prelude.h`: no-ops (one thread) |
| 8 | `io.cpp` includes `uv.h` | `uv/unix.h` needs `netdb.h`, `termios.h`, `pwd.h` | shims with declarations only; libuv v1.48.0 headers; no libuv code linked |
| 9 | `debug.cpp`, `io.cpp`, `stackinfo.cpp` under `LEAN_EMSCRIPTEN` | `emscripten.h`, `emscripten/stack.h` | shim headers: `EM_ASM` is empty, the stack bounds come from `__stack_low` and `__stack_high` |
| 10 | `object.cpp`, `lock_simple_atomic` | `std::atomic::wait` reads the clock (finding 2) | patch 5: a plain store without threads |
| 11 | threads | no `wasm32-wasip1-threads` build tried | single-threaded, as the shipped build: only `lean_initialize_runtime_module`, so no task manager thread starts |
| 12 | `Init.System.IO` against `io.cpp` | `lean_io_create_tempfile`, `lean_io_create_tempdir`: function signature mismatch warning | same warning as the shipped build, which allows exactly these two |
| 13 | `formal/lean4/ffi/l4_ext.c` | the SPARQL 1.1 §17.6 extension-function host call-out has no host | compiled without Emscripten: answers "no value"; a component would import it as a WIT function |
| 14 | `object.cpp`, `string_to_list_core` | the wasm32 `List.nil` defect that `build-wasm.sh` step 1b patches | patch 3: the same fix |

Toolchain notes: `wasm-component-ld` (the wasip2 linker driver) refuses
`--start-group`; `wasm-ld` needs none. wasmtime 37 has no option for the legacy
exception instructions that clang 21 emits.

## Method notes

* Clock calls were counted with `bench/count-imports.mjs` (it wraps the
  preview2-shim functions before the jco module loads), and attributed to
  their callers from `new Error().stack` in the wrapper, with
  `Error.stackTraceLimit = 60`, on a build that kept the wasm name section.
* The before-and-after numbers of finding 2 are single sequential sessions on
  the same machine, not the table method.
