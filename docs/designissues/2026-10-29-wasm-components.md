# Factoidal as WebAssembly components: build strategies, measured

Date: 2026-10-29 (measurements of 2026-10-28). Track C, milestone 1 of
https://github.com/danbri/factoidal/issues/1167 (modular wasm with the
Component Model; owner decision 2026-10-28). Experiment, numbers and the
list of Lean runtime blockers: `experiments/wasm-components/RESULTS.md`.
Nothing in the experiment changes the shipped build, the npm package or a
`danbri/factoidal-builds` workflow.

## 1. Question

Issue 1167 asks for a modular wasm architecture: Factoidal as several
components with WIT interfaces, composed with `wac`, run by wasmtime and in
browsers through `jco`, in place of the one Emscripten module of today
(`formal/lean4/Wasm/build-wasm.sh`). Before any component boundary is drawn,
two things must be known:

1. Can the Lean runtime and Lean's C output be built as a WASI component at
   all, and what does the runtime need?
2. What does each build strategy cost in size, start-up and throughput,
   against the current Emscripten build, on the same Lean code and inputs?

## 2. What was built

One Lean subset, `experiments/wasm-components/lean/WcCore.lean`: the RDF 1.1
Turtle reader and the shipped `queryDataset` evaluation path
(`L4Wasm.Ops.queryParsedDataset`), 1,146 C files with its import closure.
It was built in these ways:

| Strategy of issue 1167 | Build | Status |
| --- | --- | --- |
| 1, baseline | Emscripten 6.0.8, the flags of `build-wasm.sh`, `-O3` and `-Oz` | runs in Node and Chromium |
| 2 | wasi-sdk 34, `wasm32-wasip1` core module + preview1 reactor adapter, WIT exports by wit-bindgen C | component; composed with a Rust component by `wac plug`; runs in wasmtime 49 |
| 2 | wasi-sdk 34, `wasm32-wasip2` | component; same |
| 2, browser | the wasip1 component without wasm exception handling, through jco 1.38 | runs in Node 22 and headless Chromium |
| 3 | wasm-ld static link of the Lean objects, the Lean runtime and a Rust static library | one core module; runs in wasmtime 49 |
| 4 | `-mtail-call`, `-msimd128`, wasm exception handling, Binaryen after the link | all run; see section 4 |

The WIT package (`wit/factoidal.wit`):

```wit
package factoidal:core@0.1.0;
interface rdf {
  turtle-to-nquads: func(turtle: string, base: option<string>) -> result<string, string>;
  query: func(turtle: string, sparql: string) -> string;
}
world engine { export rdf; }
world client { import rdf; }
```

All 13 builds give the same bytes for the N-Quads and for the query answer
on both inputs (6,000 and 60,000 triples).

## 3. The Lean runtime under WASI

The runtime of Lean v4.33.1 needs fourteen accommodations (B0 to B14 in
RESULTS.md). Three of them are decisive; the rest are a line or a stub each.

- **Exceptions (B7, B11, B12).** Lean's C++ runtime throws. wasi-sdk 27 and
  32 have no libunwind, so the runtime does not link. wasi-sdk 34
  (2026-08-24) ships an exception-enabled libc++ and libunwind. clang 23
  still emits the legacy exception instructions, which wasmtime 37 and 49
  reject; Binaryen's `--translate-to-exnref` converts them. jco 1.38 rejects
  any component with exception instructions, so the browser build compiles
  the runtime without wasm exception handling and makes a throw trap. Lean
  compiled C does not throw; the runtime throws on conditions that end the
  computation (allocation failure, internal errors), so the trap build
  changes the error report, not an answer.
- **The `LEAN_EMSCRIPTEN` macro (B0).** Upstream keys the 32-bit layout of
  closed terms in `lean.h` (`LEAN_SCALAR_PTR_LITERAL`) and the single-thread,
  no-signal paths of the runtime on `LEAN_EMSCRIPTEN`, not on the target. The
  experiment defines the macro and supplies a stand-in `emscripten.h`. An
  upstream change that keys the layout on the pointer width would remove
  this.
- **Host services (B8, B10, B13).** No processes, no libuv, no
  `/dev/urandom` under WASI. Process and libuv functions are stubs that
  fail; random bytes come from WASI `random_get`. Lean's module initialisers
  read random bytes, so B10 is needed for any module, not only for IO code.

Threads were not attempted: the Component Model has no shared memory yet,
and the shipped Emscripten module is single-threaded too. Lean's runtime
already has a single-thread configuration (`thread.h` without
`LEAN_MULTI_THREAD`) and it works under WASI.

## 4. Measurements (summary)

The full table is in RESULTS.md. A difference below 10 % is within this VM's
noise (repeats spread 5 to 10 %).

- **Throughput.** For the same Lean C, wasi-sdk's clang and Emscripten's
  clang give the same parse and query times (60k-triple parse about 250 ms
  in both). The 60k query is about 10 % slower in wasmtime 49 than in V8 12.4;
  that is the engine.
- **Size.** Stripped, the wasi core module is 5.5 % larger than the
  Emscripten module at `-O3` (6.28 against 5.95 MB; gzip 1.2 MB both) and
  4.1 % at `-Oz` (3.72 against 3.57 MB). `-Oz` saves 40 % of bytes and costs
  55 to 65 % of speed in both toolchains. wasip2 adds 0.38 MB of generated
  WASI 0.2 bindings in wasi-libc.
- **Start-up.** In Node, jco's glue doubles start-up (243 to 265 ms against
  118 ms) and adds 15 to 30 % to steady-state calls; the CPU profile puts the
  cost in the glue around WASI calls, not in the wasm. Its JavaScript is
  388 KB (50 KB gzip) against Emscripten's 63 KB (18 KB gzip). In wasmtime a
  precompiled composition starts, initialises Lean and answers two calls in
  15 to 18 ms; the ahead-of-time compile takes 1.6 to 2.2 s.
- **Component boundary.** A small call (parse and query of 2 triples) costs
  31 to 39 µs composed and 30 to 43 µs statically linked: the canonical-ABI
  copy is below the noise when each call does real Lean work.
- **Tail calls and SIMD.** No change beyond noise. Tail calls do not extend
  the recursion depth of the Turtle reader on nested blank nodes, which is
  not in tail position. The depth limit is the engine's own call stack
  (762 levels with wasmtime's 512 KiB default, 2,328 in Node, 13,877 with an
  8 MiB wasmtime stack), so the CLAUDE.md rule for input-proportional data
  (a loop or an accumulating tail call) is what removes it.

## 5. Recommendation

1. **Keep Emscripten for the shipped browser and npm module now.** In the
   browser it is smaller, starts in half the time and runs 15 to 30 % faster
   than the same code through jco, and it has wasm exception handling that
   jco cannot yet carry. Nothing measured here is a reason to change the
   package.
2. **Adopt the wasi-sdk component build for server and native-host use**
   (wasmtime, Spin, wasmCloud): it is a real component with a WIT interface,
   composes with Rust components, starts in 15 ms precompiled, and costs no
   throughput against Emscripten. Make it a second build in
   `danbri/factoidal-builds` only when a host needs it, with the runtime
   patches of `tools/patch-runtime-wasi.py` and wasi-sdk 34 or later.
3. **Draw component boundaries only at coarse operations** (parse a
   document, run a query, validate a graph), as issue 1167 says. The
   measurements give no case for splitting the Lean engine into several
   components yet: each component carries its own copy of the Lean runtime
   and of the toolchain library (`Init` and the `Std` subset: 24 % of the
   function bytes here, 1.54 of 6.42 MB in the wasm-ld map of the wasip1
   link, against 0.17 MB for the runtime and the shims), and the
   boundary cost only stays negligible while each call does real work. The
   first useful split is between the Lean engine and non-Lean components
   (a Rust or C library behind its own WIT interface), where the static link
   (strategy 3) is the alternative for chatty interfaces.
4. **Re-measure the browser path when jco carries wasm exceptions** (B12)
   and its glue cost falls; then the component can replace Emscripten in the
   browser too. Track jco releases; the experiment's `node-bench.mjs` and
   `bench/browser/` are the test.
5. **Upstream two changes to Lean** that remove most of the patch set:
   key the 32-bit layout on the pointer width (B0), and make the random-bytes
   and file-lock paths WASI-aware (B6, B10). The remaining stubs (processes,
   libuv) are host capabilities that a component should import through WIT
   if a Lean program needs them.
6. **Do not adopt tail calls or SIMD flags for speed**; they changed nothing
   measurable. Fix deep recursion in the Lean source.

## 6. Open items

- An expected-failure record is not needed: no shipped feature is claimed.
  The experiment's limits (no `IO.Process`, no file metadata, no `getEnv`
  under WASI; trap on C++ throw in the jco build) are listed in RESULTS.md
  and apply only to the experiment.
- Not measured: memory peak per build; a full-library component (the
  shipped module compiles all 1,324 repository modules of `L4Factoidal` and
  `Wasm`, against 334 here); Spin and wasmCloud hosting;
  WASI 0.3 (`wasm32-wasip3`).
