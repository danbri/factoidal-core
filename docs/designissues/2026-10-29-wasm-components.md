# Factoidal as WebAssembly components: wasi-sdk, WIT and the Emscripten build, measured

Date: 2026-10-29. Status: milestone 1 of
https://github.com/danbri/factoidal/issues/1167 (modular wasm with the
Component Model) done as an experiment; the recommendation in section 6 needs
a decision from the owner before anything in the shipped build changes.

Owner decision of 2026-10-28 (the plan in that issue): "Target architecture:
the WebAssembly Component Model (WASI Preview 2, interfaces in WIT)". Rule for
boundaries, from the same plan: "coarse interfaces become component boundaries
(\"parse this document\", \"style this subtree\", \"run this query\"); chatty
ones (per node, per triple) stay inside one component, statically linked."

Code, measurements and commands: `experiments/wasm-components/`
([README](../../experiments/wasm-components/README.md),
[RESULTS](../../experiments/wasm-components/RESULTS.md)). Nothing in the
shipped build, the npm package or the `danbri/factoidal-builds` workflows
changed.

## 1. The question

Today Lean emits C and Emscripten links one core wasm module plus JS glue
(`formal/lean4/Wasm/build-wasm.sh`, skill `lean4-wasm-export`). The plan asks
whether the same Lean C can become a component with a typed interface, built
with wasi-sdk and wit-bindgen, composed with components in other languages,
run by wasmtime natively and by jco in Node and browsers; and what each build
strategy costs in size, load time and throughput against the Emscripten build.

## 2. What was built

* A subset with two entry points, `experiments/wasm-components/lean/FxSubset.lean`:
  `parse` (the reader of the shipped `parseToDatasetJson` op, then the
  canonical N-Quads writer) and `query` (the shipped `queryDataset` op). Its
  import closure is 337 modules of `formal/lean4`, plus Lean's core library
  (864 generated C files).
* The WIT world (`wit/factoidal.wit`):

  ```wit
  package factoidal:subset@0.1.0;
  interface rdf {
    parse: func(text: string, format: string, base: string) -> result<string, string>;
    query: func(nquads: string, sparql: string) -> string;
  }
  world subset { export rdf; }
  ```

  wit-bindgen 0.46 generates the C bindings; `component/fx_component.c` maps
  them to the two Lean exports (initialisation and string conversion only;
  `Except String String` becomes `result<string, string>`).
* The same subset built four ways: Emscripten with the shipped flags (the
  baseline); wasi-sdk 30 for `wasm32-wasip2` and for `wasm32-wasip1` with the
  Preview 1 adapter; feature variants (`-Oz`, `-mtail-call`, `-msimd128`,
  `-fwasm-exceptions`); and strategy 3, one core module that `wasm-ld` links
  from the Lean C and a Rust static library.
* A Rust component (`driver-rs`, 103 KB) that imports `factoidal:subset/rdf`
  and runs as a `wasi:cli` command. `wac plug` composes it with the Lean
  component; wasmtime 37 and `jco run` (Node 22) run the result.

## 3. Results (from RESULTS.md)

On 60,000 triples of Turtle, in Node 22, medians:

| Build | Bytes (gzip) | JS glue (gzip) | load ms | init ms | parse ms | query ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Emscripten, shipped flags | 5,967,670 (1,149,729) | 60,295 (17,133) | 30 | 97 | 458 | 934 |
| component, wasip2, wasm-opt -O3 | 6,201,671 (1,122,302) | 317,043 (49,270) | 62 | 89 | 442 | 902 |
| component, without wasm-opt | 8,209,236 (1,267,631) | 324,446 (49,574) | 77 | 102 | 513 | 1,039 |
| component, -Oz | 3,708,045 (853,695) | 317,043 (49,270) | 57 | 77 | 744 | 1,219 |

The same query answer from every build (SHA-256 checked). In wasmtime the
composed component (Rust driver plus Lean) gives 479 and 953 ms; static
linking into one module gives 493 and 975 ms. Tail calls and SIMD change
nothing beyond the 10% spread between processes.

## 4. What the Lean runtime needs under WASI

Fourteen items, each with its file and fix, are in the blockers table of
RESULTS.md. In short:

* **C++ exceptions.** wasi-sdk 27 and 30 ship libc++abi without `__cxa_throw`,
  `__cxa_begin_catch`, `__cxa_end_catch`. The runtime's throw sites that this
  code can reach are fatal anyway (memory exhaustion, `unreachable_reached`,
  kernel stack checks), so the experiment aborts on a throw. A
  `-fwasm-exceptions` build links with two more stubs, but jco 1.40 refuses its
  component ("exceptions proposal not enabled"), and wasmtime 37 runs it only
  after `wasm-opt --translate-to-exnref`, because clang 21 emits the legacy
  exception instructions. Real exception support needs libc++abi and libunwind
  built with `-fwasm-exceptions`, which wasi-sdk does not ship yet.
* **POSIX parts that WASI lacks:** signals (`stack_overflow.cpp`, not
  compiled), processes (`process.cpp`, not compiled), ELF program headers
  (`compact.cpp`, not compiled), `ru_maxrss`, `/dev/urandom` (now
  `getentropy`), stdio stream locks, three libuv-header dependencies, and the
  two Emscripten headers that `-DLEAN_EMSCRIPTEN` selects. Five patches of
  `src/runtime` and three shim headers cover them
  (`runtime-wasi/patch-runtime.sh`); each patch is guarded by `__wasi__`.
* **Single thread.** As in the shipped build: only
  `lean_initialize_runtime_module`, no task manager thread. `wasip1-threads`
  was not tried.
* **Two costs that only a component host showed.** Each
  `wasi:clocks/monotonic-clock.now` call is a JavaScript call under jco. Lean's
  `lean_obj_once_cold` spin lock (`std::atomic::wait` in single-threaded libc++
  reads `steady_clock`) made 5,963 such calls during initialisation, and
  mimalloc's delayed purge made one on many frees. Patch 5 and
  `mi_option_purge_delay = -1` removed both: initialisation 181 to 216 ms
  became 88 to 102 ms, and parse and query 10% to 20% faster. The Emscripten
  build makes the same clock calls through its own cheaper import; the same two
  settings may help it too (not measured).

## 5. What the measurements do not settle

* Browsers: only Node was measured. jco's output is the same ES module for
  browsers; the load-time gap (jco glue 5.3 times the Emscripten glue) will
  matter more on a phone.
* The full engine: only a 2-function subset. The shipped module puts every op
  behind one JSON `l4_call` entry; a typed WIT for it is design work
  (records, `resource` handles for the dataset and store handles).
* Spin and wasmCloud, which the plan names for HTTP hosting, were not tried.

## 6. Recommendation

1. **Keep Emscripten for the shipped npm and browser module now.** The
   component has the same throughput and a smaller gzip size, but it loads 2
   times slower in Node because of the jco glue, and jco cannot take a build
   with wasm exceptions. Nothing is gained for the package today.
2. **Make wasi-sdk plus WIT the second build target, for composition and
   server hosting.** It works with small, guarded runtime patches, gives the
   same answers at the same speed, and runs in wasmtime without JavaScript.
   The plan's boundary rule holds in the measurements: a coarse interface that
   copies 7 MB per call pair costs nothing measurable, so components at
   "parse this document" and "run this query" boundaries are affordable.
3. **Always run `wasm-opt -O3`** on a wasi-sdk build (32% smaller, about 15%
   faster). Do not enable tail calls or SIMD for this code: no measured gain.
   Use `-Oz` only where size dominates (40% fewer bytes, 40% to 68% slower).
4. **Next steps, each its own decision:** (a) a WIT world for the core
   dispatch with typed records and `resource` handles; (b) the
   extension-function host call-out (`ffi/l4_ext.c`) as a WIT import; (c) offer
   the 5 runtime patches upstream to leanprover/lean4 as a WASI configuration;
   (d) try the two clock fixes in the Emscripten build and measure; (e) a
   `danbri/factoidal-builds` job for the component, only after the owner
   decides (this experiment dispatches nothing).

## 7. Reproduce

`experiments/wasm-components/README.md` § Reproduce. Cost on the 4-vCPU
container of 2026-10-29: tools 3 minutes; `lake build` of the closure about 25
minutes cold; core and runtime C per flag set about 5 minutes; the whole
measurement run about 60 minutes.
