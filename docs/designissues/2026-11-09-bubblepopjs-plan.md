# BubblePopJS: plan to reach the level of the leading engines (2026-11-09)

Owner, 2026-11-09, verbatim (the goal of the session): "concrete plan to take BubblePopJS into
the big league of SOTA engines, blazing fast with and without JIT. Efficient and light profiles
for lower end hardware. Modern and freshly thought through design aesthetic. Fast, compliant, and
taking every advantage from being Lean-based, with theorems typing the codebase together and
underwriting daring heuristics, optimisations, and shortcuts." And: "Remember to test on commin
real world js and wasm, including the patterns we'll increasingly see downstream from verified
languages like Lean and Rocq."

Relayed the same day from the session that wrote stages A and B: "That session stops after
landing A and B, so everything from "compile functions with captured variables" onward is yours."
So this plan starts where stage B (`wip/bpperf-vm`, `167605f4c`) stops.

Measurements behind every number here: [2026-11-09-foafnaut-perf-exploration.md](2026-11-09-foafnaut-perf-exploration.md).
Machine: one Linux x86_64 cloud VM (4 virtual CPUs). Nothing here was measured on a Mac, in the
Hub, or in a page. The JIT stages (section 8, stages E and F) rest on designs and on records of
other work in this repository, not on a measurement of a BubblePopJS JIT: none exists.

## 1. Decisions for the owner

1. Approve, change or refuse the key results of section 9 as an OKR batch for BubblePopJS
   (tracking issue: https://github.com/danbri/factoidal-core/issues/378).
2. The data layout of section 4 replaces the run-time state of stages A and B (values as Lean
   objects, registers as an `Array Value`) after stage B lands. Stage B's compiler, resolver
   and instruction set stay. Yes or no.
3. JIT route: generated WebAssembly through the existing `WasmVM.Aot` path first (the Hub; the
   desktop app's host also has a WebAssembly engine, and whether that path is wired there was
   not checked), machine code from build-time templates later. The later step needs one new
   trusted primitive (run bytes as code); it is not started without a separate decision.
4. A memory limit for a page's JavaScript heap, on by default (today one statement,
   `new Array(4294967295)`, takes all memory of the process). Proposed default: 512 MB for a
   desktop page, 64 MB in the light profile, as `RangeError: out of memory` in the page.

## 2. Where BubblePopJS is (measured 2026-11-09)

Trees: `main` (`489d5cd3a`), stage A (`wip/bpperf`, `e8d2a3e6e`), stage B (`wip/bpperf-vm`,
`167605f4c`). Comparison engines on the same machine: QuickJS-NG 0.18.0 and V8 of Node 22
(`--jitless`, and with its JIT).

### 2.1 Single operations

Nanoseconds for one operation, less the loop (`bubblepop_perf/opcost.py`; the full table of 61
operations is in the exploration record). "Core model" is the Lean program of section 5.

| Operation | main | Stage A | Stage B | Stage B with the conversions of 2026-11-09 | Core model | QuickJS-NG | V8 no JIT |
|---|---|---|---|---|---|---|---|
| the loop itself (`i < n; i++`) | 320 | 132 | 48 | 50 | 7.6 | 8 | 8 |
| `s = s + k` | 204 | 113 | 18 | 15 | 1.9 | 2 | 2 |
| `s = i < k` | 175 | 108 | 17 | 13 |  | 5 | 4 |
| `s = o.x` | 179 | 113 | 27 | 20 | 3.3 | 7 | 5 |
| `o.x = i` | 258 | 114 | 86 | 81 | 3.4 | 6 | 2 |
| `s = a[3]` | 231 | 172 | 79 | 27 |  | 5 | 2 |
| `a[3] = i` | 400 | 243 | 195 | 175 |  | 6 | 6 |
| `s = i \| 1` | 536 | 465 | 394 | 92 |  | 5 | 5 |
| `s = G` (global) | 184 | 175 | 36 | 29 |  | 3 | 3 |
| `s = g1(i)` (top-level function) | 848 | 343 | 166 | 150 | 7.1 | 15 | 12 |
| `s = o.m(i)` | 822 | 269 | 142 | 136 |  | 18 | 14 |
| `s = h1(i)` (inner function) | 795 | 264 | 286 | 298 |  | 16 | 12 |
| `s = { x: i, y: k }` | 735 | 597 | 411 | 386 | 4.4 | 66 | 13 |
| `s = function () { return i; }` | 1309 | 1098 | 1049 | 968 |  | 119 | 11 |
| `s = t.charCodeAt(3)` | 556 | 483 | 416 | 362 |  | 25 | 12 |
| `try { s = i; } catch (e) {}` | 177 | 139 | 221 | 224 |  | 7 | 3 |

A V8 or QuickJS-NG figure under 10 ns has an error of a few ns: the loop is subtracted.

### 2.2 Real-world code

`bubblepop_perf/realworld.py`: each workload is a library's single-file build and a driver that
prints a checksum. An answer counts only when it equals the reference engine's. CPU
milliseconds at the larger size, less the load; "x" is the ratio to QuickJS-NG; MB is peak
resident memory.

| Workload | main | Stage A | Stage B | Stage B with the conversions of 2026-11-09 | QuickJS-NG | V8 no JIT | V8 |
|---|---|---|---|---|---|---|---|
| lodash 4.17.21 (collections) | 1,709 ms, x22.7, 412 MB | 733 ms, x9.7, 42 MB | 417 ms, x5.5, 42 MB | 359 ms, x4.8, 42 MB | 75 ms, 17 MB | 34 ms, x0.4, 51 MB | 42 ms, x0.6, 58 MB |
| acorn 8.11.3 (a JavaScript parser) | 1,609 ms, x12.6, 254 MB | 1,007 ms, x7.9, 32 MB | 935 ms, x7.3, 34 MB | 895 ms, x7.0, 32 MB | 127 ms, 17 MB | 57 ms, x0.4, 46 MB | 94 ms, x0.7, 55 MB |
| pako 2.1.0 (zlib; typed arrays, bit operators) | 3,648 ms, x57.2, 100 MB | 2,910 ms, x45.7, 21 MB | 2,744 ms, x43.0, 20 MB | 2,019 ms, x31.7, 20 MB | 64 ms, 17 MB | 51 ms, x0.8, 44 MB | 61 ms, x1.0, 51 MB |
| marked 4.3.0 (Markdown; regular expressions) | does not load | does not load | does not load | does not load | 32 ms, 17 MB | 14 ms, x0.5, 45 MB | 14 ms, x0.4, 50 MB |
| immutable 4.3.5 (persistent maps and lists) | 2,682 ms, x22.2, 412 MB | 1,569 ms, x13.0, 77 MB | 1,176 ms, x9.7, 80 MB | 992 ms, x8.2, 80 MB | 121 ms, 17 MB | 65 ms, x0.5, 50 MB | 138 ms, x1.1, 59 MB |
| the F\*-extracted RDF and SPARQL engine (`js_of_ocaml` 6.4.1, 1.18 MB) | 6,585 ms, x27.5, 1,636 MB | 5,754 ms, x24.0, 207 MB | 5,990 ms, x25.0, 213 MB | 4,983 ms, x20.8, 214 MB | 239 ms, 21 MB | 149 ms, x0.6, 61 MB | 95 ms, x0.4, 71 MB |
| geometric mean of x, over the workloads that run | 25.1 (of 5) | 16.1 (of 5) | 13.4 (of 5) | 11.3 (of 5) | 1 | 0.5 (of 6) | 0.7 (of 6) |

CPU time includes V8's compiler threads, so on runs this short V8 with its JIT can show more
CPU time than V8 without it. Sizes are chosen so that QuickJS-NG takes 30 to 250 ms.

What the table and the profiles of the exploration record (its section on real-world code) say:

- BubblePopJS gives the right answer on 5 of the 6 workloads on every tree, among them a
  1.18 MB `js_of_ocaml` bundle extracted from F\*. `marked` does not load: the lexer takes `/`
  after `)` of a `for` or `if` header as a division (one more lexer defect and six other
  defects found the same day are in section 7.3).
- Stage B compiles 72 to 89% of the functions of these libraries and is still 5.5 to 43 times
  slower than QuickJS-NG on them. The time is in what the operations do, in four places:
  1. **Names of enclosing scopes found by text.** 43% of the F\* bundle's run is `Env.scan`
     (and 6% more is `memcmp`): a `js_of_ocaml` bundle, like every bundled application, is one
     function that holds thousands of functions and variables, and each use of one from an
     inner function scans that scope by name.
  2. **Allocation and reference counts**: 12 to 26% of every profile (`mi_malloc_small`,
     `mi_free`, `lean_dec_ref_cold`). Values, results and frames are Lean objects.
  3. **Typed arrays by string key**: in `pako`, `a[i]` on a `Uint8Array` makes the index a
     string and parses it back (`arrayIndex?`, 5%), with GMP allocation beside it.
  4. **Properties by hashing strings**: in `acorn`, `PropMap` and `hash_str` at every access.
     There are no shapes and no inline caches.
- Memory: 1.2 to 10 times QuickJS-NG on stage B (213 MB against 21 MB on the F\* bundle), 6 to
  78 times on `main` (1,636 MB). No object is ever freed, and a small object takes 328 bytes.
- Load: the F\* bundle takes 1.6 to 1.8 s to parse and start, QuickJS-NG 0.27 s, V8 0.10 s.
- The proved number conversions of 2026-11-09 (not in stage A or B) take 4 to 26% off stage B
  on these workloads.
- Added 2026-11-10. The first of the four places is repaired for names that the scope does
  not have (globals, absent names): a function environment with more than 24 names has an
  index. With the defects 1, 2, 9 and 10 repaired, `marked` runs (5.3 times QuickJS-NG) and all
  6 workloads give the reference answer. The F\* bundle went from 26.1 to 11.0 times
  QuickJS-NG in one run on one machine, and its load from 2,195 to 1,058 ms (QuickJS-NG 442).
  Geometric mean of the ratio over the six workloads: 8.4. The table above is the state
  before these repairs; the table after them is in the exploration record, section 6.6.

### 2.3 Start, size, compliance

- Empty script: 5.2 ms CPU and 11.7 MB resident (QuickJS-NG 1.9 ms and 8.3 MB). The `leanjs`
  program is 8.7 MB (QuickJS-NG 1.4 MB).
- Test262: the tree holds 6,301 files of `test/language`, and none of `test/built-ins`.
  On them: `main` 5,627 pass, 670 fail, 4 skip; stages A and B 5,629 pass, 668 fail, 4 skip.
  Most failures: object literals 171, assignment 83, compound assignment 56, `switch` 51,
  `for-in` 43, function statements 41.
- Proofs: nothing in stage A or B is proved (their own record). The number conversions are
  (the exploration record, section 7).

## 3. The target, stated as engines and numbers

| Class | Engines measured against | Why |
|---|---|---|
| Interpreter, no JIT | QuickJS-NG 0.18.0; V8 `--jitless` (Ignition) | Small C interpreter; best-known bytecode interpreter with inline caches. JavaScriptCore with no JIT is in the Mac session's table. Hermes and SpiderMonkey without JIT are to add: no binary was on this machine |
| JIT | V8 (Node 22) | The `v8` column of the corpus |
| Small devices | QuickJS-NG's start, memory and size | To add: Moddable XS and MicroQuickJS, when a light profile exists to compare |
| Compliance | Test262 (whole), the Web Platform Tests through Foafnaut, differential runs against two engines | The owner's measure of the browser is WPT |

"Leading" is then four statements, each a key result in section 9: correct on real code;
interpreter at the speed of QuickJS-NG and then of V8 without its JIT; memory and start of the
order of QuickJS-NG; a JIT tier with a measured gain where a host can run generated code.

## 4. Design

Seven rules. Each has its reason in a measurement of section 2 or in this repository's own
engine for WebAssembly (`2026-11-07-wasmvm-engine.md`, called "the WasmVM record" below).

1. **No JavaScript value is a Lean object.** A value is one 64-bit word. Registers and the
   JavaScript heap are flat arrays of words that one loop owns. Then an operation changes no
   reference count and allocates nothing. Today `s = s + k` on stage B is 329 instructions,
   a call 2,558; the model of section 5 does them in 46 and 139.
2. **One meaning, several executions.** The evaluator of `JS/Interp.lean` is the reference
   semantics. The register machine, each cache, each rewrite and each compiled form is tied
   to it by a theorem, or by a named differential check until the theorem exists.
3. **A fast path is a guarded shortcut.** It has a guard that the machine tests, and a theorem:
   when the guard holds, the shortcut's result is the general path's result. A heuristic only
   chooses WHEN to install a shortcut. It cannot change a result, so it can be aggressive.
4. **What a verifier proves once, the loop does not test.** Register numbers, jump targets
   and constant indices of verified code are in range (as `CodeOk` and `maxHeight_sound` do for
   WasmVM). Later: types that an analysis proves.
5. **Speculation with no state map.** Specialised code and general code use the same register
   frame. When a guard fails, execution goes on in the general code at the same instruction.
6. **Size and start are designed in.** The stored form of a script is bytecode. A function is
   compiled when it is first called. A profile chooses what is built in.
7. **Real code decides.** A change is judged on the corpus first, on single operations second.

### 4.1 The value word

- A number is its IEEE 754 bits. Every other value is a word above `0xFFF8000000000000`: a tag
  in the top 16 bits, a 48-bit payload. Tags: object, string, symbol, big integer, boolean,
  undefined, null, and a 32-bit integer (see 4.6).
- The words are in a `ByteArray`, read and written 8 bytes at a time with `Bytes.ld64` and
  `Bytes.st64` of `WasmVM/Exec/Bytes.lean` (one bounds test; the store is inline C with a
  Lean reference body, already in the "Trusted pieces" table of the WasmVM record).
- Not a `FloatArray`: Lean 4.33 makes every NaN the canonical NaN in `Float.ofBits`, so a tag
  kept in a NaN is lost. WasmVM met this (its record, "Operand-stack representation").
  `Float.ofBits` is applied only to a word that is a number.
- A payload is an index into a heap array, never a pointer. So the same words work on 32-bit
  WebAssembly, and a collector can move objects.

### 4.2 The heap

Flat arrays, each owned by the machine state:

- **Objects**: a header word (shape number, flags), then the property slots, in one word array.
  A 2-property object is 3 words, 24 bytes (today 328).
- **Shapes** (hidden classes): a table of (parent shape, key, slot). Adding a property moves an
  object to the child shape. An object with many keys, or with deleted keys, goes to a
  dictionary (today's `PropMap`).
- **Property keys are interned**: a key in code and in a shape is a number. No string is
  hashed at a property access.
- **Elements**: arrays hold words in an element store; a typed array's bytes are a `ByteArray`
  that element operations read at the element width, with no key.
- **Environments**: a captured variable lives in an environment record on the heap (a word
  array with a parent). The compiler turns each use into (number of parents to climb, slot).
  This is the item "compile functions with captured variables", and it removes the 43% of 2.2.
- **Strings**: a string table; concatenation makes a rope that is flattened when indexed;
  positions are UTF-16 code units, with a table for strings that are not Latin-1.
- **Frames**: the register file is one word array. A call moves the base; the return data is
  three words below the new base. JavaScript recursion uses no host stack (as stage B), a
  generator or an `await` keeps a slice of the register file, and an exception finds its
  handler in a table of pc ranges of the function.

### 4.3 The collector

Every value is a tagged word, so the roots (register file, globals, host handles) and every
object can be traced exactly, by Lean code over Lean arrays. It does not interact with Lean's
reference counts. First a mark and compact collector that runs between turns of the event loop
and when the heap passes a limit; then a nursery for young objects. Its theorem: the heap that
the roots reach is the same before and after, up to a renaming of indices.

### 4.4 Bytecode and the loop

- Stage B's register code stays as the instruction set. Its encoding becomes 32-bit words in
  an unboxed array (a `ByteArray` on 32-bit WebAssembly, where a `UInt32` in an `Array` is an
  allocated object). Today an instruction is a Lean object whose read changes two reference
  counts.
- The loop follows the WasmVM record's measured rules: one tail-recursive function on a step
  budget; `USize` indices; every exit through one function that is not inlined ("Register
  spills at the dispatch head"); few loop-carried arguments; rare operations in a second
  function, because each case added to the WasmVM loop slowed all of it by 20 to 25%.
- A verifier checks each function's code once. The loop then reads registers and code with
  proved indices.

### 4.5 Inline caches

A property read, write or method call has two cache words after its instruction: the shape it
saw and the slot it found. The fast path is: object tag, shape equal, load. One theorem covers
all of them: an object of shape `s` has key `k` in slot `i` when the shape table says so
(`shape_lookup_sound`), and the table only grows. A read through the prototype chain adds a
validity number of the prototype's shape.

### 4.6 Numbers

JavaScript numbers are doubles. Code from compilers (`js_of_ocaml`, Emscripten glue) is full
of `x | 0`, shifts and array indices. A 32-bit integer tag gives those a path with no
conversion: add with an overflow test, bit operators direct. Whether it pays is experiment E2
of section 10; the conversions themselves are already proved (`toInt32Fast`, `toUint32Fast`).

### 4.7 Tiers

| Tier | What | Where it runs |
|---|---|---|
| 0 | Register bytecode in the loop of 4.4, inline caches | Everywhere, and the only tier where a host forbids generated code |
| 1 | The same loop with operations fused and specialised from counters, each proved equal to the sequence it replaces (as `fused_refines` in WasmVM) | Everywhere |
| 2 | Each bytecode instruction as a WebAssembly template; a function is the templates of its instructions, joined | Hosts with a WebAssembly engine: the Hub, through `WasmVM.Aot` (validate in Lean, then the host compiles it; fuel metering and import routing exist and are partly proved, `2026-11-08-wasmvm-aot.md`). The desktop app's host has such an engine too; that path was not checked there |
| 2n | The same templates as machine code made at build time, copied and patched at run time | Native builds, after the decision of section 1, item 3 |
| 3 | An optimiser over a typed intermediate form: inlining, unboxed registers, bounds tests removed by a proved range analysis. Each rewrite is a theorem; the pass that applies proved rewrites needs no proof of its own | Where tier 2 or 2n runs |
| build | JavaScript that ships with the browser (what stays of `prelude.js`, 1,135 functions today, after https://github.com/danbri/factoidal-core/issues/376) compiled when the browser is built: a specialiser written in Lean turns the bytecode of a function into a Lean definition, which `leanc` compiles | Every platform, the ones with no JIT included |

The "build" row has no counterpart in an engine written in C. One theorem about the
specialiser (`specialise_sound`: the definition it makes equals the interpreter on that
bytecode) would make the compiled prelude equal to the interpreted one by proof. It is a
design: no part of it exists, and section 10 has its risk (E8).

### 4.8 Profiles

One `Profile` value, as `FontPolicy` is for fonts, read at start:

| Profile | Tiers | Heap limit | Kept out | For |
|---|---|---|---|---|
| light | 0 | 64 MB default | the parser when scripts arrive as bytecode; regular expression compiler tables until first use; `Intl`-sized tables | small devices, Textnaut, embedders |
| standard | 0, 1, build | 512 MB default | nothing | the browser where generated code is not allowed |
| fast | 0 to 3 | 512 MB default | nothing | hosts with a WebAssembly engine, or native after tier 2n |

A refused feature says so in the page (`RangeError`, or a console line that names the profile).

## 5. What the layout costs in compiled Lean: a model

`labs/demos/foafnaut/bubblepop_perf/lean/CoreModel.lean` is a Lean program with the layout of
4.1 to 4.5 and nothing else of an engine: value words in a `ByteArray`, 32-bit code words,
inline caches in the code, objects with a shape word, calls on the register file, allocation
by moving an index. It has the tag, shape and bounds tests. It has no collector, no strings,
no property addition, no prototype chain and no exceptions. It is what the fast paths can
cost, not what an engine costs.

Compiled as Lake compiles the library (`leanc -O3 -DNDEBUG`), quiet machine, 3 M iterations,
`run.sh` beside it. Nanoseconds for one operation less the loop, except the first and the
`fib` rows:

| | Core model | Core model, Lean's own bit conversions | QuickJS-NG | V8 no JIT | Stage B |
|---|---|---|---|---|---|
| the loop `i < n; i++`, ns | 7.6 | 10.6 to 13.0 | 8 | 8 | 48 |
| `s = s + k` | 1.9 | 4.2 to 6.3 | 2 | 2 | 18 |
| `s = o.x` | 3.3 | 3.0 to 4.9 | 7 | 5 | 27 |
| `o.x = i` | 3.4 | -0.4 to 3.0 | 6 | 2 | 86 |
| `s = g1(i)` (call and return) | 7.1 | 6.3 to 11.8 | 15 | 12 | 165 |
| `s = { x: i, y: k }` | 4.4 | 1.4 to 4.8 | 66 | 13 | 411 |
| `fib(30)`, ns for one call | 17.3 | 23.8 to 25.7 | 23.4 | 23.0 | 145 |
| instructions: loop, add, call | 153, 46, 139 | 224, 83, 145 | | | 972, 329, 2,558 |

The first column is the median of 5 runs (ranges in the exploration record, section 8); the
second is the range of 3 runs.

- The first column uses a one-instruction bit cast between a number and its word (inline C).
  The second uses `Float.toBits` and `Float.ofBits`, which in Lean 4.33.1 are calls into the
  runtime: 5 calls in one loop iteration.
- So the distance from stage B to QuickJS-NG on these paths is the data layout. Compiled Lean
  is not the limit: the same compiler gives 17 ns for a call of `fib` where QuickJS-NG takes 23.
- What the model leaves out costs on slow paths in every engine. Two things cost on fast
  paths too and are not in these numbers: the argument count and `this` of a real call, and
  the write barrier of a nursery. The step budget of a page turn is in the model.

## 6. Theorems

The reference semantics is the evaluator. Relation `R` joins an evaluator state (environments,
objects as records) and a machine state (register file, flat heap). The statements, in the
order they pay:

| | Statement | Makes sound | State |
|---|---|---|---|
| T0 | `natToFloat_eq`, `ofScientificFast_eq`, `toInt32_eq_fast`, `toUint32_eq_fast`, six `csimp` theorems | number conversions on machine integers | proved (2026-11-09) |
| T1 | `verify_sound`: verified code reads no register, jump target or constant out of range | the loop without those tests | to do; shape of WasmVM `CodeOk` |
| T2 | `shape_lookup_sound`, `ic_get_sound`, `ic_set_sound` | inline caches | to do |
| T3 | `step_refines`: one machine instruction from `R`-related states gives `R`-related states, one lemma for each instruction | the register machine against the evaluator | to do; by instruction, as the proof program of `skills/proof-factory` |
| T4 | `compile_sound`: for the constructs the compiler takes, the code of a function refines its body | the compiler | to do, by construct |
| T5 | `collect_preserves`: the reachable heap is the same up to renaming | the collector | to do |
| T6 | `fuse_sound` and `fused_charges_parts` for each fused or specialised instruction | tier 1, and step counts that do not change | to do; the WasmVM lemmas are the pattern |
| T7 | `template_refines` for each instruction's WebAssembly template, against the WebAssembly semantics of `WasmVM.Spec`; a composition lemma for a function | tier 2 | to do |
| T8 | `rewrite_sound` for each rewrite of tier 3 | the optimiser | to do |
| T9 | cost statements: instructions for each operation as a bound, checked on the benchmarks | a ratchet that a refactor cannot lower | to do; `Proofs/Cost.lean` in WasmVM is the pattern; https://github.com/danbri/factoidal/issues/1292 (cost theorems as a ratchet) |
| T10 | `specialise_sound`: the definition that the specialiser makes from a function's bytecode equals the interpreter on that bytecode | the "build" tier | to do |

Until a row is proved, the same claim is a differential check that runs in the tests: the
machine against the evaluator on Test262 and on the corpus (stage B's `useVm` check does this
for Test262 today). A record never says "proved" for a row that is tested.

What stays trusted: Lean's compiler and runtime; the inline C of `st64`; the bit cast of
section 5 if it is adopted; the host's WebAssembly engine for tier 2; the C compiler for the
templates of tier 2n.

## 7. Tests and measurements

### 7.1 The corpus

`realworld.py` today: lodash, acorn, pako, marked, immutable, and the F\*-extracted engine.
To add, in this order:

1. More output of verified-language toolchains: a Rocq development extracted to OCaml and
   compiled by `js_of_ocaml` (the F\* build already has that compiler); Dafny's JavaScript
   output; the Emscripten glue of a Lean-compiled module. Their shared traits are the ones
   section 2.2 found: thousands of functions in one scope, closures and partial application,
   exceptions as control flow, integers as `x | 0`, arbitrary-precision integers, high
   allocation rates.
2. WebAssembly, in BubblePopWASM. Measured on 2026-11-09 (the exploration record, 6.5):
   `l4factoidal.wasm` (Lean compiled to WebAssembly, 32.7 MB, 23,747 functions) decodes,
   validates and starts in 3.7 s for each step, with 1.5 GB of memory; QuickJS-NG as a guest
   runs `fib(24)` in 720 ms; the three `wasm_of_ocaml` modules of the F\* tree do not decode
   ("unsupported: GC type definition"). So the corpus gets these as rows, the third as an
   expected failure with an issue, and the garbage collection proposal is a need of this
   plan's users even though it is BubblePopWASM work.
3. Tools that pages and build systems run: a second parser, a minifier, a template engine,
   a Markdown renderer once the lexer defect is repaired.
4. `testharness.js` with a real WPT file: every WPT test pays for it.

### 7.2 Compliance

- Test262: fetch the whole suite at a pinned commit (the tree has `test/language` only), run
  `test/language` and `test/built-ins`, and report beside QuickJS-NG run on the same files.
- A differential run against two engines on generated inputs found 3 library defects in one
  evening (7.3). It becomes a test: `bubblepop_perf` gets the driver, the expected lines come
  from two engines that agree.

### 7.3 Defects found on 2026-11-09, on `main`, stage A and stage B

Each is one line to reproduce. They are a checklist in
https://github.com/danbri/factoidal-core/issues/378 (the plan and its key results). Items 1, 2,
8, 9 and 10 were repaired on 2026-11-10 on the branch `claude/foafnaut-perf-bottlenecks-7hpt38`,
with tests in `formal/lean4/L4Factoidal/JS/RegressionTests.lean`. Items 3 to 7 have no test
yet: each gets an expected failure that names the issue before its repair (stage B2, item 3).

1. `if (s) /y/.test(s);` and `for (...) /re/.test(x)`: "regular expression literals are not
   supported" (the lexer takes `/` after `)` and after `}` as division). `marked` fails on it.
2. `var b = a.x++ / 2;`: "missing ';'" (the lexer takes `/` after `++` as a regular expression).
3. `[10,11,12,13,14].lastIndexOf(13, 0)` gives 3; the answer is -1.
4. `(0.5).toString(16)` gives `0.5`; the answer is `0.8`.
5. `var b = [1,2,3]; b[1000000] = 7; b.length` gives 3; the answer is 1000001.
6. `var b = []; b.length = 5; 0 in b` gives true; the answer is false.
7. `new Array(4294967295)` takes all memory (section 1, item 4).
8. On stage B only: `s += x` copies the string at each append (400,000 appends: 0.13 s on stage
   A, 1.86 s on stage B). `vmLoop`'s `.add` appends while the register still holds the string.
   Repaired for a local variable; a global in a compiled top-level loop still copies.
9. Found 2026-11-10: `function f() { f = 1 }` threw "Assignment to constant variable" (a
   function declaration had the private name scope of a function expression). Babel's helpers
   do this. Repaired.
10. Found 2026-11-10: no `encodeURI` and no `decodeURI`; `marked` then wrote links as plain
    text. Repaired.

### 7.4 Speed and memory in CI

`opcost.py --callgrind` gives instructions for each operation, the same on every machine. A
table of bounds for the operations of 2.1 becomes a gate, as `wasmvm-bench engine --check` is
for WasmVM. `realworld.py` exits 1 on a wrong answer today; it gets floors for time ratios on
a quiet runner.

## 8. Stages

Each stage ends with numbers from the commands named. Work items are one commit each.

**Stage B2: finish what stage B started** (on stage B's state; no layout change)

1. Captured variables by (parents, slot); functions that make closures compile. Exit: the F\*
   workload's `Env.scan` share under 2% (now 43%).
2. `try`, `switch`, `for-of`, `for-in`, classes with `super` in the compiler. Exit: 95% of the
   corpus's functions compile (now 72 to 89%).
3. The defects of 7.3, each with its test first.
4. Typed array reads and writes with no key string. Exit: `pako` under 10 times QuickJS-NG
   (now 43; 32 with the conversions of 2026-11-09).
5. `Number.isSafeInteger` and the literal `4294967295.0` in `vmLoop` and `evalExpr` as named
   constants (`tools/lean-literal-parse-audit.py --float-literals`).

**Stage C: the data layout** (section 4.1 to 4.5)

6. Value words and the register file; the bridge to the evaluator for what is not compiled.
7. Objects, shapes, interned keys; inline caches for read, write and method call.
8. Environments, strings as ropes, elements, typed arrays on the flat heap.
9. The collector, and the heap limit of section 1.
10. `verify_sound` (T1) and the inline cache theorems (T2).
   Exit: key results 2 to 5 of section 9 at their stage C figures.

**Stage D: tier 1, profiles, compliance**

11. Counters; fused and specialised instructions with T6; the 32-bit integer path if E2 says so.
12. Functions compiled at first call; scripts stored as bytecode; the `light` profile.
13. The prelude compiled at build time (the "build" row of 4.7), after E8.
14. Test262 whole; the differential test; `step_refines` for the instruction set (T3).

**Stage E: tier 2**, after experiment E3. **Stage F: tier 3 and tier 2n.**

## 9. Key results (proposed)

Baseline: stage B at `167605f4c` on the machine of the exploration record, unless a line says
otherwise. Commands are from the repository root; engines are named as in `realworld.py`.

| | Key result | Baseline | Stage C | Stage D | Command |
|---|---|---|---|---|---|
| 1 | Corpus workloads with the reference answer | 5 of 6 | 6 of 6, of at least 12 | all of at least 20, 5 from verified-language toolchains | `realworld.py`, exit 0 |
| 2 | Run time over QuickJS-NG, geometric mean of the corpus | 13.4 (11.3 with the conversions of 2026-11-09) | at most 2.0 | at most 1.0 | `realworld.py` |
| 3 | `fib(30)`, ns for one call | 145 (QuickJS-NG 23.4) | at most 30 | at most 20 | the exploration record, section 8 |
| 4 | Peak memory over QuickJS-NG, largest ratio in the corpus | 10.1 (213 MB against 21 MB) | at most 3 | at most 2 | `realworld.py` |
| 5 | Load of the F\* bundle (parse and start) | 1,633 ms (QuickJS-NG 272) | at most 2 times QuickJS-NG | at most 1.5 times | `realworld.py --only fstar-sparql` |
| 6 | Empty script: CPU ms and resident MB, `light` profile | 5.2 ms, 11.7 MB (QuickJS-NG 1.9, 8.3) | | at most 3 ms, 8 MB | the exploration record |
| 7 | Test262 `test/language` and `test/built-ins`, whole suite at a pinned commit | not measured (5,629 pass of 6,301 files of the tree's part) | measured, with QuickJS-NG beside it | at least QuickJS-NG's pass count less 2% | `leanjs test262` |
| 8 | Defects of 7.3 open | 8 | 0 | 0 | their tests |
| 9 | Theorem rows of section 6 proved | T0 | T0 to T2 | T0 to T3, T5, T6 | `lake build`, `#print axioms` |
| 10 | Tier 2 on the Hub over tier 1, on `fib` and one corpus workload | no tier 2 | E3 done | decision from E3 | `hub_scripts_speed.mjs` |

Key results 2 to 5 at stage D rest on section 5: on its paths the layout is at QuickJS-NG's
cost or under it. They do not rest on a measurement of a whole engine, and section 10 says
what could make them wrong.

## 10. Risks, and the experiment that settles each

| | Risk | Experiment |
|---|---|---|
| E1 | The loop gets slower as it gets its full instruction set (WasmVM: 20 to 25% for each batch of cases) | Grow the model to 60 operations with a rare-operation function; measure the first 8 again |
| E2 | A 32-bit integer tag costs more on float code than it saves on integer code | Two models; `pako` and the F\* bundle's operation mix decide |
| E3 | Generated WebAssembly must read the register file and the heap, which are Lean arrays in the engine's own memory on the Hub | One template (`add`) through `WasmVM.Aot` with the engine's memory imported and base addresses passed at entry; measure a loop; state what a wrong template could touch |
| E4 | The collector's cost and pauses in a page that animates | The collector on the model with a synthetic allocation mix of the F\* bundle (allocation rate from the profile) |
| E5 | The proofs T3 and T4 are large | Prove `step_refines` for 5 instructions first and count the lines for each; then set the order |
| E6 | 32-bit WebAssembly: boxed `UInt32`, call depth 100 | Compile the model with the engine's Wasm toolchain; its loop makes no host call, so depth should not matter. Measure |
| E7 | Two layouts live at once during stage C (the evaluator's objects and the flat heap) | The bridge converts at calls between compiled and uncompiled functions; stage B2 item 2 makes those rare first |
| E8 | The build-time specialiser makes Lean definitions too large for Lean's compiler, or `specialise_sound` is out of reach | Specialise 10 functions of `prelude.js` by hand first: compile time, code size, speed against the loop; state the theorem for 3 instructions |

## 11. Not measured, not known

- Anything on a Mac, in the Hub, in a page with a DOM, or on 32-bit WebAssembly.
- A whole-suite Test262 or WPT figure for any tree.
- JavaScriptCore, Hermes, SpiderMonkey, XS, MicroQuickJS: no binaries here.
- A BubblePopJS JIT of any kind. Section 4.7's tiers 2 to 3 are designs.
- BubblePopWASM beyond the four modules of the exploration record, section 6.5.
- The corpus has 6 workloads. Six do not make a geometric mean that a decision should rest on
  alone; section 7.1 is there to change that.
