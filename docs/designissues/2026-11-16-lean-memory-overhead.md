# Memory-management overhead in BubblePopJS: a limit of the strategy, or of how the code is written and built?

Date: 2026-11-16. Tracking issue: [BubblePopJS JIT: proven equivalent to the interpreter](https://github.com/danbri/factoidal-core/issues/471).
Size and build settings: [issue 551](https://github.com/danbri/factoidal-core/issues/551).
Earlier record, whose finding this one examines: [BubblePopJS heap: measurements, design and migration plan](../bubblepopjs-heap.md).

The heap record found that 29 to 57% of script time is allocation, free, thread-local lookups and
reference-count slow paths, and that most allocations are result cells of the monad, tuples and `Option` cells
rather than JavaScript values. The question here: is that a limit of writing the engine in Lean 4 and compiling
it through Lean's C backend, or a matter of idioms, data structures, fast paths and build settings?

## Verdict

**Not fundamental. One real compiler limit, which constrains style and costs proofs; the rest is how the code is
written and how the C is built.** The reasons, each measured below:

1. **The same generated C runs 15 to 22% faster with different build settings.** Link-time optimisation across
   the engine's C and three units of Lean's runtime (object, alloc, mimalloc) takes the library corpus to 0.85 of
   the time of the build Lake makes, and with a profile to 0.78; a held-out Test262 selection runs in 0.77 to
   0.88 of the time of the build without it. No Lean source changes. A cost that a linker flag removes is not a property of the language.
2. **The same Lean definition costs 18 ns as a call and 1.3 ns inlined.** A monadic helper that is not inlined
   allocates its result cell; inlined into a caller that matches on the result at once, it allocates nothing.
   A helper that returns a scalar, or the state record itself, costs 3 to 6 ns. The cost is attached to a
   calling convention, and the source chooses the convention.
3. **The allocations are concentrated in a few places.** On pako 13.9% of all allocations are in `arrayIndex?`
   (a string key parsed back into a number for each element access) and 15.7% in `toNum` (a boxed float in a
   result cell for a value that already is a number); on marked 61% are in one loop. These are sites, not a
   property spread evenly over the program.
4. **The one real limit: Lean 4 has no unboxed multiple or sum results.** In the pinned 4.33.1 and in every
   release up to 4.36.0, a function that is not inlined and returns `M α`, a pair, an `Option` or a boxed sum
   allocates that result. Lean's published plan puts stack-allocated objects in design until early 2027. So
   for at least the coming months, a hot path in this engine has to be written so that its functions return a
   scalar, one object, or the machine state, or are inlined. That is a rule about style. Its price is proofs: a
   path rewritten this way needs a refinement theorem against the readable definition.
5. **Memory management is not the whole gap.** On the corpus BubblePopJS executes 4 to 21 times the
   instructions of QuickJS, which also counts references and uses `malloc`. Removing every allocation would
   give at most 1.4 to 2.3 times. The larger part is elsewhere: string property keys, generic paths where a
   fast path would do, and a few algorithms that are wrong for their size (typed-array element access is the
   clearest: 21 times QuickJS on pako).

What would make it fundamental, and was looked for: a cost per reference-count operation that cannot be
avoided (not found: 2.6 to 5.8 operations per allocation, non-atomic, no multi-threaded object seen in the
profiles); a floor on allocation cost (the floor measured is about 10 ns for a cell with the runtime inlined,
against 1.3 ns for no cell: high, but paid only where the source asks for a cell); an inability to keep scalars
unboxed (not so: `UInt64`, `Float`, `USize` and small `Nat` are machine values in locals, parameters, results
and structure fields).

## What was measured

- **Machine**: Apple M1, 8 cores, macOS, shared with other agents (load 5 to 17). Times are cycle counts
  (`/usr/bin/time -l`, "cycles elapsed") scaled to milliseconds at 3.2 GHz, least of 7 interleaved runs under
  the timing lock; instruction counts ("instructions retired") are given beside them because they do not move
  with load. A difference under 3% in cycles is noise here; instruction counts repeat to 0.1%.
- **Program**: `leanjs`, from the C that Lean 4.33.1 generated for main `4dc55d8a0` with the import fix of
  [PR 554](https://github.com/danbri/factoidal-core/pull/554) (70 modules, 41.7 MB of C). Every variant below is
  compiled from the same C files, so results differ only by the build.
- **Workloads**: the library corpus of [`realworld.py`](../../labs/demos/foafnaut/bubblepop_perf/realworld.py)
  (lodash, acorn, pako, marked, immutable) at size 4N; 2,351 Test262 files of six directories that no profile
  was trained on; offline page snapshots of the real-page survey (development test inputs only).
- **Instruments**: the counting build and the sample-profile reader of
  [`bubblepop_perf/alloc/`](../../labs/demos/foafnaut/bubblepop_perf/alloc/); two new microbenchmarks,
  [`alloc/IdiomBench.lean`](../../labs/demos/foafnaut/bubblepop_perf/alloc/IdiomBench.lean) and
  [`alloc/SteerBench.lean`](../../labs/demos/foafnaut/bubblepop_perf/alloc/SteerBench.lean) (single files with
  no import: `lean -c` then `leanc -O3 -DNDEBUG`, as [`lean/run.sh`](../../labs/demos/foafnaut/bubblepop_perf/lean/run.sh) does).
- **One mix to know about**: the `leanjs` variants with link-time optimisation used a runtime `object.cpp`
  compiled without `LEAN_USE_GMP` beside the toolchain's GNU MP units. Their outputs and Test262 verdicts are
  the same as the others'. The engine library build has no such mix (its runtime is the one without GNU MP).

## A. Idioms: where the cells come from

The engine's monad is `JSM H = EStateM Abrupt (HeapOf H)`: one layer, state and exception together. A call of a
function of type `M α` that the compiler does not inline returns `EStateM.Result.ok a s`, a constructor with two
fields: one allocation of 24 bytes (32 in the allocator's size class), and one free when the caller has taken
it apart. A `Float` result is boxed first (16 bytes more). `Option α` and `α × β` results are cells in the same
way; `Option UInt64` is two.

`IdiomBench.lean` times one call of a small helper (an array read and a test that can fail) written eleven
ways, 30 million iterations, native arm64. "Lake build" is the toolchain's `clang -O3` and runtime as shipped;
"LTO" is the build of section D (runtime inlined, no heartbeat count):

| The helper returns | Lake build, ns a call | LTO, ns a call | Allocations a call |
|---|---|---|---|
| `M UInt64` (`EStateM`), not inlined | 18.1 | 11.1 | 1 |
| `M UInt64`, `@[inline]` | 1.3 | 1.6 | 0 |
| `Option UInt64` | 20.4 | 13.7 | 2 |
| `UInt64 × Bool` | 20.5 | 13.5 | 1 or 2 |
| `UInt64 × St` (state passing) | 21.1 | 12.3 | 1 |
| `UInt64`, a sentinel for failure | 2.8 | 1.5 | 0 |
| `St → St`, the result in a scalar field of the state, failure in a flag | 5.7 | 3.8 | 0 |
| `ST σ UInt64`, state in an `ST.Ref` | 7.4 | 10.4 | 0 (the reference read is a call into the runtime) |
| `EST ε σ UInt64`, state in an `ST.Ref` | 21.1 | 12.6 | 1 |
| a boxed sum (`V.num x`) | 13.7 | 8.0 | 1 |
| `Float` | 1.4 | 1.5 | 0 |

What follows from it:

- **A result cell costs 10 to 18 ns; no cell costs 1.3 to 6 ns.** The interpreter makes one for almost every
  helper call. This is finding 5 of the heap record, priced.
- **`@[inline]` on a small monadic helper whose caller matches at once is free and needs no proof.** The
  definition does not change. It was the whole of steps 6 and 7 of the heap plan.
- **Result in the state.** A helper of type `HeapOf H → HeapOf H` that leaves its answer in a scalar field (or
  one object field) of the record and its failure in a flag allocates nothing and updates the record in place
  when it is the only reference. This is the provable form for the hot helpers of the register machine: it is
  a pure function, and it equals the monadic one by a simulation lemma.
- **`ST` with a reference removes the cell but not the cost**, and its operations are opaque to proofs. `EST`
  (exceptions) still allocates. Moving the heap into an `ST.Ref` is not a gain here.
- **`Option` and pairs from lookups** (`Env.slot?`, `arrayIndex?`, `AssocList.get?`, `takeAt`) are cells unless
  the function is inlined into a caller that matches at once. A sentinel result (`Env.slotN` returns `names.size`
  for "absent") is the pattern already used in `Value.lean`; it costs nothing.
- **A record update inlined into a large function can lose its in-place update**: the compiler passes the
  record's fields through a join point and builds a new record (the heap record's step 1a). The update as a
  small function of its own, not inlined, keeps it. The undo log of
  [PR 550](https://github.com/danbri/factoidal-core/pull/550) is a second case to watch (section F).
- **Reference counting is not the problem.** 2.6 to 5.8 count operations per allocation, all on the
  single-threaded path: the sample profiles show no `lean_inc_ref_cold` and no `lean_mark_mt`; the slow path seen
  is `lean_dec_ref_cold`, which is the free of a dead cell.

Not done: a full `trace.compiler.ir.result` of the evaluator. The generated C carries the same information
(each allocation site with its constructor shape and line), and the counting build reads it by function.

## B. Data structures and algorithms

Counts on the current tree (run less load; counting build of the same C):

| Workload | allocations | largest sources, share of allocations |
|---|---|---|
| lodash | 11.7 M | `vmLoop` 52.3%, `binop` 7.2%, `looseEq` 5.3%, `toNum` 3.2%, `typeOf` 3.0% |
| immutable | 22.8 M | `vmLoop` 25.3%, `toNum` 11.7%, `setElem` 10.0%, `takeAt` 3.9%, `setOwnData` 3.3% |
| acorn | 22.6 M | hash map lookup (`AssocList.get?`) 13.5%, `vmLoop` 12.5%, `evalExpr` 8.5%, `setOwnData` 4.5%, a `for` range loop 4.4% |
| marked | 5.2 M | the `for` loop over start positions of the regular expression matcher 61.3%, `matchNode` 5.5% |
| pako | 59.0 M | `toNum` 15.7%, `arrayIndex?` 13.9%, `vmLoop` 7.7%, `evalExpr` 7.5%, `typedWriteV` 6.0%, `AssocList.get?` 5.9%, `setOwnData` 4.9%, `liveLen` 4.6% |

Defects of representation and algorithm that these show, largest first:

1. **Property keys are strings, so an element access parses its index.** `a[i]` turns `i` into a string and
   `arrayIndex?` parses it back: three allocations a call (two iterator records of `String.all` and
   `String.foldl`, and the `Option`), 8.2 M calls on pako. The atoms of the heap plan remove the round trip;
   until then a numeric key path that never makes the string would.
2. **Typed-array elements are read and written through lists and powers.** `typedRead` builds
   `List.range w` and adds `byte * 2 ^ (8 * k)` for each element; `typedBytes` does the reverse with a list, an
   array map and `Int` powers. Only the one-byte types have a direct path (a `@[csimp]` pair, proved). On pako
   these two, with `Int.pow` and `List.range`, own 12.8% of all samples in memory management alone
   (308 of 2,404), and pako is 21 times QuickJS. Direct paths for the two- and four-byte integer types are the
   same kind of theorem as the existing one. A draft was written and not landed: its proof did not check
   within the time available (see "Not done").
3. **`toNum` returns `M Float`** for a value that is nearly always `.num x`: a boxed float and a result cell for
   nothing (4.6 M of each on pako). A pure first case in the caller (`match v with | .num x => x | _ => ← toNum n v`)
   removes both and is equal by one `rfl`-style lemma.
4. **Hash map lookups return `Option`** (`AssocList.get?`, 13.5% of acorn's allocations): the global and
   property index lookups. An inlined lookup, or `getD` with a sentinel, removes the cell.
5. **The matcher makes one state record per start position** (marked). A first-character test before the
   record is made is step 6's remaining item.

List against array and persistent against in-place: no list on a hot path was found beyond the typed-array
code above and the frame list (`List VFrame`) the heap plan already replaces. The arrays of the heap are updated
in place (copied bytes are 0.6 to 4.9% of allocated bytes).

## C. Fast paths

Share of each workload's allocations that a pure first case in front of the generic path would remove, with no
change of representation, from the counts above:

| Fast path | lodash | immutable | acorn | pako | Theorem |
|---|---|---|---|---|---|
| number operand: `toNum`, bit operators, `binop` on two numbers | 10% | 14% | 3% | 18% | fast = monadic, by cases on the value |
| element access with a number key on an array or typed array (no string, no `arrayIndex?`) | 1% | 4% | 1% | 19% | equal to the string-key path: `arrayIndex? (toString i) = some i` for `i < 2^32 - 1` |
| typed-array read and write of 2 and 4 bytes | 0 | 0 | 0 | 6%, and the `Int` powers | `@[csimp]`, as the one-byte case |
| booleans as constants, `typeof` strings as constants | 13% | 3% | 3% | 1% | `rfl` |
| compiled call without tuples and `Option` (step 1b of the heap plan) | 27% | 11% | 7% | 3% | step equations of `vmLoop` |

These are the "guarded fast path" form that the tier-1 work on
[PR 557](https://github.com/danbri/factoidal-core/pull/557) has now proved for the evaluator; they belong in
that structure and are listed for it, not started here, because both edit `Interp.lean`.

## D. Build of the extracted C

All rows: the same generated C. Geometric mean over the five libraries of cycles, least of 7, against the
build that Lake makes (`clang -O3`, toolchain runtime); instruction counts in the second column.

| Build | time | instructions | binary |
|---|---|---|---|
| Lake's build (the `leanjs` that Test262 runs use) | 1.000 | 1.000 | 11.42 MB |
| no heartbeat count at an allocation (what the native engine library has had since `fd53dac77`) | 0.941 | 0.953 | 11.39 MB |
| `-O2` in place of `-O3` | within noise of the row above | 0.956 | 11.42 MB |
| Apple clang 17 in place of the toolchain's clang 22 | 0.973 | 0.957 | 11.53 MB |
| ThinLTO over the engine's C only | not timed | 0.939 | 11.37 MB |
| mimalloc's default heap in a fixed thread slot on macOS (`MI_TLS_SLOT`) | 0.939 | 0.923 | 11.53 MB |
| **ThinLTO over the engine's C and the runtime's `object.cpp`, `alloc.cpp` and mimalloc**, with the thread slot | **0.845** | 0.842 | 12.08 MB |
| the same without the thread slot | not timed | 0.85 (lodash 0.850 against 0.841) | 12.08 MB |
| profile-guided (`-fprofile-generate`, trained on the corpus at size N) | 0.856 | 0.899 | 14.68 MB |
| profile-guided, trained on lodash, acorn and marked only | 0.885 (pako 0.948, immutable 0.831) | 0.907 | 14.58 MB |
| **profile-guided and ThinLTO with the runtime** | **0.782** | 0.763 | 12.20 MB |

Held out, 2,351 Test262 files that no profile saw, against the no-heartbeat build; the five verdict lists are
byte-identical:

| Build | time | instructions |
|---|---|---|
| ThinLTO with the runtime, no thread slot | 0.881 | 0.892 |
| ThinLTO with the runtime, thread slot | 0.774 | 0.884 |
| profile-guided | 0.899 | 0.977 |
| profile-guided and ThinLTO with the runtime | 0.803 | 0.869 |

Findings:

- **Link-time optimisation with the runtime is the large, general gain: 10 to 20% of time, 11 to 16% of
  instructions, on every workload including the held-out one.** What it does: `lean_alloc_small_object` calls
  `mi_malloc_small` in the runtime, and a dying cell goes through `lean_dec_ref_cold`, `lean_del_core` and
  `mi_free`; each is a call across a library boundary in the shipped build, and inlined here. Over the
  engine's C alone it gives 1.5%: the gain is the boundary to the runtime.
- **A profile adds 6 to 8% on what it was trained on and little on what it was not** (Test262: 1.5% of
  instructions). It needs a training run inside the build. Second, after link-time optimisation, and only
  with page workloads in the training set.
- **`-O2` and `-O3` do not differ.** The compiler is not the lever; the boundary is.
- **The thread-local lookup on macOS** is real (`mi_malloc_small` reaches its heap through `_tlv_get_addr`) and
  worth 3% of instructions. The fixed slot (number 89, the one mimalloc uses when it replaces `malloc`) is
  shared by the whole process: two copies of mimalloc that both used it would corrupt each other. It is
  measured here and **not proposed** for a library that is loaded into another program. Lean 4.35 puts the
  heap and the heartbeat in one thread-local variable upstream, which halves the lookups without a slot.
- **No object takes the multi-threaded reference-count path** in these runs. The engine library with Lean
  tasks was not profiled for this.
- **`LEAN_SMALL_ALLOCATOR` no longer exists** in 4.33.1; the choice is mimalloc or `malloc`.

### Native engine library and pages

The native engine of main `6be1f3e3b` (640 C files) was built twice from the same generated C: as
`build-web-render.sh` builds it, and with Apple clang, `-flto=thin`, and the three runtime units as bitcode (no
thread slot). Library size 72.83 MB to 76.46 MB (+5.0%).

Offline snapshots of four pages, the host of the same commit, two interleaved rounds under the timing lock on a
loaded machine. The lower of the two runs is given, with the other in brackets; the spread between two runs of
one engine is up to 40% on some rows, so read the direction, not the digits:

| Page | first layout ms, as built | with LTO | longest script turn ms, as built | with LTO | first frame s, as built | with LTO |
|---|---|---|---|---|---|---|
| Wikipedia "This Is Spinal Tap" | 877 (1,221) | 770 (974) | 198 (214) | 164 (176) | 7.0 (8.3) | 5.7 (8.3) |
| MDN `display` | 1,782 (1,801) | 1,565 (1,570) | 3,669 (4,004) | 3,476 (3,559) | 11.1 (11.4) | 10.3 (10.6) |
| jvns.ca | 814 (1,210) | 730 (806) | 1,329 (1,565) | 1,073 (1,276) | 5.1 (6.3) | 4.4 (5.0) |
| Hacker News | 108 (115) | 93 (99) | 92 (102) | 95 (96) | 1.4 (1.5) | 1.4 (1.4) |

First layout falls by 10 to 14% on all four pages (layout is Lean code that allocates in the same way), the
longest script turn by 5 to 19% on three and not on Hacker News. Every run ended normally with both engines;
peak memory is unchanged (within 3%). Scroll latency did not move outside its spread.

### Wasm

`leanjs` was built as a wasm32 program from the same C (Emscripten, the runtime objects of the Wasm engine's
cache) and run under Node 22. **No timing here is a result.**

- `-O2` against `-O3` for the engine's C (the Wasm engine compiles at `-O2`): 1.009, within noise; size
  9,145,578 against 9,169,593 bytes (gzip 1,899,186 against 1,904,770).
- No heartbeat count (the Wasm engine still has the call; only the native engine dropped it): the module is
  2% smaller (8,979,072 bytes; gzip 1,893,413). Its time could not be read: under Node the build started
  0.4 s later than the others on every run and ran the workloads faster by about the same amount, and the
  cause was not found. On native the same change is 5 to 6%.
- Link-time optimisation with the runtime units as bitcode: built (9,538,003 bytes), and **it crashed on
  pako** (`unreachable`). The runtime units were recompiled here without the build's own checks of its
  wasm32 patches, so this says nothing about the method; it is not a result and is not proposed.
- `wasm-opt` levels and `-Oz` were not tried.

A Wasm measurement needs timing inside the engine (the command line's `Date.now` is fixed at 0) or the Hub's
own page timings; lever 9 below is where to start.

## E. Other compilers, settings and extractors

Checked against the 4.33.1 toolchain's own sources and the release notes of 4.22 to 4.36.0 (published
2026-11-16):

- **The code generator in 4.33.1 is already the new one** (default since 4.22; the port of the last passes was
  finished in 4.30). There is no older or newer generator to switch to.
- **Results**: `ST` and `BaseIO` results are unboxed since 4.26 (the world token is erased). `EST`, `EIO`, `IO`
  and `EStateM` results are cells in every release. The `@[unbox]` attribute exists and has no effect.
  Reset and reuse, and borrow inference, are on by default; `@&` on a parameter is honoured since 4.30.
- **Options** (`compiler.small`, `compiler.maxRecInline`, `compiler.maxRecSpecialize`, `compiler.reuse`,
  `compiler.extract_closed`): none changes how a result is returned. `compiler.small` (default 1) makes the
  compiler inline larger helpers without an attribute; not tried, because it changes code size everywhere.
- **Newer releases that touch this cost**: 4.35 compiles mimalloc into the runtime with one thread-local
  access per allocation and rounds a two-field cell to 24 bytes, not 32; 4.34 moves to mimalloc 3. Neither
  removes a cell. An upgrade is worth measuring for the allocation path alone, after the JIT proofs are
  stable on 4.33.1.
- **Planned upstream**: stack-allocated objects and uniqueness annotations are in design, with
  implementation "at the beginning of 2027". Nothing to wait for this year.
- **Other backends**: the LLVM emitter is still in the tree, untested upstream, and off in release binaries;
  when last measured it was slower than C. No maintained extractor to Rust, OCaml, JavaScript or Wasm exists
  for current Lean. C through Emscripten is the only route to Wasm. None is an option for this codebase.
- **Hand-written `@[extern]` C for hot primitives**: possible (a C function for the typed-array byte access
  or the allocation of a number box), and it moves that code out of what is proved: the theorems are about
  the Lean definition, and the C would be trusted to equal it. The same gains are available inside Lean
  (`@[csimp]` with a proof, as `typedReadByteFast`), so this is not recommended while that holds. The hygiene
  ratchet counts `extern`, so it would also show as a rise.

### Checked on the installed toolchains (4.33.1 and 4.35.0)

- **Which pipeline the build uses.** In both toolchains `Lean.Compiler.compile` (`Lean/Compiler/Main.lean`)
  calls `LCNF.main` and nothing else; no option of `Lean/Compiler/Options.lean` or `LCNF/ConfigOptions.lean`
  selects another pipeline (the fourteen `compiler.*` options are the same in both). `Lean/Compiler/Old.lean`
  is a file of naming helpers for auxiliary declarations, not a second compiler. The generated C agrees: of
  the 5,657 functions of `Interp.c`, 2,435 are specialisations (`_spec__`) and 2,727 have reduced arity
  (`___redArg`), and it has 212 extracted closed terms.
- **4.35.0 against 4.33.1 on the same file** (`IdiomBench.lean`, each with its own clang and runtime, as
  shipped; the engine itself was not built on 4.35.0, which needs every proof rechecked):

  | The helper returns | 4.33.1, ns a call | 4.35.0, ns a call |
  |---|---|---|
  | `M UInt64`, not inlined | 14.3 | 13.0 |
  | `Option UInt64` | 16.3 | 10.9 |
  | `UInt64 × Bool` | 16.8 | 14.6 |
  | a boxed sum (`V.num x`) | 10.1 | 7.7 |
  | `M UInt64`, inlined | 1.1 | 1.0 |
  | `St → St` | 4.6 | 5.0 |
  | `ST σ UInt64` with a reference | 5.6 | 8.9 |

  The generated C has the same 40 allocation sites in both, and the same size (133 kB). So **4.35.0 makes a
  cell 9 to 33% cheaper and removes none**. (This run was on a quieter machine than the table of section A;
  compare columns, not tables.)
- **The LLVM emitter is not usable**: `lean --features` prints `[]` in both toolchains and `lean -b FILE.bc`
  stops with an assertion in `library/llvm.cpp`. The release binaries are built without it, for native and so
  for wasm32 too. Using it would mean building Lean from source with LLVM enabled, on an emitter that upstream
  does not test.
- **What can be steered per definition**, timed in
  [`alloc/SteerBench.lean`](../../labs/demos/foafnaut/bubblepop_perf/alloc/SteerBench.lean) on 4.33.1 (4.35.0
  gives the same picture):

  | Case | ns a call |
  |---|---|
  | a structure parameter, borrow inferred | 2.8 |
  | the same with `@&` | 2.6 |
  | a fold that takes a function, called with a closure, not specialised | 215 |
  | the same with `@[specialize]` | 3.0 |
  | a constant table inside a function, extracted as a closed term (the default) | 2.2 |
  | the same with `compiler.extract_closed false` | 32.8 |

  - **`@&` changes nothing where inference already borrows**, which is the common case; it matters only for a
    parameter the compiler would otherwise take as owned.
  - **A higher-order helper that is not specialised is 70 times slower** (a closure, boxed arguments and an
    indirect call per element). The engine's sources under `JS/` have 41 `@[inline]`, 10 `@[noinline]`,
    2 `@&` and no `@[specialize]`; `Interp.c` still has 301 indirect applications and 56 sites that allocate a
    closure, and closures are 1.8 to 4.9% of allocations on acorn, immutable, marked and pako. Each such site
    on a hot path is a candidate (lever 6b).
  - **Closed-term extraction is on and should stay on.**

## F. Size and cost of the undo log (PR 550)

Asked by the coordinator: `leanjs` grew 11.42 to 11.87 MB between `4dc55d8a0` and `8d3af851b`.

- **Attribution by generated C** (the C of main `6be1f3e3b` against `4dc55d8a0`, the 70 modules of `leanjs`):
  `Interp.c` +1,253,820 bytes (+8.3%), `Value.c` +81,818, `Clone.c` +32,876, `Modules.c` +15,012, all others
  unchanged. Two commits changed those sources: `fa6f92ff5` (the undo log) and `cd474766b` (scripts of another
  origin run from the engine's copy; one native and one answer constructor). The growth is the undo log's:
  `HeapOf.noteObj` and `noteEnv` are `@[inline]`, and their `{ h with undoObjs := {} }` is expanded at 144
  sites in `Interp.c` (the calls of `UndoLog.noteAt`). At each site the heap's cold record is taken apart into
  its 18 fields and passed through a join point; the number of sites that can build a cold record went from 45
  to 189.
- **Does a page that never makes a synchronous request pay?** Read from the generated C, not timed: with the
  log off a write does two loads (`undoObjs`, its `base`), one comparison of small numbers, and in `updateObj`
  one more count increment; the new sites that build a cold record are the fall-back of an in-place update
  (taken only when the record is shared). No new allocation was found on the off path of `updateObj`,
  `setOwnData`, `assignLocal` or `pushEnv`.
- **Not measured: run time before and after.** No `leanjs` with the undo log could be made consistent from the
  build outputs on this machine (the only tree with it had old C for `Main`, `Tests` and `Test262`, which
  crash against the new heap record), and a Lean build needs 1.7 GB of disk when 2 GiB were free. To settle
  it: `lake build leanjs` on main and on `4dc55d8a0`+PR 554, then the interleaved corpus timing of this record
  (instruction counts are enough), and `opcount.py` for `o.x = i` and a closure-variable write.
- **To take the size back**: make `noteObj` and `noteEnv` small functions that are not inlined and take and
  return the heap (`HeapOf H → Nat → HeapOf H` after the array is put back), or test `base` inline and call a
  non-inlined function only when the log is on. The second keeps the off path at one comparison and removes
  the 144 expansions. The theorems `UndoLog.restore_of_inv` and its lemmas are about `noteAt` and do not
  change.

## Ranked levers

Gains are of script time on the library corpus unless said; "measured" rows were measured here.

| # | Lever | Gain | Status | Proof cost |
|---|---|---|---|---|
| 1 | Link-time optimisation of the engine's C with the runtime's `object.cpp`, `alloc.cpp`, mimalloc | 10 to 20% (measured, native; held-out 12 to 23%) | build setting; see "Landed and proposed" | none: no definition changes |
| 2 | Compiled call path of the register machine without tuples, `Option` and boxed return (heap plan step 1b) | lodash 6 to 7%, others 2 to 3% (estimated in the heap record) | open, in `Interp.lean` | step lemmas of `vmLoop` |
| 3 | Pure first case for numbers: `toNum`, bit operators, `binop` | pako 6%, immutable 3 to 4% (estimated from 14 to 18% of allocations) | open | one lemma a function, by cases |
| 4 | Element access by number: no string key, no `arrayIndex?`; 2- and 4-byte typed-array paths | pako 10 to 15% (12.8% of samples are in the typed-array code's memory management alone) | open; draft of the typed-array part not landed | `@[csimp]` pair; a lemma on `arrayIndex? (toString i)` |
| 5 | Profile-guided build | 6 to 8% more on trained workloads, about 1.5% held out (measured) | not proposed yet: needs a training step in the build and page workloads in it | none |
| 6 | `@[inline]` on small lookups that return `Option` (`AssocList.get?` callers, `Env.slot?`, `takeAt` users) | acorn up to 4% (13.5% of its allocations) | open | none where only an attribute is added |
| 6b | `@[specialize]` on the higher-order helpers behind the 301 indirect applications of `Interp.c`, where a profile shows one hot | not measured in the engine; 70 times on the microbenchmark | open | none: an attribute |
| 7 | Booleans and `typeof` strings as constants (heap plan step 2) | lodash 2.5% | open | `rfl` |
| 8 | Lean 4.35 or later (one thread-local access an allocation, 24-byte cells) | a cell 9 to 33% cheaper on the microbenchmark; engine not built on it | later | re-check of every proof on the new toolchain |
| 9 | Heartbeat off in the Wasm engine and in `leanjs` (native engine has it) | 5 to 6% native (measured); Wasm: see section D | small build change | none |
| 10 | Thread slot for mimalloc on macOS | 3% of instructions (measured) | not proposed: process-wide slot | none |

Not levers: `-O2` against `-O3`; another C compiler; another Lean backend; `ST.Ref` for the heap.

## Landed and proposed

**In the pull request with this record** (no Lean definition changes, so no theorem is owed):

- `FOAFNAUT_NATIVE_LTO=1` for `build-web-render.sh --native` on macOS, **off by default**: the engine's C is
  compiled by the system clang with `leanc`'s own flags and `-flto=thin`, and `build-leanrt-no-gmp.sh` (with
  `LEANRT_LTO=1`) adds `object.cpp`, `alloc.cpp` and mimalloc as bitcode to `libleanrt-no-gmp-lto.a`. Checked
  here: the runtime script in both modes (the default archive has the same members as before); the library
  linked from the 640 engine C files of main `6be1f3e3b` with exactly these flags and that archive
  (76,462,232 bytes, no GNU MP symbol, `binary-budget.py check` passes its link-content test); the four pages
  above. **Not run here: `build-web-render.sh` end to end with the flag** (it needs the Lean build of the
  engine, 1.7 GB, with 2 to 4 GiB free on the machine). It is off by default for that reason and two more:
  the library grows 5.0%, above the 2% tolerance of the size gate, so turning it on is a recorded budget
  change; and the release lane's compiler is not the one measured.
- The microbenchmarks `IdiomBench.lean` and `SteerBench.lean`, and this record.

**Proposed next, in this order:**

1. One Mac release-lane build with `FOAFNAUT_NATIVE_LTO=1`, the survey on it, then the flag on by default with
   a budget for the larger library.
2. The same for Linux (`leanc -flto=thin` with the toolchain's `lld`; the runtime units are already rebuilt
   there) and for `leanjs`, measured in CI, where Test262 runs spend their time.
3. Heartbeat off in the Wasm engine, with a timing that can be read (lever 9).
4. Levers 2 to 4, 6 and 7 inside the guarded fast-path structure of the tier-1 work, each with its lemma.
5. The undo log's write test as a non-inlined function (section F), with a before and after of `leanjs`.

## Not done, and why

- **Wider typed-array fast paths with their `@[csimp]` theorems** were drafted (if-chains over the type tag,
  proofs by `simp only` with `List.range` unfolded). The check of the proof, on a copy outside the evaluator,
  did not finish in 5 minutes twice; the cause was not found. Not landed. The definitions and the proof
  attempt are in a comment on the tracking issue for whoever takes lever 4.
- **Run time of the undo log** (section F).
- **Linux**: every timing here is macOS arm64. The Linux engine already has initial-exec thread-local storage;
  lever 1 should carry over (the calls it removes are the same), unmeasured.
- **The native engine with Lean tasks** was not checked for multi-threaded reference counts.
- **`compiler.small`** and other compiler options were read, not tried: each needs a full build of the
  evaluator.
