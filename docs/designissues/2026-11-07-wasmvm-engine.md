# WasmVM: the executable WebAssembly engine in Lean

Issue: https://github.com/danbri/factoidal/issues/1244 (WebAssembly VM in Lean).
Owner, 2026-11-07, verbatim: "Take extra care on APIs and on any opportunities for
parallelism and for theorem-backed speedups." and, on a fast form proved equal to the
spec form: "yes v much this".

This record says how the executable engine is built: the API, the run-time
representation, the proof plan, the speed-ups that a theorem pays for, and where work
runs in parallel. The reference semantics is the SpecTec-generated layer
`L4Factoidal.WasmVM.Spec` (record: `2026-11-07-wasmvm-spec-layer.md`). Numbers are in
"Measurements" at the end; each has the command that makes it.

First uses: HarfBuzz compiled to Wasm (font shaping), then media decoders and the
OpenType `Wasm` table. Page JavaScript goes to VerifiedJS (CLAUDE.md, 2026-11-07), so
a JS engine on this VM is not planned.

## Modules

All under `formal/lean4/L4Factoidal/WasmVM/`, library `WasmVM`. They import Lean core
only (the spec-test runner also imports `Lean.Data.Json`).

| Module | Contents |
|---|---|
| `Syntax` | types, the flat instruction set, the module record |
| `Binary.Leb` | LEB128: spec form, fast form, `@[csimp]` proof |
| `Binary.Decode` | `ByteArray → Except DecodeError Module` |
| `Numerics` | i32/i64 on `UInt32`/`UInt64`, f32/f64 on `Float32`/`Float` |
| `Valid` | validator and compiler to flat code, in one pass |
| `Exec.Code` | the flat operation type `Op` |
| `Exec.Store` | store, instances, values |
| `Exec.Run` | the interpreter loop |
| `Exec.Instantiate` | linking, segment initialisation, start function |
| `Api` | the public surface |
| `Proofs.*` | refinement theorems (`Proofs.Proposals`: exceptions and tail calls) |
| `SpecTest` | `lake exe wasmvm-spectest` |
| `Tests.Memory`, `Tests.Proposals` | run after the spec tests (legacy exceptions, 10^6 tail calls, `try_table` cost) |
| `Bench` | `lake exe wasmvm-bench` (`Bench.Core`: `l4core FILE` loads `l4factoidal.wasm`) |

## API

```lean
decode      : ByteArray → Except DecodeError Module
validate    : Module → Except ValidationError ValidModule
instantiate : Store → ValidModule → Array ExternVal → Except LinkError (Store × InstAddr) -- then `start`
invoke      : Store → FuncAddr → Array Value → Limits → Store × Outcome
resume      : Store → Suspended → Array Value → Limits → Store × Outcome
```

- **`ValidModule`** has a private constructor. Only `validate` makes one, so a value
  of the type is the certificate that the module passed validation. It holds the
  module, the compiled code of each function and the maximum operand-stack height of
  each function. The proof obligation `validate m = .ok v → Spec.Module_ok m` is
  stated on this function (see "Proof plan").
- **Code is compiled once per module, at validation**, not once per instance. The
  compiled code names module-local indices; an instance maps them to store addresses
  through its own arrays. N instances of HarfBuzz share one compiled copy.
- **Effect model: the engine is pure and resumable.** `invoke` is a function of the
  store. It never calls the host. When the code calls an imported host function, the
  run stops with `Outcome.hostCall f args k`. The host does its work in any monad it
  likes (`IO`, a test monad, a browser event loop), reads or writes memory through
  `Store.readMem`/`Store.writeMem` (bounds-checked, `Except`), and calls
  `resume store k results`. Fuel works the same way: `Outcome.outOfFuel k` is
  resumable. So a host function cannot change the store during a step, a host error is
  a value (`Outcome.hostError`), and one driver loop (`Api.runIO`) serves every host.
- **Outcomes**: `values (Array Value)`, `trap (TrapReason)`, `exhausted` (call depth or
  stack), `outOfFuel Suspended`, `hostCall HostFuncId (Array Value) Suspended`,
  `exception tag (Array Value)` (an exception no handler caught: its tag address and
  payload).
- **Limits**: fuel (instructions), maximum call depth, maximum memory pages (applied
  under the module's own maximum at `memory.grow`).
- **Host ABI for later** (Deno, browser, Mac app; not wired now): the same JSON op
  style as the other factoidal ops. `wasm.load {bytes:base64} → {module:id}`,
  `wasm.instantiate {module, imports:{name:{kind,…}}} → {instance:id}`,
  `wasm.invoke {instance, export, args:[{type,value}], fuel} → {result | trap | suspended:id}`,
  `wasm.resume {suspended, results}`, `wasm.memory.read/write {instance, mem, offset, bytes}`.
  Values use the spec-test JSON form (`{"type":"i32","value":"42"}`), so the runner
  and the hosts share one codec.

## WASI (later; no code now)

WASI is a layer of Lean host functions over the import API, not part of the engine.
Order: a Preview 1 subset first (`fd_write` to a debug sink, `proc_exit`,
`clock_time_get`, `random_get`, `args_*`, `environ_*`), deny by default; files and
sockets only by an explicit grant through the engine's network policy; then the
Component Model and WASI 0.2. The API carries this as follows:

- Imports are resolved by (module name, field name) against a host-function set that
  is a Lean value (`HostSet`), chosen by the embedder. An import that the set does not
  name fails at link time. So "no capability given, no access" is a statement about
  `instantiate` and the set, which can be proved.
- A host function runs between steps, on the suspended store: it reads and writes the
  instance's memory through `Store.readMem`/`Store.writeMem`, bounds-checked.
- A host function answers `resume` with `HostResult.values`, `.trap msg` or
  `.exit status`; `.exit` ends the run with `Outcome.exit status` (for `proc_exit`).

## Run-time representation

- **Flat code.** Each function body becomes an `Array Op`. Blocks, loops and `if` are
  gone: every branch op carries its target pc, the number of values it keeps and the
  operand-stack height (relative to the frame base) to cut back to. These are computed
  by the validator, which knows the static stack height at every instruction. This is
  the side table of Wizard (Titzer, 2022) folded into the op, as wasm3 does.
- **Operand stack**: one `ByteArray` for the whole run, 8 little-endian bytes per
  slot (`Slots` in `Exec/Code.lean`), read and written as one 8-byte access at a
  `USize` slot index (see "Speed pass"). i32 and f32 are zero-extended, f64 and i64 use
  the whole slot, a reference is an address with all-ones for null. v128 (SIMD,
  later) takes two slots. A `FloatArray` read through `Float.ofBits` measured faster
  but is wrong: see "Measurements".
- **Locals** are slots of the operand stack at the frame base (`fp + i`).
- **Registers**: `run` takes the stack, `sp`, `fp`, `pc` (`USize`), the code, the
  instance and the frames as separate arguments. `Machine` is built only when a run
  stops.
- **Frames**: an `Array Frame` (return pc, return code, frame base, instance). Wasm calls
  never become Lean calls, so the C stack does not grow with Wasm call depth.
- **Memory**: the `LinearMemory` interface (see "Linear memory"); backend A is a
  `ByteArray`. One bounds check per access (`ea + width ≤ size`), in the loop; the
  backend gets the proof.
- **Tables**: `Array UInt64` of references. **Globals**: one store-wide `FloatArray`.
- **Uniqueness.** In-place update needs reference count 1. The loop holds the operand
  stack, the frames and the store as separate arguments, never inside a value that is
  also kept elsewhere. Store fields are changed with `Array.modify`, which takes the
  element out before it changes it. The API takes the store by value; a caller that
  keeps an old store pays one copy, and the design says so.
- **Totality.** The loop is one tail-recursive function on fuel (`match fuel with
  | 0 => outOfFuel | n+1 => …`), so it is total, compiles to a C loop and passes
  `tools/lean-tail-recursion-audit.py`. The decoder loops are bounded by the input size.
  No `partial def`.

## Proof plan

Named theorems, in the order they will be proved:

1. `Leb.decodeU_eq_fast` (`@[csimp]`): the spec-shaped LEB128 decoder equals the fast
   one. Done in stage 1.
2. `Numerics.i32_add_refines` and the rest of the integer table: the `UInt32`/`UInt64`
   operation, read through `toNat`, equals the spec's Nat definition (`Spec.iadd_ 32`,
   `isub_`, `imul_`, `idiv_`, …). Started in stage 1.
3. `Decode.decode_sound`: `decode b = .ok m → Spec.Binary.Module b (toSpec m)` against the
   spec's binary grammar (when the spec layer has the binary grammar as a relation).
4. `Valid.validate_sound`: `validate m = .ok v → Spec.Module_ok (toSpec m)`; and
   `maxHeight_sound`: running a function never puts more than `v.maxHeight f` slots
   on its frame.
5. `Run.step_refines`: for every fast state `s` reached from a valid module, one step of
   the loop from `s` to `s'` gives `Spec.Steps (abs s) (abs s')`. The abstraction `abs`
   rebuilds the spec configuration: the operand stack below `sp` becomes the value
   prefix of the instruction list, the frames become nested `FRAME_`/`LABEL_`
   contexts, and the pc becomes the rest of the structured body. First cases: the
   numeric instructions through `Spec.Step_pure` (`binop_val`, `binop_trap`, `unop_val`,
   `testop`, `relop`).
6. `@[csimp]` equalities for hot pieces where the spec shape is a function: LEB128,
   branch-target lookup (a linear scan over the structured body equals the
   precomputed target), the integer operations.

## Theorem-backed speed-ups

- **No tag checks on values.** Validation proves each operand's type, so slots are
  untagged bits and `i32.add` reads two slots without a check. Soundness of this is
  `validate_sound` plus type preservation.
- **No stack-overflow check inside a function.** Validation gives the maximum height
  `h(f)`. The only check is at the call: `sp + h(f) ≤ capacity`, else grow or report
  exhaustion. `maxHeight_sound` justifies the skip.
- **Branch targets in range.** The compiler makes every target `< code.size`. The
  invariant `CodeOk code` (every successor pc is in range) lets the loop index the code
  with `code[pc]'h` and no bounds check, with `pc : Fin code.size` (stage 2).
- **Memory bounds.** One check per access, on `ea + width`; the 8 byte reads after it
  use proved indices.
- **`@[csimp]`** swaps of spec-shaped reference functions (LEB128 first).
- **In-place updates** of stack, memory, tables and globals, by keeping references
  unique (above).
- Later: superinstructions (`local.get; i32.const; i32.add`) proved equal to the
  sequence; constant-time `br_table` by array index.

## Parallelism

Lean gives `Task.spawn` (pure) and `IO.asTask` (effects) on a thread pool. On native both
run in parallel. In the Emscripten build without pthreads, tasks run one after the other,
so every parallel path must also be correct and not slower when run serially; each
parallel path below has a `parallel := false` switch.

| Where | Safe because | Worth it when |
|---|---|---|
| Decoding code-section entries | each entry is length-prefixed and independent | large modules (HarfBuzz: thousands of functions) |
| Validating and compiling function bodies | each body needs only the module context, which is read-only | same |
| Spec-test files | each file has its own store | always (about 150 files) |
| Independent instances | no shared store | host-side batch work (shaping many runs) |

One instance's run stays single-threaded (until the threads proposal, later). The
parallel decode and validate give the same result as the serial ones because they map
a pure function over an array; the theorem is `Array.map` equals the task-based map
(`Task.get` of `Task.spawn` is the function value).

## Scope

Stage 1: Wasm 1.0 (MVP) plus multi-value, sign extension, non-trapping float-to-int,
bulk memory, reference types and multi-memory. Stage 2 (2026-11-08): exception handling
(3.0 `try_table`, `throw`, `throw_ref`, `exnref`, tags; and the legacy `try`, `catch`,
`catch_all`, `delegate`, `rethrow` that Emscripten emits), tail calls and typed function
references. Later, with room left in `Syntax` (`ValType.v128`, `HeapType` with type
indices, `Op` constructors): SIMD, GC, memory64, threads.

Floating point, where the host C library can differ: `Float.sqrt`/`Float32.sqrt`
(correctly rounded by IEEE 754 in every C library we use), `floor`/`ceil`/`trunc`
(exact), `nearest` is our own code (round half to even, sign of zero kept), not C
`round`. min, max, copysign, abs and neg work on bits or with explicit NaN and zero
cases. NaN results of arithmetic come from the hardware: an arithmetic NaN on ARM64 and
x86-64, which the spec allows; a canonical NaN result for non-NaN inputs. i64 to f32
uses the direct C conversion (one rounding), not a path through f64.

## Measurements

Filled in by each stage; the commands are in `L4Factoidal/WasmVM/Bench.lean`.

All numbers: Apple M1 (8 cores, 4 performance), native build, 2026-11-07, with other
sessions' builds running on the machine (load average about 2.5). Commands run in
`formal/lean4`.

### Spec tests

`lake exe wasmvm-spectest` over `third_party/wasm-spec/test/core-json` (259 files,
65353 commands). 2026-11-08, after exceptions, tail calls and typed function
references: **pass 35501, fail 0, not run 29852.** By part:

| Part | pass | not run | why not run |
|---|---|---|---|
| core | 27988 | 757 | text-format modules, GC types (`rec`, `sub`), SIMD in core files |
| exceptions | 98 | 12 | `cast` uses GC instructions; 3 `tag` modules use `rec` groups; 2 text-format modules |
| multi-memory | 912 | 0 | |
| memory64 directory | 6367 | 2352 | 64-bit address type |
| simd | 122 | 25868 | SIMD |
| gc | 14 | 784 | GC types |
| relaxed-simd | 0 | 79 | proposal not done |

By proposal (files, before and after):

| Area | files | before: pass, fail, not run | after: pass, fail, not run |
|---|---|---|---|
| exception handling | `tag`, `throw`, `throw_ref`, `try_table`, `cast` | 0, 0, 110 | 98, 0, 12 |
| tail calls | `return_call`, `return_call_indirect`, `return_call_ref` | 1, 0, 186 | 176, 0, 11 (text format) |
| typed function references | `call_ref`, `br_on_null`, `br_on_non_null`, `ref_as_non_null` | 0, 0, 64 | 64, 0, 0 |
| files that needed these for some modules | `imports`, `exports`, `ref_null`, `unreached-valid`, `unreached-invalid` | 385, 0, 98 | 464, 0, 19 |

The suite has no legacy `try`; `Tests/Proposals.lean` has 13 legacy cases with the
results Node 22 gives for the same binary (all pass), and runs after the spec tests.

Before (2026-11-07): pass 35085, fail 0, not run 30268:

| Part | pass | not run | why not run |
|---|---|---|---|
| core (2.0 + 3.0 reference types, tail and GC files) | 27612 | 1075 | text-format modules, tail calls, `call_ref`, tags |
| multi-memory | 912 | 0 | |
| memory64 directory | 6367 | 2352 | 64-bit address type |
| simd | 122 | 25868 | SIMD |
| gc | 14 | 784 | GC types |
| exceptions, relaxed-simd | 0 | 189 | proposals not done |

Files in parallel (one `IO.asTask` each): 1.1 s; `--serial`: 2.15 s.

### Interpreter

`lake exe wasmvm-bench engine 10000000` (the module is in `Bench/Engine.lean`):

| Function | instructions | time | million instructions per second |
|---|---|---|---|
| `sum` loop, 10^7 iterations | 140 000 008 | 3.6 s | 38 |
| `memsum` (a store and a load per iteration) | 240 000 004 | 8.0 s | 29 |
| `fib(30)` recursive calls | 28 271 637 | 0.78 s | 36 |

This is about 25 ns per instruction: slow next to wasm3 (about 1 ns). The main cost is
the slot form (8 checked byte reads and writes per slot). Next steps are in "Next".

### Decoder and validator

`lake exe wasmvm-bench decode FILE`:

| Module | size | functions | decode | validate and compile, serial | parallel |
|---|---|---|---|---|---|
| a Rust `wasm-bindgen` module (`kgx/web_bg.wasm`) | 3.7 MB | 4482 | 270 ms | 207 ms | 174 ms |
| `wikilambda` (Emscripten) | 28.4 MB | 19365 | 1113 ms | 807 ms | 655 ms |

**Parallel decode of the code section** (`Binary.decodeParallel`, 2026-11-08). A scan
of the size fields gives every entry's start; entries are decoded in chunks of about
1/64 of the section (at least 64 KiB), one `Task.spawn` per chunk; results are taken
in order, the first error in entry order wins, and from the first entry the scan
cannot place, the serial loop takes over, so the result and the error are those of
`decode`. Checked on every module of the spec tests: `wasmvm-spectest` decodes each
module both ways and fails when the functions or the error message differ (pass
35085, fail 0). `wikilambda` (28.4 MB, 19365 functions, `wasmvm-bench decode`):

| decode | serial | code entries in parallel |
|---|---|---|
| ms | 1079 to 1100 | 714 to 716 |

1.5 times faster, so it is kept. `decode` stays serial (the reference); embedders of
large modules call `decodeParallel`. The rest of the time is serial: the other
sections, and `b.extract 0 e`, which copies the module up to the end of each section
so that a reader cannot see past it (a cost to remove later with an end bound).

The factoidal core `l4factoidal.wasm` (31 MB) is not decoded yet: it has a tag section
(exceptions). Parallel compilation of bodies gains only 1.2x; decode is not parallel yet.

### Operand-stack representation

`lake exe wasmvm-bench repr`, `Bench/Repr.lean`. Same program in each: two pushes, two reads, one add,
one write, 20 million times.

| Representation | ns per iteration |
|---|---|
| `FloatArray`, slots as bits, loop arguments (WRONG for NaN patterns) | 17 |
| `FloatArray` inside a structure updated with `{ m with … }` | 17 |
| `Array UInt64` (boxed slots) | 24 |
| `ByteArray`, 8 bytes per slot (used) | 25 |
| `ByteArray`, one check and proved byte indices | 36 |

A machine structure costs nothing over separate arguments: Lean reuses the unique
structure in place. The `FloatArray` form is NOT used. Lean 4.33 models `Float` with all
NaNs equal, and the compiled `Float.ofBits` turns every NaN bit pattern into the
canonical NaN. An i64 such as -1 (all ones) is a NaN pattern, so it did not survive a
round trip through the stack: the spec test `fac` (`fac-opt`) failed with
0x7f38000000000000. The stack is the `ByteArray` form (25 ns). The same fact means a
float operation sees a NaN operand as the canonical NaN; the result is still an
arithmetic NaN, which the spec allows, and `abs`, `neg`, `copysign`, loads, stores and
reinterpretations work on bits and never call `Float.ofBits`.

## Linear memory

Issue https://github.com/danbri/factoidal/issues/1289 (memory backends), section 1.
Code: `Exec/Memory.lean`.

- **Interface.** `class LinearMemory (M)`: `size`, `create n max`, `grow`, `load8/16/32/64`,
  `store8/16/32/64` (little-endian), `copyWithin`, `copyInto`, `fill`, `writeBytes`
  (data segments, `memory.init`, host writes), `readBytes` (host reads). Each load and
  store takes a proof `ea + w ≤ size m`; the loop makes the one check.
- **No dispatch per access.** The store is `StoreOf M`; `run`, `invoke`, `resume`,
  `instantiateRun` and the drivers take `[LinearMemory M]` and are `@[specialize]`.
  In the emitted C for the benchmark (`Bench/Engine.c`) the loop is the copy
  `Run.run_at_..._spec`, and a store is the inline 4-byte `memcpy` of backend A, with
  no closure call. Measured: `memsum` 162 million instructions per second with the
  interface, against 29 before the speed pass (the slot change is in the same step;
  the interface itself showed no cost: `memsum` and `sum` moved by the same factor).
- **Backend A** `ByteMem` (a `ByteArray`) is the reference model. `size` is
  `data.usize.toNat`, so the proof from the loop's check gives the `USize` offsets.
- **Backend B** (page-aligned host memory in a C shim, for Metal): not built. The
  interface allows it: nothing outside `ByteMem` assumes a `ByteArray`; `create` gets
  the most bytes the memory may have, so B can reserve that range and commit pages at
  `grow`; `Tests/Memory.lean` has `differential M N`, which runs one export on stores
  over two backends and compares results and memory bytes (today `ByteMem` against
  `ByteMem`).
- **Ownership rule.** A memory value is held by exactly one `MemInst` in one store.
  The loop holds the store with reference count 1, so a store changes the memory in
  place. A host function gets the store (in `resume`'s caller), not the memory; it
  reads and writes through `Store.readMem`/`Store.writeMem` and gives the store back
  through `resume`. A caller that keeps an old store pays one copy of each memory it
  then writes. In engine code, change a memory only inside `st.mems.modify` with the
  `MemInst` taken apart first (`fun ⟨data, max⟩ => ..`): with `{ mi with data := .. }`
  under a dependent `if`, the compiler kept a second reference to the memory and every
  store copied it (found by the benchmark: `memsum` 11 million instructions per second
  with 64 KiB of memory).
- **Test.** `Tests/Memory.lean`, run at the end of `lake exe wasmvm-spectest` and by
  `lake exe wasmvm-bench memtest`: 10^3, then 10^6 stores into 64 KiB and into 64 MiB
  of memory; the 64 MiB run must take at most 4 times the 64 KiB run plus 200 ms.
  Result: 10^6 stores, 145 ms and 145 ms, pass. Red check with the copying form of
  `storeMem`: 10^3 stores, 1 ms against 2337 ms, FAIL.

## Speed pass

All on the Apple M1 above, `lake exe wasmvm-bench engine` (10^7 iterations; `fib(30)`),
million Wasm instructions per second. Spec tests after each row: pass 35085, fail 0.

| Change | sum | memsum | fib | Justifying theorem |
|---|---|---|---|---|
| before (stage 1) | 39 | 30 | 37 | |
| slots: one `USize` check per access, 8-byte load in Lean, 8-byte store in inline C; registers as `run` arguments; memory interface | 191 | 164 | 156 | `Slots.slot_ok`, `Bytes.byte_ok`, `Bytes.nat_ok`, `Run.pc_ok` |
| 9 fused ops (below) | 257 | 202 | 168 | `Proofs.Fuse.fuse_agrees` (from `run_parts`, `run_fused`, `run_fusedJump`, `fuseAt_sound`, `fuse_sound`) |
| `NumOp.evalBin` `@[inline]` (it was a C call with its own `switch` in each binary op) | 270 to 296 | 221 | 174 | none needed (same function) |
| `Simple.exec` takes the slots and `sp` as two arguments (with one `SP` argument the compiler allocated and freed a pair in `lUn`, 5% of samples in `mi_free`) | 336 to 360 | 211 | 175 | none needed (`Simple.execAll` is unchanged up to structure eta; the `Proofs/Fuse.lean` proofs still check) |

Tried and dropped: `NumOp.evalUn` `@[inline]` (sum 300, memsum 190, fib 150: the float
cases made the loop larger and slower).

Speed-up over stage 1: sum 8.6 to 9.2 times, memsum 7 times, fib 4.7 times. The 10x
target is not reached; see "Next". Instruction counts are the same as before fusion
(140 000 008, 240 000 004, 28 271 637), so a fused op takes the fuel of its parts.
Runs vary by about 10% (other sessions build on the machine).

**Slot form, measured first** (`lake exe wasmvm-bench repr`, ns per iteration of
2 pushes, 2 reads, 1 add, 1 write):

| Representation | ns |
|---|---|
| `ByteArray`, eight checked byte reads and writes (stage 1) | 25 |
| `Array UInt64` (Lean boxes each `UInt64`: an allocation per write) | 25 |
| `FloatArray` (WRONG for NaN patterns) | 17 |
| F: `ByteArray`, `USize` slot index, one check, `uget`/`uset` with proved indices | 8.5 |
| X: as F, the store as one inline-C `memcpy` | 3.3 |

- Lean core 4.33 has no 8-byte load or store on `ByteArray` (`ByteArray.toUInt64LE!`
  needs an array of size 8). In form F the eight `uget`s after one check compile to ONE
  64-bit load (`ldr x`, checked in the ARM64 code), so loads stay in Lean. Eight
  `uset`s stay eight byte stores, each after its own uniqueness check (a byte store
  may alias the reference count), and a following 8-byte load of the same slot cannot
  take its value from them. So stores are `Bytes.st16/st32/st64`: a Lean reference
  body (the `uset` chain, which proofs use) with an `@[extern c inline]` body, one
  `memcpy` after the same uniqueness check as `lean_byte_array_uset`. This C is
  trusted to equal the Lean body (byte order: `__builtin_bswap` on a big-endian host).
  The Lean interpreter cannot run it, so no `#eval`/`#guard` may call a store.
- Split typed stacks: not measured. Lean has no unboxed array of `UInt32` or
  `UInt64`; a `FloatArray` for floats has the NaN defect above.
- **Checks removed, and the theorem for each.** Per slot access, 8 bounds checks
  became 1: `Slots.slot_ok` (from `i < s.usize / 8`, the 8 bytes at `8i` are under
  `s.usize`) and `Bytes.byte_ok` (each `o + k`, `k < w`, does not wrap and is under
  `s.size`). Per memory access, `w` checks became 1, the loop's `ea + w ≤ size`:
  `Bytes.nat_ok` (the `Nat` address is the `USize` offset). The code fetch is
  `code.uget pc` after `pc < code.usize`: `Run.pc_ok`. Remaining: one compare per
  slot access. Removing it needs `maxHeight_sound` and a typing invariant carried by
  `run` (next steps).

## Fused ops

`lake exe wasmvm-bench profile DIR` (`Bench/Profile.lean`) counts op pairs and triples:
executed in the benchmarks (one instruction per `run` call), and present in the
compiled code of the 1687 spec-test modules. Before fusion, the benchmarks ran mostly
`local.get; const` (4929 per 3 runs), `local.get; local.get` (4001), `i32.add;
local.set` (3000), `local.get; const; i32.add`, `const; i32.add; local.set`, a compare
then `jumpIf`, and `const; i32.and` before a load. The spec-test modules are mostly
test scaffolding (`const; return`, `const; load i64`), so they did not choose the set.

The fused ops (`Exec/Code.lean`; `op` is a numeric op that cannot trap):

| Op | Parts |
|---|---|
| `llBin x y op` | `local.get x; local.get y; op` |
| `lcBin x c op` | `local.get x; const c; op` |
| `cBin c op` | `const c; op` |
| `lUn x op` | `local.get x; op` (unary) |
| `binSet op z` | `op; local.set z` |
| `lcBinSet x c op z` | `local.get x; const c; op; local.set z` |
| `llBinJump x y op t z` | `local.get x; local.get y; op; jumpIf t` (`jumpUnless` when `z`) |
| `lcBinJump x c op t z` | `local.get x; const c; op; jumpIf/jumpUnless t` |
| `binJump op t z` | `op; jumpIf/jumpUnless t` |

- `fuse` runs after the validator's compiler. It replaces the op at the start of a
  group and leaves the parts after it, so the code keeps its length and a branch into
  the middle of a group finds the original ops. Longest match first.
- `run` executes a fused op as `Simple.exec` of its parts in order, each part written
  to the slots as the single op would (so the states are equal, not only equal below
  `sp`). It takes the fuel of all its parts; with less fuel it runs only its first
  part and goes to `pc + 1`.
- **The general lemma** is `Proofs.Fuse.run_parts`: straight-line ops in the code from
  `pc`, run one at a time, give `Simple.execAll` of them and `run` at `pc + k` with `k`
  less fuel. Each fusion's small proof is its case in `run_fused`/`run_fusedJump`
  (unfold `run` once; the definition is its expansion). `fused_agrees` puts these
  together; `fuseAt_sound` and `fuse_sound` show the pass only makes well-formed fused
  ops where the original code holds the parts; `fuse_agrees` is the result for
  compiled code (side condition: the code has fewer than `USize.size` ops).
  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Not proved: whole runs of `fuse c` and `c` agree (induction on fuel; it also needs
  every function in the store fused the same way).

## The dispatch loop in C

Checked in `.lake/build/ir/L4Factoidal/WasmVM/Bench/Engine.c`, the copy of `run`
specialised for `ByteMem` (`Run.run_at_..._spec`), after the changes above:

- One C function, one `switch (lean_obj_tag(op))` (ARM64: a jump table, `br x9`), and
  a `goto _start` for each tail call. No call per instruction except the slow paths.
- No allocation per instruction: `lean_alloc_ctor` is only on the exits (the result
  tuple and `Machine`) and in `call` (the `Frame`). Before: the `Machine` structure was
  reset and reused at each step, with an increment and decrement of each of its seven
  fields.
- `UInt64` slot values and `sp`, `fp`, `pc` are unboxed (`uint64_t`, `size_t`).
- Per instruction, two reference-count operations remain on the code: `lean_array_uget`
  increments the `Op` it reads and the case decrements it after reading the fields
  (Lean has no borrowed array read). A `Nat` field of an `Op` is read with
  `lean_usize_of_nat`. Removing these needs the code in an unboxed array (bytecode in a
  `ByteArray`): "Next".
- The fuel is a `Nat` (two inline `Nat` operations per step); it is what makes `run`
  structurally recursive.
- Before `NumOp.evalBin` was `@[inline]`, every binary op called it (a second
  `switch` behind a call).

## Exception handling

Issue 1244, 2026-11-08. Code: `Valid.lean` (compile), `Exec/Code.lean` (`Handler`,
`CatchTarget`), `Exec/Run.lean` (`raise`, `unwind`, `cold`). Both forms are read: the
3.0 form (`try_table` with `catch`, `catch_ref`, `catch_all`, `catch_all_ref`;
`throw`, `throw_ref`; `exnref`) and the legacy form (`try`, `catch`, `catch_all`,
`delegate`, `rethrow`), which Emscripten emits for C++ with `-fwasm-exceptions` and
which `l4factoidal.wasm` uses (419 `try` blocks; `wasm-tools validate` needs its
`legacy_exceptions` feature).

**Store.** Tags are store entries (`ExcStore.tags`, the canonical function type of
each; a tag import is matched by type like a function import). An exception is an
`ExnInst` (tag address, payload slots) in `ExcStore.exns`; an `exnref` slot holds its
index. Exceptions are never freed, so the store grows by one entry per `throw` (a
program that throws in a loop grows without bound; a later collector, or reuse once no
`exnref` can reach an entry, is open).

**Handler tables, like the branch side table.** The validator gives each function a
table of entries, one per `try_table` or legacy `try`:

- `start`, `stop`: the range of ops of the body (pcs of the flat code; `fuse` keeps
  every pc, so the range stays exact);
- `catches`: for each clause, the tag (module index, or none for catch-all), the pc to
  go to, the operand height (relative to `fp`) where its values go, and which values:
  the payload, the exception reference after it (`catch_ref`, `catch_all_ref`), or the
  exception reference before it (legacy `catch`, see below);
- `next`: the entry to search when no clause matches: the enclosing `try`, or for a
  legacy `delegate l` the handler that applies at label `l`.

Entries are in the order their `try` starts, and ranges nest, so the innermost entry
that holds a pc is the last one that holds it. The table is stored as one extra op,
`Op.handlers`, after the final `return_` of the function, where no pc reaches; only
functions with a `try` have it. So a `Frame` needs no new field: the code array a
frame already holds carries its table (`handlersOf code`).

**Unwinding** (`Run.unwind`). To raise exception `e` at pc `p`: take the innermost
entry holding `p`, test its clauses in order (`catchFor`: the first catch-all, or the
first clause whose tag address is `e`'s), then the entries that `next` names. When one
matches, write its values at `fp + height` and go to its pc. When none matches, pop a
frame and search the caller at its call site (the frame's return pc minus 1). With no
frame left, the run stops with `Event.exception e`, and the API gives
`Outcome.exception tag payload`. Traps are not exceptions: `try_table` does not catch
them (spec test `unreachable-not-caught`).

**Legacy `catch` and `rethrow`.** A legacy clause needs the caught exception later
(`rethrow l` throws it again). The validator keeps it on the operand stack, in a slot
below the clause's frame: at a legacy `catch`, the stack is cut to the `try`'s height,
the exception reference goes in the next slot, then the payload. Branches to the
`try`'s label still cut to the `try`'s height (`Ctrl.base`, the branch height, is
the height without the slot); the end of the clause moves its results down over the
slot (a `br` to the next pc). `rethrow l` reads the slot at `fp + base` of the clause
`l` names. So no hidden locals and no change to `nLocals`.

**What it costs when nothing is thrown: nothing.** `try_table` and `try` compile to no
op: the code inside is the code of a plain `block`. `Tests/Proposals.lean`
(`tryIsFree`) checks this: a 10^7-iteration loop inside `try_table` compiles to the
same ops as inside a `block` (plus the table after the end), and runs the same
140 000 008 instructions in the same time (382 ms and 382 ms). There is no handler
stack to push or pop on `try`, call or return. A `throw` pays a scan of the handler
tables of the frames it unwinds (linear in the entries of each function).

**Spec layer.** `Spec/Wasm30.lean` (generated from WebAssembly/spec f3268fa9) has the
3.0 rules: `Step.throw`, `Step_read.throw_ref_*` (one per clause kind, `_next`,
`_empty`, `_label`, `_frame`, `_null`), `Step_read.try_table`, the `HANDLER_`
administrative instruction and its `Step_pure` rules. It has no legacy rules (the
legacy form is not in 3.0), so the legacy cases are tested, not proved. The generated
`throw_ref_handler_next` binds its `x` and `val_lst` apart from the clause it skips (two
binders named `x`, two named `val_lst`), so as generated it lets any clause be skipped;
the theorems below use it only for clauses whose tag does not match. Reported to the
spec-layer owners in this record, not fixed here (`WasmVM/Spec*` is theirs).

## Tail calls

`return_call f`, `return_call_indirect t x`, `return_call_ref t`
(`Run.enterTail`). The callee's arguments, the top `nParams` slots, move down to the
caller's `fp`; the callee's locals are set up there; the run goes on with the callee's
code and the SAME frame stack and `fp`. The frame stack never grows, and the operand
stack needs only `fp + maxHeight(callee)` slots. A tail call to a host function is an
ordinary host call: the validator emits `return_ k` after every tail call op, which
returns the host's results when the run resumes (it is never reached after a Wasm
callee). Inside a `try_table`, a tail call leaves the handler behind, as the spec says
(spec test `return-call-in-try-catch` expects the exception to escape).

Test (`Tests/Proposals.lean`, `tailConstantSpace`): 10^6 tail calls through each of
`return_call`, `return_call_indirect` (two functions in turn) and `return_call_ref`,
with a call-depth limit of 4 and 64 operand slots, give the right sums (93 ms for the
`return_call` loop); the same recursion with `call` stops with "call stack exhausted"
(the control). Theorem: `Proofs.Proposals.cold_tail_frames`.

## Typed function references

`call_ref t` (trap "null function reference" on null), `return_call_ref t`,
`ref.as_non_null` (trap "null reference"), `br_on_null l`, `br_on_non_null l`, and
the typing of `ref.func` as `(ref $t)`. Non-null reference types and non-defaultable
locals were already validated. A reference is a slot (`nullRef` is all ones), so
`br_on_null` and `br_on_non_null` are a compare and a `brMove`.

## Cold ops: new cases outside `run`

The first version put every new op as a case of `run`. The benchmarks fell (best of 5,
interleaved with the build of the commit before, same machine): sum 363 to 265,
memsum 212 to 170, fib 176 to 145 million instructions per second. The C of the hot
cases was unchanged; the larger function made the C compiler's register allocation
worse for all of them. Three steps brought it back, each measured:

| Step | sum | memsum | fib |
|---|---|---|---|
| before these proposals (d750b4515) | 363 | 211 | 176 |
| new ops as cases of `run` | 265 | 170 | 145 |
| new ops in `cold` (a `@[noinline]` function returning `.go` registers or `.stop`), called from one case per op group | 349 | 206 | 165 |
| `cold`'s `RunLimits` borrowed (`@&`): passing it to `cold` had made `run` own it, with a `lean_dec_ref` on every exit | 344 | 205 | 165 |
| `cold` called from ONE `default` case (`| o => cold ..`) instead of four (Lean had copied the call into each `switch` case of the group) | 369 | 215 | 180 |

Tried and not the cause: the order of `Op` constructors (the new ones are now last,
so the old ops keep their numbers), and the two new store fields (now one, `exc`).
Rule for later proposals: a new op that is not hot goes in `cold`, reached by the one
`default` case; only an op that benchmarks show hot becomes a case of `run`.

## Factoidal's own core: `l4factoidal.wasm`

`lake exe wasmvm-bench l4core FILE` (`Bench/Core.lean`), with the 31.3 MB build in
`npm/factoidal-lean/` (as `tools/fetch-builds.sh --set web` installs it):

| Step | result |
|---|---|
| decode (code entries in parallel) | 23300 functions, 18 imports, 1 tag; 1.6 s |
| validate and compile (parallel) | 1.75 s; 419 handler-table entries |
| instantiate with stub imports | ok; memory 256 pages |
| `__wasm_call_ctors` (export `t`) | returns, 4 ms |
| `l4_init` (export `w`) | returns 1 (the Lean runtime and every module initialised) in 18 s |
| `l4_version_c` (export `x`) | `l4factoidal-wasm 0.2.0 (dispatch: RDF parse/serialize, SPARQL query+update, RDFS/OWL-RL closures, RDFC-1.0, CL/IKL)` |

The stubs are the least each import needs (no files, no environment, clock 0;
`emscripten_resize_heap` grows memory 0 through `Store.growMem`). What was missing: the
Lean runtime opens `/dev/urandom` at start; with `openat` answering ENOENT, `l4_init`
returned 0 and printed "uncaught exception: no such file or directory (error code: 44)
file: /dev/urandom". The stub now serves it as a file of constant bytes (a test stub,
not a source of randomness). A real host needs WASI `random_get` or an equivalent.
18 s for `l4_init` is the module initialisers run by the interpreter (it calls
`clock_time_get` 8697 times); not measured further.

## Trusted pieces

Code whose meaning is not checked by Lean's kernel, in the engine and its tools. Lean's
compiler and runtime, and the C library's float functions (see "Scope"), are trusted
as for all compiled Lean.

| Piece | What is trusted | Lean reference | How it is tested |
|---|---|---|---|
| `Exec/Bytes.lean` `Bytes.st16`, `st32`, `st64` (`@[extern c inline]`) | one `memcpy` of 2, 4 or 8 bytes after the uniqueness check that `lean_byte_array_uset` makes (copy when shared), byte swap on a big-endian host | the `uset` chain in each definition's body (the proofs use it) | every slot write and every memory store of the spec tests (35501 pass) and of `memtest`; the Lean interpreter cannot run them, so no `#eval` calls a store |
| `Bench/Repr.lean` `rdX`, `wrX` (`@[extern c inline]`) | an 8-byte load and store; benchmark only, not in the engine | `rdF`, `wrF` | `wasmvm-bench repr` prints each variant's result beside the others; not compared automatically |

Not trusted pieces: `@[csimp]` (`Binary.Leb.uSpec_eq_fast` is a theorem),
`@[noinline]` and `@&` (compiler hints; they do not change what a function computes).
These proposals added no extern.

## Theorems proved (stage 1)

All with axioms `propext`, `Classical.choice`, `Quot.sound` only; no `sorry`.

- `Binary.Leb.uSpec_eq_fast` (`@[csimp]`): the LEB128 grammar `u(N)` written as in the
  spec equals the loop. The decoder calls the grammar form; compiled code runs the
  loop (`tools/lean-csimp-reach.py` passes).
- `Proofs.i32_bin_refines`: the pattern for an i32 binary instruction without a trap.
  If the spec function on the two read constants gives the read result, then one
  engine step (`NumOp.evalBin` on two slots) is a `Spec.Step_pure` step
  (`binop_val`). The read is `absI32`, the low 32 bits of the slot.
- `Proofs.i32_add_refines`, `i32_sub_refines`, `i32_mul_refines`: the pattern applied
  to `Spec.iadd_`, `Spec.isub_`, `Spec.imul_` (Nat definitions, modulo 2^32).

## Theorems proved (stage 2: exceptions and tail calls)

`Proofs/Proposals.lean`. Axioms: `propext`, `Classical.choice`, `Quot.sound` (checked
with `#print axioms`); no `sorry`.

- `throw_reaches_catch`: in any state, `throw x` with its payload, directly inside a
  `HANDLER_` whose first clause is `catch x l`, reaches the payload and `br l` in two
  spec steps (`Step.throw` under `Step.ctxt_handler`, then
  `Step_read.throw_ref_handler_catch`), with the new exception appended to the store.
  `throw_reaches_catch_all`: the same for `catch_all l`.
- `skip_clauses`: clauses whose tag is not the exception's are passed over in order
  (`throw_ref_handler_next`). With the two above this is what the engine's `catchFor`
  does: the first clause whose tag matches, or the first catch-all.
- `return_call_keeps_args`: a tail call from a frame keeps the top `n` values (the
  callee's arguments) and drops the rest of the frame
  (`Step_read.return_call_ref_frame_addr`).
- `cold_tail_frames`: the engine's three tail-call ops go on with the same frame stack
  and the same `fp`.
- `vals_beq_self`, `exninst_beq_self`: the generated `BEq` on spec values and
  exceptions is reflexive (the rules' side conditions need it).

Open obligations (stated, not proved):

- `unwind_refines`: for a fast state reached from a valid module, if `raise` gives
  `.caught` at a clause, the abstraction of the state (proof plan item 5) takes spec
  steps (`throw`, then `throw_ref_label`/`_frame`/`_handler_next` out to the handler,
  then the clause's rule) to the abstraction of the state after `deliver`. It needs
  the abstraction `abs` and a lemma that the innermost handler entry holding the pc is
  the innermost `HANDLER_` around the instruction in the nested body.
- `uncaught_refines`: if `raise` gives `.uncaught`, the spec configuration reaches
  `REF_EXN_ADDR a; THROW_REF` at top level.
- `enterTail_refines`: the slots after `enterTail` are the abstraction of the frame
  that `return_call_ref_frame_addr` then `call_ref_func` give (needs `moveDown` read
  back through `Slots.rd`, which needs `ld64` of `st64` on the Lean reference).
- Legacy exceptions: no spec rules exist to prove against; tested only.

## Next

1. Speed (now 4.7 to 9.2 times stage 1; target 10x): memory 0 held as a loop
   argument during a run (a load now reads `st.mems[inst.mems[0]]` with reference
   counts, a store rebuilds the store record); code as bytecode in a `ByteArray`
   (no reference counts per instruction); the last slot check removed with
   `maxHeight_sound` and a typing invariant carried by `run`; a cheaper `call`/`return`
   (`fib` is call-bound); whole-run equality of fused and unfused code.
2. Refinement: the rest of the integer table (div, rem with `binop_trap`, shifts,
   compares through `Step_pure.relop`), then `Run.step_refines` with the abstraction to
   `Spec.config`.
3. Proposals in the order of the planned uses: SIMD (HarfBuzz builds use it when
   enabled), memory64, GC. Exceptions, tail calls and `call_ref` are done (stage 2).
   A real host for `l4factoidal.wasm` (WASI subset with `random_get`), and why its
   `l4_init` takes 18 s.
4. Parallel compile by chunks of equal byte size; decode without the per-section
   copy (`b.extract 0 e`).
5. The JSON op form for the hosts, and the Emscripten build of the engine.
