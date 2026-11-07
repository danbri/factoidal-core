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
| `Proofs.*` | refinement theorems |
| `SpecTest` | `lake exe wasmvm-spectest` |
| `Bench` | `lake exe wasmvm-bench` |

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
  stack), `outOfFuel Suspended`, `hostCall HostFuncId (Array Value) Suspended`.
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
  slot (`Slots` in `Exec/Code.lean`). i32 and f32 are zero-extended, f64 and i64 use
  the whole slot, a reference is an address with all-ones for null. v128 (SIMD,
  later) takes two slots. A `FloatArray` read through `Float.ofBits` measured faster
  but is wrong: see "Measurements".
- **Locals** are slots of the operand stack at the frame base (`fp + i`).
- **Frames**: an `Array Frame` (return pc, return code, frame base, instance). Wasm calls
  never become Lean calls, so the C stack does not grow with Wasm call depth.
- **Memory**: `ByteArray`, little-endian loads and stores assembled from bytes, one
  bounds check per access (`ea + width ≤ size`).
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
bulk memory, reference types and multi-memory. Later, with room left in `Syntax`
(`ValType.v128`, `HeapType` with type indices, `Op` constructors): SIMD, GC, exceptions,
memory64, tail calls, threads.

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
65353 commands): **pass 35085, fail 0, not run 30268.**

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

## Next

1. Speed: slots as `UInt64` reads with `USize` indices and proofs, or registers for the
   top of stack; superinstructions (`local.get; i32.const; i32.add`); a `br_if` that
   fuses the compare. Target: 10x.
2. Refinement: the rest of the integer table (div, rem with `binop_trap`, shifts,
   compares through `Step_pure.relop`), then `Run.step_refines` with the abstraction to
   `Spec.config`.
3. Proposals in the order of the planned uses: exceptions (tags; needed by the
   factoidal core wasm and by Emscripten C++ code), tail calls, `call_ref`, SIMD
   (HarfBuzz builds use it when enabled), memory64, GC.
4. Parallel decode of the code section; parallel compile by chunks of equal byte size.
5. The JSON op form for the hosts, and the Emscripten build of the engine.
