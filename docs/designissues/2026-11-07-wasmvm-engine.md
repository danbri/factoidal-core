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

## Run-time representation

- **Flat code.** Each function body becomes an `Array Op`. Blocks, loops and `if` are
  gone: every branch op carries its target pc, the number of values it keeps and the
  operand-stack height (relative to the frame base) to cut back to. These are computed
  by the validator, which knows the static stack height at every instruction. This is
  the side table of Wizard (Titzer, 2022) folded into the op, as wasm3 does.
- **Operand stack**: one `FloatArray` for the whole run, slots read and written as bits
  (`Float.ofBits`/`Float.toBits`, a `memcpy` in C). A `FloatArray` is an unboxed array
  of 64-bit cells; `Array UInt64` boxes each slot. Measured below. i32 and f32 are
  zero-extended, f64 and i64 use the whole slot, a reference is an address with
  all-ones for null. v128 (SIMD, later) takes two slots.
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

**Operand-stack representation** (`lake exe wasmvm-bench`, `Bench/Repr.lean`, Apple
M-series, native, 2026-11-07). Same program in each: two pushes, two reads, one add,
one write, 20 million times.

| Representation | ns per iteration |
|---|---|
| `FloatArray`, slots as bits, loop arguments | 17 |
| `FloatArray` inside a structure updated with `{ m with … }` | 17 |
| `Array UInt64` (boxed slots) | 24 |
| `ByteArray`, 8 bytes per slot | 25 |

So the stack is a `FloatArray`, and a machine structure costs nothing over separate
arguments: Lean reuses the unique structure in place.
