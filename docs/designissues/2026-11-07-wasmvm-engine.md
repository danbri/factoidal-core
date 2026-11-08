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
| `Proofs.*` | refinement theorems (`Proofs.Proposals`: exceptions and tail calls; `Proofs.Refine`, `Proofs.RefineRun`: the state abstraction `R` and `step_refines`) |
| `SpecTest` | `lake exe wasmvm-spectest` |
| `Tests.Memory`, `Tests.Proposals`, `Tests.Wasi` | run after the spec tests (legacy exceptions, 10^6 tail calls, `try_table` cost, WASI) |
| `Wasi`, `WasiIO` | WASI Preview 1 host, deny by default (`Tests.Wasi`: `lake exe wasmvm-bench wasi`) |
| `Bench` | `lake exe wasmvm-bench` (`Bench.Core`: `l4core FILE` loads `l4factoidal.wasm`; `Bench.HarfBuzz`: `harfbuzz WASM`) |

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
- **Host ABI** (Deno, browser, Mac app; a first form is wired in the Foafnaut engine,
  see "In the Foafnaut engine" below; the full form is later): the same JSON op
  style as the other factoidal ops. `wasm.load {bytes:base64} → {module:id}`,
  `wasm.instantiate {module, imports:{name:{kind,…}}} → {instance:id}`,
  `wasm.invoke {instance, export, args:[{type,value}], fuel} → {result | trap | suspended:id}`,
  `wasm.resume {suspended, results}`, `wasm.memory.read/write {instance, mem, offset, bytes}`.
  Values use the spec-test JSON form (`{"type":"i32","value":"42"}`), so the runner
  and the hosts share one codec.

## WASI Preview 1

Issue https://github.com/danbri/factoidal/issues/1289 (section 4), 2026-11-08. Code:
`Wasi.lean` (host, linker, theorems; imports `Api` only), `WasiIO.lean` (capability
sources in `IO`, `load`, `Loaded.run`), `Tests/Wasi.lean`. Reference: the Preview 1
witx in `third_party/wasi/` (WebAssembly/WASI at 9ea0e7534f, the last commit with
`legacy/preview1/witx`). Errno values, the `$fdstat` layout (24 bytes: filetype u8 at
0, flags u16 at 2, rights u64 at 8 and 16), the `$rights` bit of `fd_write` (bit 6)
and the core type of each function (the witx lowering) follow those files.

WASI is a layer of Lean host functions over the import API, not part of the engine.
Files and sockets later only by an explicit grant through the engine's network
policy; then the Component Model and WASI 0.2.

**Linking.** `Wasi.link st md extra` binds every import of the module: a
`wasi_snapshot_preview1` import must be one of the 46 Preview 1 functions (`Fn`) with
its witx type, else a link error; another import must be one the embedder's `extra`
accepts. Each import gets one host function, whose host id is the import's index.
`Wasi.host caps mem bindings extraFn` is the host function set for `runIO`; `mem` is
the store address of the instance's exported `memory`.

**Functions.** All 46 link, so a module that imports more than it uses still runs.

| Functions | Answer |
|---|---|
| `args_get`, `args_sizes_get`, `environ_get`, `environ_sizes_get` | the strings of `Caps.args`, `Caps.env` (UTF-8, NUL after each) |
| `clock_time_get`, `clock_res_get` | `Caps.clock id`, `Caps.clockRes id`; `ENOTCAPABLE` when not granted, `EINVAL` for an id over 3 |
| `random_get` | `Caps.random n`; `ENOTCAPABLE` when not granted; `EFAULT` before the source is asked when the buffer is out of bounds |
| `fd_write` | fd 1 to `Caps.stdout`, fd 2 to `Caps.stderr` (`ENOTCAPABLE` without a sink); fd 0 and fd over 2: `EBADF`. The bytes go to the sink only after every iovec and the result pointer are checked |
| `fd_fdstat_get` | fd 0 to 2: character device, rights `fd_write` for 1 and 2 when their sink is granted, else none; fd over 2: `EBADF` |
| `proc_exit` | `HostResult.exit`, which ends the run with `Outcome.exit` |
| `sched_yield` | success |
| the other 19 `fd_*` (`fd_read`, `fd_seek`, `fd_close`, `fd_prestat_get`, ...) | `EBADF` |
| the 10 `path_*` and 4 `sock_*` | `ENOTCAPABLE` |
| `poll_oneoff`, `proc_raise` | `ENOSYS` |

A pointer out of bounds is `EFAULT`; memory is read and written only through
`Store.readMem`/`Store.writeMem`.

**The capability record** (`Caps m`, built by the embedder in Lean):

| Field | Meaning | `{}` |
|---|---|---|
| `args`, `env` | the strings; `env` entries are `KEY=VALUE` | none |
| `clock : UInt32 → Option (m UInt64)` | the action that reads clock `id`, in ns | no clock |
| `clockRes : UInt32 → Option UInt64` | the stated resolution | none |
| `random : Option (Nat → m ByteArray)` | the random source, a host function | none |
| `stdout`, `stderr : Option (ByteArray → m Unit)` | the sinks: capture or forward | none |

There is no field for files, directories or sockets: this host cannot grant them.
`WasiIO.lean` gives the sources: `systemClock` (realtime from `Std.Time.Timestamp.now`,
monotonic from `IO.monoNanosNow`; the CPU clocks are not granted), `systemRandom`
(`IO.getRandomBytes`), `seededRandom seed` (SplitMix64: deterministic, NOT random;
a test that uses it says so), `capture ref`, `forwardStdout`, `forwardStderr`.

**Deny by default: the theorems** (`Wasi.lean`; axioms `propext`, `Quot.sound`, and
`Classical.choice` for `resolve_wasi` only; no `sorry`):

- `denied_is_pure`: for every function that is not granted (35 of 46,
  `denied_count`), in EVERY monad, for every capability record, memory, argument list
  and store, `call caps mem f args st = pure (st, .values #[.i32 f.denyErrno])`. So
  the call runs no action at all (the host is generic in its monad and has no action
  but those in `Caps`), leaves the store and memory unchanged, and
  `denyErrno_ne_success` says it never answers success.
- `path_open_denied`: `path_open` answers `ENOTCAPABLE`; `fd_read_denied`: `fd_read`
  and `fd_pread` answer `EBADF`; `path_sock_denied`: every `path_*` and `sock_*`
  function is denied with `ENOTCAPABLE`.
- `host_path_open`: in the host function set (`host`), an import bound to `path_open`
  answers `ENOTCAPABLE`, whatever the capabilities and the embedder's other functions.
  `resolve_wasi`: the linker binds a `wasi_snapshot_preview1` import only to the
  Preview 1 function of that name, never to an embedder function.
- `fd_write_needs_sink`, `random_get_needs_source`, `clock_time_get_needs_clock`: with
  the capability not granted, the function never succeeds and is `pure` (no effect).

Stated plainly: no host function of this module can open, read or write a file or a
socket, and none of the 35 denied functions has any effect, in any embedding. Not
proved: that the 11 granted functions write only the memory ranges the witx names
(tested byte by byte, below), and that `link` gives `host` exactly
`md.imports.mapM resolve` (it does by definition; no lemma about `Array.mapM` is
stated).

**Trusted host pieces** (outside Lean's kernel): `IO.getRandomBytes`,
`IO.monoNanosNow`, `Std.Time.Timestamp.now`, and the stdout/stderr writes, used only
through the capability record. `IO.getRandomBytes` is the Lean runtime's call to the
operating system's random source.

**Tests** (`lake exe wasmvm-bench wasi`, and at the end of `wasmvm-spectest`), all pass:

| Part | checks |
|---|---|
| the function table (46 names, round trip, `pathSock` is the `path_`/`sock_` set) | 4 |
| `wasi_all.c` (Emscripten 6.0.8): 45 imports typed by the C compiler from Emscripten's `wasi/api.h` link (an outside check of the witx lowering; `sock_accept` is not in that header), and each answers the expected errno with no capabilities | 46 |
| `wasi_hand.wat`: each granted function with memory checked byte by byte (fixed arguments, environment, clock, and `seededRandom 42`, deterministic); denied functions with all 64 KiB of memory checked unchanged; no-capability answers | 30 |
| a wrong type and a non-Preview 1 name are link errors | 2 |
| `third_party/wasi-testsuite` (WebAssembly/wasi-testsuite, Apache-2.0): 12 AssemblyScript tests (args, environ, fd_write, proc_exit, random_get) and 4 C clock tests, with REAL randomness | 16 |

A red check, run once: with `random := none` in the suite's capabilities, both
`random_get` tests fail (`abort`, exit 255); with one wrong byte in an expected
`$fdstat`, its check fails.

**`l4factoidal.wasm`** imports no `wasi_snapshot_preview1` module: its 18 imports are
Emscripten's own, in module `a` with minified names. Eight are the WASI functions
under Emscripten's names (`_fd_write`, `_fd_read`, `_fd_close`, `_fd_seek`,
`_fd_fdstat_get`, `_environ_get`, `_environ_sizes_get`, `_clock_time_get`) with the
witx types; `Bench/Core.lean` sends these to `Wasi.call` when the type matches. The Lean
runtime opens `/dev/urandom` with `___syscall_openat` and reads it with `_fd_read`:
the bench opens that one path as fd 3 only when `Caps.random` is granted, and serves
fd 3 from `Caps.random` = `systemRandom`. Result (2026-11-08): `l4_init` returns 1
(18.2 s, 8556 clock reads), the version string is printed, and 8 bytes of real
randomness from `IO.getRandomBytes` reached the module. The constant-byte stub is gone.

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
   `testop`, `relop`). Done for a first instruction set on 2026-11-08 as `step_refines`, with
   `abs` a relation `R` (section "Refinement: the state abstraction").
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

## Speed pass 2: real workloads (2026-11-08)

Issues https://github.com/danbri/factoidal/issues/1244 and
https://github.com/danbri/factoidal/issues/1292 (cost theorems as a ratchet). Apple
M1, other sessions building on the machine; every "before/after" pair below was
measured with both binaries on the same quiet machine, runs interleaved. The guest
modules are frozen copies (QuickJS-NG 0.18.0 with the entry point of this commit,
`harfbuzz-wasmvm.wasm`, `vp8-wasmvm.wasm`), so the numbers do not move with the
guests.

| Benchmark | before | after | factor |
|---|---|---|---|
| `engine` sum, M instructions/s | 354 | 359 to 381 | 1.0 to 1.08 |
| `engine` memsum | 203 | 207 to 228 | 1.0 to 1.1 |
| `engine` fib(30) | 178 | 177 | 1.0 |
| HarfBuzz `hbw_shape`, shapes a second (6 cases) | 2399 to 4542 | 3538 to 6196 | 1.36 to 1.48 |
| QuickJS fib(24) | 1252 ms (116 M/s) | 819 ms (177 M/s) | 1.53 |
| QuickJS loop and JSON | 2548 ms (129 M/s) | 1636 ms (201 M/s) | 1.56 |
| VP8 320x180, decode only | 12.7 fps (137 M/s) | 17.9 fps (194 M/s) | 1.41 |
| `l4factoidal.wasm` `l4_init` | 17.9 s | 2.8 s | 6.3 |

The 2x target for QuickJS and VP8 is NOT reached: 1.5x and 1.4x.

### What was slow, found by sampling (`sample PID`), not by guessing

1. **Multi-threaded code objects.** `Wasi.load` (QuickJS, HarfBuzz, the media
   decoders) compiles with `validateParallel`. A `Task`'s result is marked
   multi-threaded with everything it reaches, and the reference count of a
   multi-threaded object changes by atomic operations in
   `lean_inc_ref_cold`/`lean_dec_ref_cold`. `run` changes the count of the op it reads
   at every instruction, so every instruction of these guests went through two
   atomic calls (14% of VP8 samples in `lean_dec_ref_cold`; the benchmark module,
   validated serially, never showed it). `compileAll` now copies what the tasks give
   (`CompiledFunc.fresh`): each op is rebuilt, which allocates a new single-threaded
   object. The compiler turns `match o with | .br t => .br t` back into `o`, so each
   `Nat` field gets `+ freshZero`, a `@[noinline]` zero (and `keepNumOp` for
   `Op.num`). `CompiledFunc.fresh_eq`, `Op.fresh_id`: the copy is the identity.
   Effect: QuickJS 1.40x, VP8 1.28x, HarfBuzz 1.3x.
2. **Host writes copied the whole memory.** `Wasi.answer st (put mem st ..)` and
   `fd_write` kept the old store for their error path, so the write saw a shared store
   and copied the memory. `l4_init` spent 97% of its time in `memmove` (16 MiB at each
   of 8553 `clock_time_get`). `StoreOf.writeMemS` gives the store back on both paths;
   Wasi, the data segments of `instantiate` and the DOM host (`putOut`) use it.
   `writeMem_of_writeMemS`, `writeMemS_false`: `putOut_within` and `call_store` are
   proved as before. `l4_init` 17.9 s to 3.1 s.
3. **Register spills at the dispatch head.** In the ARM64 code of `run`, `pc`, `sp`
   and the slot array were in stack slots, loaded at every instruction: each of the
   dozens of exits built the result (four allocations) inline, and the calls on those
   paths left too few registers for the loop. All exits now call one `@[noinline]
   Run.stop` (the result tuple; the proofs unfold through it). `pc` and the code array
   stay in registers. sum 353 to 379, QuickJS 7%, VP8 7%.

### Fused ops, second set: measured and NOT kept

Profiles of the real workloads (`WASMVM_PROFILE=1`, `Bench/Sample.lean`: 48
instructions recorded one at a time out of every 3048, a fused op counted as its first
part):

| Pair | QuickJS fib(24) | VP8 |
|---|---|---|
| `local.get; const` | 7.1% | 10.0% |
| `local.set; local.get` | 5.4% | 1.1% |
| `local.tee; local.get` | 1.5% | 6.4% |
| `local.tee; const` | 4.1% | 1.5% |
| `local.get; i32.load` (all widths) | 4.2% | 1.5% |
| binary op; `local.tee` | 2.4% | 7.0% |
| compare; `select` | 0 | 4.6% |
| `call` (all) | 0.2% | 0.2% |

QuickJS's own calls are not Wasm calls: its interpreter loop is loads, stores,
`br_table` and local traffic, so calls and returns are not what bounds it.

Ten fused ops were built from this table, each with the existing one-lemma pattern
(`Op.parts`, `fuseAt`, `fusedSimple`, a case of `run`), and `fuseAt_sound`,
`fuse_agrees` and `fused_refines` covered them without new lemmas (the tactic of
`fuseAt_sound` became `repeat' split at h`). Measured, interleaved with the build
without them:

| Variant | sum | fib | QuickJS fib(24) | VP8 fps |
|---|---|---|---|---|
| without | 379 | 178 | 822 ms | 18.0 |
| ten new ops | 274 | 151 | 1031 ms | 14.7 |
| three new ops (`binTee`, `teeGet`, `setGet`) | 290 | 150 | 1119 ms | 13.8 |
| the ten as cases of `run`, but `fuse` never makes them | 269 | 146 | 1271 ms | 11.6 |
| the three as constructors only, no case in `run` | 378 | 179 | 861 ms | 18.0 |

Every case added to `run`, used or not, made every benchmark 20 to 25% slower: the C
compiler spills the loop registers again. Moving the table and bulk-memory ops out of
`run` into `cold` did not give that room back (3% slower). So the fused ops of this
pass are not in the engine. Further fusion needs a smaller loop first (fewer
loop-carried arguments: `lim`, `inst`, `frames` and the code change only at calls and
returns, and could be one object), or fused ops executed by one case.

Also tried and not kept: `enter` as `@[noinline]` (fib 177 to 103).

### Calls and returns

Not changed. `call` allocates one `Frame` and pushes it; `return` pops it. fib(30) is
177 M/s. A cheaper frame (no allocation, return data in the slots) is open; it changes
`run`'s arguments and so the proofs of `RefineRun`, and the profiles show QuickJS and
VP8 do not need it.

### Code as bytes, memory 0 as a loop argument, the last slot check

Not done. Found on the way: the reference-count change on the op read at each
instruction is two plain stores for single-threaded code (item 1 removed the atomic
form). Lean's compiler reads an array element borrowed (`lean_array_uget_borrowed`)
when the array stays alive across the element's uses (`ExplicitRC`, "derived
borrows"); in `run` it does not, because some branches consume the code array while
the op is still in use.

### Native library slower than the Wasm engine

`build-web-render.sh --native` compiled the Lean C with `leanc -O2` and without
`-DNDEBUG`. In `lean.h`, `assert` is active without `NDEBUG` (64 uses, among them
`lean_ctor_get`, `lean_ctor_set`, the array accessors), so every field read of the
interpreter made a check. Lake builds with `-O3 -DNDEBUG`, and the Wasm build of the
same script has `-DNDEBUG`. The native build now uses `-O3 -DNDEBUG`. Not measured in
the native library here (its build needs the full core `.lake`, which this machine had
no disk for); the cause is from the flags and `lean.h`. `build-web-state.sh` has the
same `-O2` without `-DNDEBUG` (not WasmVM; left to its owner).

### Cost model and ratchet

- `Proofs/Cost.lean`: `cost o` is the Wasm instructions an op stands for (its parts,
  else 1); `cost_fused`, `fuseAt_parts`; `fused_charges_parts`: at a pc where `fuse`
  put a fused op, `run` on the fused code with `cost f + n` fuel (one case of the loop)
  and `run` on the original code (one case per part) reach the same registers with
  `n` left. So fusion never changes the instruction count a run reports.
- Left as a statement: a dispatch count of whole runs (`run` with a counter, proved
  equal to `run` on everything but the counter; then dispatches ≤ fuel and
  `= fuel − Σ (cost f − 1)` over the fused ops run).
- `wasmvm-bench engine --check`: each benchmark must run exactly its unfused
  instruction count (sum 140 000 008, memsum 240 000 004, fib 28 271 637) and at least
  a floor of million instructions a second, best of 3: sum 240, memsum 140, fib 110
  (today 359 to 381, 207 to 228, 177 on a quiet machine; 298, 179, 137 while other
  sessions built, so the floors leave about 20% under the loaded figures). Raise a
  floor when the engine gets faster; never lower one without a line here saying why.

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
`throw_ref_handler_next` used to bind its `x` and `val_lst` apart from the clause it
skips, so it let any clause be skipped. Fixed in the generator on 2026-11-08 (spectec
patch 0005, spec-layer record section 9b): the rule now requires that no earlier
`throw_ref` rule applies to the clause.

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
file: /dev/urandom". The first fix served it as a file of constant bytes; since
2026-11-08 the bench uses the WASI host and serves `/dev/urandom` from
`IO.getRandomBytes` ("WASI Preview 1").
18 s for `l4_init` is the module initialisers run by the interpreter (it calls
`clock_time_get` 8697 times); not measured further.

## HarfBuzz in the VM

2026-11-08. HarfBuzz 15.0.0 (MIT, "Old MIT" licence in its `COPYING`;
https://github.com/harfbuzz/harfbuzz, tag `15.0.0`, commit 35f656a1a2) compiled to a
standalone WebAssembly module and shaping text inside WasmVM. Licence policy:
permissive, so it is fine to use; the binary is NOT in the repository. The owner
decides later whether it is vendored or built.

**Build** (`tools/wasmvm/build-harfbuzz.sh [WORKDIR]`, default `~/working/hb-wasm`):
a shallow clone at the pinned tag (the script checks the commit), then Emscripten
6.0.8 (`/opt/homebrew/bin/emcc`) on the amalgamated `src/harfbuzz.cc` and the entry
point `tools/wasmvm/harfbuzz/hb_wasmvm_entry.c`:

    emcc -Oz -std=c++17 -fno-exceptions -fno-rtti -DHB_NO_MT -mno-simd128 -c harfbuzz.cc
    emcc -Oz -mno-simd128 -c hb_wasmvm_entry.c
    emcc -Oz -fno-exceptions -mno-simd128 harfbuzz.o entry.o \
      -sSTANDALONE_WASM --no-entry -sALLOW_MEMORY_GROWTH -sINITIAL_MEMORY=4MB

No threads (`HB_NO_MT`), no C++ exceptions, no SIMD. HarfBuzz's own OpenType shapers
are in the default build; its experimental Wasm shaper (`HB_HAS_WASM`) is off unless a
build defines it, and this one does not.

| Build | size | instructions per call (the 6 strings) | calls per second |
|---|---|---|---|
| `-Oz` (the script's default) | 591 580 bytes | 16 858 to 36 383 | 2631 to 4810 |
| `-O2` (`HB_BOTH=1`) | 916 953 bytes | 11 506 to 26 571 | 3654 to 6824 |

**Imports**: `wasi_snapshot_preview1` `fd_write`, `fd_close`, `fd_seek`,
`environ_sizes_get`, `environ_get` (HarfBuzz reads `HB_OPTIONS` with `getenv`), and
`env.emscripten_notify_memory_growth` (the harness gives a function that does
nothing). Capabilities given: an empty environment and output forwarded; no clock, no
randomness, no files. **Wasm features used** (`wasm-tools print`): sign extension
(`i32.extend8_s`, `i32.extend16_s`, `i64.extend16_s`), non-trapping float-to-int
(`i32/i64.trunc_sat_*`), bulk memory (`memory.copy`, `memory.fill`); no SIMD, no
exceptions, no tail calls. `wasm-tools validate` passes with the MVP plus those and
no SIMD. WasmVM runs all of them, so no instruction is missing.

**Entry point** (`hbw_shape(font, font_len, text, text_len, out, out_cap) -> count`):
UTF-8 text, segment properties guessed (`hb_buffer_guess_segment_properties`, as
`hb-shape` does), font scale = units per em, no features; 6 i32 per glyph (id,
cluster as a UTF-8 byte offset, x and y advance, x and y offset), in font units. The
face and font of the last font pointer are kept, so many strings with one font load
it once. `hbw_alloc`, `hbw_free` give the host memory to write into.

**Run** (`lake exe wasmvm-bench harfbuzz WASM [N]`, `Bench/HarfBuzz.lean`): load
with the WASI host (114 ms for decode, validate, link and instantiate of the `-Oz`
build; 170 ms for `-O2`), `_initialize`, copy the fonts
`third_party/fonts/noto-sans/NotoSans-Regular.ttf` and
`third_party/fonts/noto-sans-armenian/NotoSansArmenian-Regular.ttf` into its memory,
shape, and compare with the native `hb-shape` 15.0.0 (Homebrew; the same release)
run with `--no-glyph-names --utf8-clusters --output-format=json`. Glyph ids, clusters,
advances and offsets:

| Case | Text | Font | Result (WasmVM, glyph@cluster+advance<offset>) | Native |
|---|---|---|---|---|
| ffi ligature | `office` | Noto Sans | 82@0+605, 1656@1+946, 70@4+480, 72@5+564 | same |
| kerning | `AVATAR Wo` | Noto Sans | 36@0+599, 57@1+560, 36@2+569, 55@3+486, 36@4+639, 53@5+622, 3@6+260, 58@7+910, 82@8+605 | same |
| combining marks | `e` U+0301 `a` U+0308 U+0323 | Noto Sans | 171@0+564 (composed é), 759@3+561, 2662@3+0<-279,0> | same |
| stacked marks | `x` U+0301 U+0302 U+0303 | Noto Sans | 91@0+529, 2665@0+0<6,0>, 2667@0+0<-268,229>, 2671@0+0<42,458> | same |
| Armenian | `Բարև ձեզ` | Noto Sans Armenian | 9@0+696, 55@2+920, 87@4+597, 94@6+630, 6@8+260, 71@9+599, 59@11+597, 60@13+600 | same |
| Armenian ligature | U+FB13 ` մն` | Noto Sans Armenian | 102@0+1195, 6@3+260, 102@4+1195 | same |

**6 of 6 agree with native HarfBuzz; 0 differences.** The Lean shaper
(`Rendering/SfntShape.lean`) was not compared in this step; the native tool covers
all six cases.

**Speed** (500 calls per string, Apple M1, other builds running): 2631 to 4810
shaping calls per second for the `-Oz` build, 3654 to 6824 for `-O2`; 80 to 97
million Wasm instructions per second, about half of `fib` in the engine benchmark
(this code is call- and memory-heavy). Native HarfBuzz speed was not measured here.

`WasiIO.Loaded.run` takes the store out of the `Loaded` record before the run: while
the record also held it, the first memory write of a run would copy the whole memory.

## Audio and video decoders in the VM

2026-11-08: libopus, libvorbis and libvpx's VP8 decoder, built to Wasm by
`tools/wasmvm/build-media.sh`, decode in WasmVM; Ogg and WebM are read in Lean
(`L4Factoidal/Media/`). Record: `docs/designissues/2026-11-08-media-wasmvm.md`.

## In the Foafnaut engine: `wasmRun` and `foafnaut:wasm`

WasmVM is compiled into the Foafnaut engine (`labs/demos/foafnaut/WebWasm.lean`, in
`build-web-render.sh`), so the Hub page and the native Foafnaut browser run WebAssembly
with Lean. The host browser's own WebAssembly runs only the Foafnaut engine; it never
runs the user's module. Document ops, in the JSON op form of the other engine ops:

- `wasmInfo`: engine name, ops and limits. Hosts call it first; an engine from before
  these ops answers "unknown document operation" (an error answer of an existing
  export, so an old engine is never asked to run a missing export, issue 1274).
- `wasmRun {wasmBase64, export?, args?, fuel?}`: stage reached (`decode`, `limits`,
  `validate`, `link`, `instantiate`, `start`, `run`), exports with their types, the
  values (spec-test JSON form, with a `shown` text), trap or uncaught exception,
  instructions run (`invokeSteps`, and `resumeSteps`, added to `Api.lean` for runs
  with host calls), nanoseconds and instructions per second, and what the print
  functions printed.
- `wasmSpecSample`: six files of the core suite (fac, i32, i64, conversions, call,
  loop; `WebWasmSample.lean`, made by `web-wasm/make-spec-sample.py`) and the 13 legacy
  exception cases of `Tests.Proposals`.
- `wasmPage {wasmBase64?, url?, export?}`: the page `foafnaut:wasm` as HTML, which the
  engine then lays out like any page. Address bar `:wasm`, or `:wasm NAME.wasm#export`
  for a module of the pages folder (same origin; `pages/hello-wasm.wasm` is one); Hub
  URL `?page=wasm` or `?page=wasm/hello-wasm.wasm#main`.

Imports: a module that imports from `wasi_snapshot_preview1` gets the WASI host
(`WasmVM.Wasi`, deny by default) with only `fd_write` to stdout and stderr granted,
into the page's output, and one program argument; no clock, randomness, environment or
files (`pages/hello-wasi.wasm` is the demo). Any other module gets the `spectest` set
(print functions log their arguments). Everything else is refused at link time. Limits, checked in Lean: module 4 MiB, fuel
10^8 by default and 2*10^9 at most, 512 memory pages (32 MiB), table minimum 10^6,
call depth 10^4, 2^20 operand slots, 10^4 host calls. Times come from the host clock
through `WebWasm.timed`, whose logical model is time 0.

Size, 2026-11-08 (macOS arm64; the baseline is the build of the same renderer sources
without WasmVM): `libweb-render.dylib` 45.71 MB to 48.58 MB (+2.87 MB);
`web-render.wasm` 16.88 MB to 18.32 MB (+1.44 MB). Most of it is the interpreter loop (`Exec/Run`, and
its copy specialised into `WebWasm`), the validator, the decoder and the two test
modules; the spec sample text is 0.39 MB. The native library is over the 2 MB mark, the Wasm engine
under it; kept: the owner wants the engine testable on the Hub.

Results in the engine (`wasmPage`, this Mac): spec sample 1709 pass, 0 fail (both
engines). Million instructions per second, native library / Wasm engine in Deno (V8) /
Wasm engine on the Hub page in Chromium: fib(22) 58 / 119 / 78, sum 90 / 246 / 170,
memsum 69 / 168 / 190, tail calls 59 / 115 / 120. The native library was slower than
the Wasm engine and than `lake exe wasmvm-bench` (sum 369): it was compiled without
`-DNDEBUG`, so `lean.h`'s asserts ran (fixed 2026-11-08, "Speed pass 2").

## QuickJS in WasmVM

2026-11-08. Page scripts run in QuickJS-NG v0.18.0 (MIT;
https://github.com/quickjs-ng/quickjs, the version that
`labs/demos/foafnaut/web-render/script-engine/quickjs.mjs` already pins), compiled to
a standalone WebAssembly module and run by WasmVM. No host JavaScript engine runs the
page script, natively or on the Hub. The DOM stays in Lean: each DOM operation of a
script is one host import that Lean serves on its DOM arena (`DOM.Arena`). The binary
is NOT in the repository.

**Build** (`tools/wasmvm/build-quickjs.sh [WORKDIR]`, default `~/working/qjs-wasm`;
README and licences in `tools/wasmvm/quickjs/README.md`): the release tarball (SHA-256
checked), the four library files (`quickjs.c`, `libregexp.c`, `libunicode.c`,
`dtoa.c`; not `quickjs-libc.c`, so no `std` or `os` module) and the entry point
`tools/wasmvm/quickjs/qjs_wasmvm_entry.c`, with Emscripten 6.0.8:

    emcc -O2 -fno-exceptions -mno-simd128 -D_GNU_SOURCE -funsigned-char -c ...
    emcc -O2 ... -sSTANDALONE_WASM --no-entry -sALLOW_MEMORY_GROWTH -sINITIAL_MEMORY=4MB \
      -sSTACK_SIZE=1MB -sERROR_ON_UNDEFINED_SYMBOLS=0

No threads, no atomics, no SIMD, no exceptions. 1 001 097 bytes; 11 s to build; the
whole work directory (source, objects, Test262 sample) is under 30 MB.

**Imports**: 13 functions of the module `foafnaut_dom` (below);
`wasi_snapshot_preview1` `clock_time_get`, `fd_write`, `fd_seek`, `fd_close`,
`environ_sizes_get`, `environ_get`; `env.emscripten_notify_memory_growth` (does
nothing). WASI capabilities given: a virtual clock only, which the event loop sets.
QuickJS-NG stops at `unreachable` in `JS_NewRuntime` when the clock answers an error
(the same in V8), so a clock must be granted; it is the event loop's clock, so
`Date.now()` is virtual time (0 at the start). No randomness, output, environment or
files.

**Exports** (the ABI is in the comment at the top of the entry point):

- `qjs_new()`: runtime (64 MB heap limit, 768 KB JS stack limit) and context, then a
  JavaScript prelude that builds `document` (`getElementById`, `querySelector` for
  `#id`, `body`, `html`; `createElement`; `documentElement`, `body`, `head`), elements
  (`textContent`, `getAttribute`, `setAttribute`, `hasAttribute`, `id`, `tagName`,
  `appendChild`, `append`, `addEventListener`, `onclick`), `console`, `setTimeout`,
  `setInterval`, `clearTimeout`, `clearInterval`, `queueMicrotask`, `window`, `self`.
  The prelude gets the native functions as an argument; they are not globals.
- `qjs_eval(src, len) -> result`: a classic script in global scope (`let` and `class`
  bindings are shared between scripts, as in HTML).
- `qjs_call(callback, target, event) -> result`: run one registered callback: a
  listener with the event's target node, or a timer with target -1. Calls with the
  same event number share one event object, so `preventDefault` is seen by the later
  listeners of the same dispatch.
- `qjs_release(callback)`, `qjs_alloc`, `qjs_free`, and `qjs_test262` (Test262 only:
  a fresh context with `print` and `$262`).
- Each of `qjs_eval` and `qjs_call` ends with a microtask checkpoint: QuickJS's promise
  jobs run until none is left. A result is `u32 status` (0 normal, 1 exception),
  `u32 length`, UTF-8 text (the completion value, or the exception and its stack).

**The host** (`WasmVM/Hosts/Dom.lean`): `Import` names the 13 imports with their
types; `call` serves one. Strings cross as (pointer, length) in UTF-8 and are read
with `Store.readMem` (bounds checked; a pointer outside memory traps). Mutations are
the typed `Command`s of `WebRenderScript` (`setTextContent`, `setAttribute`, with its
bounds: 64 KiB strings, 256-byte attribute names, 4096 commands, 1048576 nodes) plus
`createElement` and `appendChild`, applied with the `DOM.Arena` operations
(`Dom.setTextContent`, `Dom.setAttribute`, `Dom.createElement`, `Dom.appendChild`), so
DOM errors are the arena's (`InvalidCharacterError`, `HierarchyRequestError`). The host
keeps the list of commands, so it can send the same list to another arena. Timers and
listeners only record a `Request` (`listen node type callback`, `timer id callback
delay repeating`, `clearTimer id`); the embedder's event loop decides which callback
runs and when, and runs it with `qjs_call`. The host is a pure function of its state,
the arguments and the store: no monad, so no network, file, clock or randomness.
Theorems (no `sorry`):

- `call_writes_within`: an import with no output buffer returns the store unchanged;
  the three that return a string (`tag_name`, `text_content_get`, `get_attribute`)
  change it at most by one `writeMem` of at most `capacity` bytes at the buffer the
  module gave (`WritesWithin`). A string that does not fit is not written; the length
  is returned and the module asks again with a larger buffer.
- `call_store`: so a DOM import never grows memory or changes tables, globals or
  functions.
- `Import.all_names_distinct`, `Import.ofName?_name`.

**Run** (`lake exe wasmvm-bench qjs WASM [REACTOR]`, `Bench/QuickJS.lean`; machine:
the owner's Mac, 2026-11-08):

- Load, `_initialize` and `qjs_new`: 220 ms.
- Plain JavaScript, 25 cases, 25 pass: arithmetic and float printing, strings and
  UTF-16 length, closures, arrays, JSON, `try`/`catch`, classes with private fields,
  `extends`/`super`, destructuring, `Map`/`Set`, generators, regular expressions with
  `\p{L}`, BigInt, `Date` on the virtual clock, promises and `queueMicrotask` (order
  after the checkpoint: `sync,then 1,micro`), `async`/`await`, no host objects
  (`process`, `require`, `fetch`, `XMLHttpRequest`, `WebAssembly` are undefined), a
  thrown `RangeError`, a `SyntaxError`, `fib(20)`, and unbounded recursion caught as
  a `RangeError`.
- Scripted pages, parsed with the Lean HTML parser; Lean dispatches the clicks (the
  target's `click` listeners, in the order added) and runs the timers. 8 pages, 8 as
  expected:
  - compared with the host-run QuickJS path (`tools/wasmvm/quickjs/host-reference.mjs`:
    the pinned `qjs-wasi-reactor.wasm` in Node with `guest.mjs` and the same element
    snapshot and sources): `fixtures/scripted.html` (2 clicks),
    `fixtures/mvp.html` (3 clicks, `preventDefault`), two scripts that share a `let`
    binding with `this` and `event.type` in the listener, and two listeners where the
    second sees the first's `preventDefault`. Same commands, logs and
    `defaultPrevented` in every turn.
  - with an expected result (the host-run path has no timers, `createElement` or
    promise jobs): `setTimeout` order by due time, `setInterval` with `clearInterval`,
    a cleared `setTimeout`; `createElement`, `setAttribute`, `appendChild` from a
    click; promise jobs after a script and after a callback; a refused attribute name
    (`InvalidCharacterError`, caught in the script). The host-run reference without
    its Lean DOM binding accepts that name, so that case is not compared with it.
- Speed: 104 to 121 million Wasm instructions per second on QuickJS (the interpreter
  loop of QuickJS is a large `switch`, which suits the engine). `fib(24)`: 146 M
  instructions, 1.39 s (native QuickJS-NG, same build flags: 8 ms, about 170 times
  faster). A loop of 200 000 iterations plus `JSON.stringify` of 2000 objects: 329 M
  instructions, 2.7 s (native 18 ms). One scripted-page turn (a click that sets
  `textContent`): 40 000 to 70 000 instructions, 0.5 to 1 ms. Running the scripts of
  a page: 170 000 to 420 000 instructions, 2 to 12 ms.

**Test262** (`tools/wasmvm/quickjs/test262-sample.py 500 1244`, then
`lake exe wasmvm-bench test262 WASM DIR [NATIVE [FUEL]]`, `Bench/Test262.lean`): 500
tests drawn at random (seed 1244) from `test/built-ins`, `test/language` and
`test/annexB` of Test262 at commit 5ef1e5723b (the commit that QuickJS-NG v0.18.0
pins). 64 are not run, by QuickJS-NG's own `test262.conf`: 10 module tests, 54 with a
feature it marks `skip` (for example Temporal). The 436 others run once each,
non-strict unless `onlyStrict` (the upstream runner runs both modes), with the harness
files the test names, in a fresh context.

- WasmVM, budget 2 G instructions per test: 431 of 436 pass (98.8 %), 15.8 G
  instructions in 130 s (121 M per second).
- Native QuickJS-NG (the same entry point built with `cc -DQJS_NATIVE`): 434 of 436
  pass in 0.7 s.
- The 2 failures in both: dynamic `import()` of a fixture module; the page host gives
  no module loader (deny by default).
- 3 more fail in the VM with the default budget of 2 G instructions per test: the
  `RegExp` property-escape tests `Script=Kannada`, `Script_Extensions=Kannada` and
  `Script_Extensions=Tibetan` (upstream's `test262.conf` names that directory as
  slow). With a budget of 40 G they pass: 6.6 G instructions for the 3, 53 s. So with
  enough fuel the VM gives the same result as native on all 436: 434 pass (99.5 %).
  No case passes natively and fails in the VM for another reason.
- Apple's EU bar for an alternative engine is 80 % of Test262 without a JIT.
  QuickJS-NG in WasmVM is over it on this sample. This is a sample of 436, not the
  full suite (about 48 600 files in the three directories).

**What wiring into the Foafnaut engine needs**:

1. The engine (`WebRenderScript`) loads the QuickJS module once per page, with this
   host on the page's arena, in place of the host-run worker. The command list of the
   host is the list `WebRenderScript.applyCommands` takes today; `createElement` and
   `appendChild` need two new cases there.
2. The event loop (`L4Factoidal.EventLoop`, the "event-loop" work) takes the
   `Request`s as its timer and listener calls and gives back which callback runs
   next; the embedder runs it with `qjs_call`. The virtual clock of the WASI caps is
   the event loop's clock.
3. Speed: a page script of a few hundred thousand instructions is a few milliseconds;
   a heavy script is about 170 times slower than native QuickJS. The engine speed
   work (above, "Next" 1) applies directly.
4. The module (1 MB) is not committed. The owner decides whether it is vendored or
   built (as for HarfBuzz).

## Trusted pieces

Code whose meaning is not checked by Lean's kernel, in the engine and its tools. Lean's
compiler and runtime, and the C library's float functions (see "Scope"), are trusted
as for all compiled Lean.

| Piece | What is trusted | Lean reference | How it is tested |
|---|---|---|---|
| `Exec/Bytes.lean` `Bytes.st16`, `st32`, `st64` (`@[extern c inline]`) | one `memcpy` of 2, 4 or 8 bytes after the uniqueness check that `lean_byte_array_uset` makes (copy when shared), byte swap on a big-endian host | the `uset` chain in each definition's body (the proofs use it) | every slot write and every memory store of the spec tests (35501 pass) and of `memtest`; the Lean interpreter cannot run them, so no `#eval` calls a store |
| `Bench/Repr.lean` `rdX`, `wrX` (`@[extern c inline]`) | an 8-byte load and store; benchmark only, not in the engine | `rdF`, `wrF` | `wasmvm-bench repr` prints each variant's result beside the others; not compared automatically |

| `WasiIO.lean` capability sources | `IO.getRandomBytes` (the operating system's random source), `IO.monoNanosNow`, `Std.Time.Timestamp.now`, the stdout and stderr writes | none: these are I/O; the WASI host reaches them only through `Caps` (`denied_is_pure`) | `Tests/Wasi.lean`: the wasi-testsuite clock and random tests |

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

Open obligations: now stated against the state abstraction `R`, as exact theorem
statements, in "Refinement: the state abstraction" below. `enterTail_refines` has
moved forward: the read-back it needed (`moveDown` through `Slots.rd`, `ld64` of
`st64`) is proved (`SlotLemmas.moveDown_rd`, `rd_wr_same`, `rd_wr_ne`).
Legacy exceptions: no spec rules exist to prove against; tested only.

## Refinement: the state abstraction (stage 3, 2026-11-08)

Code: `Proofs/Slots.lean`, `Proofs/Memory.lean`, `Proofs/Refine.lean`,
`Proofs/RefineRun.lean`. Axioms of every theorem below: `propext`,
`Classical.choice`, `Quot.sound` (`#print axioms`); no `sorry`. The spec is
`Spec/Wasm30.lean` after spectec patches 0005 and 0006 (spec-layer record, section
9b): both defects were found by these proofs.

### The abstraction

A relation, not a function: `R e c` (`RefineRun.lean`) between the engine state
`e : EState M` (store, slots, `sp`, `fp`, `pc`, code, instance, frames) and a spec
`config`. The engine has no types and no nesting; both come from witnesses:

- `Comp code locals maxH L d pc ts is pe te` (the compiler's relation): the spec
  instructions `is` are compiled into `code` from `pc` to `pe`; `ts`/`te` are the
  operand types of the current block at both ends, `d` the number of operand values
  below the block, `L` the labels in scope. A label `Lbl` is the side-table entry a
  branch uses (target pc, arity, height, types). `block` compiles to no op (its label
  targets the pc after its body); `loop`'s label targets its first pc; `br l` is the op
  `br (L[l]).target`. So the side table is proved right by the induction in `br_up`.
- `Nest .. L H d e te`: the open blocks, innermost first. Each is a `Hole`, the spec
  context `vals ++ [LABEL_ n cont □] ++ rest`; its values are slots and its `rest` is
  compiled (`Comp`) from the block's end pc. The outermost hole is the function's own
  label, whose end pc holds `return`.
- `ValR t b v`: slot bits `b` are value `v` at type `t` (i32 zero-extended; i64 the
  whole slot; references by address with `nullRef` for null; floats only as "a float
  constant", because the generated float encodings are opaque). `SlotsR` lifts it to a
  run of slots; `LocalsR`: slot `fp + x` is local `x` of the spec frame.
- `ActR`: the function's spec body is `plug H (valsC ++ is)`, the slots from
  `fp + nLocals` to `sp` are the holes' values then `valsC`, and `Comp` holds at `pc`.
  `DoneR`: after a branch to the function's own label, only the results remain.
- `R e c`: `c = config (state S f0) (wrap cs m f body)` with `ActR` or `DoneR` for
  `body`; `wrap` puts `FRAME_ m f body` inside the callers' bodies (`CallersR`, each
  caller's slots below the callee's `fp`); `StoreR`: each engine memory is the spec
  memory at the same address, read through `LinearMemoryLaws.byte`; size side
  conditions (slots and code below `USize.size`, room for `maxH` slots above `fp`).

### Theorems

The general shape, proved:

```lean
theorem step_refines (e e' : EState M) (c : Spec.config) (hR : R e c) (hs : stepE e = some e') :
    ∃ c', Spec.Steps c c' ∧ R e' c'
theorem stepE_run (lim : RunLimits) (e e' : EState M) (n : Nat) (h : stepE e = some e') :
    e.run lim (n + 1) = e'.run lim n
```

`stepE` is one engine step for the covered ops, written as the cases of `run`;
`stepE_run` says `run` makes exactly that step. Covered: `const` (i32, i64),
`local.get`, `local.set`, `local.tee`, i32/i64 `add`/`sub`/`mul`, `br`, `br_if` (taken
and not), `block`/`loop`/`end` (spec steps only: `norm` enters and leaves blocks with
`Step_read.block`/`loop` and `label_vals`, the engine takes no step), `i32.load` and
`i32.store` on memory 0 through `LinearMemory` (backend laws `LinearMemoryLaws`,
proved for `ByteMem`). The parts, each a theorem:

| Theorem | Statement (short) |
|---|---|
| `SlotLemmas.rd_wr_same`, `rd_wr_ne`, `moveDown_rd`, `le64_bytes` | slot read-back on the Lean reference bodies of `ld64`/`st64` |
| `MemLaws.ld32_eq`, `st32_byte`, instance `LinearMemoryLaws ByteMem` | `load32` is 4 bytes little-endian; `store32` writes them and keeps the rest |
| `i64_add_refines`, `i64_sub_refines`, `i64_mul_refines`, `bin_step` | each `BinR` op is `Step_pure.binop_val` (i32 from stage 1) |
| `exit_level`, `enter_block`, `enter_loop`, `norm` | block structure, spec side only |
| `op_const32/64`, `op_localGet/Set/Tee`, `op_binop`, `op_load`, `op_store` | body-level step lemmas |
| `br_up`, `op_br`, `op_brIf_true`, `op_brIf_false` | `br_label_succ` l times then `br_label_zero`; the side-table target and `brMove` agree |
| `step_wrap`, `steps_wrap`, `CallersR.frame` | steps in the running function lift through `FRAME_` and the callers |
| `case_*`, `step_refines` | the whole-state theorem |
| `fused_refines` | a fused op without a jump (`llBin`, `lcBin`, `cBin`, `binSet`, `lcBinSet`): `run` on `fuse code` reaches the registers `after` (`Fuse.fuse_agrees`), and `R` holds there (`simple_chain`: one `step_refines` per part) |

### Left, as exact statements

```lean
-- the compiler establishes the relation (validator item 4, now with a target):
theorem compile_establishes (c : Ctx) (fc : FnCtx) (body : Array Instr) (cf : CompiledFunc)
    (h : compileFunc c fc body = .ok cf) :
    ∃ is L pe rs, Comp cf.code fc.locals.toList cf.maxHeight L 0 0 [] is pe rs ∧
      Nest cf.code fc.locals.toList cf.maxHeight s fp L [⟨[], rs.length, [], []⟩] 0 pe rs ∧
      toSpec body = is            -- for every s, fp; `toSpec`: Syntax.Instr to Spec.instr
-- the jumps the validator emits for `br_if` with nothing to move, `if`, `else`:
theorem step_refines_jump : R e c → stepE' e = some e' → ∃ c', Spec.Steps c c' ∧ R e' c'
  -- with `Comp.jumpIf`, `Comp.ifElse` and `stepOp` cases for `jump`, `jumpIf`, `jumpUnless`
-- calls and returns (CallersR gains the call site; Step.call_ref_func, frame_vals):
theorem step_refines_call : R e c → stepOp e (.call f) = ... → ∃ c', Spec.Steps c c' ∧ R e' c'
theorem step_refines_return : R e c → e.code[e.pc.toNat]? = some (.return_ k) → ...
-- exceptions (stage 2 obligations, stated against R):
theorem unwind_refines (hR : R e c) (hthrow : e.code[e.pc.toNat]? = some (.throw x n))
    (hcaught : raise st' exn e.stack e.fp e.pc e.code e.inst e.frames
      = .caught stack' sp' fp' pc' code' inst' frames') :
    ∃ c', Spec.Steps c c' ∧ R ⟨st', stack', sp', fp', pc', code', inst', frames'⟩ c'
  -- needs `HANDLER_` holes in `Nest` (a `tryTable` hole kind) and: the innermost handler
  -- entry holding pc (`innermost`, `searchChain`) is the innermost HANDLER_ around it
theorem uncaught_refines (hR : R e c) (hthrow : ...) (hunc : raise .. = .uncaught) :
    ∃ S f0, Spec.Steps c (.mk_config (.mk_state S f0) [.REF_EXN_ADDR exn, .THROW_REF])
theorem enterTail_refines (hR : R e c) (hop : e.code[e.pc.toNat]? = some (.returnCall f))
    (hok : enterTail lim e.st e.stack e.sp e.fp (e.inst.funcs[f]!) = .ok stack' sp' code' inst') :
    ∃ c', Spec.Steps c c' ∧ R ⟨e.st, stack', sp', e.fp, 0, code', inst', e.frames⟩ c'
  -- moveDown read-back is proved (moveDown_rd); left: Slots.grow and initLocals read-back,
  -- and the spec side return_call_ref_frame_addr then call_ref_func
-- whole runs of fused and unfused code agree (induction on fuel; every function fused):
theorem run_fuse_agrees : (∀ fa, st.funcs code fused) → run lim st .. (fuse c) .. n = run lim st .. c .. n
```

Also left: floats (`ValR` relates them only as "a float constant"), `drop`/`select`,
unary ops, the jump-ending fused ops (`llBinJump`, `lcBinJump`, `binJump`: they end in
`jumpIf`/`jumpUnless`), globals and tables in `StoreR`, and the generator's dropped
iteration lengths (spec-layer section 9b, third defect): the generated `block`,
`br_label_zero` and `call_ref_func` do not tie `n` to the number of values, so these
theorems are proved against relations that allow more than the official ones; the
engine's steps keep the counts, but the theorems do not yet say so.

### Speed tricks and their proofs

| Trick | Covered by proof |
|---|---|
| Precomputed branch targets (side table in the op) | yes for `br`, `br_if` (`br_up`, `Comp.br`), given `Comp` (compiler theorem open) |
| Untyped slots, no tag checks | yes: the types are `Comp`'s, `ValR` per slot |
| One bounds check per slot access (8 byte checks removed) | yes: `rd_wr_same`/`rd_wr_ne` on the Lean reference body; `R` keeps every access in range |
| One bounds check per memory access | yes for `i32.load`/`i32.store` (`LinearMemoryLaws`, `ByteMem`) |
| Fused ops | yes for the five without a jump (`fused_refines`); not the three ending in a jump |
| Trusted inline C stores (`Bytes.st16/32/64`) | no: the proofs are about the Lean bodies; the C `memcpy` is trusted to equal them ("Trusted pieces") |
| No stack-overflow check inside a function | in `R` as `fp + maxH ≤ slots` and `Comp`'s push bound; `maxHeight_sound` (compiler) open |
| `cold` ops, tail calls, exceptions | no (statements above) |
| Single-threaded copies of parallel-compiled code (`CompiledFunc.fresh`) | yes: `CompiledFunc.fresh_eq`, `Op.fresh_id` (the copy is the identity) |
| In-place host writes (`StoreOf.writeMemS`) | yes: `writeMem_of_writeMemS`, `writeMemS_false`; `putOut_within` unchanged |
| Exits of `run` through `Run.stop` | definitional: `stop` is the result tuple; every proof about `run` unfolds through it |
| Fused ops charge the fuel of their parts | yes: `Proofs.Cost.fused_charges_parts`; checked on the benchmarks by `engine --check` |


## Next

1. Speed (see "Speed pass 2" for the state on 2026-11-08: QuickJS 1.5x, VP8 1.4x of
   the 2x asked). First a smaller loop: fewer loop-carried arguments of `run` (`lim`,
   `inst`, `frames`, code change only at calls and returns), so that fused ops can be
   added without the spills that each new case brought; then the fused ops of the
   profiles. Older items: memory 0 held as a loop
   argument during a run (a load now reads `st.mems[inst.mems[0]]` with reference
   counts, a store rebuilds the store record); code as bytecode in a `ByteArray`
   (no reference counts per instruction); the last slot check removed with
   `maxHeight_sound` and a typing invariant carried by `run`; a cheaper `call`/`return`
   (`fib` is call-bound); whole-run equality of fused and unfused code.
2. Refinement: the rest of the integer table (div, rem with `binop_trap`, shifts,
   compares through `Step_pure.relop`), then `Run.step_refines` with the abstraction to
   `Spec.config`.
3. Proposals in the order of the planned uses: SIMD (HarfBuzz builds use it when
   enabled; ours is built without it, "HarfBuzz in the VM"), memory64, GC. Exceptions, tail calls and `call_ref` are done (stage 2).
   Why `l4factoidal.wasm`'s `l4_init` takes 18 s (its host now has real randomness:
   "WASI Preview 1").
4. Parallel compile by chunks of equal byte size; decode without the per-section
   copy (`b.extract 0 e`).
5. The JSON op form for the hosts: done for the Foafnaut engine (`wasmRun`,
   `foafnaut:wasm`, above); handles for instances and suspended runs, and WASI there.
