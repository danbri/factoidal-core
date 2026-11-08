# WasmVM AOT: validated guest WebAssembly translated for the host's engine

Date: 2026-11-08. Issue: https://github.com/danbri/factoidal/issues/1244 (WebAssembly VM
in Lean). Author: aot, a subagent of session depmap-0e. Related records:
`2026-11-07-wasmvm-engine.md` (the engine), `2026-11-07-wasmvm-spec-layer.md` (the
spec relations), `2026-11-08-page-scripts.md` (page scripts in QuickJS).

## 1. The problem

On the Hub the Foafnaut engine is Lean compiled to WebAssembly by Emscripten. A guest
module (QuickJS-NG for page scripts, HarfBuzz, the media decoders) runs in WasmVM, an
interpreter written in Lean, so on the Hub the guest is interpreted by an interpreter
that itself runs as WebAssembly: about 11 million guest instructions a second, against
about 180 to 360 million natively (`2026-11-07-wasmvm-engine.md`, "Speed pass 2").
QuickJS page scripts are then too slow for animation.

## 2. What this adds

A compiler from a validated guest module to a host module. Lean decodes and validates
the guest, translates it (`WasmVM/Aot/Translate.lean`), and writes the binary
(`WasmVM/Aot/Encode.lean`). The host's WebAssembly engine (the browser's, on the Hub)
compiles and runs the result. Lean keeps every decision:

- what is instantiated and when: Lean asks the host for an instance and for each run of
  an export, one at a time (section 5);
- which imports exist: only the guest's own imports, each routed back to the Lean host
  function the interpreter would call (WASI under `Wasi.Caps`, the `foafnaut_dom` and
  event-loop imports of `Hosts/Page.lean`);
- what the guest may touch: its own memory and table only, under Lean's page limit, and
  a fuel budget Lean sets before each run.

Every DOM effect is still a typed `Hosts.Dom.Command` made by Lean on Lean's arena, and
the HTML event loop is still `L4Factoidal.EventLoop`: the session code is the same code
for both machines (section 5).

## 3. The translation

For a trusted, validated guest the translation is close to the identity on code
(`Aot.translateModule`):

| Part | Guest | Host module |
|---|---|---|
| imports | any function imports | import `k` keeps its type, is renamed `aot`.`i{k}` |
| table, memory, global, tag imports | refused | |
| memory | exactly one, defined | the same, maximum `min(own, pages)` (2048 pages, 128 MiB, as `Hosts.Page.Limits.pages`) |
| globals | kept | one more, `(mut i64)`, appended (no index moves) and exported as `aot_fuel` |
| exports | kept | the same plus `aot_fuel` |
| function bodies | | a `charge c` at the start and after each `loop` header, nothing else |
| types, tables, elements, data, start, tags | | unchanged |

**Import rewiring.** Import `k` becomes `aot.i{k}` so the host's import object can give
every import one function without any name logic: the function for `i{k}` passes `k`
and the arguments to Lean, which serves them with binding `k` of `Wasi.link` (the
binding the interpreter uses). Duplicate imports of one name stay distinct.

**Memory isolation.** The guest's memory is a separate `WebAssembly.Memory` created by
the instantiation; the guest imports no memory, table or global, so it can reach no
other state. Every load and store is bounds-checked by the host engine against that
memory (the same check the interpreter makes, `ea + width <= size`). `memory.grow`
stops at the page limit because the maximum in the module is the limit.

**Fuel.** `charge c` is ten instructions with no net stack effect:

    global.get $fuel  i64.const c  i64.sub  global.set $fuel
    global.get $fuel  i64.const 0  i64.lt_s  if  unreachable  end

`c` counts the straight line that every entry into the region it heads runs
(`Aot.regionCosts`): the region is the function body outside its loops, or a loop body
outside its inner loops, and the straight line is its instructions from the start up
to and including the first one after which control may leave (`Aot.mayLeave`: a
branch, `return`, `if`, a nested `loop`, a throw, a tail call, `unreachable`). Only
instructions that do work count: `block`, `loop`, `end`, `else`, `try`, `try_table` and
`nop` give the code its structure, and the engines run them at no cost (WasmVM compiles
them to no op). Each charge is at least 1. Every entry runs all the counted
instructions or traps, every way back to earlier code is a branch to a loop header,
which charges again, and every call charges at the callee's start. So the fuel charged
is at most the instructions run (plus one for an entry that runs none), and every loop
round and every call charges at least 1: a guest stopped for fuel `F` has run at
least `F` instructions less one per region entry that ran none, and no guest runs
forever.

Two versions were measured and dropped. Charging the whole region (an upper bound)
charged thousands for each round of QuickJS's interpreter loop, which is one loop
around a `br_table` over all its byte codes: 1.6 x 10^9 fuel for 4.5 x 10^6
instructions, so the interpreter's per-run budget (4 x 10^9) would have stopped
ordinary pages. Counting the structural instructions too charged each round the
hundreds of `block`s that open before that `br_table`: 5.3 x 10^8 fuel for the 1.46 x
10^8 instructions of `fib(24)`. As now: `timers-and-clicks.html` 4.0 x 10^6 fuel
against 1.5 x 10^7 instructions of the interpreter; 73 WPT pages 2.7 x 10^9 against 1.0
x 10^10 (27 %).

Lean sets the global to the session's per-run budget (`Limits.fuel`, 4 x 10^9, as on
the interpreter) before each run and reads it back after; the difference is the run's
cost in fuel units, and the `instructions` of a turn on the AOT path are these units (a
count of the instructions that do work, at most the interpreter's count). A guest that runs out traps at `unreachable` with the
global below zero, and Lean reports "out of fuel". Terminating the worker would also
stop a runaway guest, but it would end the Lean engine with it.

**Not changed.** Tail calls, exceptions (3.0 and legacy), reference types, bulk memory,
multi-value and sign extension pass through: the host engine runs them. The encoder
writes every construct the decoder reads.

## 4. Correctness

**The theorem to aim for.** For a guest `m` that validates and a translation
`translate m pages = .ok (t, plan)`: every run of an export of `t` under the host's
WebAssembly semantics, with the imports of section 5, gives the same observable behaviour
as the run of the same export of `m` under `Spec/Wasm30` (or the engine `Exec.Run`, by
`step_refines`), as observed through the imports: the same sequence of import calls with
the same arguments, the same memory bytes at each call, and the same results, except
where one of the two runs out of fuel: the interpreter's budget counts instructions,
the translated module's counts the straight lines of section 3 (at most the
instructions), so the translated run may run longer before it stops.

Stated in the spec layer: let `erase` remove the charges. Then the host semantics of
`t` with fuel `F` simulates `Spec.Steps` of `m` step for step on the erased code, with
the extra global ignored, until the global goes below zero.

**What is proved now** (`WasmVM/Aot/Translate.lean`; axioms in section 9):

- `erase_instrument`: erasing the charges from each translated body gives the original
  body; `translate_funcs`: each function keeps its type and locals, and its body is the
  original with charges. So the code is the identity up to the fuel instrumentation, as
  a syntactic theorem over every instruction (`erase_emit`, by induction over the body).
- `translate_import_desc`: import `k` keeps its kind and type (the import map is
  type-preserving); `translate_import_route`: import `k` of `t` is named `importName k`
  and the plan routes it back to import `k` of `m`; `translate_import_names` and
  `importName_injective`: two translated imports with one name are the same import. So
  the import map is a bijection between the import positions of `m` and of `t`,
  type-preserving, with the route back in the plan.
- `translate_exports`: the exports are those of `m`, then `aot_fuel`.
- `translate_rest`: types, tables, data segments, start function and tags are unchanged;
  the memory count is unchanged, and each memory's maximum is at most `pages`.
- `translate_eq`: the checked `translate` is the pure `translateModule` once the checks
  pass. `instrument_eq`, `emitAcc_eq`: the loop that runs (`emitAcc`, an accumulator,
  since a body has tens of thousands of instructions) is the list function the
  theorems are about.
- The charge in the spec semantics (`Proofs/Aot.lean`, `Proofs/AotCheck.lean`):
  `charge_take`: the first four instructions of `charge g c`, in any state whose global
  `g` holds the i64 `F`, take `Spec.Steps` to the instructions after them with global `g`
  set to `F - c` and no other change (`with_global`); `charge_check`: when global `g`
  holds an i64 under 2^63, the last six take `Spec.Steps` to the instructions after
  them with the state unchanged (`global.get`, `i64.lt_s` giving 0 by
  `relop_lt_nonneg`, `if` taking the empty arm, `block`, the label's end). So a charge
  that does not run out is, in `Spec/Wasm30`, a change of the fuel global and nothing
  else: the "commutes with the semantics up to fuel" statement for one charge.

**The session code** (`Hosts/Page.lean`): `Prog.runLocal_bind` and
`Prog.runLocal_pure` say that `runLocal` is a monad morphism to `Id`, and `runP_local`
that a run on the interpreter is `Session.run`. So the interpreter path of the
refactored code is, step by step, the code it was before: each ask answered by the
interpreter as it comes, in order. The event loop's host is `DriverM`, the
`EventLoop.Driver` of `Session.advance` with its `run` in a monad;
`DriverM.ofDriver_advanceGo` (with `ofDriver_frameGo`, `ofDriver_frame`) proves that in
`Id` it is `Driver.advanceGo` step for step, so the one-frame-per-advance theorems of
`EventLoop.Driver` are about the same loop.

**What is tested, not proved.** That the translation preserves validation (`validate t`
succeeds when `validate m` does) and that `Encode.encode` inverts `Binary.decode`:
`wasmvm-bench aot third_party/wasm-spec/test/core-json` round-trips every module of the
spec tests and validates every translated one (section 9), and the Hub's engine compiles
the translated QuickJS module.

**What is left as statements.**

```lean
-- the encoder: decode inverts it (a structural induction over the module record,
-- with one lemma per reader of Binary/Decode.lean)
theorem decode_encode (m : Module) (h : WellFormed m) : Binary.decode (Encode.encode m) = .ok m
-- validation is preserved: `charge` types as [] -> [] in any context with global g : mut i64
theorem translate_valid : validate m = .ok v → translate m p = .ok (t, plan) → ∃ v', validate t = .ok v'
-- the fuel instrumentation commutes with the semantics up to fuel (Spec.Steps on t,
-- erased, are Spec.Steps on m; a run of t that keeps fuel >= 0 is a run of m)
theorem fuel_bound : a run of t that charges F fuel runs at least F instructions of m
```

`fuel_bound` needs the region argument of section 3 as an invariant of `Spec.Steps`,
and the whole-run theorem needs the engine side too: that the translated module, run by
WasmVM's own interpreter, refines `Spec.Steps` of the original (it would follow from
`step_refines` once the compiler theorem `compile_establishes` of the engine record is
proved, with `charge_take` and `charge_check` for the inserted code).

**The trust boundary.** Proved: the translation, as a function on `Syntax.Module`.
Tested: the encoder (round trip) and validation preservation. Trusted: the host
engine's WebAssembly implementation (V8, JavaScriptCore, SpiderMonkey) runs the module
by the WebAssembly semantics: its compiler, its bounds checks and its isolation of one
instance's memory from another. This is the same trust the Hub already gives the host
engine for the Foafnaut engine itself, and the same kind of trust as the host GPU
running the WGSL that Lean emits. Also trusted: the worker's driver (section 5), which
copies bytes and calls functions as Lean's answers say; it decides nothing.

## 5. Running it: Lean drives, the host executes

**One session code, two machines.** The session logic of page scripts
(`Hosts/Page.lean`: start, scripts, microtask checkpoints, the event loop, clicks,
frames) is written once as a program `Prog`: pure Lean that, where it needs the guest,
stops with an `Ask` and goes on with the `Reply`:

| Ask | Reply |
|---|---|
| `invoke fa args`: run export `fa` (host calls served on the session's host state) | the `Outcome` (values or trap) and the instructions or fuel units |
| `read ptr len` | the bytes, or an out-of-bounds error |
| `write ptr bytes` | done, or an out-of-bounds error |

`Prog.runLocal` answers each ask with the interpreter (`Session.run` on the session's
store): the interpreter path, which gives the results of before, step for step. The
AOT path answers each ask through the host: the engine op `scriptSession` returns the
ask to the worker as JSON, the worker does it on the instance and calls back with the
reply (`action:"resume"`), and Lean continues the program from where it stopped. The
paused program lives in the engine (`WebScripts.Held`) between the calls.

**Host calls.** While the host runs an export, a guest import calls the worker's
function for `aot.i{k}`, which calls the engine op `scriptSession` with
`action:"host"`, `k`, the arguments, the memory size and the bytes of the ranges the
import reads (`Hosts.Page.readsOf`, a table Lean gives with the module: for each import,
which argument pairs are a pointer and a length, and the bound above which Lean reads
nothing). Lean serves the call with the same binding and the same host function as the
interpreter, on a `Window` (`Aot/Window.lean`): a `LinearMemory` backend that holds the
memory size, the ranges the host sent, and the writes the function makes. The answer is
the results and the writes; the worker copies the writes into the guest's memory and
returns the results to the guest. A host trap or `proc_exit` is a JavaScript exception
that unwinds the guest, and the run's reply says so. A host-call budget per run is
counted in Lean (`Limits.hostCalls`).

**The script clock.** `Page.ScriptClock` counts a run's instructions as script time.
On the AOT path it counts fuel units (section 3) the same way: Lean marks the clock when
it asks for a run (`PageAot.startRun`), at each host call (the worker sends the fuel
global with the call) and when the run ends (`ranReply`, which also moves the loop's
clock up to script time), as `Session.run` does. Fuel units are fewer than the
interpreter's instructions (about a quarter on the pages measured), so on the AOT path
script time passes more slowly for the same script; both are a stated rate, not a
measurement of the run.

**Instances.** On the Hub, the worker asks `scriptSession info`; an engine with this
work answers `aot:true`. The worker then gives the guest bytes with the family
`guest:quickjs-aot` (the same byte call as before), Lean decodes, validates and
translates, and `action:"aotModule"` returns the host module as a raw section of
`web_document_call_bin` with the import table in the JSON head. The worker compiles it
once (`WebAssembly.compile`). For each page, Lean's first ask is a fresh instance
(`WebAssembly.Instance` of the compiled module with the generic import object), then
`_initialize`, `qjs_new` and page mode, then the page's scripts. With an engine without
`aot` in its info, or when the compile fails, the worker loads the guest for the
interpreter, as before; there is no JavaScript copy of any Lean logic and no fallback
to an older engine.

**Native.** The native engine (Deno with `libweb-render.dylib`, and the Mac app) keeps
the interpreter in this slice; see section 7.

## 6. The rule: does the host browser do our work?

No. The rule is that the host browser must not do the work of the Foafnaut engine:
layout, rendering, the DOM, the event loop and scripting are Lean's. Here Lean decides
everything: it validates the guest, emits the host module, decides when an instance
exists and when each export runs with what arguments and what fuel, serves every import
with its own host functions on its own DOM arena, and keeps the event loop. The host
engine only executes code that Lean emitted and validated, in an instance whose every
import is a Lean function, much as the host GPU runs the WGSL that Lean emits for the
page. The host browser's JavaScript engine still never runs a page script: QuickJS
does, as WebAssembly code that Lean produced. This is the line between the host as an
executor of Lean's output (allowed: GPU shaders, this) and the host as an implementer of
web features (not allowed: overlaying host `<video>`, host iframes, host layout).

## 7. Native

Three ways to get the same speed natively, compared:

| Path | Speed (QuickJS) | Cost | Verdict |
|---|---|---|---|
| keep the interpreter (`Exec.Run`, native) | 177 M instructions/s, fib(24) 0.82 s (engine record) | none | the default now |
| the same translated module in the host's Wasm engine where one exists (Deno's V8 in `run_html.ts`) | near native | the driver of section 5 in TypeScript | possible now; not for the Mac app without Deno |
| Wasm to C emitted by Lean (like wasm2c), compiled by clang at build time for the fixed guests (QuickJS, HarfBuzz, decoders), linked into the native library | native minus bounds checks | a C emitter in Lean (the translation is the same per instruction; the trust moves to clang, as for Lean's own C) | worth it for QuickJS only once pages need it: the interpreter is 170 times slower than native QuickJS |

A Wasm-to-native JIT in Lean (emitting ARM64) is not worth it: it is what the host
engines already are, and its proofs would cover far more than the C path's.

## 8. Theorems and axioms

`#print axioms` of each (2026-11-08); no `sorry`, no `native_decide`, no `bv_decide`.

| Theorem | File:line | Axioms |
|---|---|---|
| `isCharge_charge`, `erase_emit`, `erase_instrument` | `Aot/Translate.lean`:60, 165, 175 | propext, Classical.choice, Quot.sound |
| `emitAcc_toList`, `emitAcc_eq`, `instrument_eq` | `Aot/Translate.lean`:137, 145, 155 | propext, Quot.sound |
| `translate_eq`, `translate_import_desc`, `translate_import_route`, `translate_exports`, `translate_rest` | `Aot/Translate.lean`:216, 223, 232, 242, 257 | propext, Quot.sound |
| `translate_funcs` | `Aot/Translate.lean`:249 | propext, Classical.choice, Quot.sound |
| `importName_injective`, `translate_import_names` | `Proofs/AotNames.lean`:13, 17 | propext, Classical.choice, Quot.sound |
| `charge_take` | `Proofs/Aot.lean`:24 | propext, Classical.choice, Quot.sound |
| `relop_lt_nonneg`, `charge_check` | `Proofs/AotCheck.lean`:30, 42 | propext, Classical.choice, Quot.sound |
| `Prog.runLocal_bind`, `runP_local` | `Hosts/Page.lean`:286, 301 | propext, Classical.choice, Quot.sound |
| `DriverM.ofDriver_frameGo`, `ofDriver_frame` | `Hosts/Page.lean`:516, 525 | propext |
| `DriverM.ofDriver_advanceGo` | `Hosts/Page.lean`:530 | propext, Quot.sound |

`AotNames` is apart from `Translate` because `Nat.repr_injective` is in
`Std.Data.String.ToNat`, which the engine's Wasm build does not link.

## 9. Tests

- **Encoder and translator** (`lake exe wasmvm-bench aot third_party/wasm-spec/test/core-json`,
  `Tests/Aot.lean`): 5967 files, 3437 decode; all 3437 round-trip (`encode (decode
  (encode m)) = encode m`, and the re-decoded module validates exactly when the
  original does); 251 translated (those with one memory of their own and only function
  imports) all decode and validate again; 0 failures.
- **QuickJS** (`wasmvm-bench aot-module`): the published guest (1 070 033 bytes, 29
  imports) translates in about 0.2 s natively to a host module of 1 114 243 bytes;
  `wasm-tools validate` accepts it.
- **The whole AOT path, natively** (`wasmvm-bench page WASM ROOT FILE... --aot`,
  `Tests/AotPage.lean`): WasmVM stands in for the host's engine and runs the TRANSLATED
  module, driven ask by ask exactly as the worker drives it, every import call passed
  back with the read table and served on a `Window`. Logs, errors, DOM commands, clock,
  tasks, jobs and body text are compared with the interpreter's session: the demo pages
  `timers-and-clicks.html`, `showcase-dataviz-script.html`, `foaf-explorer.html`,
  `webgpu-triangle.html`: all the same (with the published guest and with a guest built
  from the current prelude); 73 WPT pages (`dom/nodes` 40 files, `dom/events`
  25, `html/webappapis/timers` and `microtask-queuing` 8, with iframe navigations
  answered as the interpreter run answers them): all 73 the same. These runs set
  `--instructions-per-ms 1000000000000`, so that script time (section 5) does not move
  the clock; with the default rate the same runs differ in the clock only, since the
  AOT path counts fuel units as script time.
- **V8, no Lean** (Node 22): the translated QuickJS with stub imports runs `fib(24)` in
  29 ms; the untranslated guest in 28 ms. The fuel checks cost about 5 %.
- **The interpreter path is unchanged by the refactor** (the WPT testharness runner,
  `tests/browser-wpt/testharness-run.ts --engine bench`, all 394 pages of its
  directories, with `wasmvm-bench` built from main before this work and from this work,
  the same guest): 12388 of 13689 subtests pass in both, and every page has the same
  harness status and the same subtest results.
- `native_html_scripts_test.ts` (2) and `native_html_pointer_test.ts` (1), interpreter
  path, Wasm engine and native library: pass. `hub_links_check.mjs` with the engine of
  this work: pass.

## 10. Measurements on the Hub

`node labs/demos/foafnaut/hub_scripts_speed.mjs --guest qjs-wasmvm.wasm` (headless
Chrome, Apple M1, other builds running on the machine; the local stand-in for GitHub
Pages serves this checkout's Hub files and the engine built from it; `wasmvm` is the same
worker and engine with the AOT probe answered false). Each figure is the wall time of the
turn in the worker (the engine call and, on the AOT path, every ask and host call).

The engine and worker of this record, the published QuickJS guest, while two WPT runs
and an engine build loaded the machine:

| Case | WasmVM in the engine (before) | AOT (after) | Speed-up |
|---|---|---|---|
| `fib(24)` in QuickJS: the start turn of a page whose script computes it | 18 067 ms | 84 ms | 216x |
| a WPT page start (`dom/nodes/Node-appendChild.html` with testharness.js) | 18 888 ms | 449 ms | 42x |
| one animation turn of `timers-and-clicks.html` (mean over 4 s) | 51.5 ms | 1.45 ms | 36x |

Two earlier runs on a quieter machine, with the engine before the rebase on the script
clock, gave 205x and 186x, 42x and 48x, 35x and 46x (`fib(24)` 72 to 82 ms against
14.8 to 15.2 s). Fuel: `fib(24)` 2.9 x 10^7 against the interpreter's 1.46 x 10^8
instructions; the WPT start 4.2 x 10^7 against 1.50 x 10^8.

The WPT page makes 8 382 host calls in its start turn, each one engine call with a JSON
request; that, not the guest's code, is most of its time. The animation turn is now
small next to the frame itself (layout and drawing, 34 to 40 ms a frame on this
machine), so the page shows 15 to 17 frames in 4 s against 8 or 9 before; the next limit is the frame, not the
script.

## 11. What is left

- Host calls by bytes (`web_document_font_call_bin` style) instead of JSON: the WPT
  start would gain most.
- The native path (section 7): the same driver in `run_html.ts` with Deno's V8, or Wasm
  to C for the fixed guests.
- The whole-run refinement theorem of section 4, `decode_encode`, `translate_valid`,
  `fuel_bound`.
- HarfBuzz and the media decoders through the same translation (their hosts are WASI
  only, so `readsOf` needs `fd_write` with a sink when output is granted).
- A deep JavaScript recursion can now reach the host engine's own stack limit before
  QuickJS's 768 KB limit; it ends the run as a trap ("Maximum call stack size
  exceeded") where the interpreter gave a JavaScript `RangeError`.
