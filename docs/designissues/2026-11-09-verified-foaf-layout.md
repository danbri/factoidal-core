# A verified FOAF overlap check in page WebAssembly

Date: 2026-11-09. Author: foafprove, a subagent of session depmap-0e. Related: the FOAF
graph's overlap certificate (Hub README, "Foafnaut: the FOAF graph shows only layouts that
pass the overlap check"), WasmVM (issue 1244; records `2026-11-07-wasmvm-engine.md`,
`2026-11-07-wasmvm-spec-layer.md`), page WebAssembly (`2026-11-08-page-wasm.md`).

The owner asked for the FOAF graph layout in portable web code, proved to implement the
Lean algorithm, with every bridging step a theorem under explicit assumptions, and no
Foafnaut-only page API. This record says what is proved (stage 1, the overlap check, on
the binary), what is assumed, what is not done (stage 2, the force step), how fast it is,
and how to rebuild and recheck it.

## 1. The Lean algorithm, pinned

The Lean FOAF graph (`labs/demos/foafnaut/FoafNaut.lean`) has no force layout: positions
ease in integer steps toward sixteen fixed radial targets (`Model.targets`, `Model.ease`).
Its guarantee is not a layout that cannot overlap but a CHECKED certificate:
`L4Factoidal.UI.LayoutPolicy`:

- `overlapSum b others` = the sum over the other boxes of `(b.intersection o).area`
  (`Box.area` = `(right - left).toNat * (bottom - top).toNat`, all `Int`/`Nat`).
- `checkFootprints cfg boxes`: for node `i`, `others` = every other present box, in index
  order; the node is accepted iff `0 < area ∧ 10000 * overlapSum ≤ cfg.overlapBps * area`.
- `certify cfg boxes` = every node accepted; `certify_sound`, `certify_iff`
  (`LayoutAccepted`): a certified layout meets the budget for every node.
- Presentation (`UI/Presentation.lean`, `FoafPresentation.lean`): a layout reaches the
  screen only as an `Approved` value; when a candidate fails, the last approved frame stays.

Number type: `Int` and `Nat` throughout, no `Float`. So no fixed-point reformulation was
needed: the kernel is integer code and the Lean definitions are the spec as they stand.

## 2. The kernel

`labs/demos/foafnaut/wasm/foaf-check.wat`, hand-written (353 bytes assembled), exports
`check(n, bps, boxes, out) -> i32` and its memory. Boxes are four little-endian i32 each
at `boxes`; the kernel writes one i32 flag per node at `out` and returns 1 iff every
node passes. Integer only (i32 addresses, i64 arithmetic, `select` for min/max/clamp),
no allocator, no imports, no calls.

AssemblyScript was considered and not used: its output carries runtime and GC glue that
would all have to be proved, and the proof is about the binary whatever produced it, so
the smallest binary is the cheapest to prove. The assembler is wabt `wat2wasm` 1.0.42
(Apache-2.0, Homebrew `wabt`); it is not trusted (section 4).

## 3. What is proved

All in `formal/lean4/L4Factoidal/WasmVM/Proofs/`, library `WasmVM`. `#print axioms` of
every theorem below: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `axiom`,
no `native_decide`, no `bv_decide`.

| Theorem | Statement |
|---|---|
| `FoafCheck.checkBytes_flat` | WasmVM's decoder (`Binary.decode`), evaluated by the Lean kernel (`decide +kernel`) on the checked-in bytes `checkBytes`, gives the flat body `checkFlat` |
| `FoafCheck.checkFlat_nest`, `checkBytes_body` | that body nests to `checkBody`, the structured instruction list the proofs run |
| `FoafCheck.checkBytes_shape` | the module: one function `[i32 i32 i32 i32] -> [i32]`, locals 5 × i32 and 8 × i64, exports `memory` and `check`, one memory, no imports, tables, globals, data or start |
| `FoafCheck.if_body`, `inner_loop`, `outer_loop`, `check_body` | the body under the spec semantics: loop invariants for the overlap sum (`sumTo`) and the flags written so far (`flagWrite`) |
| `FoafCheck.check_spec` | invoking the function (`Spec.Step.call_ref_func`) with the page's arguments, the generated relation `Spec.Steps` reaches the result `allBit` with memory holding the flags `flagsK` at `out` and every other byte unchanged |
| `FoafCheckSpec.checkFootprints_eq`, `flagsK_eq`, `certifyK_eq` | the kernel's arithmetic (`sumTo`, `okK`, `flagsK`, `certifyK`) is `checkFootprints` / `certify` on the boxes |
| `FoafCheck.check_certifies` | **transfer**: the result is 1 iff `LayoutPolicy.certify cfg (boxes.map some)`; then `LayoutAccepted`; the flag of node `i` is the certificate's `accepted` for node `i` |
| `FoafCheck.foaf_check_binary` | the same for the function whose code the bytes decode to |
| `FoafCheck.page_check_certifies` | under the `Bridge` hypotheses (section 5), what a host returns to the page is that |

### The method: a verified symbolic executor over the spec

`Proofs/SpecWP.lean` defines `Sem z vs is Q B` directly over `Spec.Steps` (the relation
generated from the WebAssembly 3.0 SpecTec sources): from state `z` with stack `vs`, the
spec semantics runs `is`, inside any following code, to a normal end satisfying `Q` or to
a branch out satisfying `B`. It is a definition, not a second semantics. Each rule is a
theorem proved from the generated rules:

- `SpecWP.lean`: `sem_steps`/`sem_step`/`sem_pure` (a local step under the context
  rules), `sem_val`, `sem_br`, `sem_brIf`, `sem_block`, `sem_loop`, `sem_if`, built on
  `steps_ctx`, `steps_label`, `steps_frame` (Steps lifted through `ctxt_instrs`,
  `ctxt_label`, `ctxt_frame`).
- `SpecWPOps.lean`: `local.get/set/tee`, `i32.add/mul/ge_u/ne`,
  `i64.add/sub/mul/gt_s/lt_s/le_s`, `i64.extend_i32_u`, `select`, `i32.load`, `i32.store`,
  on values `i32v k` (`k mod 2^32`) and `i64v x` (`x mod 2^64`, two's complement); `enc64_*`
  tie the generated `iadd_`/`isub_`/`imul_` and the Builtins comparisons (`BitVec.slt/sle`)
  to `Int`.
- `SpecWPSubset.lean`: the subset as syntax (`KI`), its flat form read from WasmVM's
  `Instr` (`FKI.ofInstr`, the opcode table), nesting (`FKI.nestBody`), meaning
  (`KI.toSpec`), the stack-top-first rules `semR_*`, and reflexive `==` on the spec
  records a call compares.

The kernel proof (`FoafCheck.lean`) is then a few dozen lines: a tactic `wstep` applies
the rule for the next instruction, `wnorm` normalises the state (locals as an explicit
list, `select` results as `min`/`max`), and side conditions (signed ranges) go to
`omega`. The whole if-body (64 instructions) is `repeat wstep` plus four loads. The
loops are inductions on the remaining count with invariants.

Two looseness points of the generated layer, and why they do not weaken the result: the
generated `block`/`br_label_zero` do not tie label arity to the values kept (spec-layer
record 9b): every use here keeps none, which is the official arity of `[] -> []`; the
generated `store_num_val` has no bounds premise: every store here is in bounds
(`Inputs.out_in`).

## 4. The binary, and the assembler not trusted

`labs/demos/foafnaut/wasm/build.sh` assembles the `.wat` and writes the bytes twice:
`Proofs/FoafCheckBytes.lean` (`checkBytes`, generated) and the hex block between the
`foaf-check.wasm: BEGIN/END` markers of `pages/foaf-explorer-verified.html`.
`build.sh --check` re-assembles and fails if either copy differs (it is in `test.sh`).
The proof is about `checkBytes`, read by WasmVM's decoder inside the kernel, so the page
runs exactly the bytes the theorems are about, and a wrong assembler could only make
`checkBytes_flat` fail.

**For the owner (Iron Rule 9):** the 353 bytes are checked in (as a Lean byte literal and
as hex in the page), as `wasm-mandelbrot.html` already does. They are always the
assembler output of the checked-in source (`build.sh --check`), but they are bytes in the
tree. The alternative is to generate both at build time (Lean file and page), at the cost
of a build step before the proof library and the demo pages; say which you want.

## 5. The assumptions (the `Bridge` structure), as hypotheses

`FoafCheckBinary.lean` states them as fields of `structure Bridge (host : HostRun) : Prop`,
used as a hypothesis of `page_check_certifies`; there is no `axiom`.

- **(a) Host semantics** (`Bridge.spec`). The host instantiates `checkBytes` as the
  WebAssembly specification does (some spec store holds a function whose code is the
  decoded body, with the declared type and locals, and the memory the call sees) and,
  when the spec relation reaches a result, returns that result and memory. This includes
  that WasmVM's decoder and the opcode table `FKI.ofInstr`/`KI.toSpec` give the bytes the
  binary format's meaning: the generated spec layer has no binary grammar (spec-layer
  record, G3), so there is nothing in Lean to prove that against. It also includes the
  spec's determinism on this code (integers only: no float, no host call, no
  `memory.grow`, no relaxed SIMD), which is what lets one reachable result stand for the
  host's; determinism of the generated relation is not proved. Evidence: WasmVM runs the
  official spec test suite (35501 pass, engine record); V8 and the other engines are
  tested against the same suite; and the bench (section 7) compares the kernel against a
  JavaScript reference on every run, in Chrome and on both Foafnaut engines.
- **(b) Floats.** None in the kernel (`KI` has no float instruction; `checkBytes_flat`
  would fail on one), so no NaN or rounding question arises in the proved part. The
  page's float positions become integer boxes in the glue (c).
- **(c) Glue** (`Inputs`). The page writes each box as four little-endian i32 at
  `boxes` (one `Int32Array.set`, on a little-endian host, which the page checks once),
  passes `n`, `bps = 500`, `boxes = 0`, `out = 16 n`, and reads the flags. `Inputs`
  is the contract: coordinates in `[0, 32768)` (the page clamps to its stage, as Lean's
  footprints are cut to the viewport), `n < 2^16`, the regions inside the 64 KiB memory
  and apart. The glue is not proved against BubblePopJS's semantics; it is a contract.

Not covered by any theorem: that the boxes the page builds (halo plus an ESTIMATED label
width: the page measures no text) are what is painted; pixels and GPU rasterisation; and
the page's force layout (stage 2 below). Exactly as the Lean graph's certificate, the
theorem is about the boxes.

TCB, then: the Lean kernel; the generated spec layer `Spec/Wasm30.lean` and the
hand-written `Spec/Builtins.lean` as the meaning of WebAssembly; WasmVM's decoder and the
20-line opcode table as the meaning of the bytes (a); the host engine (a); the glue
contract (c).

## 6. The page

`labs/demos/foafnaut/pages/foaf-explorer-verified.html`: the FOAF explorer with one rule
added. Each frame, after the (unchanged, unproved) JavaScript force steps, the page builds
the footprints, calls `check` through the standard WebAssembly API
(`WebAssembly.instantiate`, `exports.check`, `exports.memory`), and draws the frame only
if the result is 1; otherwise the last accepted frame stays, and a new person joins the
stage only with the first accepted frame that has them. A line under the stage says
"layout check: verified Wasm (theorem FoafCheck.page_check_certifies)" with frames
checked and held; where WebAssembly is missing it says the check is off and draws every
frame (the existing JS behaviour). The layout gained a footprint push-apart force and a
wider spawn ring so that accepted frames come soon. Runs in Chrome and in Foafnaut on
both script engines (`bubblepop_pages_test.ts` now includes it; the engines agree).

## 7. Performance

`labs/demos/foafnaut/wasm/check_bench.ts` (deno; `--html FILE` for a browser). Phases:
the explorer's force step (JS), the verified check (Wasm), and the same check in
JavaScript (bench only, never in a page). Foafnaut: native engine library built from main
6620c2635 plus canvas work (this branch changes no engine code), times are the engine's
own per turn; Chrome: `performance.now()`. Milliseconds per call, MacBook, 2026-11-09.

| | n | force step (JS) | check, Wasm (verified) | check, JS (reference) |
|---|---|---|---|---|
| Foafnaut, BubblePopJS | 25 | 2.55 | 1.05 | 9.09 |
| Foafnaut, QuickJS-NG in WasmVM | 25 | 20.9 | 3.67 | 62.8 |
| Chrome (V8) | 25 | 0.032 | 0.004 | 0.006 |
| Foafnaut, BubblePopJS | 500 | 457 | 178 | 3537 |
| Foafnaut, QuickJS-NG in WasmVM | 500 | 3601 | 237 | 23951 |
| Chrome (V8) | 500 | 0.268 | 1.318 | 1.066 |

In Foafnaut the Wasm check is 9× (BubblePopJS) and 17× (QuickJS-NG) faster than the same
check in page JavaScript, and cheaper than the force step it guards; in Chrome V8's JIT
runs the JavaScript check slightly faster than the i64 Wasm at 500 nodes (1.07 against
1.32 ms), both far inside a frame. Whole frames of the demo graph's start (120 frames of
16 ms): verified page 1.61 ms (BubblePopJS) and 10.5 ms (QuickJS-NG) a busy frame; the
original explorer 1.64 and 7.31 ms. At 500 nodes the force step, not the check, is what
does not fit a Foafnaut frame.

No cost to other pages: nothing in the engine, prelude or start path changed; the new
Lean modules are not in the engine's module list (`build-web-render.sh`), so
`web-render.wasm` and the dylib are unchanged. Lean check time: `FoafCheckBinary` 60–90 s
alone and 244 s in a loaded merge build (the decoder evaluated in the kernel), `FoafCheck` about 15 s, the rest a few
seconds each.

## 8. Not done: stage 2, the force step

The page's springs and repulsion are JavaScript floats, and are not proved. A proof of
them on the binary would need either float semantics in the spec layer (all float
operators are opaque there today) or a fixed-point formulation in both Lean and Wasm;
the spring needs a square root (an integer Newton loop) and the repulsion a division, so
the obligations are bounds and termination of that loop, beyond what `SpecWPOps` covers
(`div_s`, `rem`, shifts). With the certificate in place the force step carries no safety
claim, so stage 2 is a nice-to-have.

## 9. Later: WGSL

A WGSL compute-shader version would need a semantics for the WGSL subset in Lean: PageGpu
has the AST and the validator, not an execution semantics. The pieces: values (i32, u32,
vectors) and their arithmetic with WGSL's wrapping rules; storage buffers as a byte map
with the same little-endian encoding lemmas as here; a single invocation's structured
statements (`loop`, `if`, `break`) in the same `Sem` style; then the parallel part, which
is new: workgroups and barriers, and a proof that invocations write disjoint ranges (here
one invocation per node writing its own flag), so the parallel result equals a sequential
one. The overlap check is a good first kernel for it: one invocation per node, read-only
input, one write each.

## 10. Rebuild and recheck

```sh
labs/demos/foafnaut/wasm/build.sh            # re-assemble; rewrite both byte copies
labs/demos/foafnaut/wasm/build.sh --check    # in test.sh: the copies are the assembler output
cd formal/lean4 && lake build WasmVM         # includes Proofs/SpecWP*, FoafCheck*
deno run --allow-read --allow-write --allow-ffi --allow-env labs/demos/foafnaut/wasm/check_bench.ts
```
