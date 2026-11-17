# Presenter synchronous refinement — 2026-11-17

Statement before implementation: for a synchronous engine which supplies a frame newer than
any shown frame on each band request, the independently defined stage-0 loop has the same
final presenter state and output list as `Presenter.run` on the expanded trace. The expansion
places the completed frame immediately after its requesting external input and before the
next external input. External inputs are scroll, resize and display tick.

The model preserves the specification's suppression of an already requested scroll. A tick
presents the shown frame using `offsetOf`. The engine is an arbitrary pure function of state
and requested scroll; freshness is its explicit hypothesis. This statement proves no pixel
identity, timing, JavaScript/FFI correctness, scheduler fairness or seqlock implementation.

Auxiliary statements: `run` composes over list append; appending a publication makes it the
latest mailbox value for both frames and requests. These are abstract list contracts;
randomised host tests must separately check their concrete atomic implementation.

## Draft result and checks

The model and seven lemmas are in `L4Factoidal/Presenter/Spec.lean`, already imported by the
library root. Main statement: `L4Factoidal.Presenter.run_synchronous_eq_stage0`. Helpers:
`run_append`, `step_fresh_frame`, `stage0Request_refines`, `stage0Step_refines`,
`latestWins_append`, `lastRequestSeen_append`. A sample engine proves that `FreshEngine`
is inhabited; guards exercise kept scroll, new band and resize.

`python3 tools/lean-hygiene-audit.py` passed: 0 forbidden hatches and 163 existing partial
definitions, unchanged. `python3 tools/lean-unbuilt-modules.py --gate` found two unrelated
unreachable modules (`DOM.XPath.Theorems`, `Rendering.ImportTree`); Presenter is reached.
`git diff --check` passed at the draft checkpoint.

Local type-check command used the required lock and explicit Lean project directory:
`leanlock.sh /Users/danbri/working/factoidal-presenter1/formal/lean4 lean -M 2048 L4Factoidal/Presenter/Spec.lean`.
It exited 3 before Lean ran: the sandbox hides the process table, so the lock refused to
run. The draft is not yet type-checked. The seven `#print axioms` commands are in the source
for the build to record; no axiom output is claimed here. Cloud checking remains required.

## Trace execution and compilation

The synchronous model runners are `noncomputable`: they are used in proofs and kernel
examples, not in the engine. The executable `run` has a tail-recursive replacement `runFast`.
`runAcc_eq` states the accumulator invariant (outputs reversed before the initial accumulator);
`run_eq_runFast` is the `@[csimp]` equality. This avoids new input-length C recursion or an
audit exemption for the model. These two additional lemmas also have `#print axioms` commands.
The cloud build still has to check these edits; no local lock bypass was used.

## Cloud proof result

Build 44142386010, Linux job 134248559685, compiled Presenter.Spec from
19b7477e088608488440c1250c8312f71e73ffd5. All nine printed theorem dependencies
are permitted: `run_eq_runFast` uses `propext` and `Quot.sound`; the other eight,
including `run_synchronous_eq_stage0`, use `propext` only. No `sorryAx` occurs in
these reports. The full build failed next on a record syntax error in Wire.stateOf;
that constructor is repaired separately. This result proves the stated model
refinement, not host execution, pixel parity or measured performance.
