import L4Factoidal.JS.FuelMono

/-! # Fuel monotonicity of the built-in dispatchers

`Natives.callNative`, `Natives.extraNative`, `Natives.moreNative` and `Natives.iterEach` are plain
definitions outside the evaluator's mutual block (`JS/Interp.lean`): they reach the evaluator
only through their argument `core : CoreFn H`. Each lemma here says that with two dispatchers
related by `Le` at every request, the built-in is related by `Le` too. The block's own
`callNative` (and the others) at fuel `n + 1` is the built-in with `coreRun n`, so its step in
`JS/FuelMonoSteps*.lean` is this lemma with the induction hypothesis for `coreRun`. -/

namespace L4Factoidal.JS.FuelMono
open L4Factoidal.JS

variable {H : Type}

set_option maxHeartbeats 0
set_option linter.unusedVariables false

theorem natives_iterEach_mono {c1 c2 : CoreFn H} (hc : ∀ op, Le (c1 op) (c2 op)) (it : Value)
    {f1 f2 : Value → JSM H Unit} (hf : ∀ v, Le (f1 v) (f2 v)) :
    Le (Natives.iterEach c1 it f1) (Natives.iterEach c2 it f2) := by
  unfold Natives.iterEach
  fuel_walk

theorem natives_extraNative_mono {c1 c2 : CoreFn H} (hc : ∀ op, Le (c1 op) (c2 op))
    (id : Native) (thisV : Value) (args : Array Value) (nt : Option Value) :
    Le (Natives.extraNative c1 id thisV args nt) (Natives.extraNative c2 id thisV args nt) := by
  unfold Natives.extraNative
  fuel_walk

end L4Factoidal.JS.FuelMono
