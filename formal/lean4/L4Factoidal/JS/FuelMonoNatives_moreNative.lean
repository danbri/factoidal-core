import L4Factoidal.JS.FuelMonoNatives

/-! Fuel monotonicity of `Natives.moreNative` (see `JS/FuelMonoNatives.lean`). -/

namespace L4Factoidal.JS.FuelMono
open L4Factoidal.JS

variable {H : Type}

set_option maxHeartbeats 0
set_option linter.unusedVariables false

theorem natives_moreNative_mono {c1 c2 : CoreFn H} (hc : ∀ op, Le (c1 op) (c2 op))
    (id : Native) (thisV : Value) (args : Array Value) (nt : Option Value) :
    Le (Natives.moreNative c1 id thisV args nt) (Natives.moreNative c2 id thisV args nt) := by
  unfold Natives.moreNative
  fuel_walk

end L4Factoidal.JS.FuelMono
