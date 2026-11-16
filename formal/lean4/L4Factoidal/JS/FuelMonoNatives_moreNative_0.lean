import L4Factoidal.JS.FuelMonoNativeParts

/-! Fuel monotonicity of `Natives.moreNative`, part 0 of 4 (`JS/FuelMonoNativeParts.lean`). -/

namespace L4Factoidal.JS.FuelMono
open L4Factoidal.JS

variable {H : Type}

set_option maxHeartbeats 0
set_option linter.unusedVariables false

theorem natives_moreNative_mono_0 {c1 c2 : CoreFn H} (hc : ∀ op, Le (c1 op) (c2 op))
    (id : Native) (hp : nativePart id = 0) (thisV : Value) (args : Array Value) (nt : Option Value) :
    Le (Natives.moreNative c1 id thisV args nt) (Natives.moreNative c2 id thisV args nt) := by
  unfold Natives.moreNative
  fuel_walk

end L4Factoidal.JS.FuelMono
