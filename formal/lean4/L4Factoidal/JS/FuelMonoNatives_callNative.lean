import L4Factoidal.JS.FuelMonoNatives_callNative_3

/-! Fuel monotonicity of `Natives.callNative`, from its 4 parts. -/

namespace L4Factoidal.JS.FuelMono
open L4Factoidal.JS

variable {H : Type}

theorem natives_callNative_mono {c1 c2 : CoreFn H} (hc : ∀ op, Le (c1 op) (c2 op))
    (id : Native) (thisV : Value) (args : Array Value) (nt : Option Value) :
    Le (Natives.callNative c1 id thisV args nt) (Natives.callNative c2 id thisV args nt) := by
  have hlt := nativePart_lt id
  match h : nativePart id with
  | 0 => exact natives_callNative_mono_0 hc id h thisV args nt
  | 1 => exact natives_callNative_mono_1 hc id h thisV args nt
  | 2 => exact natives_callNative_mono_2 hc id h thisV args nt
  | 3 => exact natives_callNative_mono_3 hc id h thisV args nt
  | _ + 4 => omega

end L4Factoidal.JS.FuelMono
