import L4Factoidal.Rendering.SfntProfile

/-! Base64 of font files. `labs/demos/foafnaut/native_html_test.ts` draws a real
font through the engine; `outline-compare.sh` checks its outlines against FreeType. -/
namespace L4Factoidal.Rendering.SfntProfileTests
open SfntProfile

private def bytes (s : String) : Option (List UInt8) := (decodeBase64 s).map (·.toList)

example : bytes "" = some [] := by native_decide
example : bytes "TWFu" = some [77,97,110] := by native_decide
example : bytes "TWE=" = some [77,97] := by native_decide
example : bytes "TQ==" = some [77] := by native_decide
example : bytes "/+8A" = some [255,239,0] := by native_decide
example : bytes "TWF" = none := by native_decide
example : bytes "TW!u" = none := by native_decide
example : bytes "T=Fu" = none := by native_decide

end L4Factoidal.Rendering.SfntProfileTests
