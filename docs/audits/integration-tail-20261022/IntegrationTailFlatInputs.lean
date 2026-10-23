import L4Factoidal.Regex.Profiles
import L4Factoidal.RIF.Engine
import L4Factoidal.OWL.CertNames

-- Focused Lean evaluator controls. The separate emitted-C audit checks that
-- flat loops compile to jumps; this file does not claim a Wasm execution.
open L4Factoidal

#print axioms Regex.Ecma.lower_eq_lowerTR
#print axioms Regex.Profiles.xsdLiterals_eq_xsdLiteralsTR
#print axioms Regex.quoteReplacement_eq_quoteReplacementTR
#print axioms RIF.groundMatch_eq_groundMatchTR
#print axioms RIF.groundMatches_eq_groundMatchesTR
#print axioms RIF.matchTm_eq_matchTmTR
#print axioms OWL.CertNames.frame_eq_frameTR

private def check (name : String) (actual : Bool) : IO Unit := do
  if actual then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}")

def main : IO Unit := do
  let n := 100000
  check "ecma-flat-dot-100000" ((Regex.Ecma.lower (List.replicate n 46) false).length == n * 7)
  check "xsd-flat-anchors-100000" ((Regex.Profiles.xsdLiterals (List.replicate n '^') false).length == n * 2)
  check "replacement-flat-dollar-100000" ((Regex.quoteReplacement (List.replicate n 36)).length == n * 2)
  check "cert-name-flat-characters-100000" ((OWL.CertNames.frame (List.replicate n '+')).length == n * 2 + 1)
  let int1 := RIF.GTerm.const "1" (RIF.xsdNs ++ "integer")
  let int01 := RIF.GTerm.const "01" (RIF.xsdNs ++ "integer")
  check "ground-list-value-equality-100000"
    (RIF.groundMatch (.list (List.replicate n int1)) (.list (List.replicate n int01)) == .yes)
  let unsupported1 := RIF.GTerm.const "a" "urn:unsupported-space"
  let unsupported2 := RIF.GTerm.const "b" "urn:unsupported-space"
  check "ground-list-unknown-100000"
    (RIF.groundMatches (List.replicate n unsupported1) (List.replicate n unsupported2) == .unknown)
  check "ground-list-no-controls-unknown"
    (RIF.groundMatches [unsupported1, int1] [unsupported2, .const "2" (RIF.xsdNs ++ "integer")] == .no)
  let result := RIF.matchTm [] (.list (List.replicate n (.var "x"))) (.list (List.replicate n int1))
  check "pattern-list-binding-100000" (result.1.isSome && !result.2)
  check "pattern-list-late-mismatch"
    ((RIF.matchTm [] (.list [.var "x", .var "x"]) (.list [int1, .const "2" (RIF.xsdNs ++ "integer")])).1.isNone)

#eval main
