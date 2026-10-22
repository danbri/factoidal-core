import L4Factoidal.RIF.Engine

namespace L4Factoidal.RIF.NumericTests
private def n (s : String) (dt : String := "integer") := gLit s (xsdNs ++ dt)

-- Regressions: all failed before the shared-value numeric migration.
#guard evalFunc "numeric-add" [n "1.25" "decimal", n "2"] == some (n "3.25" "decimal")
#guard evalFunc "numeric-multiply" [n "1.5" "decimal", n "2"] == some (n "3" "decimal")
#guard evalFunc "numeric-divide" [n "5", n "2"] == some (n "2.5" "decimal")
#guard evalFunc "numeric-integer-divide" [n "-5", n "2"] == some (n "-2")
#guard evalFunc "numeric-integer-mod" [n "-5", n "2"] == some (n "-1")
#guard evalFunc "numeric-mod" [n "4.5" "decimal", n "1.2" "decimal"] == some (n "0.9" "decimal")
#guard evalPred "numeric-equal" [n "16777217" "float", n "16777216" "float"] == .yes
#guard evalPred "numeric-equal" [n "NaN" "double", n "NaN" "double"] == .no
#guard evalPred "numeric-less-than" [n "0", n "INF" "double"] == .yes
#guard evalPred "numeric-greater-than-or-equal" [n "NaN" "float", n "0"] == .no

private def resultValue (op : String) (args : List GTerm) := (evalFunc op args).bind numericValue?
private def expected (s : String) (dt : String := "double") := numericValue? (n s dt)

#guard resultValue "numeric-add" [n "16777216" "float", n "1"] == expected "16777216" "float"
#guard resultValue "numeric-add" [n "16777216" "float", n "1" "double"] == expected "16777217"
#guard resultValue "numeric-add" [n "0.1" "double", n "0.2" "double"] == expected "0.30000000000000004"
#guard resultValue "numeric-multiply" [n "3.4e38" "float", n "2"] == expected "INF" "float"
#guard resultValue "numeric-divide" [n "1" "double", n "-0" "double"] == expected "-INF"
#guard resultValue "numeric-divide" [n "0" "double", n "0" "double"] == expected "NaN"
#guard resultValue "numeric-mod" [n "-0" "double", n "3"] == expected "-0"
#guard resultValue "numeric-mod" [n "3" "float", n "INF" "float"] == expected "3" "float"
#guard resultValue "numeric-mod" [n "INF" "double", n "3"] == expected "NaN"
#guard resultValue "numeric-mod" [n "3" "double", n "0"] == expected "NaN"
#guard evalFunc "numeric-integer-divide" [n "-3.5" "decimal", n "3"] == some (n "-1")
#guard evalFunc "numeric-integer-divide" [n "-3", n "-2"] == some (n "1")
#guard evalFunc "numeric-integer-divide" [n "3.1e1" "double", n "6"] == some (n "5")
#guard evalFunc "numeric-integer-divide" [n "3", n "INF" "double"] == some (n "0")
#guard evalFunc "numeric-integer-divide" [n "INF" "double", n "3"] == none
#guard evalFunc "numeric-integer-divide" [n "3", n "NaN" "double"] == none
#guard evalFunc "numeric-integer-divide" [n "1", n "-0" "float"] == none
#guard evalFunc "numeric-integer-divide" [n "1e308" "double", n "1e-308" "double"] == none
#guard evalFunc "numeric-divide" [n "1", n "0"] == none
#guard evalFunc "numeric-mod" [n "1.5" "decimal", n "0"] == none
#guard evalFunc "numeric-add" [n "128" "byte", n "1"] == none
#guard evalFunc "numeric-add" [n "1" "string", n "1"] == none
#guard evalFunc "numeric-add" [n "1" "boolean", n "1"] == none
#guard evalPred "numeric-equal" [n "bad" "double", n "1"] == .unknown
#guard evalPred "numeric-not-equal" [n "NaN" "double", n "1"] == .yes
#guard evalPred "numeric-less-than-or-equal" [n "NaN" "double", n "1"] == .no
#guard evalPred "numeric-equal" [n "9007199254740993" "double", n "9007199254740992" "double"] == .yes
#guard evalPred "numeric-equal" [n "1e-50" "float", n "0"] == .yes
#guard evalPred "numeric-equal" [n "-0" "double", n "0"] == .yes
#guard evalPred "numeric-equal" [n "INF" "double", n "INF" "float"] == .yes
#guard evalPred "numeric-less-than" [n "-INF" "float", n "0"] == .yes
#guard evalFunc "numeric-add" [n "127" "byte", n "1" "byte"] == some (n "128")
#guard addDec "1.25" "2.5" == some "3.75"
#guard subDec "-1.25" "2.5" == some "-3.75"
#guard mulDec "-1.25" "2.5" == some "-3.125"
#guard numericLex (n "16777217" "float") == some "16777216"

-- Precision scales with magnitude instead of erasing small decimal quotients.
private def tiny := "0." ++ String.ofList (List.replicate 50 '0') ++ "1"
#guard evalFunc "numeric-divide" [n tiny "decimal", n "2"] ==
  some (n ("0." ++ String.ofList (List.replicate 51 '0') ++ "5") "decimal")
#guard (evalFunc "numeric-divide" [n "1", n "3"]).isSome

-- A decimal function result participates in actual rule matching.
private def rule : Rule :=
  { head := .pos "urn:answer" iriSpace [.var "x"]
    body := some (.atom (.equal (.var "x")
      (.external (funcNs ++ "numeric-add") [.const "1.25" (xsdNs ++ "decimal"), .const "2" (xsdNs ++ "integer")])))}
#guard entails [rule] [] (.atom (.pos "urn:answer" iriSpace [.const "3.25" (xsdNs ++ "decimal")])) 3 == .holds

end L4Factoidal.RIF.NumericTests
