/- F&O 4.0 fn:parse-xml / fn:parse-xml-fragment option admission.
   QT4 parse-xml-fragment-505/506/507. Retaining locations is optional;
   accepting the boolean option and rejecting wrong types is not optional.
   These closed kernel checks cover parseOpts, not the full query evaluator. -/
import L4Factoidal.XPath4.XmlParse

namespace L4Factoidal.XPath4.XmlParseOptionTests

private def opts (key : String) (value : Seq) : Seq :=
  [.map [(Atomic.ofStr key, value)]]
private def outcome (options : Seq) (env : Env := {}) : String :=
  match parseOpts env options with
  | .ok _ => "ok"
  | .error e => e.code

example : outcome (opts "retain-location" (sBool true)) = "ok" := by decide
example : outcome (opts "retain-location" (sBool false)) = "ok" := by decide
example : outcome (opts "retain-location" (sStr "yes")) = "XPTY0004" := by decide
example : outcome (opts "retain-location" (sInt 1)) = "XPTY0004" := by decide
example : outcome (opts "retain-location" []) = "XPTY0004" := by decide
example : outcome (opts "retain-location" (sBool true ++ sBool false)) = "XPTY0004" := by decide
example : outcome [] = "ok" := by decide
example : outcome (opts "unknown-option" (sBool true)) = "XPTY0004" := by decide
example : outcome (opts "strip-space" (sStr "all")) = "ok" := by decide
example : outcome (opts "strip-space" (sStr "invalid")) = "XPTY0004" := by decide
#guard outcome (opts "xsd-validation" (sStr "invalid")) == "FODC0008"
-- Official QT4 fn-parse-xml/parse-xml-437: option value versus option type.
#guard outcome (opts "xsd-validation" (sStr "sporadic")) == "FODC0008"
#guard outcome (opts "xsd-validation" (sBool true)) == "XPTY0004"
#guard outcome (opts "xsd-validation" (sInt 1)) == "XPTY0004"
#guard outcome (opts "xsd-validation" []) == "XPTY0004"
#guard outcome (opts "xsd-validation" (sStr "strict" ++ sStr "lax")) == "XPTY0004"
#guard outcome (opts "xsd-validation" (sStr "skip")) == "ok"
#guard outcome (opts "xsd-validation" (sStr "strict")) == "ok"
#guard outcome (opts "xsd-validation" (sStr "lax")) == "ok"
#guard outcome (opts "xsd-validation" [.atom (Atomic.ofUri "strict")]) == "ok"
#guard outcome (opts "xsd-validation" [.atom (Atomic.untypedOf "lax")]) == "ok"
example : outcome (opts "trust-external" (sStr "yes")) = "XPTY0004" := by decide
example : outcome (opts "dtd-validation" (sBool true)) { dtdValidation := false } = "FODC0013" := by decide
example : outcome (opts "xinclude" (sBool true)) { xinclude := false } = "FODC0013" := by decide

end L4Factoidal.XPath4.XmlParseOptionTests
