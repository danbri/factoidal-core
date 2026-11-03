import L4Factoidal.Dataflow.NodeSettings

namespace L4Factoidal.Dataflow
open L4Factoidal.JSON

private def refused {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

#guard refused (validateQt4Settings "xpath4Eval" [])
#guard refused (validateQt4Settings "xqueryEval" [("query", .number "1")])
#guard refused (validateQt4Settings "xslt4Transform" [("stylesheet", .string "x"), ("fetch", .bool true)])
#guard (validateQt4Settings "xpath4Eval" [("expression", .string "1")]).isOk

private def checkPublic (name key : String) (outWire : Wire) : Bool :=
  match registry.find? (·.nodeName == name) with
  | none => false
  | some e =>
    e.status == .tested && e.wireIn == .text && e.wireOut == outWire &&
    match nodeSettings e [(key, .string "text")] with
    | .error _ => false
    | .ok settings => !settings.checked && settings.status == "tested" && settings.outW == outWire

#guard checkPublic "xpath4Eval" "expression" .xdmResult
#guard checkPublic "xqueryEval" "query" .xdmResult
#guard checkPublic "xslt4Transform" "stylesheet" .xsltResult
#guard !Wire.conv .xdmResult .xml
#guard !Wire.conv .xsltResult .xml
#guard !Wire.conv .xsltResult .text
-- Existing public registry names remain present alongside the new bindings.
#guard registry.any (·.nodeName == "XPath 4.0 evaluation (XDM 4.0, F&O 4.0 subset)")
#guard registry.any (·.nodeName == "XSLT 4.0 transformation")

end L4Factoidal.Dataflow
