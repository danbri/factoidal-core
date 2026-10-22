/- SPARQL §17.4.3.13 / RFC 4647 basic filtering through both callers. -/
import L4Factoidal.SHACL.NodeExpr

namespace L4Factoidal.SHACL.LanguageBridgeTests
open RDF SPARQL

private def str (s : String) : Term := .literal (Literal.string s)
private def run (a b : Term) : EvalResult :=
  (Expr.functionCall langMatchesIri [.var "a", .var "b"]).eval [("a", a), ("b", b)]

#guard sparqlApply "langMatches" [str "EN-us", str "en"] == [mkBoolLit true]
#guard sparqlApply "langMatches" [str "en-US", str "EN"] == [mkBoolLit true]
#guard sparqlApply "langMatches" [str "enochian", str "en"] == [mkBoolLit false]
#guard sparqlApply "langMatches" [str "de-Latn-DE", str "de-*-DE"] == [mkBoolLit false]
#guard sparqlApply "langMatches" [str "", str "*"] == [mkBoolLit false]
#guard sparqlApply "langMatches" [str "en", str "*"] == [mkBoolLit true]

private def invalid : List Term :=
  [.literal (mkTypedLiteral "12" xsdInteger), .literal (Literal.langString "en" "en"),
   .literal (Literal.dirLangString "en" "en" .ltr), .iri ⟨"urn:en", rfl⟩, .bnode "en"]
#guard invalid.all (fun v => run v (str "*") == .error)
#guard invalid.all (fun v => run (str "en") v == .error)
#guard invalid.all (fun v => sparqlApply "langMatches" [v, str "*"] == [])
#guard invalid.all (fun v => sparqlApply "langMatches" [str "en", v] == [])
#guard sparqlApply "langMatches" [str "en"] == []
#guard sparqlApply "langMatches" [str "en", str "en", str "en"] == []
#guard run (str "EN-us") (str "en") == .bool true

end L4Factoidal.SHACL.LanguageBridgeTests
