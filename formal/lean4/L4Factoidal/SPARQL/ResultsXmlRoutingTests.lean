import L4Factoidal.SPARQL.ResultsXmlRouting

namespace L4Factoidal.SPARQL
open L4Factoidal.RDF

private def literalResult (text : String) : QueryResult :=
  .bindings ["value"] [[("value", .literal ⟨
    { lexicalForm := text, datatype := xsdString, langTag := none, direction := none }, rfl⟩)]]

private def refused (report : SrxReport) : Bool :=
  match report with
  | .diagnostic error => !error.isEmpty
  | .xml _ _ _ => false

#guard (QueryResult.boolean true).toSrxReport.xml? == some (QueryResult.boolean true).toSrx
#guard (QueryResult.boolean false).toSrxReport.xml? == some (QueryResult.boolean false).toSrx
#guard (QueryResult.bindings [] []).toSrxReport.xml? == some (QueryResult.bindings [] []).toSrx
-- Escaping is preserved, including entity-looking data and supplementary characters.
#guard (literalResult "<&>\"' &amp; 😀").toSrxReport.xml? ==
  some (literalResult "<&>\"' &amp; 😀").toSrx
#guard (literalResult "\t\n\r").toSrxReport.xml?.isSome
#guard (literalResult (String.singleton (Char.ofNat 0xFFFD))).toSrxReport.xml?.isSome
#guard (literalResult (String.singleton (Char.ofNat 0x10000))).toSrxReport.xml?.isSome
#guard (literalResult (String.singleton (Char.ofNat 0x10FFFF))).toSrxReport.xml?.isSome
-- XML 1.0 forbidden characters are refused, never removed/replaced/escaped to invalid references.
#guard refused (literalResult (String.singleton (Char.ofNat 0))).toSrxReport
#guard refused (literalResult (String.singleton (Char.ofNat 1))).toSrxReport
#guard refused (literalResult (String.singleton (Char.ofNat 8))).toSrxReport
#guard refused (literalResult (String.singleton (Char.ofNat 11))).toSrxReport
#guard refused (literalResult (String.singleton (Char.ofNat 12))).toSrxReport
#guard refused (literalResult (String.singleton (Char.ofNat 31))).toSrxReport
#guard refused (literalResult (String.singleton (Char.ofNat 0xFFFE))).toSrxReport
#guard refused (literalResult (String.singleton (Char.ofNat 0xFFFF))).toSrxReport
-- Admission checks the full serialization, including variable names/attributes.
#guard refused (QueryResult.bindings ["bad" ++ String.singleton (Char.ofNat 1)] []).toSrxReport
-- Current SRX directional-literal output uses an undeclared its prefix. This
-- public context parser accepts it; do not claim namespace validation here.
private def directionalResult : QueryResult := .bindings ["value"] [[("value", .literal ⟨
  { lexicalForm := "hello", datatype := rdfDirLangString,
    langTag := some "en", direction := some .ltr }, rfl⟩)]]
#guard directionalResult.toSrxReport.xml?.isSome
#guard (parseSrxDocument "<a xmlns='urn:a'/>").isOk
#guard (parseSrxDocument "<a its:dir='ltr'/>").isOk

#print axioms QueryResult.toSrxReport_exact
end L4Factoidal.SPARQL

#print axioms L4Factoidal.SPARQL.QueryResult.toSrxReport_refused

#print axioms L4Factoidal.SPARQL.QueryResult.toSrxReport_accepted
