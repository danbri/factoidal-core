/-
Wasm.Ops.LiteralValue — the value of a literal and the literal of a
JavaScript value, over the dispatch ABI
(https://github.com/danbri/factoidal/issues/1051 items 1, 2 and 3). Every
decision is in `L4Factoidal.RDF.LiteralValue`; this module reads and writes
JSON.

  literalValue(termJson)
    termJson: a literal as a SPARQL 1.1 Results JSON term object
      {"type":"literal","value":LEX,"datatype":IRI?,"xml:lang":TAG?,
       "its:dir":"ltr"|"rtl"?} (no `datatype`: xsd:string, or
      rdf:langString / rdf:dirLangString when `xml:lang` is present).
    -> {"ok":true,"datatype":IRI,"recognized":B,"valid":B,"value":{…},
        "canonical":LEX}
       (`valid` only when `recognized`; `value` and `canonical` only when
       valid and the datatype has a value model; the value shapes are in
       the header of `RDF/LiteralValue.lean`).

  literalFromValue(valueJson, datatype)
    valueJson: {"js":"number"|"bigint"|"boolean"|"string"|"date","v":TEXT}
      (a number as its `Number::toString` text, `-0` as "-0"; a Date as the
      text of `getTime()`), the encoding of `Wasm/Ops/ExtFns.lean`.
    datatype: "" (the engine's table, `XSD.JsValue.jsLiteral`), or an XSD
      built-in by IRI or local name.
    -> {"ok":true,"value":LEX,"datatype":IRI}, or an error envelope with code
       `literal.value` when the value is not in the datatype's value space.

Both ops are pure and in the core table.
-/
import Wasm.Ops.Support
import L4Factoidal.RDF.LiteralValue

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.RDF

/-- `literalValue(termJson)`. -/
def literalValueOp (termJson : String) : String :=
  match L4Factoidal.JSON.parseJson? termJson with
  | none => errJson "literalValue: the argument is not JSON"
  | some j =>
    match j.getString? "type", j.getString? "value" with
    | some t, _ =>
        if t != "literal" then errJson s!"literalValue: the term is not a literal (type '{t}')"
        else literalValueOf j
    | none, some _ => literalValueOf j
    | none, none => errJson "literalValue: not a term (no 'value' member)"
where
  literalValueOf (j : Json) : String :=
    match j.getString? "value" with
    | none => errJson "literalValue: not a term (no 'value' member)"
    | some lex =>
      let lang := j.getString? "xml:lang"
      let dir := j.getString? "its:dir"
      let dt := match j.getString? "datatype", lang, dir with
        | some d, _, _ => d
        | none, some _, none => rdfLangString.val
        | none, some _, some _ => rdfDirLangString.val
        | none, none, _ => xsdString.val
      let a := LiteralValue.analyze lex dt lang dir
      okWith (a.fields dt)

/-- `literalFromValue(valueJson, datatype)`. -/
def literalFromValueOp (valueJson hint : String) : String :=
  match L4Factoidal.JSON.parseJson? valueJson with
  | none => errJson "literalFromValue: the value argument is not JSON"
  | some j =>
    match j.getString? "js", (match j.field? "v" with
        | some (.string x) => some x
        | some (.bool b) => some (if b then "true" else "false")
        | _ => none) with
    | some tag, some v =>
        let hintB := if hint.isEmpty then some none else (LiteralValue.hintOf? hint).map some
        match hintB with
        | none => errJson s!"literalFromValue: '{hint}' is not an XML Schema 1.1 built-in datatype the engine has"
        | some h =>
          match LiteralValue.jsValueLiteral tag v h with
          | .ok (b, lex) => okWith [("value", .string lex), ("datatype", .string b.iri)]
          | .error e => errJson e
    | _, _ => errJson "literalFromValue: expected {\"js\":TYPE,\"v\":TEXT}"

/-- The op names of this module (pure, in the core table). -/
def literalOpNames : List String := ["literalValue", "literalFromValue"]

/-- Serve one of `literalOpNames`, or `none`. -/
def callLiteral (op : String) (args : List String) : Option String :=
  match op, args with
  | "literalValue", [a] => some (literalValueOp a)
  | "literalValue", _ => some (errJson s!"literalValue expects 1 argument, got {args.length}")
  | "literalFromValue", [a] => some (literalFromValueOp a "")
  | "literalFromValue", [a, b] => some (literalFromValueOp a b)
  | "literalFromValue", _ =>
      some (errJson s!"literalFromValue expects 1 or 2 arguments, got {args.length}")
  | _, _ => none

/-! ## Build-time checks -/

#guard literalValueOp "{\"type\":\"literal\",\"value\":\"01\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#integer\"}" ==
  "{\"ok\":true,\"datatype\":\"http://www.w3.org/2001/XMLSchema#integer\",\"recognized\":true,\"valid\":true,\"value\":{\"kind\":\"decimal\",\"decimal\":\"1\",\"integer\":true,\"number\":1},\"canonical\":\"1\"}"
#guard literalValueOp "{\"type\":\"literal\",\"value\":\"x\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#integer\"}" ==
  "{\"ok\":true,\"datatype\":\"http://www.w3.org/2001/XMLSchema#integer\",\"recognized\":true,\"valid\":false}"
#guard literalValueOp "{\"type\":\"literal\",\"value\":\"a\"}" ==
  "{\"ok\":true,\"datatype\":\"http://www.w3.org/2001/XMLSchema#string\",\"recognized\":true,\"valid\":true,\"value\":{\"kind\":\"string\",\"string\":\"a\"},\"canonical\":\"a\"}"
#guard literalValueOp "{\"type\":\"literal\",\"value\":\"a\",\"xml:lang\":\"en-GB\"}" ==
  "{\"ok\":true,\"datatype\":\"http://www.w3.org/1999/02/22-rdf-syntax-ns#langString\",\"recognized\":true,\"valid\":true,\"value\":{\"kind\":\"langString\",\"string\":\"a\",\"language\":\"en-gb\"},\"canonical\":\"a\"}"
#guard (literalValueOp "{\"type\":\"uri\",\"value\":\"http://e/\"}").startsWith "{\"ok\":false"
#guard (literalValueOp "not json").startsWith "{\"ok\":false"
#guard literalFromValueOp "{\"js\":\"number\",\"v\":\"99\"}" "int" ==
  "{\"ok\":true,\"value\":\"99\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#int\"}"
#guard literalFromValueOp "{\"js\":\"number\",\"v\":\"99\"}" "" ==
  "{\"ok\":true,\"value\":\"99\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#integer\"}"
#guard literalFromValueOp "{\"js\":\"boolean\",\"v\":true}" "" ==
  "{\"ok\":true,\"value\":\"true\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#boolean\"}"
#guard (literalFromValueOp "{\"js\":\"number\",\"v\":\"1.5\"}" "int").startsWith "{\"ok\":false"
#guard (literalFromValueOp "{\"js\":\"number\",\"v\":\"1\"}" "http://example.org/dt").startsWith "{\"ok\":false"
#guard callLiteral "literalFromValue" [] == some "{\"ok\":false,\"error\":\"literalFromValue expects 1 or 2 arguments, got 0\"}"
#guard callLiteral "other" [] == none

end L4Wasm.Ops
