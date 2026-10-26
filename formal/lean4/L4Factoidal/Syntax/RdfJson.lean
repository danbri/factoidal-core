/-
L4Factoidal.Syntax.RdfJson — RDF/JSON: an RDF graph as a JSON object.

Spec: "RDF 1.1 JSON Alternate Serialization (RDF/JSON)", W3C Working
Group Note, https://www.w3.org/TR/rdf-json/ . A graph is an object from
subject to an object from predicate IRI to an array of object-term
objects:

    { "http://ex/s": { "http://ex/p": [ { "type": "literal",
                                            "value": "x", "lang": "en" } ] } }

`type` is `uri`, `bnode` or `literal`; a blank node subject or object
is written `_:label`; a literal may carry `lang` or `datatype`. The
Note describes triples only, so a dataset is serialised as the union of
its graphs, and a serialiser that is given a triple term refuses it.

## Reading numbers and booleans

The Note says `value` is a string. Real writers also emit a JSON number
(`RMLTTC0004e` ships `"value": 33`). A number or boolean with no
`datatype` is read as the literal JSON would type it, `xsd:integer`,
`xsd:double` or `xsd:boolean`, the same natural mapping RML applies to a
JSON source; read as the plain string `"33"` it would be a different
literal from the one the writer meant.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.Syntax.RdfJson

open L4Factoidal.RDF
open L4Factoidal.JSON

private def xsdIri (n : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ n

/-- One object term as the Note's object-term JSON. -/
def termToJson : Term → Except String Json
  | .iri i => .ok (.object [("value", .string i.val), ("type", .string "uri")])
  | .bnode b => .ok (.object [("value", .string ("_:" ++ b)), ("type", .string "bnode")])
  | .literal l =>
      let l := l.val
      let base : List (String × Json) :=
        [("value", .string l.lexicalForm), ("type", .string "literal")]
      match l.langTag with
      | some tag => .ok (.object (base ++ [("lang", .string tag)]))
      | none =>
          if l.datatype.val == xsdIri "string" then .ok (.object base)
          else .ok (.object (base ++ [("datatype", .string l.datatype.val)]))
  | .tripleTerm .. => .error "RDF/JSON cannot carry a triple term"

private def subjectKey : Subject → String
  | .iri i => i.val
  | .bnode b => "_:" ++ b

/-- Group triples by subject and then predicate, keeping first-seen
    order, and render the whole graph. -/
def graphToJson (g : Graph) : Except String Json := do
  let subjects : List String := g.foldl (fun acc t =>
    let k := subjectKey t.s
    if acc.contains k then acc else acc ++ [k]) []
  let mut out : List (String × Json) := []
  for s in subjects do
    let ts := g.filter (fun t => subjectKey t.s == s)
    let preds : List String := ts.foldl (fun acc t =>
      if acc.contains t.p.val then acc else acc ++ [t.p.val]) []
    let mut pj : List (String × Json) := []
    for p in preds do
      let mut objs : List Json := []
      for t in ts.filter (fun t => t.p.val == p) do
        objs := objs ++ [← termToJson t.o]
      pj := pj ++ [(p, Json.array objs)]
    out := out ++ [(s, Json.object pj)]
  return Json.object out

def graphToRdfJson (g : Graph) : Except String String :=
  (graphToJson g).map toStringCompact

/-- The literal a JSON `value` denotes, given the optional `lang` and
    `datatype`. -/
private def literalOf (v : Json) (lang dt : Option String) : Except String Term :=
  let lexAndNatural : Option (String × Option String) :=
    match v with
    | .string s => some (s, none)
    | .number n =>
        some (n, some (xsdIri (if n.toList.any (fun c => c == '.' || c == 'e' || c == 'E')
                                then "double" else "integer")))
    | .bool b => some ((if b then "true" else "false"), some (xsdIri "boolean"))
    | _ => none
  match lexAndNatural with
  | none => .error "a literal value is a string, number or boolean"
  | some (lex, natural) =>
      match lang with
      | some tag => .ok (.literal (Literal.langString lex tag))
      | none =>
          let dtStr := match dt with
            | some d => d
            | none => natural.getD (xsdIri "string")
          if h : isIri dtStr then
            if hw : (⟨dtStr, h⟩ : WfIri) != rdfLangString && (⟨dtStr, h⟩ : WfIri) != rdfDirLangString then
              .ok (.literal ⟨{ lexicalForm := lex, datatype := ⟨dtStr, h⟩, langTag := none,
                               direction := none }, by simpa [literalWf] using hw⟩)
            else .ok (.literal (Literal.string lex))
          else .error s!"'{dtStr}' is not a datatype IRI"

private def termOfJson (j : Json) : Except String Term := do
  let value ← match j.field? "value" with
    | some v => pure v
    | none => throw "an object term has a value"
  let type ← match (j.field? "type").bind Json.asString? with
    | some t => pure t
    | none => throw "an object term has a type"
  match type with
  | "uri" =>
      match value with
      | .string s =>
          if h : isIri s then pure (Term.iri ⟨s, h⟩) else throw s!"'{s}' is not an IRI"
      | _ => throw "a uri value is a string"
  | "bnode" =>
      match value with
      | .string s => pure (Term.bnode (if s.startsWith "_:" then (s.drop 2).toString else s))
      | _ => throw "a bnode value is a string"
  | "literal" =>
      literalOf value ((j.field? "lang").bind Json.asString?) ((j.field? "datatype").bind Json.asString?)
  | other => throw s!"unknown term type '{other}'"

/-- Read an RDF/JSON document. A malformed document is an error, not a
    partial graph. -/
def parseRdfJson (text : String) : Except String Graph := do
  let root ← match parseJson text with
    | .ok j => pure j
    | .error _ => throw "not JSON"
  let subjects ← match root with
    | .object fs => pure fs
    | _ => throw "an RDF/JSON document is an object"
  let mut g : Graph := []
  for (s, preds) in subjects do
    let subj : Subject ←
      if s.startsWith "_:" then pure (Subject.bnode (s.drop 2).toString)
      else if h : isIri s then pure (Subject.iri ⟨s, h⟩)
      else throw s!"'{s}' is not an IRI"
    let pfs ← match preds with
      | .object fs => pure fs
      | _ => throw "a subject maps to an object of predicates"
    for (p, objs) in pfs do
      let pIri : WfIri ← if h : isIri p then pure ⟨p, h⟩ else throw s!"'{p}' is not an IRI"
      let os ← match objs with
        | .array xs => pure xs
        | _ => throw "a predicate maps to an array"
      for o in os do
        g := g ++ [{ s := subj, p := pIri, o := ← termOfJson o }]
  return g

/-! ## Build-time checks -/

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def sample : Graph :=
  [ { s := .iri (iri! "http://ex/s"), p := iri! "http://ex/p", o := .literal (Literal.string "x") }
  , { s := .iri (iri! "http://ex/s"), p := iri! "http://ex/p", o := .literal (Literal.langString "hi" "en") }
  , { s := .iri (iri! "http://ex/s"), p := iri! "http://ex/q", o := .iri (iri! "http://ex/o") }
  , { s := .bnode "b1", p := iri! "http://ex/q", o := .bnode "b2" } ]

#guard (graphToRdfJson sample).toOption ==
  some "{\"http://ex/s\":{\"http://ex/p\":[{\"value\":\"x\",\"type\":\"literal\"},{\"value\":\"hi\",\"type\":\"literal\",\"lang\":\"en\"}],\"http://ex/q\":[{\"value\":\"http://ex/o\",\"type\":\"uri\"}]},\"_:b1\":{\"http://ex/q\":[{\"value\":\"_:b2\",\"type\":\"bnode\"}]}}"
-- Written and read back, the graph is the same triples.
#guard match graphToRdfJson sample with
       | .ok t => (match parseRdfJson t with
                   | .ok g => g.length == 4 && g.all (fun t => sample.any (fun u => t == u))
                   | .error _ => false)
       | .error _ => false
-- A JSON number is read as the literal JSON would type it.
#guard match parseRdfJson "{\"http://ex/s\":{\"http://ex/p\":[{\"type\":\"literal\",\"value\":33}]}}" with
       | .ok [t] => (match t.o with
           | .literal l => l.val.lexicalForm == "33" && l.val.datatype.val == xsdIri "integer"
           | _ => false)
       | _ => false
-- A string with no datatype is a plain string; a typed one keeps its datatype.
#guard match parseRdfJson "{\"http://ex/s\":{\"http://ex/p\":[{\"type\":\"literal\",\"value\":\"33\"}]}}" with
       | .ok [t] => (match t.o with | .literal l => l.val.datatype.val == xsdIri "string" | _ => false)
       | _ => false
#guard match parseRdfJson "{\"http://ex/s\":{\"http://ex/p\":[{\"type\":\"literal\",\"value\":\"33\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#integer\"}]}}" with
       | .ok [t] => (match t.o with | .literal l => l.val.datatype.val == xsdIri "integer" | _ => false)
       | _ => false
-- Malformed documents are errors, not partial graphs.
#guard (parseRdfJson "[]").toOption.isNone
#guard (parseRdfJson "{\"s\":{}}").toOption.isNone
#guard (parseRdfJson "{\"http://ex/s\":{\"http://ex/p\":[{\"type\":\"nope\",\"value\":\"x\"}]}}").toOption.isNone
#guard (parseRdfJson "{\"http://ex/s\":{\"http://ex/p\":{\"type\":\"uri\"}}}").toOption.isNone
-- A triple term has no RDF/JSON form.
private def tripleTermGraph : Graph :=
  [{ s := .iri (iri! "http://ex/s"), p := iri! "http://ex/p", o := tt }]
where tt : Term := .tripleTerm (.iri (iri! "http://ex/a")) (iri! "http://ex/b") (.iri (iri! "http://ex/c"))
#guard (graphToRdfJson tripleTermGraph).toOption.isNone

end L4Factoidal.Syntax.RdfJson
