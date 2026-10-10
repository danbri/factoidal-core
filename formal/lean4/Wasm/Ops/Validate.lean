/-
Wasm.Ops.Validate — the SHACL and ShEx validation operations of the npm
entry (https://github.com/danbri/factoidal/issues/713 stage 3).

  shaclValidate(dataNquads, shapesNquads)
    -> {"ok":true,"conforms":true|false,"reportNquads":"…"}
  shexValidate(dataNquads, schemaText, focus, shape)
    -> {"ok":true,"verdict":true|false}

The envelopes follow the F* npm entry (`bin/npm-entry/entry_extras.ml`,
`shacl_validate_json` and `shex_validate_json`) member for member.

`shaclValidate` reads the DEFAULT graph of each argument. The shapes graph
is decoded (`SHACL.decodeShapesGraph`), the data graph is validated with
`SHACL.validateFull` (SHACL Core, SHACL-SPARQL constraints and SHACL 1.2
node expressions; the raw shapes graph is passed too, for the SPARQL
`$shapesGraph` pre-binding of SHACL §5.3.1) and the report is the graph of
`SHACL.reportToGraph`: one `sh:ValidationReport` with `sh:conforms` and one
`sh:result` per validation result, as N-Triples text. This is the pipeline
`Harness/ShaclProbe.lean` scores against the W3C SHACL test suites. Two
outcomes are refusals, not reports: a shapes graph that uses a feature the
decoder does not read (`ShapesGraph.unsupported`, the SPARQL-based target of
SHACL-AF), and a validation failure in the sense of SHACL §5.3.2 (a query
that cannot be pre-bound), which produces no report.

`shexValidate` reads the DEFAULT graph of `dataNquads`. The schema text is
ShExJ when its first non-whitespace character is `{` and ShExC otherwise —
the rule the F* entry states, and no ShExC document starts with `{`. The
focus and the shape are an IRI or `_:label`; an empty shape selects the
schema's START shape expression (`ShEx.validateStart`), any other shape is a
shape label (`ShEx.validateNode`). An `IMPORT` is not followed (no file or
network access through this entry). The F* function answered `null` outside
its decidable fragment; the Lean validator decides every schema it reads,
so `verdict` is always a boolean.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.Syntax.NTriples
import L4Factoidal.SHACL.Report
import L4Factoidal.SHACL.NodeExpr
import L4Factoidal.ShEx.FromJson
import L4Factoidal.ShEx.Compact
import L4Factoidal.ShEx.Satisfies

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- `shaclValidate(dataNquads, shapesNquads)`. -/
def shaclValidate (dataNq shapesNq : String) : String :=
  match parseNQuadsFast dataNq .rdf12 with
  | .error e => errJson s!"shaclValidate(data): {fmtParseError e}"
  | .ok dataDs =>
  match parseNQuadsFast shapesNq .rdf12 with
  | .error e => errJson s!"shaclValidate(shapes): {fmtParseError e}"
  | .ok shapesDs =>
    let shapesG := shapesDs.default
    let sg := L4Factoidal.SHACL.decodeShapesGraph shapesG
    if !sg.unsupported.isEmpty then
      errJson ("shaclValidate: the shapes graph uses a feature this validator does not read: "
               ++ String.intercalate ", " sg.unsupported)
    else
    let report := L4Factoidal.SHACL.validateFull dataDs.default shapesG sg {}
    match report.failure with
    | some why => errJson s!"shaclValidate: validation failure (SHACL 5.3.2): {why}"
    | none =>
      match Graph.toNTriples (L4Factoidal.SHACL.reportToGraph report) .rdf12 with
      | .error e => errJson s!"shaclValidate: report serialisation: {e}"
      | .ok lines =>
          okWith [("conforms", .bool report.conforms), ("reportNquads", .string lines)]

/-- A focus node or shape label given as an IRI or `_:label`. -/
private def nodeOfText (s : String) : Option Term :=
  if s.startsWith "_:" then
    if s.length > 2 then some (.bnode (String.ofList (s.toList.drop 2))) else none
  else if h : isIri s then some (.iri ⟨s, h⟩) else none

/-- The schema text, read as ShExJ or ShExC by its first non-whitespace
character. -/
private def schemaOfText (text : String) : Except String L4Factoidal.ShEx.Schema :=
  if (text.toList.dropWhile Char.isWhitespace).head? == some '{' then
    match parseJson? text with
    | none => .error "the ShExJ schema is not a JSON document"
    | some j =>
      match L4Factoidal.ShEx.schemaOf j with
      | some sch => .ok sch
      | none => .error "the JSON document is not a ShExJ schema this validator reads"
  else
    L4Factoidal.ShEx.Compact.parseShExC text

/-- `shexValidate(dataNquads, schemaText, focus, shape)`. -/
def shexValidate (dataNq schemaText focus shape : String) : String :=
  match parseNQuadsFast dataNq .rdf12 with
  | .error e => errJson s!"shexValidate(data): {fmtParseError e}"
  | .ok ds =>
  match schemaOfText schemaText with
  | .error e => errJson s!"shexValidate(schema): {e}"
  | .ok sch =>
  match nodeOfText focus with
  | none => errJson s!"shexValidate: the focus '{focus}' is not an IRI or _:label"
  | some n =>
    let verdict :=
      if shape.isEmpty then L4Factoidal.ShEx.validateStart sch ds.default n
      else L4Factoidal.ShEx.validateNode sch ds.default shape n
    okWith [("verdict", .bool verdict)]

/-! ## Build-time checks (positive and negative) -/

private def vData : String :=
  "<http://e/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Person> .\n" ++
  "<http://e/alice> <http://e/name> \"Alice\" .\n" ++
  "<http://e/dave> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Person> .\n"

private def vShapes : String :=
  "<http://e/PS> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://www.w3.org/ns/shacl#NodeShape> .\n" ++
  "<http://e/PS> <http://www.w3.org/ns/shacl#targetClass> <http://e/Person> .\n" ++
  "<http://e/PS> <http://www.w3.org/ns/shacl#property> _:p .\n" ++
  "_:p <http://www.w3.org/ns/shacl#path> <http://e/name> .\n" ++
  "_:p <http://www.w3.org/ns/shacl#minCount> \"1\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n"

private def vHas (s sub : String) : Bool := (s.splitOn sub).length > 1

-- SHACL: dave has no name, so the data graph does not conform; alice alone does.
#guard (shaclValidate vData vShapes).startsWith "{\"ok\":true,\"conforms\":false"
#guard vHas (shaclValidate vData vShapes) "http://e/dave"
#guard (shaclValidate (vData.splitOn "<http://e/dave>").head! vShapes).startsWith
         "{\"ok\":true,\"conforms\":true"
#guard (shaclValidate "garbage" vShapes).startsWith "{\"ok\":false"

private def vShExC : String :=
  "PREFIX e: <http://e/>\ne:S { e:name LITERAL }\n"

private def vShExJ : String :=
  "{\"type\":\"Schema\",\"shapes\":[{\"type\":\"ShapeDecl\",\"id\":\"http://e/S\"," ++
  "\"shapeExpr\":{\"type\":\"Shape\",\"expression\":{\"type\":\"TripleConstraint\"," ++
  "\"predicate\":\"http://e/name\",\"valueExpr\":{\"type\":\"NodeConstraint\"," ++
  "\"nodeKind\":\"literal\"}}}}]}"

-- ShEx: alice has a literal name, dave has none; both schema syntaxes agree.
#guard shexValidate vData vShExJ "http://e/alice" "http://e/S" == "{\"ok\":true,\"verdict\":true}"
#guard shexValidate vData vShExJ "http://e/dave" "http://e/S" == "{\"ok\":true,\"verdict\":false}"
#guard shexValidate vData vShExC "http://e/alice" "http://e/S" == "{\"ok\":true,\"verdict\":true}"
#guard shexValidate vData vShExC "http://e/dave" "http://e/S" == "{\"ok\":true,\"verdict\":false}"
#guard (shexValidate vData vShExC "not an iri" "http://e/S").startsWith "{\"ok\":false"
#guard (shexValidate vData "{ not json" "http://e/alice" "http://e/S").startsWith "{\"ok\":false"

end L4Wasm.Ops
