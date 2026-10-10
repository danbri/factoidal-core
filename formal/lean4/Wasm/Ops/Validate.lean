/-
Wasm.Ops.Validate — the SHACL validation operation of the npm entry
(https://github.com/danbri/factoidal/issues/713 stage 3).

  shaclValidate(dataNquads, shapesNquads)
    -> {"ok":true,"conforms":true|false,"reportNquads":"…"}

The envelope follows the F* npm entry (`bin/npm-entry/entry_extras.ml`,
`shacl_validate_json`) member for member. `shexValidate` was in this module
until 2026-10-10 and is now in `Wasm/Ops/ShExValidate.lean`, so that the core
dispatch (`Wasm/CoreDispatch.lean`, issue 713 stage 4) serves SHACL without
linking the ShEx validator.

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

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.Syntax.NTriples
import L4Factoidal.SHACL.Report
import L4Factoidal.SHACL.NodeExpr

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

end L4Wasm.Ops
