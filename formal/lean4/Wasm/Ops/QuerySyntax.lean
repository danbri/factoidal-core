import Wasm.Ops.Support
import L4Factoidal.Wikidata.Parser

namespace L4Wasm.Ops
open L4Factoidal.SPARQL

/-- Inspect the same unlowered query AST used by the parser. This operation
does not evaluate the query or require a dataset. -/
def parseSparqlStructure (text wdqs version : String) : String := Id.run do
  let version ← match version with
    | "1.1" => pure SparqlVersion.v11
    | "1.2" => pure SparqlVersion.v12
    | _ => return errJson "SPARQL version must be 1.1 or 1.2"
  let result := if wdqs == "true" then L4Factoidal.Wikidata.parseQuerySyntax text none version
    else
      match parseSparqlWith topFuel text none version with
      | .ok query => .ok query
      | .error error =>
        match parseSparqlWith (scaledFuel text) text none version with
        | .ok query => .ok query
        | .error _ => .error error
  match result with
  | .error error => return errJson s!"SPARQL parse error: {error.msg} (offset {error.pos})"
  | .ok query =>
    let form := match query.form with
      | .select _ => "select"
      | .ask => "ask"
      | .construct _ => "construct"
      | .describe _ => "describe"
    return okWith [("result", .object [("form", .string form),
      ("variables", .array (query.projectedVars.map .string)), ("sse", .string query.toSse)])]

end L4Wasm.Ops
