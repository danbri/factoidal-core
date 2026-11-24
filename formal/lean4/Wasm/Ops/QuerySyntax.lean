import Wasm.Ops.Support
import L4Factoidal.SPARQL.QueryDocument

namespace L4Wasm.Ops
open L4Factoidal.SPARQL
open L4Factoidal.JSON

private def sparqlVersion? : String → Option SparqlVersion
  | "1.1" => some .v11
  | "1.2" => some .v12
  | _ => none

/-- Inspect the same unlowered query AST used by the parser. This operation
does not evaluate the query or require a dataset. -/
def parseSparqlStructure (text wdqs version : String) (includeComments : Bool := false) : String := Id.run do
  let some version := sparqlVersion? version | return errJson "SPARQL version must be 1.1 or 1.2"
  match parseUnloweredQuery text (wdqs == "true") version with
  | .error error => return errJson s!"SPARQL parse error: {error.msg} (offset {error.pos})"
  | .ok query =>
    let form := match query.form with
      | .select _ => "select"
      | .ask => "ask"
      | .construct _ => "construct"
      | .describe _ => "describe"
    let fields := [("form", .string form),
      ("variables", .array (query.projectedVars.map .string)), ("sse", .string query.toSse)]
    let comments := if includeComments then
      [("comments", .array ((sourceComments text version.is12).map sourceCommentJson))]
      else []
    return okWith [("result", .object (fields ++ comments))]

/-- Full query and source inspection. Query parse failures are in the result;
the transport error channel is reserved for malformed requests. -/
def parseSparqlAst (text options : String) : String := Id.run do
  let .ok (.object fields) := parseJson options | return errJson "SPARQL parse options must be an object"
  let options := Json.object fields
  let some version := sparqlVersion? ((options.getString? "version").getD "1.1") |
    return errJson "SPARQL version must be 1.1 or 1.2"
  let wdqs := (options.getBool? "wdqs").getD false
  let base := options.getString? "base"
  return okWith [("result", parseQueryDocument text wdqs version base)]

end L4Wasm.Ops
