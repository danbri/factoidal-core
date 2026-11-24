import L4Factoidal.SPARQL.QueryDocument
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! Native JSON-lines transport for tests of the SPARQL query document.
The optional `canonical` switch emits the ordinary parser's AST. -/

open L4Factoidal.JSON L4Factoidal.SPARQL

private def runRequest (line : String) : Except String Json := do
  let request ← (parseJson line).mapError toString
  let some query := request.getString? "query" | throw "Expected a query string"
  let version ← match (request.getString? "version").getD "1.1" with
    | "1.1" => pure SparqlVersion.v11
    | "1.2" => pure SparqlVersion.v12
    | _ => throw "SPARQL version must be 1.1 or 1.2"
  let wdqs := (request.getBool? "wdqs").getD false
  let base := request.getString? "base"
  if (request.getBool? "canonical").getD false then
    return match parseUnloweredQuery query wdqs version base with
      | .ok ast => queryAstJson ast
      | .error _ => .null
  else
    return parseQueryDocument query wdqs version base

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := match runRequest line with
      | .ok value => value
      | .error message => Json.object [("error", .string message)]
    output.putStrLn (toStringCompact result)
    output.flush
