/- Probe original WDQS corpus text without modifying prefixes. A rejection is
an observation, not evidence that a query is invalid on WDQS. -/
import Lean
import L4Factoidal.SPARQL.Parser
open Lean L4Factoidal.SPARQL
private def records (text : String) : Except String (Array Json) := do
  let doc ← Json.parse text
  (← doc.getObjVal? "queries").getArr?
private def requiredString (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?
private def inspect (j : Json) : Except String Json := do
  let query ← requiredString j "query"
  let page ← requiredString j "page"
  let ordinal ← j.getObjVal? "ordinal"
  let (accepted, message) := match parseSparql query none .v11 with
    | .ok _ => (true, "")
    | .error e => (false, e.msg)
  pure <| Json.mkObj [("page", toJson page), ("ordinal", ordinal),
    ("accepted", toJson accepted), ("message", toJson message)]
def main : IO UInt32 := do
  let text ← IO.FS.readFile "Wikidata/corpus/martin-poulter/queries.json"
  let .ok items := records text | IO.eprintln "invalid corpus JSON"; return 1
  let stdout ← IO.getStdout
  let mut count := 0
  for item in items do
    match inspect item with
    | .error e => IO.eprintln s!"invalid corpus record: {e}"; return 1
    | .ok result =>
      stdout.putStrLn result.compress
      count := count + 1
  IO.eprintln s!"Inspected {count} original queries; acceptance is not a conformance score."
  return 0
