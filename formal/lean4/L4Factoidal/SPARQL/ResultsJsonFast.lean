import L4Factoidal.SPARQL.ResultsJson

/-!
Accumulator-based rendering of the existing SPARQL Results JSON specification.
Lean's `String.intercalate` grows a tail-recursive accumulator instead of
repeatedly appending an already-rendered result suffix. Term and binding
rendering, row order, duplicates, variable order, and the wrapper stay unchanged.
`ResultsJsonFastTheorems` proves equality to `QueryResult.toSrj`; it does not
prove a runtime cost bound or a parser round trip.
-/

namespace L4Factoidal.SPARQL

/-- SPARQL Results JSON §3.2: the existing row objects, comma-separated in order. -/
def rowsJoinedFast (rows : SolutionSeq) : String :=
  String.intercalate "," (rows.map rowJson)

/-- SPARQL Results JSON §§3–4, with accumulator-based binding-row rendering. -/
def QueryResult.toSrjFast : QueryResult → String
  | .bindings vars rows =>
      "{\"head\":{\"vars\":[" ++ varListJson vars ++ "]}," ++
      "\"results\":{\"bindings\":[" ++ rowsJoinedFast rows ++ "]}}"
  | .boolean answer =>
      "{\"head\":{},\"boolean\":" ++ (if answer then "true" else "false") ++ "}"

end L4Factoidal.SPARQL
