import L4Factoidal.SPARQL.ResultsJsonFast
import Init.Data.String.Lemmas.Intercalate

namespace L4Factoidal.SPARQL

theorem rowsJoinedFast_eq (rows : SolutionSeq) : rowsJoinedFast rows = rowsJoined rows := by
  induction rows with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          simpa only [rowsJoinedFast, List.map_cons, String.intercalate_cons_cons, rowsJoined]
            using congrArg (fun rendered => rowJson first ++ "," ++ rendered) inductionHypothesis

theorem QueryResult.toSrjFast_eq (result : QueryResult) : result.toSrjFast = result.toSrj := by
  cases result with
  | bindings variables rows =>
      exact congrArg
        (fun rendered => "{\"head\":{\"vars\":[" ++ varListJson variables ++ "]}," ++
          "\"results\":{\"bindings\":[" ++ rendered ++ "]}}")
        (rowsJoinedFast_eq rows)
  | boolean answer => rfl

theorem QueryResult.toSrjFast_bytes_eq (result : QueryResult) :
    result.toSrjFast.toUTF8 = result.toSrj.toUTF8 :=
  congrArg String.toUTF8 result.toSrjFast_eq

#print axioms rowsJoinedFast_eq
#print axioms QueryResult.toSrjFast_eq
#print axioms QueryResult.toSrjFast_bytes_eq

end L4Factoidal.SPARQL
