/- The projected header is query metadata, independent of the graph and
evaluation environment. This fixes the old output-derived header without
changing solution mappings or their evaluation. Scope follows §18.2.1. -/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

theorem evalSelect_header (env : EvalEnv) (dataset : Dataset) (query : Query) :
    (evalSelect env dataset query).1 = query.projectedVars := by
  cases query with
  | mk form dataset pattern group having modifier values base => cases form <;> rfl

theorem evalSelect_header_independent (query : Query) (env₁ env₂ : EvalEnv)
    (dataset₁ dataset₂ : Dataset) :
    (evalSelect env₁ dataset₁ query).1 = (evalSelect env₂ dataset₂ query).1 := by
  rw [evalSelect_header, evalSelect_header]

theorem projectedVars_explicit (items : List SelectItem) (dataset : List DatasetClause)
    (pattern : QueryPattern) (group : Option (List GroupCondition)) (having : List Expr)
    (modifier : SolutionModifier) (values : Option (List Binding)) (base : Option String) :
    (Query.mk (.select (.vars items)) dataset pattern group having modifier values base).projectedVars =
      selectItemVars items := rfl

private theorem eraseDups_nodup (names : List String) : names.eraseDups.Nodup := by
  match names with
  | [] => simp
  | name :: rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp
      · exact eraseDups_nodup (rest.filter fun other => !other == name)
termination_by names.length
decreasing_by
  have := List.length_filter_le (fun other => !other == name) rest
  simp only [List.length_cons]
  omega

theorem projectedVars_star_nodup (dataset : List DatasetClause) (pattern : QueryPattern)
    (group : Option (List GroupCondition)) (having : List Expr) (modifier : SolutionModifier)
    (values : Option (List Binding)) (base : Option String) :
    (Query.mk (.select .all) dataset pattern group having modifier values base).projectedVars.Nodup := by
  exact eraseDups_nodup _

#print axioms evalSelect_header_independent
#print axioms projectedVars_star_nodup

end L4Factoidal.SPARQL
