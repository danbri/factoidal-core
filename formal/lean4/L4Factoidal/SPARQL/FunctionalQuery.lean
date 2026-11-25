/- Pure transformations over the parser and evaluator's actual query AST.
These operations do not validate SPARQL scope or establish equivalence. -/
import L4Factoidal.SPARQL.Expr
namespace L4Factoidal.SPARQL

def Query.mapPattern (f : QueryPattern → QueryPattern) : Query → Query
  | .mk form dataset pattern groupBy having modifier postValues base =>
      .mk form dataset (f pattern) groupBy having modifier postValues base

def Query.mapModifier (f : SolutionModifier → SolutionModifier) : Query → Query
  | .mk form dataset pattern groupBy having modifier postValues base =>
      .mk form dataset pattern groupBy having (f modifier) postValues base

theorem Query.mapPattern_id (q : Query) : q.mapPattern id = q := by
  cases q
  rfl

theorem Query.mapPattern_comp (f g : QueryPattern → QueryPattern) (q : Query) :
    (q.mapPattern f).mapPattern g = q.mapPattern (g ∘ f) := by
  cases q
  rfl

theorem Query.mapModifier_id (q : Query) : q.mapModifier id = q := by
  cases q
  rfl

theorem Query.mapPattern_mapModifier (f : QueryPattern → QueryPattern)
    (g : SolutionModifier → SolutionModifier) (q : Query) :
    (q.mapPattern f).mapModifier g = (q.mapModifier g).mapPattern f := by
  cases q
  rfl
end L4Factoidal.SPARQL
