import L4Factoidal.SPARQL.MetadataCount
import L4Factoidal.SPARQL.OrderedSubjectTheorems

namespace L4Factoidal.SPARQL.MetadataCount

open L4Factoidal.RDF L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan L4Factoidal.SPARQL.StoreFastPath
open L4Factoidal.SPARQL.StoreDataset

theorem predicate_count (source : OWL.RL.Index) (valid : source.Wf graph) (p : WfIri) :
    backendCountExact (.indexed source) { p := some p } = (source.withPred p).length := by
  change (tripleMatchesBound { p := some p } (source.withPred p)).length = _
  congr 1
  apply List.filter_eq_self.mpr
  intro triple member
  simp [boundMatches, OrderedSubject.predicate_bucket source valid p triple member]

theorem cardinality_eq (ordered : OrderedSubject.Index source) (valid : source.Wf graph)
    (bound : PatternBound) (count : Nat) (found : cardinality? ordered bound = some count) :
    count = backendCountExact (.indexed source) bound := by
  rcases bound with ⟨s, p, o⟩
  cases s <;> cases p <;> cases o <;>
    simp only [cardinality?] at found <;> try contradiction
  all_goals simp only [Option.some.injEq] at found; subst count
  · simp [backendCountExact, capsOfBackend, capsOfIndexed, igEstimate, igSearch,
      tripleMatchesBound, boundMatches, OWL.RL.Index.toGraph]
    change source.all.size = (source.all.toList.filter (fun _ => true)).length
    rw [List.filter_eq_self.mpr (by intro _ _; rfl), Array.length_toList]
  · rename_i p
    rw [predicate_count source valid]
    have length := congrArg List.length (ordered.valid p false)
    simpa using length

/-- Every successful metadata count is the complete existing backend result,
    including its scalar datatype, alias, OFFSET and LIMIT. -/
theorem countRows_eq_backend (ordered : OrderedSubject.Index source) (valid : source.Wf graph)
    (query : Query) (rows : SolutionSeq) (found : countRows? ordered query = some rows)
    (env : EvalEnv) :
    some rows = runSelectQueryBackendDataset env query { default := .indexed source, named := [] } := by
  unfold countRows? at found
  dsimp only at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  split at found <;> try contradiction
  next _ graphNone _ alias tp countSome _ count cardSome =>
    simp only [Option.some.injEq] at found
    subst rows
    have exactCount := cardinality_eq ordered valid (patternBoundFor tp []) count cardSome
    unfold runSelectQueryBackendDataset
    change _ = evalSelectBackendDataset env (backendQuery query) _
    simp only [evalSelectBackendDataset, graphNone, evalSelectBackendOnGraph, countSome]
    rw [exactCount]
    rfl

#print axioms cardinality_eq
#print axioms countRows_eq_backend

end L4Factoidal.SPARQL.MetadataCount
