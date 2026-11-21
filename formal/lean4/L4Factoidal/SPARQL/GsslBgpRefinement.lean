import L4Factoidal.SPARQL.SharedSubjectTripleRefinement
import L4Factoidal.SPARQL.IndexedEvalRefinement
import L4Factoidal.SPARQL.GsslFastPath

/-!
An RDF-level two-pattern plan for the proposed GPU path. The first relation
is an explicit predicate selection over source triples. The second stage
still calls the engine's RDF matcher; there is no integer encoding or GPU
dispatch here. The theorem connects this plan to the actual indexed evaluator.
-/
namespace L4Factoidal.SPARQL.GsslBgpRefinement

open L4Factoidal.RDF
open L4Factoidal.SPARQL.SharedSubjectTriple
open L4Factoidal.SPARQL.SharedSubjectTripleRefinement

/-- Ordered first-pattern selection followed by the engine's second-pattern
matching, with exactly the binding layout used by the SPARQL matcher. -/
def rdfPlan (person colleague : VarName) (knows works object : WfIri)
    (graph : Graph) : SolutionSeq :=
  (predicateFragment knows graph).flatMap fun triple =>
    evalTP ⟨.var colleague, .iri works, .iri object⟩ graph
      [(colleague, triple.o), (person, triple.s.toTerm)]

/-- The RDF-level plan gives the exact ordered result of the indexed BGP
evaluator for all graphs and all distinct variable names. This is not yet a
proof about encoded integer triples or a device result. -/
theorem rdfPlan_eq_evalBgpIdx (person colleague : VarName)
    (knows works object : WfIri) (graph : Graph) (different : person ≠ colleague) :
    rdfPlan person colleague knows works object graph =
      evalBgpIdx [⟨.var person, .iri knows, .var colleague⟩,
        ⟨.var colleague, .iri works, .iri object⟩] graph := by
  rw [evalBgpIdx_eq_evalBgp]
  unfold evalBgp
  simp only [evalBgpFrom, Binding.empty]
  rw [evalTP_first person colleague knows graph different]
  simp [rdfPlan, List.flatMap_map]

/-- The concrete RDF plan discharges the candidate premise of the fallback
boundary for this pattern, without assuming candidate correctness. This is
still a CPU reference plan, not a proof of a GPU response. -/
theorem resolve_rdfPlan (person colleague : VarName)
    (knows works object : WfIri) (graph : Graph) (different : person ≠ colleague) :
    GsslFastPath.resolve
      [⟨.var person, .iri knows, .var colleague⟩,
       ⟨.var colleague, .iri works, .iri object⟩]
      graph (some (rdfPlan person colleague knows works object graph)) =
    evalBgpIdx [⟨.var person, .iri knows, .var colleague⟩,
      ⟨.var colleague, .iri works, .iri object⟩] graph := by
  apply GsslFastPath.resolve_eq_indexed
  intro rows _ h
  cases h
  exact rdfPlan_eq_evalBgpIdx person colleague knows works object graph different

#print axioms rdfPlan_eq_evalBgpIdx
#print axioms resolve_rdfPlan

end L4Factoidal.SPARQL.GsslBgpRefinement
