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

/-- A second-pattern selection on a single triple. Comparisons deliberately use
the same RDF equality and predicate orientation as the engine matcher. -/
def rightMatch (colleague : VarName) (works object : WfIri)
    (binding : Binding) (triple : Triple) : Option Binding :=
  match binding.lookup colleague with
  | none => none
  | some key =>
    if key.eqb triple.s.toTerm then
      if works == triple.p then
        match triple.o with
        | .iri actual => if object == actual then some binding else none
        | _ => none
      else none
    else none

/-- With the join variable bound, the independent right-side test is exactly
the engine's triple matcher, including non-IRI objects and RDF equality. -/
theorem rightMatch_eq_tpMatch (colleague : VarName) (works object : WfIri)
    (binding : Binding) (triple : Triple) (key : Term)
    (bound : binding.lookup colleague = some key) :
    rightMatch colleague works object binding triple =
      tpMatch ⟨.var colleague, .iri works, .iri object⟩ triple binding := by
  cases hkey : key.eqb triple.s.toTerm <;> cases hpred : works == triple.p <;>
    simp [rightMatch, tpMatch, tryBindSubject, tryBindTerm, bound, hkey, hpred]
  cases triple.o <;> simp

/-- Ordered filter/map of the complete RDF graph for an already-bound key. -/
def rightSelect (colleague : VarName) (works object : WfIri)
    (graph : Graph) (binding : Binding) : SolutionSeq :=
  graph.filterMap (rightMatch colleague works object binding)

theorem rightSelect_eq_evalTP (colleague : VarName) (works object : WfIri)
    (graph : Graph) (binding : Binding) (key : Term)
    (bound : binding.lookup colleague = some key) :
    rightSelect colleague works object graph binding =
      evalTP ⟨.var colleague, .iri works, .iri object⟩ graph binding := by
  unfold rightSelect evalTP
  apply congrArg (fun f => graph.filterMap f)
  funext triple
  exact rightMatch_eq_tpMatch colleague works object binding triple key bound

/-- A relational RDF plan with explicit left selection and right-side
selection/join. The graph is scanned in original order on both sides. -/
def relationalPlan (person colleague : VarName) (knows works object : WfIri)
    (graph : Graph) : SolutionSeq :=
  (predicateFragment knows graph).flatMap fun triple =>
    rightSelect colleague works object graph
      [(colleague, triple.o), (person, triple.s.toTerm)]

theorem relationalPlan_eq_rdfPlan (person colleague : VarName)
    (knows works object : WfIri) (graph : Graph) :
    relationalPlan person colleague knows works object graph =
      rdfPlan person colleague knows works object graph := by
  unfold relationalPlan rdfPlan
  apply congrArg (fun f => (predicateFragment knows graph).flatMap f)
  funext triple
  exact rightSelect_eq_evalTP colleague works object graph
    [(colleague, triple.o), (person, triple.s.toTerm)] triple.o
    (by simp [Binding.lookup])

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

/-- Both explicit RDF selections and their join reproduce the exact ordered
indexed-engine result, for every graph and distinct pair of variables. -/
theorem relationalPlan_eq_evalBgpIdx (person colleague : VarName)
    (knows works object : WfIri) (graph : Graph) (different : person ≠ colleague) :
    relationalPlan person colleague knows works object graph =
      evalBgpIdx [⟨.var person, .iri knows, .var colleague⟩,
        ⟨.var colleague, .iri works, .iri object⟩] graph :=
  (relationalPlan_eq_rdfPlan person colleague knows works object graph).trans
    (rdfPlan_eq_evalBgpIdx person colleague knows works object graph different)

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
#print axioms rightMatch_eq_tpMatch
#print axioms rightSelect_eq_evalTP
#print axioms relationalPlan_eq_rdfPlan
#print axioms relationalPlan_eq_evalBgpIdx

end L4Factoidal.SPARQL.GsslBgpRefinement
