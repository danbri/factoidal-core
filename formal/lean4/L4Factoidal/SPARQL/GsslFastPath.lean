import L4Factoidal.SPARQL.Algebra

/-!
Conservative integration boundary for a future GSSL BGP backend. The host
must provide the backend result for the exact query and graph snapshot. This
module does not dispatch a GPU, encode RDF terms, or prove a shader correct.
-/
namespace L4Factoidal.SPARQL.GsslFastPath

open L4Factoidal.RDF

/-- The initial two-pattern shape has two distinct variables, fixed IRI
predicates, and a fixed IRI object in the second pattern. This recognises
syntax only: encoding, capacities, device availability, and backend
correctness remain separate obligations. -/
def supports : Bgp → Bool
  | [⟨.var person, .iri _, .var colleague⟩,
     ⟨.var colleague', .iri _, .iri _⟩] =>
      (person != colleague) && (colleague == colleague')
  | _ => false

/-- Resolve a result offered by the host. A missing result or unsupported
pattern uses the same indexed evaluator as `GraphPattern.evalIn`. An empty
successful GPU result is `some []`, not `none`. -/
def resolve (bgp : Bgp) (graph : Graph) (candidate : Option SolutionSeq) : SolutionSeq :=
  if supports bgp then
    match candidate with
    | some rows => rows
    | none => evalBgpIdx bgp graph
  else evalBgpIdx bgp graph

/-- Conditional integration theorem against the engine's indexed BGP path.
The hypothesis is a real obligation: every candidate accepted at this boundary
must equal the engine result as an ordered list, including binding layout and
multiplicity. The theorem does not prove or check that obligation. -/
theorem resolve_eq_indexed (bgp : Bgp) (graph : Graph) (candidate : Option SolutionSeq)
    (correct : ∀ rows, supports bgp = true → candidate = some rows →
      rows = evalBgpIdx bgp graph) :
    resolve bgp graph candidate = evalBgpIdx bgp graph := by
  cases hs : supports bgp with
  | false => simp [resolve, hs]
  | true =>
      cases hc : candidate with
      | none => simp [resolve, hs]
      | some rows => simp [resolve, hs, correct rows hs hc]

/-- Unsupported syntax always takes the existing engine path, regardless of
any offered candidate. -/
theorem unsupported_fallback (bgp : Bgp) (graph : Graph)
    (candidate : Option SolutionSeq) (h : supports bgp = false) :
    resolve bgp graph candidate = evalBgpIdx bgp graph := by
  simp [resolve, h]

/-- Device absence, failure, cancellation or capacity refusal must be
represented by `none`, and falls back even for supported syntax. -/
theorem missing_fallback (bgp : Bgp) (graph : Graph) :
    resolve bgp graph none = evalBgpIdx bgp graph := by
  cases h : supports bgp <;> simp [resolve, h]

#print axioms resolve_eq_indexed
#print axioms unsupported_fallback
#print axioms missing_fallback

end L4Factoidal.SPARQL.GsslFastPath
