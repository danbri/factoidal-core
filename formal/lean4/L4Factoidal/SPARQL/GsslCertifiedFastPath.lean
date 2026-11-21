import L4Factoidal.SPARQL.GsslBgpRefinement

/-!
# Proof-carrying GSSL candidate boundary

The raw host-candidate interface in GsslFastPath is intentionally conditional:
it cannot validate an arbitrary GPU result. This module provides a *logical*
API requiring evidence that a candidate has the exact ordered indexed-engine
semantics for precisely this query and active graph.

An untrusted GPU readback cannot construct this type merely from bytes.
An implementation may instead use a separately established correctness proof
for its backend, or decline the fast path and use the CPU evaluator.

No runtime proof serialization, WGSL lowering, or physical GPU verification is
claimed here; proof erasure alone is not evidence of correctness at a JS boundary.
-/
namespace L4Factoidal.SPARQL.GsslCertifiedFastPath

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-- The query and source graph are indices of the certificate, preventing
    an exact-result proof for another query or snapshot from being reused. -/
structure CertifiedCandidate (bgp : Bgp) (graph : Graph) where
  rows : SolutionSeq
  exact : rows = evalBgpIdx bgp graph

/-- This is the safe *logical* resolver. It may accept a fast-path answer
    only when an exact semantic certificate is available at the Lean boundary.
    Unsupported syntax and absence of a candidate use the reference evaluator. -/
def resolve (bgp : Bgp) (graph : Graph)
    (candidate : Option (CertifiedCandidate bgp graph)) : SolutionSeq :=
  if GsslFastPath.supports bgp then
    match candidate with
    | none => evalBgpIdx bgp graph
    | some certified => certified.rows
  else
    evalBgpIdx bgp graph

theorem resolve_eq_indexed (bgp : Bgp) (graph : Graph)
    (candidate : Option (CertifiedCandidate bgp graph)) :
    resolve bgp graph candidate = evalBgpIdx bgp graph := by
  cases hs : GsslFastPath.supports bgp with
  | false => simp [resolve, hs]
  | true =>
      cases candidate with
      | none => simp [resolve, hs]
      | some certified =>
          simpa [resolve, hs] using certified.exact

/-- This is a genuine constructor of a certified candidate: the *existing*
    RDF-level plan has a theorem against the shipping indexed evaluator.
    It does NOT certify the experimental GPU backend. -/
def fromRdfPlan (person colleague : VarName)
    (knows works object : WfIri) (graph : Graph)
    (different : person ≠ colleague) :
    CertifiedCandidate
      [⟨.var person, .iri knows, .var colleague⟩,
       ⟨.var colleague, .iri works, .iri object⟩] graph :=
  { rows := GsslBgpRefinement.rdfPlan person colleague knows works object graph
    exact := GsslBgpRefinement.rdfPlan_eq_evalBgpIdx
      person colleague knows works object graph different }

/-- Example of a domain-specific theorem discharging the generic admission
    obligation without asserting anything about actual device execution. -/
theorem certifiedRdfPlan_eq_indexed (person colleague : VarName)
    (knows works object : WfIri) (graph : Graph)
    (different : person ≠ colleague) :
    resolve
      [⟨.var person, .iri knows, .var colleague⟩,
       ⟨.var colleague, .iri works, .iri object⟩]
      graph (some (fromRdfPlan person colleague knows works object graph different)) =
    evalBgpIdx
      [⟨.var person, .iri knows, .var colleague⟩,
       ⟨.var colleague, .iri works, .iri object⟩] graph :=
  resolve_eq_indexed _ _ _

#print axioms resolve_eq_indexed
#print axioms certifiedRdfPlan_eq_indexed

end L4Factoidal.SPARQL.GsslCertifiedFastPath
