/-
L4Factoidal.Claims.Witnesses — hypothesis witnesses for the claims register
(`foundation/claims.toml`; https://github.com/danbri/factoidal-core/issues/1180,
P3 of batch https://github.com/danbri/factoidal-core/issues/1189).

A claim with hypotheses says nothing when its hypotheses cannot hold at the same
time (anti-pattern 29 and its relatives). Each theorem here applies one claim's
theorem at concrete arguments and proves every hypothesis there. The conclusion
is discarded (`True`): what Lean checks is that the application elaborates, so
the hypotheses are satisfiable together. `tools/claims-gate.py` checks that each
witness named in the register exists and applies its claim's theorem.

Says: the hypotheses of the named claim are satisfiable together, at the
arguments shown. Does not say: that they hold for any input that matters in
practice; the arguments are the smallest that work (an empty dataset, an empty
graph).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Compose
import L4Factoidal.Storage.BackendRefinement

namespace L4Factoidal.Claims

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.Dataflow

/-! ## `sparql-eval-lawful-dataset` (`Dataflow.query_sound`) -/

/-- An evaluator that answers the foundation's reference answer and names no
assumption. -/
def referenceEvaluator : LawfulEvaluator where
  run := referenceAnswer
  assumed_contractOn := fun _ => False
  sound := fun _ _ _ => Or.inl rfl

theorem referenceEvaluator_assumptionHolds : referenceEvaluator.AssumptionHolds :=
  fun _ _ h => h.elim

/-- The empty dataset, with its set proof. -/
def emptyCertified : CertifiedDataset := ⟨Dataset.empty, Dataset.isSet_empty⟩

/-- Witness: a lawful evaluator, a store with no named assumption, and a
dataset that is a set with the store's denotation, at once. -/
theorem query_sound_witness (env : EvalEnv) (q : Query) : True :=
  (fun _ => trivial) (query_sound referenceEvaluator referenceEvaluator_assumptionHolds
    (LawfulDataset.ofCertified emptyCertified)
    (by first
      | exact Assumed.nil
      | (intro a h; simp [LawfulDataset.ofCertified, LawfulDataset.indexed] at h))
    (ds := Dataset.empty) Dataset.isSet_empty rfl env q)

/-! ## `backend-bgp-refinement` (`Storage.BackendRefinement.evalBgpBackend_solEquiv`) -/

/-- Witness: the list backend of the empty graph is exact for membership in
it, and the empty graph has no repeated keys. -/
theorem evalBgpBackend_solEquiv_witness (b : Bgp) : True :=
  (fun _ => trivial) (Storage.BackendRefinement.evalBgpBackend_solEquiv
    (gb := GraphBackend.list []) (G := fun t => KeyMem [] t) (g := [])
    (by first
      | exact ⟨Graph.keyNodup_nil, fun _ => Iff.rfl⟩
      | (simp only [BackendExact]; exact ⟨Graph.keyNodup_nil, fun _ => Iff.rfl⟩)
      | (unfold BackendExact; exact ⟨Graph.keyNodup_nil, fun _ => Iff.rfl⟩))
    Graph.keyNodup_nil (fun _ => Iff.rfl) b)

end L4Factoidal.Claims
