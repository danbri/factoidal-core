/-
L4Factoidal.OWL.RLSemiNaiveTheorems — the four obligations of
https://github.com/danbri/factoidal/issues/756 for the semi-naive OWL 2 RL
closure `indexedClosureSN` (`RLClosureIndexed.lean`, Section 11).

Owner, 2026-10-10, verbatim: "Can we extend this approach to semi-naïve
OWL/RDFS evaluation eventually, but the proof target would change. Instead of
proving that both implementations return identical results after every
round, prove that they compute equivalent saturated closures".

The semi-naive rounds here are proved to return the SAME LIST as the naive
rounds (`indexedClosureSN_eq`): a semi-naive round emits a sub-list of the
naive round's conclusions from which only triples already in the round's
input are missing, and `addAll` drops exactly those. That is stronger than
the equality at saturation the issue asks for, so the four obligations
follow from the theorems about `closure` (`RLTheorems.lean`), and the
order of the closure's output is the naive order by proof.

1. **Soundness** — `indexedClosureSN_sound`: every triple of the closure is
   a `Derives` instance. No hypothesis.
2. **Saturation at termination** — `stepSNI_saturated`: a semi-naive round
   that adds nothing (an empty delta) leaves a graph closed under every
   row: `step S = S`, i.e. `stepConclusions S ⊆ S`
   (`stepSNI_closed`). With the fuel dichotomy
   (`indexedClosureSN_saturated_or_underfueled`), the loop's result is
   saturated or the loop used all its fuel.
3. **Least fixed point** — `indexedClosureSN_complete`: a saturated result
   contains every `Derives` instance (from `complete_of_saturated`: `g ⊆ S`
   and `S` closed imply `Derives g ⊆ S`). With 1:
   `mem_indexedClosureSN_iff`, `t ∈ C g ↔ Derives g t`.
4. **Naive and semi-naive are equal** — as lists, at every fuel
   (`indexedClosureSN_eq`), hence as sets (`mem_indexedClosureSN_iff_closure`).

Termination (item 4 of the issue's proof target) is NOT proved: that
`closureFuelBound g` rounds are enough, so that the hypotheses of 3 hold at
`closureFix`. It is the same open obligation as the naive loop's
(`RLTheorems.lean` header, items 2 and 3), since the two loops are the same
list at every fuel. No run-time check is needed for the equality: the
semi-naive loop takes the naive loop's rounds by proof. Expected-failure
row: `Harness/ProofObligations.lean`,
`L4Factoidal.OWL.RL.closureFix_saturated`.
-/
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.OWL.RLTheorems

namespace L4Factoidal.OWL.RL

open L4Factoidal.RDF

/-- **1. Soundness.** Every triple of the semi-naive closure is derivable. -/
theorem indexedClosureSN_sound (g : Graph) (fuel : Nat) {t : Triple}
    (h : t ∈ indexedClosureSN g fuel) : Derives g t := by
  rw [indexedClosureSN_eq] at h
  exact closure_sound fuel g h

/-- **2. Saturation at termination**, for one round: a semi-naive round that
adds nothing to its input leaves it closed: one naive round adds nothing. -/
theorem stepSNI_saturated {i : Index} {S : Graph} {lo : Nat} (h : i.Wf S)
    (hr : RoundOk S lo) (h0 : (stepSNI i lo).all.size = i.all.size) :
    RL.step S = S := by
  apply step_eq_of_length_eq
  rw [← (h.stepSN hr).all, ← h.all, Array.length_toList, Array.length_toList]
  exact h0

/-- The same, as closure under every row: every conclusion of every row at
every driving triple of `S`, and every premise-free axiom, is in `S`. -/
theorem stepSNI_closed {i : Index} {S : Graph} {lo : Nat} (h : i.Wf S)
    (hr : RoundOk S lo) (h0 : (stepSNI i lo).all.size = i.all.size) :
    ∀ t ∈ stepConclusions S, t ∈ S := by
  intro t ht
  have := mem_step_of_mem_conclusions ht
  rwa [stepSNI_saturated h hr h0] at this

/-- **2'. The fuel dichotomy** for the semi-naive loop: its result is
saturated, or the loop grew the graph by one triple per unit of fuel. -/
theorem indexedClosureSN_saturated_or_underfueled (g : Graph) (fuel : Nat) :
    RL.step (indexedClosureSN g fuel) = indexedClosureSN g fuel ∨
      g.length + fuel ≤ (indexedClosureSN g fuel).length := by
  rw [indexedClosureSN_eq]
  exact closure_saturated_or_underfueled fuel g

/-- **3. Least fixed point.** A saturated semi-naive closure whose
collection walks are adequately fuelled contains every derivable triple. -/
theorem indexedClosureSN_complete {g : Graph} {fuel : Nat}
    (hsat : RL.step (indexedClosureSN g fuel) = indexedClosureSN g fuel)
    (hlf : ListFuelAdequate (indexedClosureSN g fuel) (listFuel (indexedClosureSN g fuel)))
    {t : Triple} (h : Derives g t) : t ∈ indexedClosureSN g fuel := by
  rw [indexedClosureSN_eq] at hsat hlf ⊢
  exact closure_complete_of_saturated hsat hlf h

/-- **1 and 3 together**: the semi-naive closure is the set of derivable
triples, under the two hypotheses of 3. -/
theorem mem_indexedClosureSN_iff {g : Graph} {fuel : Nat}
    (hsat : RL.step (indexedClosureSN g fuel) = indexedClosureSN g fuel)
    (hlf : ListFuelAdequate (indexedClosureSN g fuel) (listFuel (indexedClosureSN g fuel)))
    (t : Triple) : t ∈ indexedClosureSN g fuel ↔ Derives g t :=
  ⟨indexedClosureSN_sound g fuel, indexedClosureSN_complete hsat hlf⟩

/-- **4. Naive and semi-naive are equal as sets** (the list equality
`indexedClosureSN_eq` gives more: the same order). -/
theorem mem_indexedClosureSN_iff_closure (g : Graph) (fuel : Nat) (t : Triple) :
    t ∈ indexedClosureSN g fuel ↔ t ∈ RL.closure g fuel := by
  rw [indexedClosureSN_eq]

/-- The naive indexed loop and the semi-naive loop return the same list. -/
theorem indexedClosureSN_eq_indexedClosure (g : Graph) (fuel : Nat) :
    indexedClosureSN g fuel = indexedClosure g fuel := by
  rw [indexedClosureSN_eq, indexedClosure_eq]

end L4Factoidal.OWL.RL

-- 'L4Factoidal.OWL.RL.indexedClosureSN_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.OWL.RL.indexedClosureSN_eq
#print axioms L4Factoidal.OWL.RL.indexedClosureSN_sound
#print axioms L4Factoidal.OWL.RL.stepSNI_saturated
#print axioms L4Factoidal.OWL.RL.stepSNI_closed
#print axioms L4Factoidal.OWL.RL.indexedClosureSN_saturated_or_underfueled
#print axioms L4Factoidal.OWL.RL.indexedClosureSN_complete
#print axioms L4Factoidal.OWL.RL.mem_indexedClosureSN_iff
#print axioms L4Factoidal.OWL.RL.mem_indexedClosureSN_iff_closure
#print axioms L4Factoidal.OWL.RL.indexedClosureSN_eq_indexedClosure
#print axioms L4Factoidal.OWL.RL.prpSpo2_ok
#print axioms L4Factoidal.OWL.RL.clsInt1_ok
#print axioms L4Factoidal.OWL.RL.rowTable_ok
