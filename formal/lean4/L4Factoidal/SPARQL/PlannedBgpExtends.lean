import L4Factoidal.SPARQL.StorePlan
import L4Factoidal.SPARQL.BgpRefinement

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- SPARQL 1.1 §18.3: restricting an already compatible result to an
    earlier mapping cannot introduce a conflict, including duplicate seeds. -/
theorem Binding.compatible_of_extends (before after : Binding)
    (extension : Extends before after) (seed : Binding)
    (compatible : seed.compatible after = true) : seed.compatible before = true := by
  induction seed with
  | nil => rfl
  | cons assignment rest inductionHypothesis =>
      rcases assignment with ⟨name, term⟩
      simp only [Binding.compatible, Bool.and_eq_true] at compatible ⊢
      refine ⟨?_, inductionHypothesis compatible.2⟩
      cases found : before.lookup name with
      | none => rfl
      | some existing =>
          have retained := extension name existing found
          simpa only [retained] using compatible.1

namespace StorePlan

/-- The planner's reverse accumulator retains the complete ordered flatMap
    of its recursive results, followed by the prior reverse accumulator. -/
theorem evalBgpConcatMapAcc_eq (patterns : Bgp) (backend : StoreBackend.GraphBackend)
    (fuel : Nat) (rows reversed : SolutionSeq) :
    evalBgpConcatMapAcc patterns backend fuel rows reversed =
      (rows.flatMap (fun row => evalBgpFromMuFuel patterns backend row fuel)).reverse ++ reversed := by
  induction rows generalizing reversed with
  | nil => rfl
  | cons row rest inductionHypothesis =>
      simp only [evalBgpConcatMapAcc, inductionHypothesis, List.flatMap_cons,
        List.reverse_append, List.reverseAux_eq, List.append_assoc]

/-- SPARQL 1.1 §18.3: every planned BGP result retains every value
    previously bound by its seed, independently of the backend or fuel. -/
theorem evalBgpFromMuFuel_extends (fuel : Nat) :
    ∀ (patterns : Bgp) (backend : StoreBackend.GraphBackend)
      (before after : Binding),
      after ∈ evalBgpFromMuFuel patterns backend before fuel → Extends before after := by
  induction fuel with
  | zero =>
      intro patterns backend before after member
      simp only [evalBgpFromMuFuel, List.mem_singleton] at member
      subst after
      exact Extends.refl before
  | succ fuel inductionHypothesis =>
      intro patterns backend before after member
      cases patterns with
      | nil =>
          simp only [evalBgpFromMuFuel, List.mem_singleton] at member
          subst after
          exact Extends.refl before
      | cons first rest =>
          simp only [evalBgpFromMuFuel] at member
          cases chosen : chooseBestTpBackend backend before (first :: rest) with
          | none =>
              simp only [chosen, List.mem_singleton] at member
              subst after
              exact Extends.refl before
          | some selected =>
              rcases selected with ⟨pattern, remaining⟩
              simp only [chosen, evalBgpConcatMapAcc_eq, List.append_nil,
                List.mem_reverse, List.mem_flatMap] at member
              obtain ⟨intermediate, matched, result⟩ := member
              simp only [evalSingleTpBackend, List.mem_filterMap] at matched
              obtain ⟨triple, _, matched⟩ := matched
              exact (tpMatch_extends matched).trans
                (inductionHypothesis remaining backend intermediate after result)

end StorePlan

#print axioms Binding.compatible_of_extends
#print axioms StorePlan.evalBgpConcatMapAcc_eq
#print axioms StorePlan.evalBgpFromMuFuel_extends

end L4Factoidal.SPARQL
