/-
Checked-saturation refinement and completeness for the actual RDFS runner.
Issue: https://github.com/danbri/factoidal-core/issues/745.
-/
import L4Factoidal.RDFS.Checked
import L4Factoidal.RDFS.FullClosureTheorems

namespace L4Factoidal.RDFS.Checked

open L4Factoidal.RDF

/-- Refinement and resource invariant.
Says: successful checked iteration equals the existing explicit-fuel loop,
is saturated under the actual full step, and fits the retained triple cap.
Does not say: a cap bounds intermediate allocations or guarantees success. -/
theorem loop_success {maxTriples fuel : Nat} {g out : Graph}
    (h : loop maxTriples fuel g = .ok out) :
    fullClosureLoop g fuel = out ∧ fullStep out = out ∧ out.length ≤ maxTriples := by
  induction fuel generalizing g with
  | zero => simp [loop] at h
  | succ fuel ih =>
      simp only [loop] at h
      split at h
      · cases h
      · rename_i hsize
        split at h
        · cases h
        · split at h
          · rename_i hfixed
            cases h
            exact ⟨by simp only [fullClosureLoop, hfixed, ↓reduceIte],
              addAll_eq_of_length_eq _ _ hfixed, Nat.le_of_not_gt hsize⟩
          · rename_i hnotfixed
            obtain ⟨heq, hsat, hbound⟩ := ih h
            exact ⟨by simp only [fullClosureLoop, hnotfixed, ↓reduceIte]; exact heq,
              hsat, hbound⟩

/-- Public admission invariant.
Says: full-RDFS checked success retains the real axiom-seeded execution,
actual saturation and the output cap.
Does not say: the legacy automatic fuel is sufficient for every input. -/
theorem fullClosure_success {limits : Limits} {D cmps : List WfIri} {g out : Graph}
    (h : fullClosure limits D cmps g = .ok out) :
    fullClosureLoop (addAll g (axiomaticTriples D cmps)) limits.maxRounds = out ∧
      fullStep out = out ∧ out.length ≤ limits.maxTriples := by
  simp only [fullClosure] at h
  split at h
  · cases h
  · exact loop_success h

/-- Extensivity.
Says: checked full-RDFS success retains each original input triple.
Does not say: byte serialisation or duplicate multiplicity is canonical. -/
theorem fullClosure_extensive {limits : Limits} {D cmps : List WfIri} {g out : Graph}
    (h : fullClosure limits D cmps g = .ok out) {t : Triple} (ht : t ∈ g) : t ∈ out := by
  rw [← (fullClosure_success h).1]
  exact fullClosureLoop_extensive _ _ (mem_addAll_of_mem _ _ ht)

/-- Derivational soundness.
Says: every accepted output triple is derivable from the input and the
specified axiom seed using the existing full-RDFS derivation relation.
Does not say: an independent review of that relation or compiler is complete. -/
theorem fullClosure_sound {limits : Limits} {D cmps : List WfIri} {g out : Graph}
    (h : fullClosure limits D cmps g = .ok out) {t : Triple} (ht : t ∈ out) :
    DerivesFull (axiomaticTriples D cmps) g t := by
  rw [← (fullClosure_success h).1] at ht
  exact DerivesFull.cut (fun _ hu => seeded_sound hu) (fullClosureLoop_sound _ _ _ ht)

/-- Derivational completeness of the accepted result.
Says: every triple derivable with the supplied full-RDFS axiom seed is a
member of a successful checked output; saturation is established by the
actual runner, not supplied by the caller as a hypothesis.
Does not say: unrestricted RDF semantic non-entailment follows from ASK false. -/
theorem fullClosure_complete {limits : Limits} {D cmps : List WfIri} {g out : Graph}
    (h : fullClosure limits D cmps g = .ok out) {t : Triple}
    (ht : DerivesFull (axiomaticTriples D cmps) g t) : Graph.mem t out = true := by
  obtain ⟨heq, hsat, _⟩ := fullClosure_success h
  apply fullComplete_of_saturated hsat ?_ ?_ ht
  · intro u hu
    rw [← heq]
    exact graphMem_fullClosureLoop_of_graphMem _ _ (graphMem_addAll_of_mem_list _ _ hu)
  · intro u hu
    exact graphMem_of_mem (fullClosure_extensive h hu)

/-- Exhaustion behaviour.
Says: zero checked rounds return an exhaustion error, even for a fixed point.
Does not say: an error carries an accepted partial graph. -/
theorem loop_zero (maxTriples : Nat) (g : Graph) :
    loop maxTriples 0 g = .error .exhausted := rfl

#print axioms loop_success
#print axioms fullClosure_success
#print axioms fullClosure_extensive
#print axioms fullClosure_sound
#print axioms fullClosure_complete
#print axioms loop_zero

end L4Factoidal.RDFS.Checked
