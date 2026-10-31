import L4Factoidal.Dataflow.Stage

/- Sufficient non-output conditions derived from the existing composition
   theorems. These apply to Stage.comp, not automatically to a JS/IO host.
   Failure to prove a contract is not a proof that its proposition is false. -/
namespace L4Factoidal.Dataflow.Stage
variable {ε α β γ : Type}

/-- A witnessed upstream error propagates without invoking a downstream stage. -/
theorem comp_error_left (s : Stage ε α β) (t : Stage ε β γ)
    (a : α) (e : ε) (h : s.run a = .error e) :
    (s.comp t).run a = .error e := by
  change (match s.run a with | .ok b => t.run b | .error err => .error err) = .error e
  rw [h]

/-- An upstream error rules out every successful composite output. -/
theorem comp_no_success_of_error (s : Stage ε α β) (t : Stage ε β γ)
    (a : α) (e : ε) (h : s.run a = .error e) :
    ∀ c, (s.comp t).run a ≠ .ok c := by
  intro c hc
  obtain ⟨b, hb, _⟩ := comp_ok s t hc
  rw [h] at hb
  cases hb

/-- A contradiction between the two contracts rules out a specified output.
This requires an actual refutation for every middle value, not an unchecked
badge or an absent proof. It does not establish host termination. -/
theorem comp_no_output_of_incompatible_contracts
    (s : Stage ε α β) (t : Stage ε β γ) (a : α) (c : γ)
    (incompatible : ∀ b, ¬ (s.contract a b ∧ t.contract b c)) :
    (s.comp t).run a ≠ .ok c := by
  intro hc
  obtain ⟨b, hs, ht⟩ := comp_ok_contract s t hc
  exact incompatible b ⟨hs, ht⟩

#print axioms comp_error_left
#print axioms comp_no_success_of_error
#print axioms comp_no_output_of_incompatible_contracts
end L4Factoidal.Dataflow.Stage
