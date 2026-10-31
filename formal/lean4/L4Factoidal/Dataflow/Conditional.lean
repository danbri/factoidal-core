/- Structured conditional execution for stages. The decidable predicate is
chosen by the application. Admission/refusal witnesses concern that predicate,
not a global validity or human-usefulness verdict. Only the selected stage's
run occurs in this definition. This is not an IO effect trace or DAG scheduler. -/
import L4Factoidal.Dataflow.Stage

namespace L4Factoidal.Dataflow.Stage
variable {ε α β γ : Type}

/-- Evidence of the decision on this exact input. Proofs erase at runtime;
the admitted/rejected constructor remains available to the host report. -/
inductive Admission (P : α → Prop) (a : α) where
  | admitted (witness : P a)
  | rejected (witness : ¬ P a)

def Admission.accepted {P : α → Prop} {a : α} : Admission P a → Bool
  | .admitted _ => true
  | .rejected _ => false

theorem Admission.accepted_iff {P : α → Prop} {a : α} (evidence : Admission P a) :
    evidence.accepted = true ↔ P a := by
  cases evidence with
  | admitted witness => simp [Admission.accepted, witness]
  | rejected witness => simp [Admission.accepted, witness]

/-- Both branches have the same value type, with input-indexed decision evidence. -/
structure Routed (P : α → Prop) (β : Type) (a : α) where
  admission : Admission P a
  value : β

/-- The selected contract, applied to the same exact input and branch witness. -/
def Routed.contract {P : α → Prop}
    (accept : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β)
    {a : α} (out : Routed P β a) : Prop :=
  match out.admission with
  | .admitted witness => accept.contract ⟨a,witness⟩ out.value
  | .rejected witness => reject.contract ⟨a,witness⟩ out.value

/-- Decide once, then run one branch. Expensive/effectful branch work must be
inside its run, not precomputed as arguments before calling the conditional. -/
def runRouted (P : α → Prop) [DecidablePred P]
    (accept : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β)
    (a : α) : Except ε (Routed P β a) :=
  if witness : P a then
    (accept.run ⟨a,witness⟩).map (fun value => ⟨.admitted witness,value⟩)
  else
    (reject.run ⟨a,witness⟩).map (fun value => ⟨.rejected witness,value⟩)

/-- Successful routed output carries the selected branch contract. -/
theorem runRouted_sound (P : α → Prop) [DecidablePred P]
    (accept : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β)
    (a : α) (out : Routed P β a) (success : runRouted P accept reject a = .ok out) :
    out.contract accept reject := by
  unfold runRouted at success
  split at success
  · rename_i admitted
    cases result : accept.run ⟨a,admitted⟩ with
    | error e => simp [result, Except.map] at success
    | ok value =>
      simp only [result, Except.map, Except.ok.injEq] at success
      subst out
      exact accept.sound _ _ result
  · rename_i rejected
    cases result : reject.run ⟨a,rejected⟩ with
    | error e => simp [result, Except.map] at success
    | ok value =>
      simp only [result, Except.map, Except.ok.injEq] at success
      subst out
      exact reject.sound _ _ result

/-- The ordinary Stage view uses the same routed producer, retaining its
predicate-indexed branch contract for composition through Stage.comp. -/
def choose (P : α → Prop) [DecidablePred P]
    (accept : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β) : Stage ε α β where
  run a := (runRouted P accept reject a).map (·.value)
  contract a value := ∃ evidence : Admission P a,
    (Routed.mk evidence value).contract accept reject
  sound := by
    intro a value success
    cases result : runRouted P accept reject a with
    | error e => simp [result, Except.map] at success
    | ok out =>
      simp only [result, Except.map, Except.ok.injEq] at success
      subst value
      exact ⟨out.admission, runRouted_sound P accept reject a out result⟩

/-- Operational equation: admission runs the admitted branch and preserves its result. -/
theorem choose_run_admitted (P : α → Prop) [DecidablePred P]
    (accept : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β)
    (a : α) (witness : P a) :
    (choose P accept reject).run a = accept.run ⟨a,witness⟩ := by
  cases result : accept.run ⟨a,witness⟩ <;> simp [choose, runRouted, witness, result, Except.map]

theorem choose_run_rejected (P : α → Prop) [DecidablePred P]
    (accept : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β)
    (a : α) (witness : ¬ P a) :
    (choose P accept reject).run a = reject.run ⟨a,witness⟩ := by
  cases result : reject.run ⟨a,witness⟩ <;> simp [choose, runRouted, witness, result, Except.map]

/-- Replacing the entire unselected rejected stage cannot change the routed
result. This is an equation of pure computation, not an external-effect trace. -/
theorem runRouted_admitted_independent (P : α → Prop) [DecidablePred P]
    (accept : Stage ε {a // P a} β) (reject₁ reject₂ : Stage ε {a // ¬ P a} β)
    (a : α) (witness : P a) :
    runRouted P accept reject₁ a = runRouted P accept reject₂ a := by
  simp [runRouted, witness]

theorem runRouted_rejected_independent (P : α → Prop) [DecidablePred P]
    (accept₁ accept₂ : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β)
    (a : α) (witness : ¬ P a) :
    runRouted P accept₁ reject a = runRouted P accept₂ reject a := by
  simp [runRouted, witness]

theorem choose_contract_admitted (P : α → Prop) [DecidablePred P]
    (accept : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β)
    (a : α) (value : β) (witness : P a) :
    (choose P accept reject).contract a value ↔ accept.contract ⟨a,witness⟩ value := by
  constructor
  · rintro ⟨evidence, holds⟩
    cases evidence with
    | admitted _ => exact holds
    | rejected denied => exact (denied witness).elim
  · intro holds
    exact ⟨.admitted witness, holds⟩

theorem choose_contract_rejected (P : α → Prop) [DecidablePred P]
    (accept : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β)
    (a : α) (value : β) (witness : ¬ P a) :
    (choose P accept reject).contract a value ↔ reject.contract ⟨a,witness⟩ value := by
  constructor
  · rintro ⟨evidence, holds⟩
    cases evidence with
    | admitted admitted => exact (witness admitted).elim
    | rejected _ => exact holds
  · intro holds
    exact ⟨.rejected witness, holds⟩

/-- Successful composition has an actual selected-branch middle value and
both contracts, together with the admission proof or explicit refutation. -/
theorem choose_comp_ok (P : α → Prop) [DecidablePred P]
    (accept : Stage ε {a // P a} β) (reject : Stage ε {a // ¬ P a} β)
    (next : Stage ε β γ) (a : α) (out : γ)
    (success : ((choose P accept reject).comp next).run a = .ok out) :
    (∃ (witness : P a) (middle : β), accept.run ⟨a,witness⟩ = .ok middle ∧
      next.run middle = .ok out ∧ accept.contract ⟨a,witness⟩ middle ∧ next.contract middle out) ∨
    (∃ (witness : ¬ P a) (middle : β), reject.run ⟨a,witness⟩ = .ok middle ∧
      next.run middle = .ok out ∧ reject.contract ⟨a,witness⟩ middle ∧ next.contract middle out) := by
  obtain ⟨middle, selected, continued⟩ := comp_ok (choose P accept reject) next success
  by_cases witness : P a
  · rw [choose_run_admitted P accept reject a witness] at selected
    exact Or.inl ⟨witness,middle,selected,continued,accept.sound _ _ selected,next.sound _ _ continued⟩
  · rw [choose_run_rejected P accept reject a witness] at selected
    exact Or.inr ⟨witness,middle,selected,continued,reject.sound _ _ selected,next.sound _ _ continued⟩

#print axioms Admission.accepted_iff
#print axioms runRouted_sound
#print axioms choose
#print axioms choose_run_admitted
#print axioms choose_run_rejected
#print axioms runRouted_admitted_independent
#print axioms runRouted_rejected_independent
#print axioms choose_comp_ok
end L4Factoidal.Dataflow.Stage
