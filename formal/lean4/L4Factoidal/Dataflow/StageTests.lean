/-
L4Factoidal.Dataflow.StageTests — checks of `Dataflow/Stage.lean`, evaluated
during `lake build` (https://github.com/danbri/factoidal/issues/975, phase A3).

* Composition runs the first stage and then the second; an error of the first
  stage stops the run (`#guard`).
* The contract of a composition is the relational composition of the two
  contracts (`example`, by `rfl`), and a successful composite run gives a
  middle value that satisfies both contracts.
* An IO stage has no proof of its contract: its contract is the named
  assumption, and a stage made from it needs `IOStage.Realised` as a
  hypothesis.
* Negative cases: a run that fails gives no contract; the composite contract
  of two stages whose contracts cannot meet is false.

No executable imports this module.
-/
import L4Factoidal.Dataflow.Stage

namespace L4Factoidal.Dataflow.StageTests

open L4Factoidal.Dataflow

/-- Doubles; the contract states the output. -/
private def dbl : Stage String Nat Nat :=
  Stage.ofFun (fun n => 2 * n) (fun a b => b = 2 * a) (fun _ => rfl)

/-- Refuses zero; the contract says the output is the input and not zero. -/
private def nonZero : Stage String Nat Nat where
  run n := if n = 0 then .error "zero" else .ok n
  contract a b := b = a ∧ a ≠ 0
  sound := by
    intro a b h
    by_cases h0 : a = 0
    · simp [h0] at h
    · simp [h0] at h
      exact ⟨h.symm, h0⟩

private def okVal? {ε β : Type} : Except ε β → Option β
  | .ok b => some b
  | .error _ => none

private def errVal? {ε β : Type} : Except ε β → Option ε
  | .ok _ => none
  | .error e => some e

#guard okVal? ((nonZero.comp dbl).run 3) == some 6
#guard okVal? ((nonZero.comp dbl).run 0) == none
#guard errVal? ((dbl.comp nonZero).run 0) == some "zero"

/-- The composite contract is the relational composition. -/
example : (nonZero.comp dbl).contract = RelComp nonZero.contract dbl.contract := rfl

/-- A successful composite run has a middle value. -/
example (c : Nat) (h : (nonZero.comp dbl).run 5 = .ok c) : c = 10 := by
  obtain ⟨b, ⟨hb, _⟩, hc⟩ := Stage.comp_ok_contract nonZero dbl h
  rw [hc, hb]

-- `Stage.second` keeps the first component.
#guard okVal? ((Stage.second (α := String) dbl).run ("x", 4)) == some ("x", 8)

/-- An IO stage: the contract is the assumption, named by the definition. -/
private def EchoAssumption (a b : Nat) : Prop := b = a

private def echoIO : IOStage String Nat Nat := { assumption := EchoAssumption }

/-- With the named assumption as a hypothesis, the IO stage composes. -/
example (readBack : Nat → Except String Nat) (hrw : echoIO.Realised readBack) (c : Nat)
    (h : ((echoIO.toStage readBack hrw).comp dbl).run 7 = .ok c) : c = 14 := by
  obtain ⟨b, hb, hc⟩ := Stage.comp_ok_contract _ dbl h
  have hb' : b = 7 := hb
  rw [hc, hb']

/-- Negative: no output with a contract when the run fails. -/
example : ¬ ∃ b, nonZero.run 0 = .ok b := by
  rintro ⟨b, h⟩
  simp [nonZero] at h

/-- Negative: the contracts of `dbl` then a stage that wants an odd number
    cannot meet. -/
example : ¬ RelComp dbl.contract (fun (b : Nat) (_ : Nat) => b % 2 = 1) 3 0 := by
  rintro ⟨b, hb, ho⟩
  have hb' : b = 2 * 3 := hb
  rw [hb'] at ho
  simp at ho

/-- Composition is associative in its contract. -/
example : ((nonZero.comp dbl).comp dbl).contract = (nonZero.comp (dbl.comp dbl)).contract :=
  RelComp.assoc _ _ _

end L4Factoidal.Dataflow.StageTests
