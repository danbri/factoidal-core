/-
L4Factoidal.Storage.Sbm11.UpdateOverlayTheorems — the replay of the entries of a
SPARQL 1.1 Update operation over ids (https://github.com/danbri/factoidal/issues/849).

`Harness/Sbm11Update.lean` compiles a DELETE/INSERT to the removes of its
deletes followed by the adds of its inserts (`SPARQL/UpdateStore.lean`,
`changeEntries`), a COPY to a CLEAR of the destination followed by the adds of
the source's triples. The replay of such a list of entries (`Overlay.replay`)
gives:

  * `denote_change`: the quads of the result are `(S minus D) union I`
    (SPARQL 1.1 Update section 3.1.3: both sets come from the state before the
    operation);
  * `denote_clear_adds`: a CLEAR of graph `g` followed by adds is
    `(S minus the quads of g) union I` (section 3.2.3, COPY).

Both build on `OverlayTheorems.step_add`, `step_remove`, `step_clear`. No
`sorry`, no `axiom`, no `native_decide`.
-/
import L4Factoidal.Storage.Sbm11.OverlayTheorems

namespace L4Factoidal.Storage.Sbm11.UpdateOverlayTheorems

open L4Factoidal.Storage.Sbm11.Overlay
open L4Factoidal.Storage.Sbm11.OverlayTheorems
open L4Factoidal.Storage.Sbm11.Block (Row)

/-- The overlay operations of one change: the removes of the deletes, then the adds of the inserts. -/
def changeOps (D I : List Row) : List Op := D.map Op.remove ++ I.map Op.add

theorem row_beq_comm (a b : Row) : (a == b) = (b == a) := by
  by_cases h : a = b
  · subst h; rfl
  · have h1 : (a == b) = false := by simpa using h
    have h2 : (b == a) = false := by simpa using Ne.symm h
    rw [h1, h2]

theorem contains_cons_row (d r : Row) (rest : List Row) :
    (d :: rest).contains r = ((d == r) || rest.contains r) := by
  simp only [List.contains, List.elem]
  rw [row_beq_comm d r]
  cases (r == d) <;> rfl

theorem denote_removes (base : Row → Bool) :
    ∀ (D : List Row) (st : State) (r : Row),
      denote base (Overlay.replay st (D.map Op.remove)) r = (denote base st r && !(D.contains r)) := by
  intro D
  induction D with
  | nil => intro st r; simp [Overlay.replay]
  | cons d rest ih =>
    intro st r
    have h := ih (step st (.remove d)) r
    have e : Overlay.replay st ((d :: rest).map Op.remove) = Overlay.replay (step st (.remove d)) (rest.map Op.remove) := rfl
    rw [e, h, step_remove, contains_cons_row]
    cases denote base st r <;> cases (d == r) <;> cases rest.contains r <;> simp

theorem denote_adds (base : Row → Bool) :
    ∀ (I : List Row) (st : State) (r : Row),
      denote base (Overlay.replay st (I.map Op.add)) r = (denote base st r || I.contains r) := by
  intro I
  induction I with
  | nil => intro st r; simp [Overlay.replay]
  | cons q rest ih =>
    intro st r
    have h := ih (step st (.add q)) r
    have e : Overlay.replay st ((q :: rest).map Op.add) = Overlay.replay (step st (.add q)) (rest.map Op.add) := rfl
    rw [e, h, step_add, contains_cons_row]
    cases denote base st r <;> cases (q == r) <;> cases rest.contains r <;> simp

/-- SPARQL 1.1 Update section 3.1.3 at the level of ids: the deletes and the inserts of one operation
come from the state before it, the removes are replayed, then the adds, and the quads of the result
are `(S minus D) union I`. -/
theorem denote_change (base : Row → Bool) (st : State) (D I : List Row) (r : Row) :
    denote base (Overlay.replay st (changeOps D I)) r = ((denote base st r && !(D.contains r)) || I.contains r) := by
  unfold changeOps
  rw [replay_append, denote_adds, denote_removes]

/-- COPY (section 3.2.3) at the level of ids: CLEAR of the destination graph, then the adds of the
source's quads. -/
theorem denote_clear_adds (base : Row → Bool) (st : State) (g : Nat) (I : List Row) (r : Row) :
    denote base (Overlay.replay st (Op.clear g :: I.map Op.add)) r =
      ((denote base st r && r.g != g) || I.contains r) := by
  have e : Overlay.replay st (Op.clear g :: I.map Op.add) = Overlay.replay (step st (.clear g)) (I.map Op.add) := rfl
  rw [e, denote_adds, step_clear]

#print axioms denote_removes
#print axioms denote_adds
#print axioms denote_change
#print axioms denote_clear_adds

end L4Factoidal.Storage.Sbm11.UpdateOverlayTheorems
