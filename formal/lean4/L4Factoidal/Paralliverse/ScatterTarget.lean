import L4Factoidal.Paralliverse.LoopTarget
import L4Factoidal.Paralliverse.PackWireTheorems

/-! # Finite storage instructions for the stable scatter

The only immutable inputs are the raw packet and completed offset binding. A lane
checks the row count before reading its descriptor. Locals 0 and 1 hold the absolute
source and destination starts. The copying loop uses native u32 address addition.
-/

namespace L4Factoidal.Paralliverse.ScatterTarget
open LoopTarget
open L4Factoidal.GpuKernel

def header : Expr := .load .packet (.literal 1)
def descriptor (field : UInt32) : Expr := .add (.literal field) (.mul (.literal 2) .globalId)
def bankBase : Expr := .add (.literal 3) (.mul (.literal 2) header)

def body : Stmt :=
  .storeWord (.add (.localWord 1) .index) (.load .packet (.add (.localWord 0) .index))

def activeLane : Stmt :=
  .seq (.assign 0 (.add bankBase (.load .packet (descriptor 3))))
    (.seq (.assign 1 (.load .auxiliary .globalId))
      (.forRange PackWire.maxWords (.load .packet (descriptor 4)) body))

def lowerScatter : DSL.Stage .scanned .packed → Stmt
  | .scatter => .whenLt .globalId header activeLane

def lane (inputs : Inputs) (gid : UInt32) (prior : Array UInt32) : Except Fault (Array UInt32) :=
  ((lowerScatter .scatter).exec inputs gid 0 ⟨fun _ => 0, prior⟩).map State.dst

def wordMemory (a : Array UInt32) : Mem UInt32 := fun j => a[j]?.getD 0

/-- Kind: instruction evaluation.
Says: the header load decides whether the whole active lane runs.
Does not say: that an active lane's descriptor is valid. -/
private theorem guard_ok (inputs : Inputs) (gid n : UInt32) (s : State)
    (head : read inputs .packet 1 = .ok n) :
    (lowerScatter .scatter).exec inputs gid 0 s =
      if gid < n then activeLane.exec inputs gid 0 s else .ok s := by
  change (read inputs .packet 1).bind (fun w =>
    if gid < w then activeLane.exec inputs gid 0 s else .ok s) = _
  rw [head] <;> rfl

/-- Kind: instruction refinement.
Says: every padded or otherwise inactive lane with a readable header returns the prior
destination, even if neither a descriptor nor an auxiliary word exists for that ID.
Does not say: that the active lanes have been dispatched. -/
theorem inactive_lane (inputs : Inputs) (gid n : UInt32) (prior : Array UInt32)
    (head : inputs.packet[1]? = some n) (inactive : ¬ gid < n) :
    lane inputs gid prior = .ok prior := by
  have hh : read inputs .packet 1 = .ok n := read_ok inputs .packet 1 n head
  unfold lane
  rw [guard_ok inputs gid n _ hh, if_neg inactive] <;> rfl

/-- Kind: arithmetic refinement.
Says: the u32 addition in a copy address equals natural addition when its sum fits.
Does not say: that the resulting address is within a supplied buffer. -/
private theorem add_index (base : UInt32) (k : Nat) (h : base.toNat + k < UInt32.size) :
    (base + UInt32.ofNat k).toNat = base.toNat + k := by
  have hk : k < UInt32.size := by omega
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' hk, Nat.mod_eq_of_lt h]

/-- Kind: instruction evaluation.
Says: one successful body reads the physical source word and changes one checked slot
of the finite destination while preserving the local registers.
Does not say: that a source word agrees with a particular logical row. -/
private theorem body_ok (inputs : Inputs) (gid k w : UInt32) (s : State)
    (hr : read inputs .packet (s.locals 0 + k) = .ok w)
    (hd : (s.locals 1 + k).toNat < s.dst.size) :
    body.exec inputs gid k s = .ok {s with dst := s.dst.set (s.locals 1 + k).toNat w hd} := by
  change (read inputs .packet (s.locals 0 + k)).bind (fun v => store s (s.locals 1 + k) v) = _
  rw [hr]
  exact store_ok s _ _ hd

/-- Kind: memory algebra.
Says: the first word of a consecutive write is installed before the remaining words.
Does not say: that two overlapping writes can be reordered. -/
private theorem writes_cons (b : Nat) (x : UInt32) (xs : List UInt32) (m : Mem UInt32) :
    applyWrites m (DSL.writesFrom b (x :: xs)) =
      applyWrites (m.write b x) (DSL.writesFrom (b + 1) xs) := by
  have h : DSL.writesFrom b (x :: xs) = (b, x) :: DSL.writesFrom (b + 1) xs := by
    simp [DSL.writesFrom, List.range'_succ]
  rw [h] <;> rfl

/-- Kind: bounded loop simulation.
Says: copying an actual finite source window with representable addresses and sufficient
destination capacity terminates without a fault and performs precisely its indexed writes
on the entire prior destination, including preservation of the tail.
Does not say: that an arbitrary packet or arbitrary offsets supply those windows. -/
theorem copy_words (inputs : Inputs) (gid : UInt32) (words : List UInt32) (k : Nat) (s : State)
    (srcFit : (s.locals 0).toNat + k + words.length < UInt32.size)
    (dstFit : (s.locals 1).toNat + k + words.length < UInt32.size)
    (room : (s.locals 1).toNat + k + words.length ≤ s.dst.size)
    (source : ∀ j (hj : j < words.length),
      inputs.packet[(s.locals 0).toNat + k + j]? = some words[j]) :
    ∃ t, iterate (fun i st => body.exec inputs gid i st) words.length (UInt32.ofNat k) s = .ok t ∧
      t.dst.size = s.dst.size ∧ wordMemory t.dst = applyWrites (wordMemory s.dst)
        (DSL.writesFrom ((s.locals 1).toNat + k) words) := by
  induction words generalizing k s with
  | nil => exact ⟨s, rfl, rfl, rfl⟩
  | cons x xs ih =>
    simp only [List.length_cons] at srcFit dstFit room
    have sa := add_index (s.locals 0) k (by omega)
    have da := add_index (s.locals 1) k (by omega)
    have rd : read inputs .packet (s.locals 0 + UInt32.ofNat k) = .ok x := by
      apply read_ok
      change inputs.packet[(s.locals 0 + UInt32.ofNat k).toNat]? = some x
      rw [sa]
      simpa using source 0 (by simp)
    have hd : (s.locals 1 + UInt32.ofNat k).toNat < s.dst.size := by rw [da]; omega
    let next : State := {s with dst := s.dst.set (s.locals 1 + UInt32.ofNat k).toNat x hd}
    have step : body.exec inputs gid (UInt32.ofNat k) s = .ok next := body_ok _ _ _ _ _ rd hd
    have size : next.dst.size = s.dst.size := by simp [next]
    have restRead : ∀ j (hj : j < xs.length),
        inputs.packet[(next.locals 0).toNat + (k + 1) + j]? = some xs[j] := by
      intro j hj
      change inputs.packet[(s.locals 0).toNat + (k + 1) + j]? = some xs[j]
      rw [show (s.locals 0).toNat + (k + 1) + j = (s.locals 0).toNat + k + (j + 1) by omega]
      exact source (j + 1) (by simpa using hj)
    obtain ⟨t, hrun, hsize, hmem⟩ := ih (k + 1) next
      (by change (s.locals 0).toNat + (k + 1) + xs.length < UInt32.size; omega)
      (by change (s.locals 1).toNat + (k + 1) + xs.length < UInt32.size; omega)
      (by rw [size]; change (s.locals 1).toNat + (k + 1) + xs.length ≤ s.dst.size; omega)
      restRead
    have stored : wordMemory next.dst = (wordMemory s.dst).write ((s.locals 1).toNat + k) x := by
      calc
        wordMemory next.dst = (wordMemory s.dst).write (s.locals 1 + UInt32.ofNat k).toNat x :=
          observe_set id 0 s.dst _ x hd
        _ = _ := by rw [da]
    refine ⟨t, ?_, hsize.trans size, ?_⟩
    · change iterate _ (xs.length + 1) _ s = _
      rw [iterate, step]
      change iterate _ xs.length (UInt32.ofNat k + 1) next = _
      rw [← UInt32.ofNat_add k 1]
      exact hrun
    · rw [hmem, stored, writes_cons] <;> rfl

#print axioms inactive_lane
#print axioms copy_words

-- Alternate offsets and an inactive lane exercise the actual checked bindings.
#guard match lane ⟨#[1, 2, 4, 3, 1, 0, 2, 8, 9, 99, 7], #[2, 0]⟩ 0 #[17, 17, 17, 17] with
  | .ok a => a == #[17, 17, 7, 17]
  | .error _ => false
#guard match lane ⟨#[1, 2, 4, 3, 1, 0, 2, 8, 9, 99, 7], #[2, 0]⟩ 1 #[17, 17, 17, 17] with
  | .ok a => a == #[8, 9, 17, 17]
  | .error _ => false
#guard match lane ⟨#[1, 1], #[]⟩ 4 #[17] with
  | .ok a => a == #[17]
  | .error _ => false

end L4Factoidal.Paralliverse.ScatterTarget
