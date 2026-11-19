import L4Factoidal.Paralliverse.LoopTarget

/-! # Single-invocation finite offset scan

Packet word 1 supplies the row count. Slot 0 in private local storage holds
the carry. The auxiliary input is the completed physical count buffer. The
caller schedules exactly one invocation, also for empty input. -/

namespace L4Factoidal.Paralliverse.ScanTarget

open LoopTarget
open L4Factoidal.GpuKernel

def header : Expr := .load .packet (.literal 1)

def body : Stmt :=
  .seq (.storeWord .index (.localWord 0))
    (.assign 0 (.add (.localWord 0) (.load .auxiliary .index)))

def terminal : Stmt := .storeWord header (.localWord 0)

def lowerScan : DSL.Stage .counted .scanned → Stmt
  | .serialScan =>
    .seq (.assign 0 (.literal 0)) (.seq (.forRange PackWire.maxRows header body) terminal)

def run (inputs : Inputs) (prior : Array UInt32) : Except Fault (Array UInt32) :=
  ((lowerScan .serialScan).exec inputs 0 0 ⟨fun _ => 0, prior⟩).map State.dst

/-- Kind: arithmetic refinement.
Says: a physical carry addition below the packet's total-word limit equals the
natural addition of the actual unsigned inputs.
Does not say: that unchecked arbitrary u32 additions avoid overflow. -/
theorem carry_add (a b : UInt32) (h : a.toNat + b.toNat ≤ PackWire.maxWords) :
    (a + b).toNat = a.toNat + b.toNat := by
  change a.toNat + b.toNat ≤ 1024 at h
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by change a.toNat + b.toNat < 4294967296; omega)]

/-- Kind: instruction simulation.
Says: the body stores the previous carry, then adds the loaded count to that same
local. The physical operation is unsigned addition.
Does not say: that the addition avoids wrapping on an unchecked count. -/
private theorem body_ok (inputs : Inputs) (s : State) (i w : UInt32)
    (h : i.toNat < s.dst.size) (hread : read inputs .auxiliary i = .ok w) :
    body.exec inputs 0 i s =
      .ok (({s with dst := s.dst.set i.toNat (s.locals 0) h} : State).assign 0 (s.locals 0 + w)) := by
  change (store s i (s.locals 0)).bind (fun t =>
    ((read inputs .auxiliary i).bind (fun v => .ok (t.locals 0 + v))).bind
      (fun v => .ok (t.assign 0 v))) = _
  rw [store_ok s i (s.locals 0) h, hread] <;> rfl

/-- Kind: instruction simulation.
Says: the last instruction stores the current carry at the index read from the header.
Does not say: that the carry has accumulated every count. -/
private theorem terminal_ok (inputs : Inputs) (s : State) (n : UInt32)
    (head : read inputs .packet 1 = .ok n) (h : n.toNat < s.dst.size) :
    terminal.exec inputs 0 0 s = .ok {s with dst := s.dst.set n.toNat (s.locals 0) h} := by
  change (read inputs .packet 1).bind (fun i => store s i (s.locals 0)) = _
  rw [head]
  exact store_ok s n (s.locals 0) h

/-- The remaining generic iterations followed by the actual terminal instruction. -/
private def suffix (inputs : Inputs) (k : Nat) (i : UInt32) (s : State) : Except Fault State :=
  (iterate (fun j st => body.exec inputs 0 j st) k i s).bind (fun st => terminal.exec inputs 0 0 st)

/-- Kind: target evaluation.
Says: a successful first loop iteration feeds its state to the remaining iterations.
Does not say: that an arbitrary first iteration succeeds. -/
private theorem suffix_step (inputs : Inputs) (k : Nat) (i : UInt32) (s next : State)
    (h : body.exec inputs 0 i s = .ok next) :
    suffix inputs (k + 1) i s = suffix inputs k (i + 1) next := by
  unfold suffix
  rw [iterate, h] <;> rfl

/-- Kind: DSL memory algebra.
Says: the first word of a consecutive write changes its own slot before the suffix.
Does not say: that the supplied values are offsets. -/
private theorem writes_cons (base x : Nat) (xs : List Nat) (m : Mem Nat) :
    applyWrites m (DSL.writesFrom base (x :: xs)) =
      applyWrites (m.write base x) (DSL.writesFrom (base + 1) xs) := by
  have h : DSL.writesFrom base (x :: xs) = (base, x) :: DSL.writesFrom (base + 1) xs := by
    simp [DSL.writesFrom, List.range'_succ]
  rw [h] <;> rfl

#print axioms carry_add

-- Compare exact finite storage, including pre-existing tail words.
#guard match run ⟨#[1, 0], #[]⟩ #[99, 23] with
  | .ok dst => dst == #[0, 23]
  | .error _ => false
#guard match run ⟨#[1, 3], #[2, 0, 4, 888]⟩ #[99, 99, 99, 99, 23] with
  | .ok dst => dst == #[0, 2, 2, 6, 23]
  | .error _ => false

end L4Factoidal.Paralliverse.ScanTarget
