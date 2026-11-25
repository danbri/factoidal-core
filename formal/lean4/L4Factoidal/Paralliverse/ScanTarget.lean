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

/-- An input-only relation between a physical count window and its natural values. -/
private def Reads (a : Array UInt32) (base : Nat) (xs : List Nat) : Prop :=
  ∀ k (hk : k < xs.length), (a[base + k]?).map UInt32.toNat = some xs[k]

/-- Kind: bounded loop simulation.
Says: executing the remaining instructions and terminal store writes exactly the
natural prefixes of the actual remaining inputs, starting with the current carry.
The rest of the finite destination retains its previous contents.
Does not say: that a device makes prior dispatch writes visible. -/
private theorem suffix_sound (inputs : Inputs) (n : UInt32)
    (head : read inputs .packet 1 = .ok n) (limit : n.toNat ≤ PackWire.maxRows)
    (xs : List Nat) (base : Nat) (s : State)
    (endAt : base + xs.length = n.toNat) (cap : n.toNat < s.dst.size)
    (budget : (s.locals 0).toNat + xs.sum ≤ PackWire.maxWords)
    (physical : Reads inputs.auxiliary base xs) :
    ∃ t, suffix inputs xs.length (UInt32.ofNat base) s = .ok t ∧
      t.dst.size = s.dst.size ∧ CountTarget.memory t.dst =
        applyWrites (CountTarget.memory s.dst)
          (DSL.writesFrom base (xs.scanl (· + ·) (s.locals 0).toNat)) := by
  induction xs generalizing base s with
  | nil =>
    have hb : base = n.toNat := by simpa using endAt
    let t : State := {s with dst := s.dst.set n.toNat (s.locals 0) cap}
    refine ⟨t, terminal_ok inputs s n head cap, by simp [t], ?_⟩
    rw [hb, List.scanl_nil, writes_cons]
    exact observe_set UInt32.toNat 0 s.dst n.toNat (s.locals 0) cap
  | cons x xs ih =>
    have remaining : base + (xs.length + 1) = n.toNat := endAt
    have baseFits : base < UInt32.size := by
      change n.toNat ≤ 128 at limit
      change base < 4294967296
      omega
    have indexNat := UInt32.toNat_ofNat_of_lt' baseFits
    have here : (inputs.auxiliary[base]?).map UInt32.toNat = some x := by
      have firstPos : 0 < (x :: xs).length := by simp
      have first := physical 0 firstPos
      rw [Nat.add_zero] at first
      exact first.trans (congrArg some (List.getElem_cons_zero x xs firstPos))
    obtain ⟨w, hw, wval⟩ := Option.map_eq_some_iff.mp here
    have hread : read inputs .auxiliary (UInt32.ofNat base) = .ok w := by
      apply read_ok
      change inputs.auxiliary[(UInt32.ofNat base).toNat]? = some w
      rw [indexNat, hw]
    have dest : (UInt32.ofNat base).toNat < s.dst.size := by rw [indexNat]; omega
    let stored : State := {s with dst := s.dst.set (UInt32.ofNat base).toNat (s.locals 0) dest}
    let next := stored.assign 0 (s.locals 0 + w)
    have step : body.exec inputs 0 (UInt32.ofNat base) s = .ok next :=
      body_ok inputs s _ w dest hread
    have size : next.dst.size = s.dst.size := by simp [next, stored, State.assign]
    have sumBound : (s.locals 0).toNat + (x + xs.sum) ≤ PackWire.maxWords := by
      simpa only [List.sum_cons] using budget
    have addOK : (s.locals 0).toNat + w.toNat ≤ PackWire.maxWords := by rw [wval]; omega
    have carry : (next.locals 0).toNat = (s.locals 0).toNat + x := by
      change (s.locals 0 + w).toNat = _
      rw [carry_add _ _ addOK, wval]
    have tailBudget : (next.locals 0).toNat + xs.sum ≤ PackWire.maxWords := by rw [carry]; omega
    have tailReads : Reads inputs.auxiliary (base + 1) xs := by
      intro k hk
      have h := physical (k + 1) (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hk)
      rw [show base + 1 + k = base + (k + 1) by omega]
      exact h
    have tailCap : n.toNat < next.dst.size := by rw [size]; exact cap
    obtain ⟨t, done_, finalSize, finalMem⟩ :=
      ih (base + 1) next (by omega) tailCap tailBudget tailReads
    refine ⟨t, ?_, finalSize.trans size, ?_⟩
    · change suffix inputs (xs.length + 1) (UInt32.ofNat base) s = _
      rw [suffix_step inputs _ _ _ next step]
      have bump : UInt32.ofNat base + 1 = UInt32.ofNat (base + 1) := (UInt32.ofNat_add base 1).symm
      rw [bump]
      exact done_
    · have mem : CountTarget.memory next.dst =
          (CountTarget.memory s.dst).write base (s.locals 0).toNat := by
        have atWord : CountTarget.memory next.dst =
            (CountTarget.memory s.dst).write (UInt32.ofNat base).toNat (s.locals 0).toNat :=
          observe_set UInt32.toNat 0 s.dst _ (s.locals 0) dest
        exact atWord.trans (congrArg (fun j => (CountTarget.memory s.dst).write j (s.locals 0).toNat) indexNat)
      rw [finalMem, carry, mem, List.scanl_cons, writes_cons]

private def initial (prior : Array UInt32) : State := (⟨fun _ => 0, prior⟩ : State).assign 0 0

/-- Kind: lowering.
Says: after the actual header read, the lowered stage initializes the carry,
executes the generic loop that many times and executes the terminal store.
Does not say: that the memory accesses inside the loop are in bounds. -/
private theorem run_suffix (inputs : Inputs) (prior : Array UInt32) (n : UInt32)
    (head : read inputs .packet 1 = .ok n) (limit : n.toNat ≤ PackWire.maxRows) :
    run inputs prior = (suffix inputs n.toNat 0 (initial prior)).map State.dst := by
  have loopOK :
      (Stmt.forRange PackWire.maxRows header body).exec inputs 0 0 (initial prior) =
        iterate (fun j st => body.exec inputs 0 j st) n.toNat 0 (initial prior) := by
    change (read inputs .packet 1).bind (fun w =>
      if w.toNat ≤ PackWire.maxRows then
        iterate (fun j st => body.exec inputs 0 j st) w.toNat 0 (initial prior)
      else .error (.loopLimit w.toNat PackWire.maxRows)) = _
    rw [head]
    exact if_pos limit
  change (((Stmt.forRange PackWire.maxRows header body).exec inputs 0 0 (initial prior)).bind
    (fun s => terminal.exec inputs 0 0 s)).map State.dst = _
  rw [loopOK] <;> rfl

/-- Kind: finite target refinement.
Says: a single lowered scan invocation reads the actual physical counts and
terminates without a fault. The finite output keeps its extent and agrees at
every slot with the DSL scan, including the terminal and any old tail words.
Does not say: that a device submitted one invocation or that a preceding count
dispatch is visible to it. -/
theorem scan_memory (inputs : Inputs) (n : Nat) (prior : Array UInt32)
    (packetN : (inputs.packet[1]?).map UInt32.toNat = some n) (limit : n ≤ PackWire.maxRows)
    (countsCap : n ≤ inputs.auxiliary.size) (offsetsCap : n + 1 ≤ prior.size)
    (total : (DSL.view n (CountTarget.memory inputs.auxiliary)).sum ≤ PackWire.maxWords) :
    ∃ out, run inputs prior = .ok out ∧ out.size = prior.size ∧ CountTarget.memory out =
      (DSL.scanDispatch n (CountTarget.memory inputs.auxiliary)).runSeq (CountTarget.memory prior) := by
  let xs := DSL.view n (CountTarget.memory inputs.auxiliary)
  have len : xs.length = n := by simp [xs, DSL.view]
  obtain ⟨w, hw, wval⟩ := Option.map_eq_some_iff.mp packetN
  have head : read inputs .packet 1 = .ok w := read_ok inputs .packet 1 w hw
  have bound : w.toNat ≤ PackWire.maxRows := by rw [wval]; exact limit
  have room : w.toNat < (initial prior).dst.size := by change w.toNat < prior.size; omega
  have budget : ((initial prior).locals 0).toNat + xs.sum ≤ PackWire.maxWords := by
    change 0 + xs.sum ≤ PackWire.maxWords
    rw [Nat.zero_add]
    exact total
  have reads : Reads inputs.auxiliary 0 xs := by
    intro i hi
    have idx : i < n := by rwa [len] at hi
    have slot := Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le idx countsCap)
    simp [xs, DSL.view, CountTarget.memory, slot]
  obtain ⟨t, done_, size, mem⟩ := suffix_sound inputs w head bound xs 0 (initial prior)
    (by omega) room budget reads
  have doneLoop : suffix inputs w.toNat 0 (initial prior) = .ok t := by
    have zero : UInt32.ofNat 0 = 0 := by decide
    simpa only [len, wval, zero] using done_
  refine ⟨t.dst, ?_, size, ?_⟩
  · rw [run_suffix _ _ w head bound, doneLoop] <;> rfl
  · change CountTarget.memory t.dst = applyWrites (CountTarget.memory prior)
      (DSL.writesFrom 0 (xs.scanl (· + ·) 0))
    exact mem

/-- Kind: observable finite offsets.
Says: all n+1 output slots equal the mathematical prefixes of the actual count
buffer, and the value read back at slot n is their total. Empty input writes zero.
Does not say: that other shader stages read the same physical buffer. -/
theorem scan_visible (inputs : Inputs) (n : Nat) (prior : Array UInt32)
    (packetN : (inputs.packet[1]?).map UInt32.toNat = some n) (limit : n ≤ PackWire.maxRows)
    (countsCap : n ≤ inputs.auxiliary.size) (offsetsCap : n + 1 ≤ prior.size)
    (total : (DSL.view n (CountTarget.memory inputs.auxiliary)).sum ≤ PackWire.maxWords) :
    ∃ out, run inputs prior = .ok out ∧
      DSL.view (n + 1) (CountTarget.memory out) =
        (DSL.view n (CountTarget.memory inputs.auxiliary)).scanl (· + ·) 0 ∧
      CountTarget.memory out n = (DSL.view n (CountTarget.memory inputs.auxiliary)).sum := by
  obtain ⟨out, done_, _, memory⟩ := scan_memory inputs n prior packetN limit countsCap offsetsCap total
  have visible : DSL.view (n + 1) (CountTarget.memory out) =
      (DSL.view n (CountTarget.memory inputs.auxiliary)).scanl (· + ·) 0 := by
    rw [memory]
    exact DSL.scan_visible n _ _ [0] (.refl _)
  refine ⟨out, done_, visible, ?_⟩
  have last := congrArg List.getLast? visible
  have splitLast : DSL.view (n + 1) (CountTarget.memory out) =
      DSL.view n (CountTarget.memory out) ++ [CountTarget.memory out n] := by
    simp [DSL.view, List.range_succ]
  rw [splitLast, List.getLast?_concat, StaticPack.scan_terminal] at last
  simpa using last

#print axioms carry_add
#print axioms scan_memory
#print axioms scan_visible

-- Compare exact finite storage, including pre-existing tail words.
#guard match run ⟨#[1, 0], #[]⟩ #[99, 23] with
  | .ok dst => dst == #[0, 23]
  | .error _ => false
#guard match run ⟨#[1, 3], #[2, 0, 4, 888]⟩ #[99, 99, 99, 99, 23] with
  | .ok dst => dst == #[0, 2, 2, 6, 23]
  | .error _ => false

end L4Factoidal.Paralliverse.ScanTarget
