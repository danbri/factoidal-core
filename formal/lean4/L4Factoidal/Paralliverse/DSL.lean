import L4Factoidal.Paralliverse.StaticPack
import L4Factoidal.GpuKernel.Race

/-!
# Paralliverse's typed packing program

A stage reads immutable input and produces a completed buffer for the next stage. Its
schedule orders whole invocations. The serial scan consists of one invocation, including
on empty input, and writes a final offset at the row count. All addresses are word
addresses in mathematical memories. Device synchronisation and instruction-level
interleavings require separate models.
-/

namespace L4Factoidal.Paralliverse.DSL
open L4Factoidal.GpuKernel

/-- Read the first n entries of a memory in address order. -/
def view {α : Type} (n : Nat) (m : Mem α) : List α := (List.range n).map m

/-- Individual writes assigning successive addresses to the supplied values. -/
def writesFrom {α : Type} (base : Nat) (xs : List α) : List (Nat × α) :=
  (List.range' base xs.length).zip xs

def countDispatch (rows : StaticPack.Rows) : Dispatch Nat where
  n := rows.length
  writes t := [(t, (rows.getD t []).length)]

/-- Invocation 0 reads counts and writes every prefix, including the terminal offset. -/
def scanDispatch (n : Nat) (countsMem : Mem Nat) : Dispatch Nat where
  n := 1
  writes _ := writesFrom 0 ((view n countsMem).scanl (· + ·) 0)

def scatterDispatch (rows : StaticPack.Rows) (offsetsMem : Mem Nat) : Dispatch UInt32 where
  n := rows.length
  writes t := writesFrom (offsetsMem t) (rows.getD t [])

structure Orders where
  count : List Nat
  scan : List Nat
  scatter : List Nat

def Valid (n : Nat) (s : Orders) : Prop :=
  s.count.Perm (List.range n) ∧ s.scan.Perm [0] ∧ s.scatter.Perm (List.range n)

def canonical (n : Nat) : Orders := ⟨List.range n, [0], List.range n⟩

/-- Invariant.
Says: there is a valid invocation schedule for every row count, including zero.
Does not say: that a particular device will make progress. -/
theorem canonical_valid (n : Nat) : Valid n (canonical n) :=
  ⟨.refl _, .refl _, .refl _⟩

structure Initial where
  counts : Mem Nat
  offsets : Mem Nat
  words : Mem UInt32

structure Env where
  rows : StaticPack.Rows
  initial : Initial
  orders : Orders

inductive Phase where
  | input | counted | scanned | packed

inductive Stage : Phase → Phase → Type where
  | count : Stage .input .counted
  | serialScan : Stage .counted .scanned
  | scatter : Stage .scanned .packed

inductive Program : Phase → Phase → Type where
  | done : Program p p
  | step : Stage p q → Program q r → Program p r

structure Counted where
  slots : Mem Nat

structure Scanned where
  slots : Mem Nat

structure Packed where
  total : Nat
  words : Mem UInt32

def Packed.read (result : Packed) : List UInt32 := StaticPack.readback result.words 0 result.total

def State : Phase → Type
  | .input => Unit
  | .counted => Counted
  | .scanned => Scanned
  | .packed => Packed

def evalStage (e : Env) {p q : Phase} : Stage p q → State p → State q
  | .count, _ => ⟨(countDispatch e.rows).runOrder e.initial.counts e.orders.count⟩
  | .serialScan, c => ⟨(scanDispatch e.rows.length c.slots).runOrder e.initial.offsets e.orders.scan⟩
  | .scatter, o =>
    ⟨o.slots e.rows.length, (scatterDispatch e.rows o.slots).runOrder e.initial.words e.orders.scatter⟩

def eval (e : Env) {p q : Phase} : Program p q → State p → State q
  | .done, v => v
  | .step op rest, v => eval e rest (evalStage e op v)

def packProgram : Program .input .packed :=
  .step .count (.step .serialScan (.step .scatter .done))

/-- Invariant.
Says: different count invocations write different slots in the count memory.
Does not say: that an external host supplies separate count and source bindings. -/
theorem count_raceFree (rows : StaticPack.Rows) : (countDispatch rows).RaceFree := by
  intro t u _ _ hne i hit hiu
  have ht : i = t := by simpa [countDispatch, keys] using hit
  have hu : i = u := by simpa [countDispatch, keys] using hiu
  exact hne (ht.symm.trans hu)

/-- Invariant.
Says: a count slot changes exactly when its invocation is present.
Does not say: that an incomplete invocation order is a valid schedule. -/
private theorem count_at (rows : StaticPack.Rows) (m : Mem Nat) (s : List Nat) (i : Nat) :
    (countDispatch rows).runOrder m s i =
      if i ∈ s then (rows.getD i []).length else m i := by
  induction s generalizing m with
  | nil => simp [Dispatch.runOrder]
  | cons t ts ih =>
    change (countDispatch rows).runOrder (m.write t (rows.getD t []).length) ts i = _
    rw [ih]
    by_cases h : i = t
    · subst i
      simp [Mem.write]
    · simp [Mem.write, h]

/-- Refinement.
Says: after any valid count dispatch the visible count buffer contains the length of every row.
Does not say: that a subsequent physical dispatch can see the buffer without synchronisation. -/
theorem count_visible (rows : StaticPack.Rows) (prior : Mem Nat) (s : List Nat)
    (hs : s.Perm (List.range rows.length)) :
    view rows.length ((countDispatch rows).runOrder prior s) = StaticPack.counts rows := by
  rw [(countDispatch rows).runOrder_perm (count_raceFree rows) s hs prior]
  change view rows.length ((countDispatch rows).runOrder prior (List.range rows.length)) = _
  apply List.ext_getElem
  · simp [view, StaticPack.counts]
  · intro i _ hi
    have hr : i < rows.length := by simpa [StaticPack.counts] using hi
    have hm := List.mem_range.mpr hr
    simp only [view, List.getElem_map, List.getElem_range, count_at, if_pos hm,
      StaticPack.counts, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]

/-- Invariant.
Says: an indexed burst names exactly the consecutive addresses of its input.
Does not say: that these addresses fit in a device allocation. -/
private theorem keys_writesFrom {α : Type} (base : Nat) (xs : List α) :
    keys (writesFrom base xs) = List.range' base xs.length :=
  List.map_fst_zip (by simp)

/-- Invariant.
Says: the indexed writes place a value at base plus its local index.
Does not say: that later stages preserve that memory. -/
private theorem burst_at {α : Type} (xs : List α) (base : Nat) (prior : Mem α)
    (i : Nat) (hi : i < xs.length) :
    applyWrites prior (writesFrom base xs) (base + i) = xs[i] := by
  induction xs generalizing base prior i with
  | nil => simp at hi
  | cons x xs ih =>
    have hw : writesFrom base (x :: xs) = (base, x) :: writesFrom (base + 1) xs := by
      simp [writesFrom, List.range'_succ]
    rw [hw]
    change applyWrites (prior.write base x) (writesFrom (base + 1) xs) (base + i) = _
    cases i with
    | zero =>
      have hm : base ∉ keys (writesFrom (base + 1) xs) := by
        rw [keys_writesFrom, List.mem_range'_1]
        omega
      change applyWrites (prior.write base x) (writesFrom (base + 1) xs) base = x
      rw [applyWrites_apply _ _ base, lastWrite_none _ _ hm]
      simp [Mem.write]
    | succ i =>
      have h : i < xs.length := by simpa using hi
      rw [show base + (i + 1) = (base + 1) + i by omega]
      exact ih (base + 1) _ i h

/-- Invariant.
Says: reading a completed indexed burst from zero recovers its inputs.
Does not say: that any specific hardware implements the word memory. -/
private theorem view_burst {α : Type} (xs : List α) (prior : Mem α) :
    view xs.length (applyWrites prior (writesFrom 0 xs)) = xs := by
  apply List.ext_getElem
  · simp [view]
  · intro i _ hi
    simp only [view, List.getElem_map, List.getElem_range]
    simpa only [Nat.zero_add] using burst_at xs 0 prior i hi

/-- Refinement.
Says: the completed serial scan writes all prefixes and the terminal total of the counts
it actually read, for every count memory and every valid scan schedule.
Does not say: that a parallel workgroup scan or a physical barrier has these semantics. -/
theorem scan_visible (n : Nat) (countsMem prior : Mem Nat) (s : List Nat) (hs : s.Perm [0]) :
    view (n + 1) ((scanDispatch n countsMem).runOrder prior s) = (view n countsMem).scanl (· + ·) 0 := by
  rw [hs.eq_singleton]
  change view (n + 1) (applyWrites prior (writesFrom 0 ((view n countsMem).scanl (· + ·) 0))) = _
  simpa only [List.length_scanl, view, List.length_map, List.length_range] using
    view_burst ((view n countsMem).scanl (· + ·) 0) prior

#print axioms canonical_valid
#print axioms count_raceFree
#print axioms count_visible
#print axioms scan_visible

-- Probe the actual memories, including a scan whose inputs are supplied independently.
#guard view 4 ((scanDispatch 3 (fun i => [2, 0, 1].getD i 9)).runOrder (fun _ => 8) [0]) == [0, 2, 2, 3]
#guard view 3 ((scatterDispatch [[11], [22]] (fun i => if i = 0 then 2 else 0)).runOrder
  (fun _ => 17) [1, 0]) == [22, 17, 11]
#guard (eval ⟨[], ⟨fun _ => 4, fun _ => 9, fun _ => 23⟩, canonical 0⟩ packProgram ()).read == []
#guard (eval ⟨[[], [9, 8], [], [9]], ⟨fun _ => 4, fun _ => 7, fun _ => 23⟩,
  ⟨[2, 0, 3, 1], [0], [1, 3, 0, 2]⟩⟩ packProgram ()).read == [9, 8, 9]
#guard view 2 ((countDispatch [[7], []]).runOrder (fun _ => 3) [0]) == [1, 3]

end L4Factoidal.Paralliverse.DSL
