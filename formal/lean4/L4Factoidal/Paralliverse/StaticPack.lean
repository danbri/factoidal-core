/-!
# Stable packing of variable-length rows of u32 words

The CPU specification concatenates the input rows. The staged evaluator counts words,
scans those counts, scatters at the computed addresses, and reads the destination.
Its functional buffer models individual word writes to an arbitrary prior memory.
All addresses and counts are natural numbers. Capacity is measured in words.
-/

namespace L4Factoidal.Paralliverse.StaticPack

abbrev Rows := List (List UInt32)
abbrev Buffer := Nat → UInt32

/-- Ordinary CPU specification, independent of the scan and scatter. -/
def packSpec (rows : Rows) : List UInt32 := rows.flatten

/-- One word count per row, including empty rows. -/
def counts (rows : Rows) : List Nat := rows.map List.length

/-- Exclusive prefix sums. Only the starting offset of each row is retained. -/
def scanFrom (base : Nat) (widths : List Nat) : List Nat :=
  (widths.scanl (· + ·) base).take widths.length

/-- Invariant.
Says: the sum of the row counts is exactly the number of output words.
Does not say: that the destination has room for those words. -/
theorem packSpec_length (rows : Rows) : (packSpec rows).length = (counts rows).sum :=
  List.length_flatten

/-- Invariant.
Says: each row has one starting offset, including a row with zero words.
Does not say: that the starting offsets are distinct. -/
theorem scanFrom_length (base : Nat) (widths : List Nat) :
    (scanFrom base widths).length = widths.length := by
  simp [scanFrom]

/-- Invariant.
Says: the first row starts at the given base and shifts the next base by its count.
Does not say: that any device has executed the scan. -/
theorem scanFrom_cons (base width : Nat) (widths : List Nat) :
    scanFrom base (width :: widths) = base :: scanFrom (base + width) widths := by
  simp [scanFrom]

/-- Invariant.
Says: the computed start of any row equals the base plus the sum of preceding counts.
Does not say: that a zero-length row has a different start from its successor. -/
theorem scanFrom_prefix (base : Nat) (pre : List Nat) (width : Nat) (rest : List Nat) :
    (scanFrom base (pre ++ width :: rest))[pre.length]? = some (base + pre.sum) := by
  induction pre generalizing base with
  | nil => simp [scanFrom_cons]
  | cons w ws ih =>
    simpa only [List.cons_append, List.length_cons, scanFrom_cons,
      List.getElem?_cons_succ, List.sum_cons, Nat.add_assoc] using ih (base + w)

/-- Invariant.
Says: the terminal accumulator of the scan is the exclusive end of the entire output.
Does not say: that the terminal accumulator is one of the per-row starting offsets. -/
theorem scan_terminal (base : Nat) (widths : List Nat) :
    (widths.scanl (· + ·) base).getLast? = some (base + widths.sum) := by
  rw [List.getLast?_scanl]
  induction widths generalizing base with
  | nil => simp
  | cons w ws ih =>
    simpa only [List.foldl_cons, List.sum_cons, Nat.add_assoc] using ih (base + w)

/-- Invariant.
Says: every computed start and its exclusive end lie within the total span.
Does not say: that each row writes at least one word. -/
theorem scanFrom_bounds (base : Nat) (widths : List Nat) (span : Nat × Nat)
    (h : span ∈ (scanFrom base widths).zip widths) :
    base ≤ span.1 ∧ span.1 + span.2 ≤ base + widths.sum := by
  induction widths generalizing base with
  | nil => simp [scanFrom] at h
  | cons w ws ih =>
    rw [scanFrom_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · constructor <;> simp
    · obtain ⟨lo, hi⟩ := ih (base + w) h
      constructor
      · omega
      · simpa only [List.sum_cons, Nat.add_assoc] using hi

/-- Invariant.
Says: each earlier row ends at or before each later row starts, so their half-open
write ranges are disjoint even when one of them is empty.
Does not say: that a device schedule or a barrier realises these ranges. -/
theorem scanFrom_disjoint (base : Nat) (widths : List Nat) :
    ((scanFrom base widths).zip widths).Pairwise (fun a b => a.1 + a.2 ≤ b.1) := by
  induction widths generalizing base with
  | nil => simp [scanFrom]
  | cons w ws ih =>
    rw [scanFrom_cons, List.zip_cons_cons, List.pairwise_cons]
    exact ⟨fun span h => (scanFrom_bounds (base + w) ws span h).1, ih (base + w)⟩

/-- Admission for word addresses. Device buffer limits, launch geometry, and the
memory available to a CPU are separate resource limits. -/
def Admitted (rows : Rows) (capacity : Nat) : Prop :=
  rows.length < UInt32.size ∧ (counts rows).sum ≤ capacity ∧ capacity < UInt32.size

instance (rows : Rows) (capacity : Nat) : Decidable (Admitted rows capacity) := by
  unfold Admitted
  infer_instance

/-- Invariant.
Says: the total number of words fits in u32 for an admitted destination.
Does not say: that converting a word offset to a byte offset fits in u32. -/
theorem admitted_total_fits (rows : Rows) (capacity : Nat) (h : Admitted rows capacity) :
    (counts rows).sum < UInt32.size :=
  Nat.lt_of_le_of_lt h.2.1 h.2.2

/-- Invariant.
Says: each local word of an admitted row span addresses a slot below the capacity
and below the u32 limit.
Does not say: that the corresponding byte address or dispatch size fits a device. -/
theorem admitted_word_bounds (rows : Rows) (capacity : Nat) (h : Admitted rows capacity)
    (span : Nat × Nat) (hs : span ∈ (scanFrom 0 (counts rows)).zip (counts rows))
    (k : Nat) (hk : k < span.2) : span.1 + k < capacity ∧ span.1 + k < UInt32.size := by
  have hend := (scanFrom_bounds 0 (counts rows) span hs).2
  have hcap := h.2.1
  have hfit := h.2.2
  constructor <;> omega

/-- Install a row one word at a time, starting at its assigned address. -/
def scatterRow : List UInt32 → Nat → Buffer → Buffer
  | [], _, dst => dst
  | v :: vs, start, dst =>
    scatterRow vs (start + 1) (fun addr => if addr = start then v else dst addr)

/-- Each row uses its supplied start. The evaluator supplies an offset for every row. -/
def scatter (starts : List Nat) (rows : Rows) (dst : Buffer) : Buffer :=
  (starts.zip rows).foldl (fun prior row => scatterRow row.2 row.1 prior) dst

/-- Observe a finite window in the resulting memory. -/
def readback (dst : Buffer) (base length : Nat) : List UInt32 :=
  (List.range' base length).map dst

/-- Sequential meaning of the three packing stages on a mathematical word buffer. -/
def packParallel (rows : Rows) (prior : Buffer) : List UInt32 :=
  let widths := counts rows
  let dst := scatter (scanFrom 0 widths) rows prior
  readback dst 0 (widths.foldl (· + ·) 0)

/-- Invariant.
Says: consecutive row writes compose at the first row's exclusive end.
Does not say: that overlapping rows may be written in either order. -/
private theorem scatterRow_append (xs ys : List UInt32) (base : Nat) (prior : Buffer) :
    scatterRow (xs ++ ys) base prior =
      scatterRow ys (base + xs.length) (scatterRow xs base prior) := by
  induction xs generalizing base prior with
  | nil => simp [scatterRow]
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons, scatterRow, ih]
    rw [show base + 1 + xs.length = base + (xs.length + 1) by omega]

/-- Refinement.
Says: scattering rows at their computed starts writes the same whole memory as writing
the CPU specification's words consecutively from the base.
Does not say: that the buffer has a particular initial value or representation. -/
theorem scatter_eq_scatterRow (rows : Rows) (base : Nat) (prior : Buffer) :
    scatter (scanFrom base (counts rows)) rows prior = scatterRow (packSpec rows) base prior := by
  induction rows generalizing base prior with
  | nil => simp [counts, scanFrom, scatter, packSpec, scatterRow]
  | cons row rows ih =>
    simp only [counts, List.map_cons, scanFrom_cons, scatter, List.zip_cons_cons,
      List.foldl_cons, packSpec, List.flatten_cons, scatterRow_append]
    exact ih (base + row.length) (scatterRow row base prior)

/-- Invariant.
Says: a row write preserves every address below its start.
Does not say: that the address belongs to an allocated device buffer. -/
private theorem scatterRow_before (xs : List UInt32) (base addr : Nat) (prior : Buffer)
    (h : addr < base) : scatterRow xs base prior addr = prior addr := by
  induction xs generalizing base prior with
  | nil => rfl
  | cons x xs ih =>
    simp only [scatterRow]
    rw [ih (base + 1) _ (by omega)]
    simp [Nat.ne_of_lt h]

/-- Invariant.
Says: a row write preserves every address at or above its exclusive end.
Does not say: that any address in the row retains its old value. -/
private theorem scatterRow_after (xs : List UInt32) (base addr : Nat) (prior : Buffer)
    (h : base + xs.length ≤ addr) : scatterRow xs base prior addr = prior addr := by
  induction xs generalizing base prior with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at h
    have ht : base + 1 + xs.length ≤ addr := by omega
    have hn : addr ≠ base := by omega
    simp only [scatterRow]
    rw [ih (base + 1) _ ht]
    simp [hn]

/-- Invariant.
Says: at every address outside the half-open output interval, the complete scatter
preserves the arbitrary prior memory.
Does not say: that the prior memory is zero-filled or that it has a physical allocation. -/
theorem scatter_frame (rows : Rows) (base addr : Nat) (prior : Buffer)
    (h : addr < base ∨ base + (counts rows).sum ≤ addr) :
    scatter (scanFrom base (counts rows)) rows prior addr = prior addr := by
  rw [scatter_eq_scatterRow]
  rcases h with before | beyond
  · exact scatterRow_before (packSpec rows) base addr prior before
  · apply scatterRow_after
    simpa only [packSpec_length] using beyond

/-- Invariant.
Says: reading the words of a consecutively written row in address order gives that row.
Does not say: that a particular GPU performed those writes. -/
private theorem readback_scatterRow (xs : List UInt32) (base : Nat) (prior : Buffer) :
    readback (scatterRow xs base prior) base xs.length = xs := by
  induction xs generalizing base prior with
  | nil => simp [readback]
  | cons x xs ih =>
    let first : Buffer := fun addr => if addr = base then x else prior addr
    change (List.range' base (xs.length + 1)).map (scatterRow xs (base + 1) first) = x :: xs
    rw [List.range'_succ, List.map_cons]
    change scatterRow xs (base + 1) first base ::
      readback (scatterRow xs (base + 1) first) (base + 1) xs.length = x :: xs
    simp only [ih, scatterRow_before xs (base + 1) base first (by omega), first, if_pos rfl]

/-- Refinement.
Says: for all rows and all prior word memories, count, exclusive scan and indexed scatter
produce the CPU specification's complete list in the same order.
Does not say: that a shader, driver or parallel schedule implements these stages. -/
theorem packParallel_eq_packSpec (rows : Rows) (prior : Buffer) :
    packParallel rows prior = packSpec rows := by
  change readback (scatter (scanFrom 0 (counts rows)) rows prior) 0 ((counts rows).foldl (· + ·) 0) = _
  rw [← List.sum_eq_foldl_nat, scatter_eq_scatterRow, ← packSpec_length, readback_scatterRow]

/-- Invariant.
Says: the local word at index k in a row appears at the prefix word count plus k
in the staged output, even when the same value occurs elsewhere.
Does not say: that values uniquely identify their source row. -/
theorem packParallel_position (pre : Rows) (row : List UInt32) (rest : Rows)
    (k : Nat) (hk : k < row.length) (prior : Buffer) :
    (packParallel (pre ++ row :: rest) prior)[(counts pre).sum + k]? = some row[k] := by
  rw [packParallel_eq_packSpec]
  change ((pre ++ row :: rest).flatten)[(counts pre).sum + k]? = some row[k]
  have hpre : (counts pre).sum = pre.flatten.length := (packSpec_length pre).symm
  rw [List.flatten_append, List.flatten_cons, hpre,
    List.getElem?_append_right (Nat.le_add_right pre.flatten.length k),
    Nat.add_sub_cancel_left, List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

/-- Check word admission before constructing the scanned offsets, stores, or readback. -/
def packChecked (rows : Rows) (capacity : Nat) (prior : Buffer) : Option (List UInt32) :=
  if Admitted rows capacity then some (packParallel rows prior) else none

/-- Refinement.
Says: the checked evaluator returns all CPU words on admission and refuses otherwise.
Does not say: that passing arithmetic admission suffices for a GPU launch. -/
theorem packChecked_eq (rows : Rows) (capacity : Nat) (prior : Buffer) :
    packChecked rows capacity prior =
      if Admitted rows capacity then some (packSpec rows) else none := by
  simp only [packChecked, packParallel_eq_packSpec]

/-- Select the CPU specification when no capacity is offered or when the candidate is
refused. An offered capacity selects only the staged Lean model in this module. -/
def packWithFallback (rows : Rows) (candidateCapacity : Option Nat) (prior : Buffer) : List UInt32 :=
  match candidateCapacity with
  | none => packSpec rows
  | some capacity =>
    match packChecked rows capacity prior with
    | none => packSpec rows
    | some packed => packed

/-- Refinement.
Says: both the checked staged path and direct CPU fallback yield the CPU result.
Does not say: that a host discovers adapters or recovers from device loss. -/
theorem packWithFallback_eq_packSpec (rows : Rows) (candidateCapacity : Option Nat) (prior : Buffer) :
    packWithFallback rows candidateCapacity prior = packSpec rows := by
  cases candidateCapacity with
  | none => rfl
  | some capacity =>
    by_cases h : Admitted rows capacity <;> simp [packWithFallback, packChecked_eq, h]

#print axioms packSpec_length
#print axioms scanFrom_length
#print axioms scanFrom_cons
#print axioms scanFrom_prefix
#print axioms scan_terminal
#print axioms scanFrom_bounds
#print axioms scanFrom_disjoint
#print axioms admitted_total_fits
#print axioms admitted_word_bounds
#print axioms scatter_eq_scatterRow
#print axioms scatter_frame
#print axioms packParallel_eq_packSpec
#print axioms packParallel_position
#print axioms packChecked_eq
#print axioms packWithFallback_eq_packSpec

-- Executable examples. The prior values expose missing stores.
#guard scanFrom 0 [0, 2, 0, 1] == [0, 0, 2, 2]
#guard decide (Admitted [[], [8, 9], [], [8]] 3)
#guard packParallel [[], [8, 9], [], [8]] (fun _ => 17) == [8, 9, 8]
#guard packParallel [[], []] (fun _ => 17) == []
#guard packParallel [] (fun _ => 17) == []

#guard readback (scatter [1, 3] [[9], [8]] (fun _ => 17)) 0 5 == [17, 9, 17, 8, 17]
#guard packChecked [[], [0, 0xffffffff], []] 2 (fun _ => 17) == some [0, 0xffffffff]
#guard packChecked [[4]] 0 (fun _ => 17) == none
#guard packChecked [] UInt32.size (fun _ => 17) == none
#guard packChecked [] (UInt32.size - 1) (fun _ => 17) == some []
#guard packWithFallback [[4, 4], [], [3]] none (fun _ => 17) == [4, 4, 3]
#guard packWithFallback [[4, 4], [], [3]] (some 2) (fun _ => 17) == [4, 4, 3]


end L4Factoidal.Paralliverse.StaticPack
