/-!
# Stable packing of variable-length rows of u32 words

The CPU specification concatenates the input rows. The staged evaluator counts words,
scans those counts, scatters at the computed addresses, and reads the destination.
Its functional buffer models individual word writes to an arbitrary prior memory.
All addresses and counts are natural numbers. Capacity is measured in words.
-/

namespace L4Factoidal.GpuKernel.StaticPack

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
  readback dst 0 widths.sum

#print axioms packSpec_length
#print axioms scanFrom_length
#print axioms scanFrom_cons
#print axioms scanFrom_prefix
#print axioms admitted_total_fits

-- Executable examples. The prior values expose missing stores.
#guard scanFrom 0 [0, 2, 0, 1] == [0, 0, 2, 2]
#guard decide (Admitted [[], [8, 9], [], [8]] 3)
#guard packParallel [[], [8, 9], [], [8]] (fun _ => 17) == [8, 9, 8]
#guard packParallel [[], []] (fun _ => 17) == []
#guard packParallel [] (fun _ => 17) == []

end L4Factoidal.GpuKernel.StaticPack
