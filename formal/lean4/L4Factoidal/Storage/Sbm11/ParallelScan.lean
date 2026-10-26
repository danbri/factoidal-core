/-
L4Factoidal.Storage.Sbm11.ParallelScan — the split of a scan into block
ranges (stage 1 of issue https://github.com/danbri/factoidal/issues/799;
record docs/designissues/2026-10-12-parallel-block-scans.md).

`chunksOf c l` cuts the list `l` of selected block numbers into consecutive
chunks of at most `c` elements (`c` below 1 is read as 1), in order. The
native query driver runs one scan per chunk as a Lean task and appends the
results in chunk order. `chunksOf_flatten` is the fact that makes this a
partition: the chunks, concatenated, are `l`.

Every recursion here is a tail call with an accumulator. The fuel argument
`f` of `chunksAcc` is the list length at the start, so each step drops at
least one element.
-/
namespace L4Factoidal.Storage.Sbm11.ParallelScan

/-- The chunks of `l`, built by `chunksAcc` onto the reversed accumulator
    `acc`; `f` bounds the number of steps (the length of `l`). -/
def chunksAcc {α : Type} (n : Nat) : Nat → List α → List (List α) → List (List α)
  | 0, _, acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | f + 1, l@(_ :: _), acc => chunksAcc n f (l.drop n) (l.take n :: acc)

/-- The consecutive chunks of `l` of at most `max c 1` elements each. -/
def chunksOf {α : Type} (c : Nat) (l : List α) : List (List α) :=
  chunksAcc (max c 1) l.length l []

/-- The chunks, concatenated after the reversed accumulator. -/
theorem chunksAcc_flatten {α : Type} (n : Nat) (hn : 1 ≤ n) :
    ∀ (f : Nat) (l : List α) (acc : List (List α)), l.length ≤ f →
      (chunksAcc n f l acc).flatten = acc.reverse.flatten ++ l := by
  intro f
  induction f with
  | zero =>
    intro l acc hl
    have hnil : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp [chunksAcc]
  | succ f ih =>
    intro l acc hl
    match l, hl with
    | [], _ => simp [chunksAcc]
    | a :: t, hl =>
      have hd : ((a :: t).drop n).length ≤ f := by
        simp only [List.length_drop, List.length_cons] at hl ⊢
        omega
      simp only [chunksAcc]
      rw [ih _ _ hd]
      simp [List.reverse_cons, List.flatten_append, List.take_append_drop, List.append_assoc]

/-- The chunks of `l` concatenated are `l`. -/
theorem chunksOf_flatten {α : Type} (c : Nat) (l : List α) :
    (chunksOf c l).flatten = l := by
  unfold chunksOf
  rw [chunksAcc_flatten (max c 1) (by omega) l.length l [] (Nat.le_refl _)]
  simp

/-- Every element of a chunk is an element of `l`. -/
theorem mem_of_mem_chunksOf {α : Type} (c : Nat) (l : List α) {X : List α}
    (hX : X ∈ chunksOf c l) {k : α} (hk : k ∈ X) : k ∈ l := by
  rw [← chunksOf_flatten c l]
  exact List.mem_flatten.mpr ⟨X, hX, hk⟩

/-! ## The chunks of `List.range n` without the list (stage 1k)

`rangeChunks c n` is `chunksOf c (List.range n)` (`rangeChunks_eq`), built
from `List.range'` segments: no list of all `n` positions, no `take`, `drop`
or `length` over it. DBpedia d10 divides 5,941 selected blocks so at every
query; the list form took about 0.2 ms of the calling thread at 4 threads
(stage 1k of docs/designissues/2026-10-12-parallel-block-scans.md). -/

theorem take_range' (c : Nat) : ∀ s k, (List.range' s k).take c = List.range' s (min c k) := by
  induction c with
  | zero => intro s k; simp
  | succ c ih =>
    intro s k
    cases k with
    | zero => simp
    | succ k =>
      rw [List.range'_succ, List.take_succ_cons, ih, Nat.succ_min_succ, List.range'_succ]

theorem drop_range' (c : Nat) : ∀ s k, (List.range' s k).drop c = List.range' (s + c) (k - c) := by
  induction c with
  | zero => intro s k; simp
  | succ c ih =>
    intro s k
    cases k with
    | zero => simp
    | succ k =>
      rw [List.range'_succ, List.drop_succ_cons, ih]
      congr 1 <;> omega

/-- The chunks from position `s` on (fuel `f`), onto the reversed
    accumulator `acc`. A tail call per chunk. -/
def rangeChunksGo (c n : Nat) : Nat → Nat → List (List Nat) → List (List Nat)
  | 0, _, acc => acc.reverse
  | f + 1, s, acc =>
    if n ≤ s then acc.reverse
    else rangeChunksGo c n f (s + c) (List.range' s (min c (n - s)) :: acc)

theorem rangeChunksGo_eq (c n : Nat) : ∀ f s acc,
    rangeChunksGo c n f s acc = chunksAcc c f (List.range' s (n - s)) acc := by
  intro f
  induction f with
  | zero => intro s acc; simp [rangeChunksGo, chunksAcc]
  | succ f ih =>
    intro s acc
    unfold rangeChunksGo
    split
    · rename_i h
      rw [show n - s = 0 by omega]
      simp [chunksAcc]
    · rename_i h
      obtain ⟨k, hk⟩ : ∃ k, n - s = k + 1 := ⟨n - s - 1, by omega⟩
      rw [hk, List.range'_succ]
      simp only [chunksAcc]
      rw [← List.range'_succ, ih, drop_range', take_range', ← hk]
      congr 2
      omega

/-- `chunksOf c (List.range n)` (`rangeChunks_eq`). -/
def rangeChunks (c n : Nat) : List (List Nat) := rangeChunksGo (max c 1) n n 0 []

theorem rangeChunks_eq (c n : Nat) : rangeChunks c n = chunksOf c (List.range n) := by
  unfold rangeChunks chunksOf
  rw [rangeChunksGo_eq, List.length_range, List.range_eq_range']
  simp

/-! ## The chunks as bounds (stage 1k)

`rangeBounds c n` gives each chunk of `rangeChunks c n` as its bounds
`(lo, hi)`: `(rangeBounds c n).map boundsList = rangeChunks c n`
(`rangeBounds_map`). A job of the worker pool that gets a pair of numbers
makes the list of its positions itself. A list that the calling thread made
and gave to a job is reachable from two threads, so the calling thread freed
each of its cells with an atomic operation at the end of the query (DBpedia
d10 at 4 threads, 5,941 positions: about 0.25 ms). -/

/-- The positions `lo, ..., hi - 1`. -/
def boundsList (p : Nat × Nat) : List Nat := List.range' p.1 (p.2 - p.1)

/-- The bounds of the chunks from position `s` on (fuel `f`), onto the
    reversed accumulator `acc`. A tail call per chunk. -/
def rangeBoundsGo (c n : Nat) : Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, acc => acc.reverse
  | f + 1, s, acc =>
    if n ≤ s then acc.reverse
    else rangeBoundsGo c n f (s + c) ((s, s + min c (n - s)) :: acc)

/-- The bounds of the chunks of `rangeChunks c n` (`rangeBounds_map`). -/
def rangeBounds (c n : Nat) : List (Nat × Nat) := rangeBoundsGo (max c 1) n n 0 []

theorem rangeBoundsGo_map (c n : Nat) : ∀ f s acc,
    (rangeBoundsGo c n f s acc).map boundsList = rangeChunksGo c n f s (acc.map boundsList) := by
  intro f
  induction f with
  | zero => intro s acc; simp [rangeBoundsGo, rangeChunksGo, List.map_reverse]
  | succ f ih =>
    intro s acc
    unfold rangeBoundsGo rangeChunksGo
    split
    · simp [List.map_reverse]
    · rw [ih]
      simp [boundsList]

theorem rangeBounds_map (c n : Nat) : (rangeBounds c n).map boundsList = rangeChunks c n := by
  simp [rangeBounds, rangeChunks, rangeBoundsGo_map]

/-! ## Ranges cut at given points (issue 961, stage 1m)

`cutBounds n cs`: consecutive ranges of `0, ..., n - 1` that end at the cut
points `cs` (each clamped to the previous end and to `n`; an empty range is
left out), then a last range to `n`. Any list of cut points gives ranges that
concatenate to `List.range n` (`cutBounds_flatten`), so the cut points can be
chosen by a heuristic (the estimated work of each block) and the theorems over
partitions of the block list still apply. -/

/-- The ranges from `lo` on, onto the reversed accumulator `acc`. A tail call
    per cut point. -/
def cutBoundsGo (n : Nat) : List Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], lo, acc => if lo < n then ((lo, n) :: acc).reverse else acc.reverse
  | c :: cs, lo, acc =>
    let hi := max lo (min n c)
    if hi == lo then cutBoundsGo n cs lo acc else cutBoundsGo n cs hi ((lo, hi) :: acc)

/-- The ranges of `0, ..., n - 1` cut at `cs`. -/
def cutBounds (n : Nat) (cs : List Nat) : List (Nat × Nat) := cutBoundsGo n cs 0 []

theorem range'_append_le {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    List.range' a (b - a) ++ List.range' b (c - b) = List.range' a (c - a) := by
  have h := List.range'_append (s := a) (m := b - a) (n := c - b) (step := 1)
  have e1 : a + 1 * (b - a) = b := by omega
  have e2 : b - a + (c - b) = c - a := by omega
  rw [e1, e2] at h
  exact h

theorem cutBoundsGo_flatten (n : Nat) : ∀ (cs : List Nat) (lo : Nat) (acc : List (Nat × Nat)),
    lo ≤ n →
    ((cutBoundsGo n cs lo acc).map boundsList).flatten
      = (acc.reverse.map boundsList).flatten ++ List.range' lo (n - lo) := by
  intro cs
  induction cs with
  | nil =>
    intro lo acc hlo
    unfold cutBoundsGo
    split
    · simp [boundsList]
    · have : n - lo = 0 := by omega
      simp [this]
  | cons c cs ih =>
    intro lo acc hlo
    unfold cutBoundsGo
    simp only
    split
    · exact ih lo acc hlo
    · rename_i hne
      have hhi : max lo (min n c) ≤ n := by omega
      have hlh : lo ≤ max lo (min n c) := by omega
      rw [ih _ _ hhi]
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
      congr 1
      simp only [boundsList]
      exact range'_append_le hlh hhi

/-- **The cut ranges cover the positions in order.** -/
theorem cutBounds_flatten (n : Nat) (cs : List Nat) :
    ((cutBounds n cs).map boundsList).flatten = List.range n := by
  unfold cutBounds
  rw [cutBoundsGo_flatten n cs 0 [] (Nat.zero_le n)]
  simp [List.range_eq_range']

/-- Cut points for `k` ranges of about equal weight: after position `i`
    when the weights of positions `0, ..., i` reach `j / k` of the total, for
    `j = 1, ..., k - 1` (at most one cut per position). A loop. Any result is
    correct for `cutBounds` (`cutBounds_flatten`). -/
def weightCutsGo (ws : Array Nat) (k tot : Nat) : Nat → Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, _, out => out.reverse
  | f + 1, i, acc, j, out =>
    if h : i < ws.size then
      let acc' := acc + ws[i]
      if j < k && j * tot ≤ acc' * k then weightCutsGo ws k tot f (i + 1) acc' (j + 1) ((i + 1) :: out)
      else weightCutsGo ws k tot f (i + 1) acc' j out
    else out.reverse

def weightCuts (ws : Array Nat) (k : Nat) : List Nat :=
  weightCutsGo ws k (ws.foldl (· + ·) 0) ws.size 0 0 1 []

end L4Factoidal.Storage.Sbm11.ParallelScan
