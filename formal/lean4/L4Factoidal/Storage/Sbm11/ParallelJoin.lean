/-
L4Factoidal.Storage.Sbm11.ParallelJoin — the merge join and the ORDER BY sort
of the SBM11 id path, divided into ranges (KR 1.2 of OKR batch 3,
https://github.com/danbri/factoidal/issues/875; costs named in
https://github.com/danbri/factoidal/issues/961; record
docs/designissues/2026-10-12-parallel-block-scans.md, stage 1f).

Merge join. `Qlvr.mergeJoin` walks the left and the right join columns once
(`mergeGo`). Here the left rows are cut into consecutive ranges
(`ranges`). For a range `[lo, hi)` the walk starts at left row `lo` and at
the first right row whose join value is not below the left value of row `lo`
(`lowerBound`, a binary search), and stops at left row `hi` (`rangePairs`).
The index pairs of the ranges, appended in range order (`concatPairs`), are
the index pairs of the single walk: `ParallelJoinTheorems.mergeJoinRanges_eq`
proves `mergeJoinRanges l r v rs = mergeJoin l r v` for join columns in
non-decreasing order and ranges that cover the left rows in order. The
native driver computes `rangePairs` of each range in a task and appends the
results in range order (`IdQuery.mergeJoinParM`).

ORDER BY sort. `Qlvr.mergeSortBy` is a bottom-up merge sort: pass `k`
merges runs of width `2^k`. A pass of width below `w`, for `w` a power of two,
merges only inside the aligned blocks `[i w, (i + 1) w)`, so sorting each
block alone and then running the passes from width `w` on the concatenation
(`sortFromWidth`) gives the array of `mergeSortBy`. That equality is checked
by the `#guard`s below and by `tests/sbm11/threads.sh` (byte-identical
answers at 1, 2, 4 and 8 threads); it is not proved.

Every recursion here is a tail call with a fuel argument.
-/
import L4Factoidal.Qlvr.Bgp
import L4Factoidal.Qlvr.Sort

namespace L4Factoidal.Storage.Sbm11.ParallelJoin

open L4Factoidal.Qlvr

/-! ## The merge join in left row ranges -/

/-- Binary search in rows `[lo, hi)` of a non-decreasing column `B`: the
    first row whose value is not below `a`, or `hi` (a tail call with
    fuel). -/
@[specialize] def lbGo (B : Nat → UInt64) (a : UInt64) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      if B ((lo + hi) / 2) < a then lbGo B a f ((lo + hi) / 2 + 1) hi
      else lbGo B a f lo ((lo + hi) / 2)
    else lo

/-- The first of rows `[0, n)` of `B` whose value is not below `a` (`n` when
    there is none). -/
@[inline] def lowerBound (B : Nat → UInt64) (n : Nat) (a : UInt64) : Nat := lbGo B a (n + 1) 0 n

/-- The merge loop for the left rows `[lo, hi)`: from left row `lo` and the
    first right row whose value is not below the left value of row `lo`. -/
@[inline] def rangePairs (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nr lo hi : Nat) : Array Nat × Array Nat :=
  mergeGo A B ok hi nr (hi - lo + (nr - lowerBound B nr (A lo)) + 1) lo (lowerBound B nr (A lo)) #[] #[]

/-- The left and the right index arrays of several ranges, appended in
    order. -/
def concatPairs (parts : List (Array Nat × Array Nat)) : Array Nat × Array Nat :=
  parts.foldl (fun acc p => (acc.1 ++ p.1, acc.2 ++ p.2)) (#[], #[])

/-- Consecutive ranges `[lo, lo + step)` from `lo` to `n` (the last one ends
    at `n`), onto the reversed accumulator (a tail call with fuel). -/
def rangesAcc (n step : Nat) : Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, lo, acc => ((lo, n) :: acc).reverse
  | f + 1, lo, acc =>
    if lo + step < n then rangesAcc n step f (lo + step) ((lo, lo + step) :: acc)
    else ((lo, n) :: acc).reverse

/-- At most `k` (and at least 1) consecutive ranges of nearly equal size
    that cover `[0, n)` in order. -/
def ranges (n k : Nat) : List (Nat × Nat) :=
  rangesAcc n (max 1 ((n + k - 1) / max k 1)) k 0 []

/-- The other shared columns of the join of `l` and `r` on `v` (the columns
    `Qlvr.mergeJoin` compares after the join column). -/
def otherCols (l r : Table) (v : String) : Array (Nat × Nat) :=
  (sharedCols l r).filter fun (a, _) => a != (l.idx v).getD 0

/-- The join column test of `Qlvr.mergeJoin`: the other shared columns
    `others` of left row `x` and right row `y` are equal. -/
@[inline] def joinOk (l r : Table) (others : Array (Nat × Nat)) (x y : Nat) : Bool :=
  others.all (fun (p, q) => l.at p x == r.at q y)

/-- `rangePairs` of the join of `l` and `r` on `v` for the range `[lo, hi)`,
    written as the list `[lo, hi]` (the chunk form of `IdQuery.Par.fold`).
    The two join columns are read from local names, so that the merge loop is
    specialised to reads of two byte arrays: with the columns passed as
    closures, every row read was a closure call that boxed its `UInt64` (an
    allocation per row in each task; olympics q07 at 4 threads, the join took
    2.5 ms against 0.45 ms on one thread). -/
def rangePairsOf (l r : Table) (v : String) : List Nat → Array Nat × Array Nat
  | [lo, hi] =>
    let ca := l.cols[(l.idx v).getD 0]!
    let cb := r.cols[(r.idx v).getD 0]!
    let others := otherCols l r v
    rangePairs (fun i => L4Factoidal.Codec.Zstd.word64 ca (8 * i)) (fun j => L4Factoidal.Codec.Zstd.word64 cb (8 * j))
      (joinOk l r others) r.rows lo hi
  | _ => (#[], #[])

/-- The merge join of `l` and `r` on `v` computed range by range: the index
    pairs of the ranges `rs` (each written `[lo, hi]`) appended in order. -/
def mergeJoinRanges (l r : Table) (v : String) (rs : List (List Nat)) : Table :=
  joinOutput l r (joinVars l r).1 (joinVars l r).2
    (concatPairs (rs.map (rangePairsOf l r v))).1 (concatPairs (rs.map (rangePairsOf l r v))).2 (some v)

/-- `ranges n k` in the chunk form `[lo, hi]`. -/
def rangeChunks (n k : Nat) : List (List Nat) := (ranges n k).map fun (lo, hi) => [lo, hi]

/-! ## A map whose elements are computed by tasks -/

/-- `xs.map f`, with `f` of every element after the first computed by a task
    (`Task.spawn`) and the first computed by the calling thread meanwhile.
    `mapPar_eq`: it is `List.map` (`Task.spawn fn` is `⟨fn ()⟩` in the
    logic). Used for pure work of a few hundred microseconds (the ranges of a
    merge join, the blocks of an ORDER BY sort): `IdQuery.Par.fold` gives each
    worker a view of the store, and that cost more than the work (olympics
    q07 at 4 threads, 2026-10-23). -/
def mapPar {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: rest =>
    let ts := rest.map fun y => Task.spawn fun _ => f y
    let a := f x
    a :: ts.map Task.get

theorem mapPar_eq {α β : Type} (f : α → β) (xs : List α) : mapPar f xs = xs.map f := by
  cases xs with
  | nil => rfl
  | cons x rest => simp [mapPar, Task.spawn]

/-! ## The ORDER BY sort from runs of width `w` -/

/-- The smallest power of two that is at least `n` (and at least 1). -/
def pow2AtLeast (n : Nat) : Nat := go 64 1
where
  go : Nat → Nat → Nat
    | 0, w => w
    | f + 1, w => if w < n then go f (2 * w) else w

/-- The passes of `mergeSortBy` from width `w` on: for an array whose aligned
    blocks of width `w` (a power of two) are each sorted by `mergeSortBy`,
    the array `mergeSortBy` gives for the whole input. -/
def sortFromWidth {α : Type} [Inhabited α] (a : Array α) (le : α → α → Bool) (w : Nat) : Array α :=
  mergeSortGo le a.size 64 a w

/-- `mergeSortBy` with the aligned blocks of width `w` sorted one by one,
    then `sortFromWidth` (the order the divided ORDER BY computes). -/
def blockSortBy {α : Type} [Inhabited α] (a : Array α) (le : α → α → Bool) (w : Nat) : Array α :=
  let w := max w 1
  let blocks := (List.range ((a.size + w - 1) / w)).map fun i => mergeSortBy (a.extract (i * w) ((i + 1) * w)) le
  sortFromWidth (blocks.foldl (· ++ ·) #[]) le w

#guard pow2AtLeast 0 == 1
#guard pow2AtLeast 73 == 128
#guard pow2AtLeast 128 == 128
#guard ranges 10 3 == [(0, 4), (4, 8), (8, 10)]
#guard ranges 10 1 == [(0, 10)]
#guard ranges 3 4 == [(0, 1), (1, 2), (2, 3)]
#guard ranges 0 4 == [(0, 0)]

/-- A pseudo-random array of `n` keys in `[0, m)` (a linear congruence). -/
private def sample (n m seed : Nat) : Array (Nat × Nat) := Id.run do
  let mut x := seed
  let mut out : Array (Nat × Nat) := #[]
  for i in [0:n] do
    x := (x * 1103515245 + 12345) % 2147483648
    out := out.push (x % m, i)
  return out

-- the block sort equals `mergeSortBy` (stable: the second component is the
-- input position) for block widths 1 to 64 and sizes that are and are not
-- multiples of the width, with many equal keys and with few
#guard (List.range 70).all fun n => [1, 2, 4, 8, 16, 64].all fun w =>
  let a := sample n 5 n
  blockSortBy a (fun x y => x.1 ≤ y.1) w == mergeSortBy a (fun x y => x.1 ≤ y.1)
#guard [291, 300, 1000, 4097].all fun n => [32, 128, 256].all fun w =>
  let a := sample n 1000 (n + w)
  blockSortBy a (fun x y => x.1 ≤ y.1) w == mergeSortBy a (fun x y => x.1 ≤ y.1)
-- a comparison that is not a total preorder still gives the same array
#guard [100, 291].all fun n => [4, 32, 128].all fun w =>
  let a := sample n 7 (3 * n)
  let le := fun (x y : Nat × Nat) => (x.1 + y.1) % 3 != 1
  blockSortBy a le w == mergeSortBy a le

end L4Factoidal.Storage.Sbm11.ParallelJoin
