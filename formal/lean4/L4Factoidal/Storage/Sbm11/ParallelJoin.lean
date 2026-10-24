/-
L4Factoidal.Storage.Sbm11.ParallelJoin — the merge join of the SBM11 id path
divided into left row ranges (KR 1.2 of OKR batch 3,
https://github.com/danbri/factoidal/issues/875; costs named in
https://github.com/danbri/factoidal/issues/961; record
docs/designissues/2026-10-12-parallel-block-scans.md, stage 1f).

`Qlvr.mergeJoin` walks the left and the right join columns once (`mergeGo`).
Here the left rows are cut into consecutive ranges (`ranges`). For a range
`[lo, hi)` the walk starts at left row `lo` and at the first right row whose
join value is not below the left value of row `lo` (`lowerBound`, a binary
search), and stops at left row `hi` (`rangePairs`). The index pairs of the
ranges, appended in range order (`concatPairs`), are the index pairs of the
single walk: `ParallelJoinTheorems.mergeJoinRanges_eq` proves
`mergeJoinRanges l r v rs = mergeJoin l r v` for join columns in
non-decreasing order and ranges that cover the left rows in order. The native
driver computes `rangePairsOf` of each range in a task (`mapPar`, which is
`List.map` in the logic: `mapPar_eq`) and appends the results in range order
(`IdQuery.mergeJoinParM`).

Every recursion here is a tail call with a fuel argument.
-/
import L4Factoidal.Qlvr.Bgp

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

/-- The length of the first range of `rangesShare n k f`: `f / 10` of an
    equal share of `n` in `k` ranges, at most `n`. -/
def shareLen (n k f : Nat) : Nat := min n (n * f / (10 * max k 1))

/-- Consecutive ranges that cover `[0, n)` in order (stage 1p of
    docs/designissues/2026-10-12-parallel-block-scans.md, issue 961): the
    first (the calling thread's range of a divided merge join) of `f / 10`
    of an equal share of `k` ranges (`shareLen`), the others nearly equal.
    `f = 10`, `k < 2`, or a first range that is empty or everything:
    `ranges n k`. At most `k` ranges. -/
def rangesShare (n k f : Nat) : List (Nat × Nat) :=
  if f == 10 || k < 2 || shareLen n k f == 0 || shareLen n k f == n then ranges n k
  else rangesAcc n (max 1 ((n - shareLen n k f + (k - 1) - 1) / (k - 1))) (k - 2) (shareLen n k f)
    [(0, shareLen n k f)]

def rangeChunksShare (n k f : Nat) : List (List Nat) := (rangesShare n k f).map fun (lo, hi) => [lo, hi]

#guard rangesShare 100 4 10 == ranges 100 4
#guard rangesShare 100 4 16 == [(0, 40), (40, 60), (60, 80), (80, 100)]

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
    logic). Used for the ranges of a merge join, which read no store:
    `IdQuery.Par.fold` gives each worker a view of the store and a page cache,
    which a pure computation does not need. -/
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

#guard ranges 10 3 == [(0, 4), (4, 8), (8, 10)]
#guard ranges 10 1 == [(0, 10)]
#guard ranges 3 4 == [(0, 1), (1, 2), (2, 3)]
#guard ranges 0 4 == [(0, 0)]
#guard mapPar (· * 2) [1, 2, 3] == [2, 4, 6]

end L4Factoidal.Storage.Sbm11.ParallelJoin
