/-
Harness/RunHeap — the selection structure of the k-way merges of the SBM11
packer (`Harness/Sbm11PackLib.lean` phases 2 and 3b,
`Harness/Sbm11DictPack.lean` phase 2;
https://github.com/danbri/factoidal/issues/804): a loser tree (tournament
tree; Knuth, TAOCP vol. 3, section 5.4.1) over the run numbers.

The heads stay in the caller's array `keys : Array (Option α)`, indexed by
run number; `none` is a run with no head left. Run `i` comes before run `j`
when its head is smaller, or when the heads are equal and `i < j`; a run with
a head comes before a run without one. This is a total order on the run
numbers, so the winner is unique: the first minimum, the run the earlier
linear scan of all heads chose. A merge through the tree takes the records in
the same order as that scan.

The tree has `m` leaves (`m` the least power of two at least the number of
runs; leaves past the last run have no head). Node `n` of `1 .. m-1` holds the
loser of the match between the winners of its two subtrees; position 0 holds
the overall winner. After the winner's head changes, `replay` plays it
against the losers on the path to the root: one comparison per level, about
log2 k for k runs. A binary heap needs two per level.

One step of a merge used to cost k comparisons (a linear scan of every head),
and k grows with the source (a term run holds at most run-terms / workers
terms), so phase 2 was quadratic in the distinct terms: 799 s of a 1,334 s
pack on 8,877,307 terms.

`replay` is a tail call with a fuel `Nat` first (64 levels), so the stack
depth does not depend on k.
-/

namespace Harness.RunHeap

/-- Run `i` comes before run `j`: a head before no head; smaller head; equal
    heads, smaller run number. `cmp` is a three-way comparison, so one call
    decides a match (a `<` test needs two calls when the heads are not in
    order). -/
@[inline] def before {α : Type} (cmp : α → α → Ordering) (keys : Array (Option α)) (i j : Nat) : Bool :=
  match (keys[i]?).bind id, (keys[j]?).bind id with
  | some a, some b =>
    match cmp a b with
    | .lt => true
    | .gt => false
    | .eq => i < j
  | some _, none => true
  | none, some _ => false
  | none, none => i < j

/-- The least power of two at least `k` and at least 1. -/
def leavesFor (k : Nat) : Nat := Id.run do
  let mut m := 1
  for _ in [0:64] do
    if m ≥ k then break
    m := 2 * m
  return m

/-- Play `w` (the current winner on the way up) against the loser stored at
    node `n`, then at the parents of `n`; store the overall winner at 0. -/
@[specialize] def replayGo {α : Type} (cmp : α → α → Ordering) (keys : Array (Option α)) :
    Nat → Array Nat → Nat → Nat → Array Nat
  | 0, t, _, w => t.set! 0 w
  | fuel + 1, t, n, w =>
    if n == 0 then t.set! 0 w
    else
      let l := t[n]!
      if before cmp keys l w then replayGo cmp keys fuel (t.set! n w) (n / 2) l
      else replayGo cmp keys fuel t (n / 2) w

/-- The head of run `i` changed (it moved on, or it has no head left):
    `i` must be the winner, `t[0]`. Restores the tree. -/
@[inline, specialize] def replay {α : Type} (cmp : α → α → Ordering) (keys : Array (Option α))
    (t : Array Nat) (i : Nat) : Array Nat :=
  replayGo cmp keys 64 t ((i + t.size) / 2) i

/-- The tree over runs `0 .. keys.size - 1`. Its size is the number of
    leaves `m`. -/
@[specialize] def build {α : Type} (cmp : α → α → Ordering) (keys : Array (Option α)) : Array Nat := Id.run do
  let m := leavesFor keys.size
  -- win[n]: the winner of the subtree at n (leaves at m .. 2m-1)
  let mut win : Array Nat := Array.replicate (2 * m) 0
  let mut t : Array Nat := Array.replicate m 0
  for i in [0:m] do
    win := win.set! (m + i) i
  for r in [0:m - 1] do
    let n := m - 1 - r
    let a := win[2 * n]!
    let b := win[2 * n + 1]!
    if before cmp keys a b then
      win := win.set! n a
      t := t.set! n b
    else
      win := win.set! n b
      t := t.set! n a
  return t.set! 0 (if m == 1 then 0 else win[1]!)

/-- The run with the least head: the winner. Its head is `none` when every
    run is exhausted. -/
@[inline] def winner (t : Array Nat) : Nat := t[0]!

/-- A k-way merge of sorted arrays through the tree: every element, in the
    order the tree gives (used by the `#guard`s below to check the tree
    against `List.mergeSort`). -/
def mergeArrays (cmp : Nat → Nat → Ordering) (runs : Array (Array Nat)) : Array Nat := Id.run do
  let mut pos : Array Nat := runs.map fun _ => 0
  let mut keys : Array (Option Nat) := runs.map (·[0]?)
  let mut t := build cmp keys
  let mut out : Array Nat := #[]
  let total := runs.foldl (fun n r => n + r.size) 0
  for _ in [0:total + 1] do
    let k := winner t
    match (keys[k]?).bind id with
    | none => break
    | some x =>
      out := out.push x
      let p := pos[k]! + 1
      pos := pos.set! k p
      keys := keys.set! k (runs[k]![p]?)
      t := replay cmp keys t k
  return out

#guard mergeArrays compare #[#[1, 4, 9], #[2, 3, 10], #[], #[0, 4, 5, 11]] ==
  #[0, 1, 2, 3, 4, 4, 5, 9, 10, 11]
#guard mergeArrays compare #[] == #[]
#guard mergeArrays compare #[#[7]] == #[7]
#guard mergeArrays compare #[#[], #[], #[3]] == #[3]
#guard
  let runs : Array (Array Nat) := (List.range 37).toArray.map fun r =>
    ((List.range (r % 11)).map fun i => (i * 7 + r * 13) % 50).mergeSort.toArray
  mergeArrays compare runs == (runs.toList.flatMap Array.toList).mergeSort.toArray
-- equal heads (here: equal tens) leave in run order: 40 (run 0), 41 (run 1), 42 (run 2)
#guard
  let runs : Array (Array Nat) := #[#[40, 70], #[41, 50], #[42]]
  mergeArrays (fun a b => compare (a / 10) (b / 10)) runs == #[40, 41, 42, 50, 70]

end Harness.RunHeap
