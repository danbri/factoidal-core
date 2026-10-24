/-
L4Factoidal.Qlvr.Sort — byte-wise comparison and a stable bottom-up merge
sort, for the side index and for ORDER BY (Factoidal/qlvr,
https://github.com/danbri/factoidal/issues/778).

## Loops

`cmpBytesLoop` is a tail call with a fuel `Nat` first. `mergeSortBy` is
three tail calls with a fuel `Nat` first: the passes (at most 64), the runs
of one pass and the elements of one merge, so the depth of the call stack
does not depend on the input size.

The four functions of the sort are `@[specialize]` (stage 1p of
docs/designissues/2026-10-12-parallel-block-scans.md, issue 961): the
compiler makes a copy for each comparison given at a call site, so that a
comparison is not a closure call with boxed arguments per element pair.
Before, `IdQuery.sipDistinct` sorted the 313 join-key words of olympics q07's
third scan with `UInt64.decLe` as a closure, about 50 microseconds.
-/

namespace L4Factoidal.Qlvr

/-- Compare bytes `i..` of `a` and `b` (unsigned, then by length). -/
def cmpBytesLoop (a b : ByteArray) : Nat → Nat → Ordering
  | 0, _ => compare a.size b.size
  | k+1, i =>
    if h : i < a.size ∧ i < b.size then
      let x := a[i]'h.1
      let y := b[i]'h.2
      if x < y then .lt else if y < x then .gt else cmpBytesLoop a b k (i + 1)
    else compare a.size b.size

/-- Byte-wise (unsigned) lexicographic order; a proper prefix sorts first. -/
def cmpBytes (a b : ByteArray) : Ordering :=
  cmpBytesLoop a b (min a.size b.size + 1) 0

/-- Merge `src[i..mid)` and `src[j..hi)` onto `out`; `k` is the fuel. -/
@[specialize] def mergeRunGo {α : Type} [Inhabited α] (src : Array α) (le : α → α → Bool) (mid hi : Nat) :
    Nat → Array α → Nat → Nat → Array α
  | 0, out, _, _ => out
  | k+1, out, i, j =>
    if i < mid && (j ≥ hi || le src[i]! src[j]!) then mergeRunGo src le mid hi k (out.push src[i]!) (i + 1) j
    else if j < hi then mergeRunGo src le mid hi k (out.push src[j]!) i (j + 1)
    else out

/-- One pass: merge every pair of adjacent runs of `width`, from `lo`. -/
@[specialize] def mergePassGo {α : Type} [Inhabited α] (src : Array α) (le : α → α → Bool) (width n : Nat) :
    Nat → Array α → Nat → Array α
  | 0, out, _ => out
  | k+1, out, lo =>
    if lo ≥ n then out
    else
      let mid := min (lo + width) n
      let hi := min (lo + 2 * width) n
      mergePassGo src le width n k (mergeRunGo src le mid hi (hi - lo) out lo mid) hi

@[specialize] def mergeSortGo {α : Type} [Inhabited α] (le : α → α → Bool) (n : Nat) :
    Nat → Array α → Nat → Array α
  | 0, src, _ => src
  | k+1, src, width =>
    if width ≥ n then src
    else mergeSortGo le n k (mergePassGo src le width n (n + 1) (Array.mkEmpty n) 0) (2 * width)

/-- A stable sort: `le a b` is "a may come before b". Bottom-up merge sort;
    `O(n log n)` comparisons, two arrays of size `n`. Every loop is a tail
    call with a fuel `Nat` first. Until 2026-10-12 it was `for` loops in
    `Id.run`, which the compiler left as the generic `forIn` loop over
    closures, one native frame per element: it overflowed the 512 KB
    canary stack sorting 20,000 keys (`l4sbm11-dict-pack`,
    https://github.com/danbri/factoidal/issues/788). -/
@[specialize] def mergeSortBy {α : Type} [Inhabited α] (a : Array α) (le : α → α → Bool) : Array α :=
  mergeSortGo le a.size 64 a 1

#guard cmpBytes "abc".toUTF8 "abd".toUTF8 == .lt
#guard cmpBytes "ab".toUTF8 "abc".toUTF8 == .lt
#guard cmpBytes "b".toUTF8 "abc".toUTF8 == .gt
#guard cmpBytes "".toUTF8 "".toUTF8 == .eq
-- byte 0xC3 (é in UTF-8) sorts after every ASCII byte
#guard cmpBytes "é".toUTF8 "z".toUTF8 == .gt
#guard mergeSortBy #[5, 3, 9, 1, 3, 0, 7] (· ≤ ·) == #[0, 1, 3, 3, 5, 7, 9]
#guard mergeSortBy (#[] : Array Nat) (· ≤ ·) == #[]
-- stable: equal keys keep their input order
#guard mergeSortBy #[(1, 'a'), (0, 'b'), (1, 'c'), (0, 'd')] (fun x y => x.1 ≤ y.1) ==
  #[(0, 'b'), (0, 'd'), (1, 'a'), (1, 'c')]

end L4Factoidal.Qlvr
