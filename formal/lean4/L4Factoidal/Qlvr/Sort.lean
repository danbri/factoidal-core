/-
L4Factoidal.Qlvr.Sort — byte-wise comparison and a stable bottom-up merge
sort, for the side index and for ORDER BY (Factoidal/qlvr,
https://github.com/danbri/factoidal/issues/778).

## Loops

`cmpBytesLoop` is a tail call with a fuel `Nat` first. `mergeSortBy` is
`for` loops in `Id.run`: the passes (at most 64), the runs of one pass and
the elements of one merge. There is no recursion, so the depth of the call
stack does not depend on the input size.
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

/-- A stable sort: `le a b` is "a may come before b". Bottom-up merge sort
    with `for` loops; `O(n log n)` comparisons, two arrays of size `n`. -/
def mergeSortBy {α : Type} [Inhabited α] (a : Array α) (le : α → α → Bool) : Array α := Id.run do
  let n := a.size
  let mut src := a
  let mut width := 1
  for _ in [0:64] do
    if width ≥ n then break
    let mut out : Array α := Array.mkEmpty n
    let mut lo := 0
    for _ in [0:n] do
      if lo ≥ n then break
      let mid := min (lo + width) n
      let hi := min (lo + 2 * width) n
      let mut i := lo
      let mut j := mid
      for _ in [0:hi - lo] do
        if i < mid && (j ≥ hi || le src[i]! src[j]!) then
          out := out.push src[i]!
          i := i + 1
        else
          out := out.push src[j]!
          j := j + 1
      lo := hi
    src := out
    width := 2 * width
  return src

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
