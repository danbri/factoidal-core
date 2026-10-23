/-
L4Factoidal.Storage.Sbm11.IdPath — the pair relations of SPARQL 1.1 property
paths on term ids (sections 9 and 18.4,
https://github.com/danbri/factoidal/issues/954). Pure helpers of
`IdQuery`'s path evaluator (`IdQuery.evalIM`); the store reads are there.

A path denotes a list of (subject id, object id) pairs (`Pairs`), as the
reference evaluator's `SPARQL.evalPath` denotes a list of term pairs. Ids are
injective on the terms of a generation and on the query-local terms
(`TermIdTheorems.toId?_eq_iff`, `IdQuery.tagLocal`), so id equality is the
term equality `Term.eqb` of the reference on the ids that occur (with the
exceptions stated in `IdJoinTheorems`).

* `compose`: sequence `p1 / p2`, per pair of `r1` in order, the pairs of
  `r2` whose subject is its object, in `r2` order: the list the reference's
  `flatMap`/`filterMap` builds (`#guard`s below; the decoding theorem of
  that list is `IdPathTheorems.evalPath_decode`).
* `dedupPairs`: each pair once (the first occurrence kept); the reference
  keeps the last occurrence (`dedupPath`), the same set.
* `reachPlus`: the nodes reachable from a node in one or more steps of an
  adjacency map, each once: a worklist with a visited set. The loop runs at
  most `fuel` rounds and answers `none` when the rounds ran out with work
  left, so it never truncates silently. `IdPathClosureTheorems` proves, for
  its list model `reachModel`, that the bound the caller passes (the number
  of edges plus two) suffices (`reachModel_some`: each round takes one node
  from the worklist, and a node enters the worklist only when it is first
  seen) and that the output is the nodes reached in one or more steps
  (`reachModel_mem`); `#guard`s there compare `reachPlus` with the model.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Qlvr.Sort
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.Storage.Sbm11.IdPath

/-- A path relation on ids: (subject id, object id) pairs, with
    multiplicity. -/
abbrev Pairs := Array (UInt64 × UInt64)

/-- The distinct values of a sorted array, in order. -/
def dedupSorted (xs : Array UInt64) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.mkEmpty xs.size
  for x in xs do
    match out.back? with
    | some y => if y != x then out := out.push x
    | none => out := out.push x
  return out

/-- The distinct values of `xs`, in non-decreasing order (the candidate form
    of `IdQuery.scanSipTableM`). -/
def sortedDistinct (xs : Array UInt64) : Array UInt64 :=
  dedupSorted (L4Factoidal.Qlvr.mergeSortBy xs (· ≤ ·))

/-- The distinct subjects of a relation, sorted. -/
def firsts (r : Pairs) : Array UInt64 := sortedDistinct (r.map (·.1))

/-- The distinct objects of a relation, sorted. -/
def seconds (r : Pairs) : Array UInt64 := sortedDistinct (r.map (·.2))

/-- The converse relation. -/
def swap (r : Pairs) : Pairs := r.map fun (a, b) => (b, a)

/-- Sequence `p1 / p2` (SPARQL 1.1 section 9.1, the reference's relational
    composition with bag semantics): per pair `(a, m)` of `r1` in order, one
    pair `(a, c)` per pair `(m, c)` of `r2`, in `r2` order. -/
def compose (r1 r2 : Pairs) : Pairs := Id.run do
  let mut idx : Std.HashMap UInt64 (Array UInt64) := {}
  for (a, b) in r2 do
    idx := idx.alter a fun
      | some xs => some (xs.push b)
      | none => some #[b]
  let mut out : Pairs := #[]
  for (a, m) in r1 do
    match idx.get? m with
    | some cs =>
      for c in cs do
        out := out.push (a, c)
    | none => pure ()
  return out

/-- Each pair once, the first occurrence kept, in order. -/
def dedupPairs (r : Pairs) : Pairs := Id.run do
  let mut seen : Std.HashSet (UInt64 × UInt64) := {}
  let mut out : Pairs := Array.mkEmpty r.size
  for x in r do
    if !seen.contains x then
      seen := seen.insert x
      out := out.push x
  return out

/-- Whether a pair occurs twice. -/
def hasDup (r : Pairs) : Bool := Id.run do
  let mut seen : Std.HashSet (UInt64 × UInt64) := {}
  for x in r do
    if seen.contains x then return true
    seen := seen.insert x
  return false

/-- The adjacency map of a relation: per subject its objects, in order. -/
def adjOf (r : Pairs) : Std.HashMap UInt64 (Array UInt64) := Id.run do
  let mut idx : Std.HashMap UInt64 (Array UInt64) := {}
  for (a, b) in r do
    idx := idx.alter a fun
      | some xs => some (xs.push b)
      | none => some #[b]
  return idx

/-- The nodes reachable from `a` in one or more steps of `adj`, each once, in
    the order they are first seen (`a` itself only when a cycle returns to
    it). A worklist and a visited set; at most `fuel` rounds, one node taken
    per round. `none` when the rounds ran out with work left: the caller then
    fails the query (`IdQuery.closureM`), it never answers a truncated
    closure. With `fuel` at least the number of edges plus two the rounds do
    not run out (`IdPathTheorems`). -/
def reachPlus (adj : Std.HashMap UInt64 (Array UInt64)) (a : UInt64) (fuel : Nat) :
    Option (Array UInt64) := Id.run do
  let mut seen : Std.HashSet UInt64 := {}
  let mut out : Array UInt64 := #[]
  let mut work : Array UInt64 := #[a]
  let mut i := 0
  for _ in [0:fuel] do
    if i ≥ work.size then return some out
    let x := work[i]!
    i := i + 1
    for y in adj.getD x #[] do
      if !seen.contains y then
        seen := seen.insert y
        out := out.push y
        work := work.push y
  if i ≥ work.size then return some out
  return none

#guard compose #[(1, 2), (1, 3), (4, 2)] #[(2, 5), (2, 6), (3, 7)] ==
  #[(1, 5), (1, 6), (1, 7), (4, 5), (4, 6)]
#guard dedupPairs #[(1, 2), (1, 2), (2, 1)] == #[(1, 2), (2, 1)]
#guard hasDup #[(1, 2), (2, 1)] == false
#guard hasDup #[(1, 2), (2, 1), (1, 2)] == true
#guard sortedDistinct #[5, 3, 5, 1, 3] == #[1, 3, 5]
#guard reachPlus (adjOf #[(1, 2), (2, 3), (3, 1), (3, 4)]) 1 6 == some #[2, 3, 1, 4]
#guard reachPlus (adjOf #[(1, 2), (2, 3)]) 3 4 == some #[]
#guard reachPlus (adjOf #[(1, 2), (2, 3), (3, 1), (3, 4)]) 1 1 == none

end L4Factoidal.Storage.Sbm11.IdPath
