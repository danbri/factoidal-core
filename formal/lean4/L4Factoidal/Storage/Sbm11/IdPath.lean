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
  (`reachModel_mem`); `IdPathPureTheorems.reachPlus_eq` proves that
  `reachPlus` over `adjOf` answers the model, list for list.

The loops are folds (`Array.foldl`) and a tail-recursive worklist
(`reachGo`), so that `IdPathPureTheorems` states each one against a list
model (https://github.com/danbri/factoidal/issues/776).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Qlvr.Sort
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.Storage.Sbm11.IdPath

/-- A path relation on ids: (subject id, object id) pairs, with
    multiplicity. -/
abbrev Pairs := Array (UInt64 × UInt64)

/-- One step of `dedupSorted`: `x` appended unless it equals the last value. -/
@[inline] def dedupStep (out : Array UInt64) (x : UInt64) : Array UInt64 :=
  match out.back? with
  | some y => if y != x then out.push x else out
  | none => out.push x

/-- The distinct values of a sorted array, in order. -/
def dedupSorted (xs : Array UInt64) : Array UInt64 :=
  xs.foldl dedupStep (Array.mkEmpty xs.size)

/-- The distinct values of `xs`, in non-decreasing order (the candidate form
    of `IdQuery.scanSipTableM`). The sort is the core library's
    `Array.mergeSort` (its list form `List.mergeSort` is proved a sorted
    permutation, `IdPathPureTheorems.sortedDistinct_spec`). -/
def sortedDistinct (xs : Array UInt64) : Array UInt64 :=
  dedupSorted (xs.mergeSort (fun a b => decide (a ≤ b)))

/-- The distinct subjects of a relation, sorted. -/
def firsts (r : Pairs) : Array UInt64 := sortedDistinct (r.map (·.1))

/-- The distinct objects of a relation, sorted. -/
def seconds (r : Pairs) : Array UInt64 := sortedDistinct (r.map (·.2))

/-- The converse relation. -/
def swap (r : Pairs) : Pairs := r.map fun (a, b) => (b, a)

/-- One pair of `adjOf`: `b` appended to the objects of `a`. -/
@[inline] def adjStep (idx : Std.HashMap UInt64 (Array UInt64)) (p : UInt64 × UInt64) :
    Std.HashMap UInt64 (Array UInt64) :=
  idx.alter p.1 fun
    | some xs => some (xs.push p.2)
    | none => some #[p.2]

/-- The adjacency map of a relation: per subject its objects, in order. -/
def adjOf (r : Pairs) : Std.HashMap UInt64 (Array UInt64) :=
  r.foldl adjStep {}

/-- Sequence `p1 / p2` (SPARQL 1.1 section 9.1, the reference's relational
    composition with bag semantics): per pair `(a, m)` of `r1` in order, one
    pair `(a, c)` per pair `(m, c)` of `r2`, in `r2` order. -/
def compose (r1 r2 : Pairs) : Pairs :=
  let idx := adjOf r2
  r1.foldl (fun out p => (idx.getD p.2 #[]).foldl (fun out c => out.push (p.1, c)) out) #[]

/-- One pair of `dedupPairs`. -/
@[inline] def dedupPairStep (s : Std.HashSet (UInt64 × UInt64) × Pairs) (x : UInt64 × UInt64) :
    Std.HashSet (UInt64 × UInt64) × Pairs :=
  if s.1.contains x then s else (s.1.insert x, s.2.push x)

/-- Each pair once, the first occurrence kept, in order. -/
def dedupPairs (r : Pairs) : Pairs :=
  (r.foldl dedupPairStep ({}, Array.mkEmpty r.size)).2

/-- One node taken by `reachPlus`: each successor not seen before appended
    to the output and to the worklist. -/
@[inline] def visitStep (s : Std.HashSet UInt64 × Array UInt64 × Array UInt64) (y : UInt64) :
    Std.HashSet UInt64 × Array UInt64 × Array UInt64 :=
  if s.1.contains y then s else (s.1.insert y, s.2.1.push y, s.2.2.push y)

/-- The worklist loop of `reachPlus`: at most `fuel` rounds, one node taken
    per round (index `i` of `work`). -/
def reachGo (adj : Std.HashMap UInt64 (Array UInt64)) :
    Nat → Std.HashSet UInt64 → Array UInt64 → Array UInt64 → Nat → Option (Array UInt64)
  | 0, _, out, work, i => if i ≥ work.size then some out else none
  | fuel + 1, seen, out, work, i =>
    if i ≥ work.size then some out
    else
      let s := (adj.getD work[i]! #[]).foldl visitStep (seen, out, work)
      reachGo adj fuel s.1 s.2.1 s.2.2 (i + 1)

/-- The nodes reachable from `a` in one or more steps of `adj`, each once, in
    the order they are first seen (`a` itself only when a cycle returns to
    it). A worklist and a visited set; at most `fuel` rounds, one node taken
    per round. `none` when the rounds ran out with work left: the caller then
    fails the query (`IdQuery.closureM`), it never answers a truncated
    closure. With `fuel` at least the number of edges plus two the rounds do
    not run out (`IdPathClosureTheorems.reachModel_some`,
    `IdPathPureTheorems.reachPlus_eq`). -/
def reachPlus (adj : Std.HashMap UInt64 (Array UInt64)) (a : UInt64) (fuel : Nat) :
    Option (Array UInt64) :=
  reachGo adj fuel {} #[] #[a] 0

#guard compose #[(1, 2), (1, 3), (4, 2)] #[(2, 5), (2, 6), (3, 7)] ==
  #[(1, 5), (1, 6), (1, 7), (4, 5), (4, 6)]
#guard dedupPairs #[(1, 2), (1, 2), (2, 1)] == #[(1, 2), (2, 1)]
#guard sortedDistinct #[5, 3, 5, 1, 3] == #[1, 3, 5]
#guard reachPlus (adjOf #[(1, 2), (2, 3), (3, 1), (3, 4)]) 1 6 == some #[2, 3, 1, 4]
#guard reachPlus (adjOf #[(1, 2), (2, 3)]) 3 4 == some #[]
#guard reachPlus (adjOf #[(1, 2), (2, 3), (3, 1), (3, 4)]) 1 1 == none

end L4Factoidal.Storage.Sbm11.IdPath
