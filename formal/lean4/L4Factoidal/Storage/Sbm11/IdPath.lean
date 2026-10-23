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

#guard compose #[(1, 2), (1, 3), (4, 2)] #[(2, 5), (2, 6), (3, 7)] ==
  #[(1, 5), (1, 6), (1, 7), (4, 5), (4, 6)]
#guard sortedDistinct #[5, 3, 5, 1, 3] == #[1, 3, 5]

end L4Factoidal.Storage.Sbm11.IdPath
