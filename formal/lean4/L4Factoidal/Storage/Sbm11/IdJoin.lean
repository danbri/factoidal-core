/-
L4Factoidal.Storage.Sbm11.IdJoin — the inner join of two id tables in which
either side may hold an unbound variable (`OptJoin.unbound`, id 0): inline
VALUES on the SBM11 id path (https://github.com/danbri/factoidal/issues/950,
parent https://github.com/danbri/factoidal/issues/775).

A VALUES block (SPARQL 1.1 section 10.2) is an id table with one column per
variable; an UNDEF cell is `unbound`. `IdQuery` joins it with the table of the
WHERE clause's triple patterns. SPARQL 1.1 section 18.5:

    Join(Ω1, Ω2) = { merge(μ1, μ2) | μ1 in Ω1, μ2 in Ω2, μ1 and μ2 compatible }

and on id tables two rows are compatible when, in every shared column, the
ids are equal or one of them is `unbound`. The merged row takes, per shared
column, the left id unless it is `unbound`, then the right id; then the right
columns the left does not have. Ids are injective on the terms of a
generation (`TermIdTheorems.toId?_eq_iff`) and on the query-local terms
(`IdQuery.tagLocal`), so id equality is RDF term identity.

## The algorithm

1. The right rows whose shared columns are all bound go into a hash index on
   those ids; the others (`loose`) are kept in a list.
2. Per left row in order: when its shared columns are all bound, the
   candidates are the hash bucket of its ids and the loose rows, merged in
   right-row order; otherwise every right row. Each candidate that is
   compatible gives a pair. So the pairs are in left-row order, and per left
   row in right-row order: the order of `IdJoinTheorems.idJoin`.
3. The output columns from the pairs.

FROM (`distinctRows`, `keepVars`; issue 953): the rows of a triple pattern
over the RDF merge of several graphs are the rows of its scans of each graph,
concatenated, with duplicate triples removed, then projected
(`IdDatasetTheorems.mergedRows_eq`).

UNION (`unionIds`): the rows of the branch tables in order, `unbound` in a
column a branch does not have (SPARQL 1.1 section 18.5 Union, multiset
union).

Theorems: `Storage/Sbm11/IdJoinTheorems.lean` (`join_decode`,
`values_decode`, `union_decode`, `unionChain_decode`). The step from these `Table` columns to rows of ids is
tested there by `#guard`s, as for `OptJoin.leftOuterJoin` (lemma L5g″ of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

## Loops

`for` loops only.
-/
import L4Factoidal.Storage.Sbm11.OptJoin
import Std.Data.HashSet

namespace L4Factoidal.Storage.Sbm11.IdJoin

open L4Factoidal.Qlvr (Table gather joinVars sharedCols)
open L4Factoidal.Storage.Sbm11.OptJoin (unbound)

/-- Rows `i` of `l` and `j` of `r` are compatible: in every shared column the
    ids are equal or one is `unbound`. -/
@[inline] def compatAt (l r : Table) (shared : Array (Nat × Nat)) (i j : Nat) : Bool :=
  shared.all fun (p, q) =>
    let a := l.at p i
    let b := r.at q j
    a == unbound || b == unbound || a == b

/-- Two increasing index arrays merged into one increasing array. -/
def mergeIdx (a b : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  for _ in [0:a.size + b.size] do
    if i < a.size then
      if j < b.size && b[j]! < a[i]! then
        out := out.push b[j]!
        j := j + 1
      else
        out := out.push a[i]!
        i := i + 1
    else if j < b.size then
      out := out.push b[j]!
      j := j + 1
  return out

/-- The pairs of compatible rows: left indices non-decreasing, per left row
    the right indices increasing. With no shared column every pair (the
    cross product). -/
def joinPairs (l r : Table) (shared : Array (Nat × Nat)) : Array Nat × Array Nat := Id.run do
  let mut hm : Std.HashMap (List UInt64) (Array Nat) := {}
  let mut loose : Array Nat := #[]
  for j in [0:r.rows] do
    let k := (shared.map fun (_, q) => r.at q j).toList
    if k.all (· != unbound) then
      hm := hm.alter k fun | some a => some (a.push j) | none => some #[j]
    else loose := loose.push j
  let mut li : Array Nat := #[]
  let mut ri : Array Nat := #[]
  for i in [0:l.rows] do
    let k := (shared.map fun (p, _) => l.at p i).toList
    if k.all (· != unbound) then
      for j in mergeIdx (hm.getD k #[]) loose do
        if compatAt l r shared i j then
          li := li.push i
          ri := ri.push j
    else
      for j in [0:r.rows] do
        if compatAt l r shared i j then
          li := li.push i
          ri := ri.push j
  return (li, ri)

/-- SPARQL 1.1 section 18.5 Join of two id tables, `unbound` an unbound
    variable: the left variables, then the right variables the left does not
    have. A shared column takes the left id, or the right id where the left
    is `unbound`. The left row order is kept; the left sort variable is kept
    when the right table does not have it. -/
def joinIds (l r : Table) : Table := Id.run do
  let shared := sharedCols l r
  let (vars, extra) := joinVars l r
  let (li, ri) := joinPairs l r shared
  let mut cols : Array ByteArray := Array.mkEmpty vars.size
  for c in [0:l.vars.size] do
    match shared.find? (·.1 == c) with
    | none => cols := cols.push (gather l.cols[c]! li)
    | some (_, q) =>
      let mut out := ByteArray.emptyWithCapacity (8 * li.size)
      for k in [0:li.size] do
        let a := l.at c li[k]!
        out := L4Factoidal.Qlvr.Side.put64 out (if a == unbound then r.at q ri[k]! else a)
      cols := cols.push out
  for k in extra do
    cols := cols.push (gather r.cols[k]! ri)
  let sortVar := match l.sortVar with
    | some v => if r.vars.contains v then none else some v
    | none => none
  return { vars, cols, rows := li.size, sortVar }

/-- SPARQL 1.1 section 18.5 Union of id tables, in order (multiset union:
    the rows of the first table, then those of the next): the variables of
    the tables in order of first occurrence, and `unbound` in a column that a
    table does not have. -/
def unionIds (ts : Array Table) : Table := Id.run do
  let mut vars : Array String := #[]
  for t in ts do
    for v in t.vars do
      if !vars.contains v then vars := vars.push v
  let mut cols : Array ByteArray := vars.map fun _ => ByteArray.empty
  let mut rows := 0
  for t in ts do
    for c in [0:vars.size] do
      match t.idx vars[c]! with
      | some k => cols := cols.modify c (· ++ t.cols[k]!)
      | none =>
        let mut b := cols[c]!
        for _ in [0:t.rows] do
          b := L4Factoidal.Qlvr.Side.put64 b unbound
        cols := cols.set! c b
    rows := rows + t.rows
  return { vars, cols, rows }

/-- The rows of `t` with duplicates removed, the first occurrence of each
    row kept, in order (https://github.com/danbri/factoidal/issues/953: the
    rows of a triple pattern over the RDF merge of the FROM graphs, SPARQL 1.1
    section 13.2.2, when the columns are every variable of the pattern). With
    no column every row is equal: one row when `t` has a row. -/
def distinctRows (t : Table) : Table := Id.run do
  let mut seen : Std.HashSet (List UInt64) := {}
  let mut idx : Array Nat := #[]
  for i in [0:t.rows] do
    let k := (List.range t.vars.size).map fun c => t.at c i
    if !seen.contains k then
      seen := seen.insert k
      idx := idx.push i
  return t.reorder idx

/-- The columns of the variables `keep` holds, in order; the rows unchanged.
    No sort variable. -/
def keepVars (t : Table) (keep : String → Bool) : Table := Id.run do
  let mut vars : Array String := #[]
  let mut cols : Array ByteArray := #[]
  for c in [0:t.vars.size] do
    if keep t.vars[c]! then
      vars := vars.push t.vars[c]!
      cols := cols.push t.cols[c]!
  return { vars, cols, rows := t.rows }

end L4Factoidal.Storage.Sbm11.IdJoin
