/-
L4Factoidal.Storage.Sbm11.OptJoin — the left outer join of the SBM11 id
path: OPTIONAL on term ids (https://github.com/danbri/factoidal/issues/775;
record docs/designissues/2026-10-12-sbm11-stage4.md section 10).

`IdQuery.translate` admits `{ base OPTIONAL { g1 } ... OPTIONAL { gk } }`
where every variable an OPTIONAL group shares with anything outside it is
bound by the base's triple patterns, and every FILTER of a group reads only
variables of the group's own triple patterns. Under those conditions the
FILTER is applied to the group's rows before the join (the condition reads
the same values in the group's row and in the merged row), so the join here
has no condition: SPARQL 1.1 section 18.5,

    LeftJoin(Ω1, Ω2, true) = for each μ1 in Ω1, the merges with the
    compatible μ2 in Ω2, or μ1 alone when there is none,

and on id tables "compatible" is "equal ids in the shared columns" (the
shared variables are bound in every left row and every right row; ids are
injective, `TermIdTheorems.toId?_eq_iff`).

## Unbound

`unbound` (0) marks an unbound variable in a column. No term id is 0
(`TermId`: tags 1 to 5, and 14 for the terms of a delta log), and no column of
an id table holds graph id 0 (a `GRAPH ?g` column holds named graphs only).
The renderer leaves such a binding out; ORDER BY puts it first (SPARQL 1.1
section 15.1); DISTINCT and GROUP BY compare it as an id.

## The algorithm

1. Inner pairs `(li, ri)` of the left and right row indices whose shared
   columns are equal, in left-row order, and per left row in right-row
   order: `Qlvr.mergeGo` when both tables are sorted on a shared variable
   (`MergeTheorems.mergeGo_pairs`), else a hash index of the right rows
   probed in left-row order (`hashPairs`).
2. `outerPairs`: for each left row, its pairs, else the row with `none`.
3. The output columns: the left columns gathered by the left indices, the
   right columns that the left does not have gathered by the right indices,
   `unbound` for `none`.

The output keeps the left row order, so a left table sorted on a variable
stays sorted on it. Theorems: `Storage/Sbm11/OptJoinTheorems.lean`.

## Loops

`runPairs` and `outerGo` are tail calls with fuel; the column copies and the
hash index are `for` loops.
-/
import L4Factoidal.Qlvr.Bgp

namespace L4Factoidal.Storage.Sbm11.OptJoin

open L4Factoidal.Qlvr (Table gather joinVars sharedCols mergeGo)

/-- The id of an unbound variable in a column. -/
def unbound : UInt64 := 0

/-- The pairs `p, p + 1, ...` whose left index is `i`, appended to `oi` and
    `oj`; returns where that run ends (a tail call with fuel). -/
def runPairs (li ri : Array Nat) (i : Nat) :
    Nat → Nat → Array Nat → Array (Option Nat) → Nat × Array Nat × Array (Option Nat)
  | 0, p, oi, oj => (p, oi, oj)
  | f + 1, p, oi, oj =>
    if p < li.size && li[p]! == i then
      runPairs li ri i f (p + 1) (oi.push i) (oj.push (some ri[p]!))
    else (p, oi, oj)

/-- Left rows `i, i + 1, ... < nl` with the pairs from `p` on: each left row
    with its run of pairs, or alone with `none` (a tail call with fuel). -/
def outerGo (nl : Nat) (li ri : Array Nat) :
    Nat → Nat → Nat → Array Nat → Array (Option Nat) → Array Nat × Array (Option Nat)
  | 0, _, _, oi, oj => (oi, oj)
  | f + 1, i, p, oi, oj =>
    if i < nl then
      match runPairs li ri i (li.size - p) p oi oj with
      | (p', oi', oj') =>
        if p' == p then outerGo nl li ri f (i + 1) p (oi.push i) (oj.push none)
        else outerGo nl li ri f (i + 1) p' oi' oj'
    else (oi, oj)

/-- The rows of the left outer join of `nl` left rows with the inner pairs
    `(li, ri)` (left indices non-decreasing and below `nl`): left index and
    right index or `none` (`OptJoinTheorems.outerPairs_eq`). -/
def outerPairs (nl : Nat) (li ri : Array Nat) : Array Nat × Array (Option Nat) :=
  outerGo nl li ri nl 0 0 #[] #[]

/-- Rows `idx` of an 8-byte column, `unbound` where `idx` holds `none`. -/
def gatherOpt (src : ByteArray) (idx : Array (Option Nat)) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (8 * idx.size)
  for o in idx do
    match o with
    | some j => out := src.copySlice (8 * j) out out.size 8 false
    | none => out := L4Factoidal.Qlvr.Side.put64 out unbound
  return out

/-- The inner pairs by a hash index of the right rows on the ids of the
    shared columns, probed in left-row order: left indices non-decreasing,
    per left row the right indices increasing. With no shared column every
    pair (the cross product). -/
def hashPairs (l r : Table) (shared : Array (Nat × Nat)) : Array Nat × Array Nat := Id.run do
  let mut li : Array Nat := #[]
  let mut ri : Array Nat := #[]
  if h : shared.size = 1 then
    let (p, q) := shared[0]
    let mut hm : Std.HashMap UInt64 (Array Nat) := {}
    for j in [0:r.rows] do
      hm := hm.alter (r.at q j) fun | some a => some (a.push j) | none => some #[j]
    for i in [0:l.rows] do
      for j in hm.getD (l.at p i) #[] do
        li := li.push i
        ri := ri.push j
  else
    let keyL (i : Nat) : List UInt64 := (shared.map fun (p, _) => l.at p i).toList
    let keyR (j : Nat) : List UInt64 := (shared.map fun (_, q) => r.at q j).toList
    let mut hm : Std.HashMap (List UInt64) (Array Nat) := {}
    for j in [0:r.rows] do
      hm := hm.alter (keyR j) fun | some a => some (a.push j) | none => some #[j]
    for i in [0:l.rows] do
      for j in hm.getD (keyL i) #[] do
        li := li.push i
        ri := ri.push j
  return (li, ri)

/-- The inner pairs and how they were found: a merge when the left table is
    sorted on a shared variable and the right table on the same variable,
    else the hash index. -/
def innerPairs (l r : Table) : Array Nat × Array Nat × String :=
  let shared := sharedCols l r
  let hash : Array Nat × Array Nat × String :=
    let (li, ri) := hashPairs l r shared
    (li, ri, if shared.isEmpty then "cross product" else "hash")
  match l.sortVar with
  | some v =>
    match l.idx v, r.idx v with
    | some lc, some rc =>
      if r.sortVar == some v then
        let others := shared.filter fun (a, _) => a != lc
        let ok (x y : Nat) : Bool := others.all (fun (p, q) => l.at p x == r.at q y)
        let (li, ri) := mergeGo (l.at lc) (r.at rc) ok l.rows r.rows (l.rows + r.rows + 1) 0 0 #[] #[]
        (li, ri, s!"merge on ?{v}")
      else hash
    | _, _ => hash
  | none => hash

/-- The left outer join of two id tables with no condition (SPARQL 1.1
    section 18.5 `LeftJoin(Ω1, Ω2, true)` when the shared variables are bound
    in every row of both): the left variables, then the right variables the
    left does not have; the left row order and sort variable are kept. Also
    says how the pairs were found. -/
def leftOuterJoin (l r : Table) : Table × String :=
  let (vars, extra) := joinVars l r
  let (li, ri, how) := innerPairs l r
  let (oi, oj) := outerPairs l.rows li ri
  ({ vars, cols := l.cols.map (gather · oi) ++ extra.map fun k => gatherOpt r.cols[k]! oj,
     rows := oi.size, sortVar := l.sortVar }, how)

end L4Factoidal.Storage.Sbm11.OptJoin
