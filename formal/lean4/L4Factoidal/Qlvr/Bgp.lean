/-
L4Factoidal.Qlvr.Bgp — basic graph patterns over a QLever index: Id order,
permutation choice, block-skipping scans, merge and hash joins
(Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).

## Plan rules

  * A triple pattern's positions are subject 0, predicate 1, object 2. Each
    is a variable, a constant `Id`, or `missing` (a constant that is not in
    the index: the pattern then has no solutions).
  * Permutation: the six files `pso pos spo sop osp ops` hold the triples
    sorted by their three columns in that order. A pattern is scanned from a
    permutation whose first `m` columns are exactly its `m` bound positions,
    so the bound values are a key prefix. Of the permutations that qualify,
    the planner takes one whose next column is the variable it wants the
    rows sorted by (for a merge join), else the first one in the order
    above.
  * Block skipping: a block is read only when the key prefix lies between
    the prefixes of its first and last triple (block metadata). A block whose
    first and last triple both carry the key prefix is "full": its key
    columns are not decoded. Only the columns that a check or an output
    needs are fetched and decompressed.
  * Estimates: the rows of the selected blocks (exact for full blocks, an
    upper bound otherwise), from the metadata alone.
  * Order: start with the pattern of least estimate; then repeatedly take,
    of the patterns that share a variable with the patterns already joined,
    the one of least estimate (a pattern that shares none only when no other
    remains: a cross product).
  * Join: when the left table is sorted by a variable the next pattern also
    has, the pattern is scanned sorted by that variable and the two are
    merged (merge join, runs of equal Ids give their cross product, other
    shared variables are checked per pair). Otherwise a hash join on the
    Ids of all shared variables, built on the smaller input.
  * Columns: a variable that occurs in one pattern only and that the query
    does not use (projection, FILTER, ORDER BY, GROUP BY) is not stored;
    the rows still count. A count-only scan of full blocks decodes nothing.
  * Graphs: the graph column is not read. Every triple of the instance is in
    the default graph; an index with named graphs would give one row per
    graph of a triple here.

Tables store each variable's column as a `ByteArray` of 8-byte Ids (no boxed
`Id` per row).

## Loops

Per-row loops (`selectRows`) are tail calls with a fuel `Nat` first and the
output as an accumulator. Joins, filters and copies are `for` loops in
`Id.run`. The loop over blocks is a `for` loop in the fetch monad.
-/
import L4Factoidal.Qlvr.Scan
import L4Factoidal.Qlvr.Side
import Std.Data.HashMap

namespace L4Factoidal.Qlvr

open L4Factoidal.Codec.Zstd (word64)

/-! ## QLever's comparison of Ids -/

/-- The numeric value of an `Int` or `Double` Id. -/
def Id.num? (x : Id) : Option Float :=
  match x.tag with
  | 2 => some (Float.ofInt (int60 x.payload))
  | 3 => some (Float.ofBits (x.bits <<< 4))
  | _ => none

def cmpFloat (a b : Float) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

/-- Compare two Ids of compatible datatypes (QLever
    `valueIdComparators::compareIds`, `global/ValueIdComparators.h:492-600`
    at commit ceace86): `Int` and `Double` by value, two `Int`s exactly, the
    same datatype by payload. `none` for incompatible datatypes. -/
def cmpIdsCompatible (a b : Id) : Option Ordering :=
  let ta := a.tag
  let tb := b.tag
  if ta == 0 || tb == 0 then none
  else if ta == 2 && tb == 2 then some (compare (int60 a.payload) (int60 b.payload))
  else if (ta == 2 || ta == 3) && (tb == 2 || tb == 3) then
    match a.num?, b.num? with
    | some x, some y => some (cmpFloat x y)
    | _, _ => none
  else if ta == tb then some (compare a.payload b.payload)
  else none

/-- `ORDER BY` order (QLever `CompareByType`): compatible Ids as above,
    others by datatype tag. Equal bits are equal. -/
def cmpIdsOrder (a b : Id) : Ordering :=
  if a.bits == b.bits then .eq
  else match cmpIdsCompatible a b with
    | some o => o
    | none => compare a.tag b.tag

#guard cmpIdsOrder (Id.ofInt (-3)) (Id.ofInt 2) == .lt
#guard cmpIdsOrder (Id.ofInt 2) (Id.ofVocabIndex 0) == .lt
#guard cmpIdsOrder (Id.ofVocabIndex 7) (Id.ofVocabIndex 5) == .gt
-- 70.0 as a Double Id against the Int 71
#guard cmpIdsOrder ⟨((3 : UInt64) <<< 60) ||| ((0x4051800000000000 : UInt64) >>> 4)⟩ (Id.ofInt 71) == .lt
#guard cmpIdsCompatible (Id.ofInt 1) (Id.ofVocabIndex 1) == none

/-! ## Patterns and permutations -/

inductive Slot where
  | var (v : String)
  | const (x : Id)
  /-- a constant that is not in the index -/
  | missing
  deriving Repr, BEq, Inhabited

structure TriplePat where
  s : Slot
  p : Slot
  o : Slot
  deriving Repr, Inhabited

def TriplePat.slot (t : TriplePat) : Nat → Slot
  | 0 => t.s
  | 1 => t.p
  | _ => t.o

def TriplePat.vars (t : TriplePat) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [0:3] do
    match t.slot i with
    | .var v => if !out.contains v then out := out.push v
    | _ => pure ()
  return out

def TriplePat.hasMissing (t : TriplePat) : Bool :=
  t.s == .missing || t.p == .missing || t.o == .missing

def TriplePat.bound (t : TriplePat) (i : Nat) : Bool :=
  match t.slot i with
  | .var _ => false
  | _ => true

/-- A permutation: its file suffix and the triple positions of its columns. -/
structure PermInfo where
  name : String
  order : Array Nat
  deriving Repr, Inhabited

def permInfos : Array PermInfo :=
  #[⟨"pso", #[1, 0, 2]⟩, ⟨"pos", #[1, 2, 0]⟩, ⟨"spo", #[0, 1, 2]⟩,
    ⟨"sop", #[0, 2, 1]⟩, ⟨"osp", #[2, 0, 1]⟩, ⟨"ops", #[2, 1, 0]⟩]

/-- The permutation for `t`: its bound positions first; then position
    `pref` when given and possible. -/
def permFor (t : TriplePat) (pref : Option Nat) : Nat := Id.run do
  let m := ([0, 1, 2].filter t.bound).length
  let mut first : Option Nat := none
  for k in [0:permInfos.size] do
    let o := permInfos[k]!.order
    let prefixOk := (List.range m).all fun j => t.bound o[j]!
    if prefixOk then
      if first.isNone then first := some k
      match pref with
      | some q => if m < 3 && o[m]! == q then return k
      | none => pure ()
  return first.getD 0

/-! ## Tables -/

/-- A table of solutions: one column (8-byte Ids) per variable. -/
structure Table where
  vars : Array String
  cols : Array ByteArray
  rows : Nat
  /-- the rows are in ascending `Id` bit order of this variable -/
  sortVar : Option String := none
  deriving Inhabited

def Table.empty (vars : Array String) : Table :=
  { vars, cols := vars.map fun _ => ByteArray.empty, rows := 0 }

def Table.idx (t : Table) (v : String) : Option Nat := t.vars.findIdx? (· == v)

@[inline] def Table.at (t : Table) (c i : Nat) : UInt64 := word64 t.cols[c]! (8 * i)

/-- Append row `i` of `src` (columns `srcCols`) to the columns `dst`. -/
@[inline] def pushRowCols (dst : Array ByteArray) (dstOff : Nat) (src : Array ByteArray)
    (srcCols : Array Nat) (i : Nat) : Array ByteArray := _root_.Id.run do
  let mut d := dst
  for k in [0:srcCols.size] do
    d := d.modify (dstOff + k) fun b => Side.put64 b (word64 src[srcCols[k]!]! (8 * i))
  return d

/-- Append the rows of `b` to `a` (same variables, in the same order). -/
def Table.append (a b : Table) : Table := _root_.Id.run do
  let mut cols := a.cols
  for k in [0:a.cols.size] do
    cols := cols.modify k fun c => c ++ b.cols[k]!
  return { a with cols, rows := a.rows + b.rows }

/-- The rows whose index `keep` holds, in order. -/
def Table.select (t : Table) (keep : Nat → Bool) : Table := _root_.Id.run do
  let all := (List.range t.vars.size).toArray
  let mut cols := t.vars.map fun _ => ByteArray.empty
  let mut n := 0
  for i in [0:t.rows] do
    if keep i then
      cols := pushRowCols cols 0 t.cols all i
      n := n + 1
  return { t with cols, rows := n }

/-- The rows in the order of the index array `perm`. -/
def Table.reorder (t : Table) (perm : Array Nat) : Table := _root_.Id.run do
  let all := (List.range t.vars.size).toArray
  let mut cols := t.vars.map fun _ => ByteArray.emptyWithCapacity (8 * perm.size)
  for i in perm do
    cols := pushRowCols cols 0 t.cols all i
  return { t with cols, rows := perm.size, sortVar := none }

/-- Rows `[lo, hi)`. -/
def Table.slice (t : Table) (lo hi : Nat) : Table :=
  let hi := min hi t.rows
  let lo := min lo hi
  { t with cols := t.cols.map (·.extract (8 * lo) (8 * hi)), rows := hi - lo }

/-! ## Scans -/

/-- What a scan reads: the permutation, the key prefix, the columns to
    output and the columns that must be equal (a variable repeated in the
    pattern). -/
structure ScanSpec where
  perm : Nat
  key : Array UInt64
  outVars : Array String
  outCols : Array Nat
  eqs : Array (Nat × Nat)
  deriving Repr, Inhabited

/-- The scan of `t` from permutation `perm`, keeping the variables `need`
    selects. -/
def mkSpec (t : TriplePat) (perm : Nat) (need : String → Bool) : ScanSpec := Id.run do
  let o := permInfos[perm]!.order
  let mut key : Array UInt64 := #[]
  let mut outVars : Array String := #[]
  let mut outCols : Array Nat := #[]
  let mut eqs : Array (Nat × Nat) := #[]
  let mut seen : Array (String × Nat) := #[]
  for c in [0:3] do
    match t.slot o[c]! with
    | .const x => key := key.push x.bits
    | .missing => key := key.push 0
    | .var v =>
      match seen.find? (·.1 == v) with
      | some (_, c0) => eqs := eqs.push (c0, c)
      | none =>
        seen := seen.push (v, c)
        if need v then
          outVars := outVars.push v
          outCols := outCols.push c
  return { perm, key, outVars, outCols, eqs }

/-- Compare the first `key.size` Ids of a block triple with `key`. -/
def prefixCmp (tr : Array Id) (key : Array UInt64) : Ordering := Id.run do
  for j in [0:key.size] do
    let a := (tr.getD j default).bits
    let b := key[j]!
    if a < b then return .lt
    if b < a then return .gt
  return .eq

def BlockMeta.selects (b : BlockMeta) (key : Array UInt64) : Bool :=
  prefixCmp b.first key != .gt && prefixCmp b.last key != .lt

def BlockMeta.full (b : BlockMeta) (key : Array UInt64) : Bool :=
  prefixCmp b.first key == .eq && prefixCmp b.last key == .eq

/-- Rows of the selected blocks: exact when every selected block is full. -/
def estimate (pm : PermMeta) (key : Array UInt64) : Nat :=
  pm.blocks.foldl (fun a b => if b.selects key then a + b.rows else a) 0

/-- Rows `i..rows-1` of a decoded block: keep those whose key columns
    (`checks`) and repeated-variable columns (`eqs`) match, appending their
    output columns to `acc`. -/
def selectRows (cols : Array ByteArray) (checks : Array (Nat × UInt64)) (eqs : Array (Nat × Nat))
    (outCols : Array Nat) (rows : Nat) :
    Nat → Nat → Array ByteArray → Nat → Array ByteArray × Nat
  | 0, _, acc, n => (acc, n)
  | k+1, i, acc, n =>
    if i ≥ rows then (acc, n)
    else
      let ok := checks.all (fun (c, x) => word64 cols[c]! (8 * i) == x) &&
        eqs.all (fun (a, b) => word64 cols[a]! (8 * i) == word64 cols[b]! (8 * i))
      if ok then selectRows cols checks eqs outCols rows k (i + 1) (pushRowCols acc 0 cols outCols i) (n + 1)
      else selectRows cols checks eqs outCols rows k (i + 1) acc n

/-- Fetch and decompress column `c` of block `b`. -/
def fetchColumn {m : Type → Type} [Monad m] (fetch : Nat → Nat → m ByteArray)
    (b : BlockMeta) (c : Nat) : ExceptT String m ByteArray := do
  let some cr := b.cols[c]? | throw s!"block {b.index}: no column {c}"
  let frame ← (fetch cr.offset cr.size : m ByteArray)
  if frame.size != cr.size then throw s!"block {b.index}: read {frame.size} of {cr.size} bytes at {cr.offset}"
  match decodeColumn frame b.rows with
  | .ok col => pure col
  | .error e => throw s!"block {b.index}: {e}"

/-- One permutation file: its metadata and positioned reads of it. -/
structure PermSrc (m : Type → Type) where
  permMeta : PermMeta
  fetch : Nat → Nat → m ByteArray

instance {m : Type → Type} [Monad m] : Inhabited (PermSrc m) :=
  ⟨{ permMeta := default, fetch := fun _ _ => pure ByteArray.empty }⟩

structure ScanStats where
  blocksRead : Nat := 0
  blocksTotal : Nat := 0
  framesRead : Nat := 0
  bytesRead : Nat := 0
  rowsOut : Nat := 0
  deriving Repr, Inhabited

/-- Scan block by block. `f` gets each block's matching rows as a table and
    answers whether to continue; the scan stops at `false`. -/
def scanFoldM {m : Type → Type} [Monad m] {σ : Type} (src : PermSrc m) (spec : ScanSpec)
    (init : σ) (f : σ → Table → ExceptT String m (σ × Bool)) : ExceptT String m (σ × ScanStats) := do
  let mut st := init
  let mut stats : ScanStats := { blocksTotal := src.permMeta.blocks.size }
  let sortVar := match spec.outCols[0]? with
    | some c => if c == spec.key.size then spec.outVars[0]? else none
    | none => none
  for b in src.permMeta.blocks do
    if !b.selects spec.key then continue
    let full := b.full spec.key
    let checks : Array (Nat × UInt64) :=
      if full then #[] else (List.range spec.key.size).toArray.map fun j => (j, spec.key[j]!)
    let needCols := (checks.map (·.1)) ++ spec.outCols ++ spec.eqs.map (·.1) ++ spec.eqs.map (·.2)
    let mut cols : Array ByteArray := #[ByteArray.empty, ByteArray.empty, ByteArray.empty]
    for c in [0:3] do
      if needCols.contains c then
        cols := cols.set! c (← fetchColumn src.fetch b c)
        stats := { stats with framesRead := stats.framesRead + 1,
                              bytesRead := stats.bytesRead + (b.cols[c]?.map (·.size)).getD 0 }
    stats := { stats with blocksRead := stats.blocksRead + 1 }
    let chunk : Table :=
      if checks.isEmpty && spec.eqs.isEmpty then
        { vars := spec.outVars, cols := spec.outCols.map (cols[·]!), rows := b.rows, sortVar }
      else
        let (acc, n) := selectRows cols checks spec.eqs spec.outCols b.rows (b.rows + 1) 0
          (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * b.rows)) 0
        { vars := spec.outVars, cols := acc, rows := n, sortVar }
    stats := { stats with rowsOut := stats.rowsOut + chunk.rows }
    let (st', more) ← f st chunk
    st := st'
    if !more then break
  return (st, stats)

/-- The whole scan as one table. -/
def scanTableM {m : Type → Type} [Monad m] (src : PermSrc m) (spec : ScanSpec) :
    ExceptT String m (Table × ScanStats) := do
  let sortVar := match spec.outCols[0]? with
    | some c => if c == spec.key.size then spec.outVars[0]? else none
    | none => none
  let init : Table := { Table.empty spec.outVars with sortVar }
  scanFoldM src spec init fun acc chunk => pure (acc.append chunk, true)

/-! ## Joins -/

/-- Output layout of a join: all of `l`'s variables, then `r`'s others. -/
def joinVars (l r : Table) : Array String × Array Nat :=
  let extra := (List.range r.vars.size).toArray.filter fun k => !l.vars.contains r.vars[k]!
  (l.vars ++ extra.map (r.vars[·]!), extra)

/-- Shared variables as column pairs `(l, r)`. -/
def sharedCols (l r : Table) : Array (Nat × Nat) :=
  (List.range l.vars.size).toArray.filterMap fun i =>
    (r.idx l.vars[i]!).map fun j => (i, j)

@[inline] def emitPair (out : Array ByteArray) (l r : Table) (lAll extra : Array Nat) (i j : Nat) :
    Array ByteArray :=
  pushRowCols (pushRowCols out 0 l.cols lAll i) lAll.size r.cols extra j

/-- Merge join of `l` and `r`, both in ascending order of variable `v`. -/
def mergeJoin (l r : Table) (v : String) : Table := _root_.Id.run do
  let (vars, extra) := joinVars l r
  let lAll := (List.range l.vars.size).toArray
  let shared := sharedCols l r
  let lc := (l.idx v).getD 0
  let rc := (r.idx v).getD 0
  let others := shared.filter fun (a, _) => a != lc
  let mut out : Array ByteArray := vars.map fun _ => ByteArray.empty
  let mut n := 0
  let mut i := 0
  let mut j := 0
  for _ in [0:l.rows + r.rows + 1] do
    if i ≥ l.rows || j ≥ r.rows then break
    let a := l.at lc i
    let b := r.at rc j
    if a < b then i := i + 1
    else if b < a then j := j + 1
    else
      let mut ie := i + 1
      for _ in [0:l.rows] do
        if ie < l.rows && l.at lc ie == a then ie := ie + 1 else break
      let mut je := j + 1
      for _ in [0:r.rows] do
        if je < r.rows && r.at rc je == a then je := je + 1 else break
      for x in [i:ie] do
        for y in [j:je] do
          if others.all (fun (p, q) => l.at p x == r.at q y) then
            out := emitPair out l r lAll extra x y
            n := n + 1
      i := ie
      j := je
  return { vars, cols := out, rows := n, sortVar := some v }

/-- Hash join on all shared variables; built on the smaller input, output
    in the order of the other input. With no shared variable, the cross
    product. -/
def hashJoin (l r : Table) : Table := _root_.Id.run do
  let (vars, extra) := joinVars l r
  let lAll := (List.range l.vars.size).toArray
  let shared := sharedCols l r
  let keyL (i : Nat) : List UInt64 := (shared.map fun (p, _) => l.at p i).toList
  let keyR (j : Nat) : List UInt64 := (shared.map fun (_, q) => r.at q j).toList
  let mut out : Array ByteArray := vars.map fun _ => ByteArray.empty
  let mut n := 0
  if r.rows ≤ l.rows then
    let mut h : Std.HashMap (List UInt64) (Array Nat) := {}
    for j in [0:r.rows] do
      h := h.alter (keyR j) fun | some a => some (a.push j) | none => some #[j]
    for i in [0:l.rows] do
      for j in h.getD (keyL i) #[] do
        out := emitPair out l r lAll extra i j
        n := n + 1
    return { vars, cols := out, rows := n, sortVar := l.sortVar }
  else
    let mut h : Std.HashMap (List UInt64) (Array Nat) := {}
    for i in [0:l.rows] do
      h := h.alter (keyL i) fun | some a => some (a.push i) | none => some #[i]
    for j in [0:r.rows] do
      for i in h.getD (keyR j) #[] do
        out := emitPair out l r lAll extra i j
        n := n + 1
    return { vars, cols := out, rows := n,
             sortVar := match r.sortVar with
               | some v => if l.vars.contains v || r.vars.contains v then some v else none
               | none => none }

/-! ## Planning and execution -/

/-- How often each variable occurs over the patterns. -/
def varCount (pats : Array TriplePat) (v : String) : Nat :=
  pats.foldl (fun a t => if t.vars.contains v then a + 1 else a) 0

/-- A position of `t` holding the variable that occurs in most patterns. -/
def bestSortPos (t : TriplePat) (pats : Array TriplePat) : Option Nat := Id.run do
  let mut best : Option (Nat × Nat) := none
  for i in [0:3] do
    match t.slot i with
    | .var v =>
      let c := varCount pats v
      match best with
      | some (_, c0) => if c > c0 then best := some (i, c)
      | none => best := some (i, c)
    | _ => pure ()
  return best.map (·.1)

def posOf (t : TriplePat) (v : String) : Option Nat :=
  [0, 1, 2].find? fun i => t.slot i == .var v

/-- Evaluate a BGP. `need v` says the query uses variable `v` after the BGP.
    Returns the solutions (only the needed and the join variables are
    stored) and one line per step for `--explain`. -/
def evalBgpM {m : Type → Type} [Monad m] (srcs : Array (PermSrc m)) (pats : Array TriplePat)
    (need : String → Bool) : ExceptT String m (Table × Array String) := do
  let allVars := pats.foldl (fun a t => t.vars.foldl (fun a v => if a.contains v then a else a.push v) a) #[]
  let keep (v : String) : Bool := need v || varCount pats v ≥ 2
  if pats.isEmpty then throw "empty basic graph pattern"
  if pats.any (·.hasMissing) then
    return ({ Table.empty (allVars.filter keep) with rows := 0 },
            #["a constant is not in the index: no solutions"])
  if srcs.size != permInfos.size then throw "need the six permutations"
  let est (t : TriplePat) : Nat :=
    let spec := mkSpec t (permFor t none) keep
    estimate srcs[spec.perm]!.permMeta spec.key
  let mut remaining := (List.range pats.size).toArray
  let mut lines : Array String := #[]
  -- first pattern
  let first := remaining.foldl (fun b k => if est pats[k]! < est pats[b]! then k else b) remaining[0]!
  remaining := remaining.filter (· != first)
  let t0 := pats[first]!
  let spec0 := mkSpec t0 (permFor t0 (bestSortPos t0 pats)) keep
  let (tab0, st0) ← scanTableM srcs[spec0.perm]! spec0
  lines := lines.push s!"pattern {first}: {permInfos[spec0.perm]!.name} key {spec0.key.size} estimate {est t0}; blocks {st0.blocksRead} of {st0.blocksTotal}, frames {st0.framesRead}, {st0.bytesRead} bytes; rows {tab0.rows}"
  let mut tab := tab0
  for _ in [0:pats.size] do
    if remaining.isEmpty then break
    let connected := remaining.filter fun k => pats[k]!.vars.any tab.vars.contains
    let cands := if connected.isEmpty then remaining else connected
    let next := cands.foldl (fun b k => if est pats[k]! < est pats[b]! then k else b) cands[0]!
    remaining := remaining.filter (· != next)
    let t := pats[next]!
    let mergeVar : Option (String × Nat) := match tab.sortVar with
      | some v => (posOf t v).bind fun q => if t.bound q then none else some (v, q)
      | none => none
    let perm := match mergeVar with
      | some (_, q) => permFor t (some q)
      | none => permFor t (bestSortPos t pats)
    let spec := mkSpec t perm keep
    let (rt, st) ← scanTableM srcs[perm]! spec
    let (joined, how) := match mergeVar with
      | some (v, _) =>
        if rt.sortVar == some v then (mergeJoin tab rt v, s!"merge join on ?{v}")
        else (hashJoin tab rt, "hash join")
      | none => (hashJoin tab rt, if (sharedCols tab rt).isEmpty then "cross product" else "hash join")
    lines := lines.push s!"pattern {next}: {permInfos[perm]!.name} key {spec.key.size} estimate {est t}; blocks {st.blocksRead} of {st.blocksTotal}, frames {st.framesRead}, {st.bytesRead} bytes; rows {rt.rows}; {how}: {joined.rows} rows"
    tab := joined
  return (tab, lines)

end L4Factoidal.Qlvr
