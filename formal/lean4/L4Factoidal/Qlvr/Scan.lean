/-
L4Factoidal.Qlvr.Scan — bound-col0 scans and block rendering over a QLever
permutation (Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).

A scan for one bound col0 value `x` (format record, section 3, "A scan for
one bound col0 value"): select the blocks with
`firstTriple.col0 ≤ x ≤ lastTriple.col0`, decompress columns 0, 1 and 2 of
each, keep the rows whose column 0 is `x`. Only the selected blocks' frames
are fetched.

The scan is written once over a fetch function `Nat → Nat → m ByteArray`
(file offset, length) so that the same code runs over a file read by
positioned reads (the native harness, `m = IO`) and over bytes in memory
(`scanPredicate`, `m = Id`).

## Loops

`collectRows` and `renderLoop` are tail calls over the rows of one block
with a fuel `Nat` first and the output as an accumulator. The loop over the
selected blocks is a `for` loop (at most the block count of the file).
-/
import L4Factoidal.Qlvr.Perm
import L4Factoidal.Qlvr.Term

namespace L4Factoidal.Qlvr

/-- Rows `i..rows-1` of a block whose column 0 equals `x`, as (col1, col2). -/
def collectRows (c0 c1 c2 : ByteArray) (x : Id) (rows : Nat) :
    Nat → Nat → Array (Id × Id) → Array (Id × Id)
  | 0, _, acc => acc
  | k+1, i, acc =>
    if i ≥ rows then acc
    else
      let acc := if (colId c0 i).bits == x.bits then acc.push (colId c1 i, colId c2 i) else acc
      collectRows c0 c1 c2 x rows k (i + 1) acc

/-- Fetch and decode columns `0..n-1` of block `b`. -/
def fetchColumns {m : Type → Type} [Monad m] (fetch : Nat → Nat → m ByteArray)
    (b : BlockMeta) (n : Nat) : ExceptT String m (Array ByteArray) := do
  if b.cols.size < n then throw s!"block {b.index}: {b.cols.size} columns, need {n}"
  let mut out : Array ByteArray := #[]
  for c in b.cols[0:n] do
    let frame ← (fetch c.offset c.size : m ByteArray)
    if frame.size != c.size then throw s!"block {b.index}: read {frame.size} of {c.size} bytes at {c.offset}"
    match decodeColumn frame b.rows with
    | .ok col => out := out.push col
    | .error e => throw s!"block {b.index}: {e}"
  pure out

/-- All (col1, col2) pairs of the rows whose col0 is `x`, in permutation
    order. Over PSO with `x` a predicate this is the (subject, object) list. -/
def scanCol0M {m : Type → Type} [Monad m] (fetch : Nat → Nat → m ByteArray)
    (pm : PermMeta) (x : Id) : ExceptT String m (Array (Id × Id)) := do
  let mut acc : Array (Id × Id) := #[]
  for b in pm.blocks do
    if b.covers x then
      let cols ← fetchColumns fetch b 3
      acc := collectRows cols[0]! cols[1]! cols[2]! x b.rows (b.rows + 1) 0 acc
  pure acc

/-- A permutation file held in memory. -/
structure MemPerm where
  permMeta : PermMeta
  bytes : ByteArray

def MemPerm.load (bytes : ByteArray) : Except String MemPerm := do
  if bytes.size < 8 then throw "permutation: shorter than its trailer"
  let s ← metaStart (bytes.extract (bytes.size - 8) bytes.size) bytes.size
  let permMeta ← parsePermMeta (bytes.extract s (bytes.size - 8)) bytes.size
  pure { permMeta, bytes }

/-- The (subject, object) pairs of predicate `pred` from the PSO permutation. -/
def scanPredicate (pso : MemPerm) (pred : Id) : Except String (Array (Id × Id)) :=
  (scanCol0M (m := _root_.Id) (fun o n => pso.bytes.extract o (o + n)) pso.permMeta pred).run

/-- Render rows `i..rows-1` of a block as N-Triples lines into `acc`.
    `sC pC oC` are the subject, predicate and object columns; when `filt` is
    `some (c, x)` only rows with `c[i] = x` are rendered. The terms of the
    previous subject and predicate are kept (`lastS`, `lastP`), so a run of
    equal Ids is decoded once. Returns the output and the number of lines. -/
def renderLoop (v : Vocab) (sC pC oC : ByteArray) (filt : Option (ByteArray × Id)) (rows : Nat) :
    Nat → Nat → Option (Id × ByteArray) → Option (Id × ByteArray) → Nat → ByteArray →
    Except String (ByteArray × Nat)
  | 0, _, _, _, n, acc => .ok (acc, n)
  | k+1, i, lastS, lastP, n, acc =>
    if i ≥ rows then .ok (acc, n)
    else
      let keep := match filt with
        | some (c, x) => (colId c i).bits == x.bits
        | none => true
      if !keep then renderLoop v sC pC oC filt rows k (i + 1) lastS lastP n acc
      else
        let s := colId sC i
        let p := colId pC i
        let o := colId oC i
        let sT : Except String ByteArray := match lastS with
          | some (x, t) => if x.bits == s.bits then .ok t else appendTerm v s ByteArray.empty
          | none => appendTerm v s ByteArray.empty
        let pT : Except String ByteArray := match lastP with
          | some (x, t) => if x.bits == p.bits then .ok t else appendTerm v p ByteArray.empty
          | none => appendTerm v p ByteArray.empty
        match sT, pT with
        | .error e, _ => .error e
        | _, .error e => .error e
        | .ok sb, .ok pb =>
          let acc := ((acc ++ sb).push 32 ++ pb).push 32
          match appendTerm v o acc with
          | .error e => .error e
          | .ok acc =>
            renderLoop v sC pC oC filt rows k (i + 1) (some (s, sb)) (some (p, pb)) (n + 1)
              ((acc.push 32 |>.push 46).push 10)

/-- Render a block of a permutation whose columns are in the order given by
    `order` (positions of subject, predicate, object among columns 0..2:
    SPO is `(0, 1, 2)`, PSO is `(1, 0, 2)`). -/
def renderBlock (v : Vocab) (cols : Array ByteArray) (order : Nat × Nat × Nat)
    (filt : Option Id) (rows : Nat) : Except String (ByteArray × Nat) :=
  let (si, pi, oi) := order
  let f := filt.map fun x => (cols[0]!, x)
  renderLoop v cols[si]! cols[pi]! cols[oi]! f rows (rows + 1) 0 none none 0
    (ByteArray.emptyWithCapacity (rows * 120))

/-- Render pairs `i..` of a scan result as N-Triples lines `s pred o .`. -/
def renderPairs (v : Vocab) (pairs : Array (Id × Id)) (predTerm : ByteArray) :
    Nat → Nat → ByteArray → Except String ByteArray
  | 0, _, acc => .ok acc
  | k+1, i, acc =>
    if h : i < pairs.size then
      let (s, o) := pairs[i]
      match appendTerm v s acc with
      | .error e => .error e
      | .ok acc =>
        match appendTerm v o ((acc.push 32 ++ predTerm).push 32) with
        | .error e => .error e
        | .ok acc => renderPairs v pairs predTerm k (i + 1) (((acc.push 32).push 46).push 10)
    else .ok acc

/-- Render vocabulary words `[i, stop)` as N-Triples terms, one per line
    (literals escaped as in `appendStored`). -/
def renderWords (v : Vocab) (stop : Nat) : Nat → Nat → ByteArray → Except String ByteArray
  | 0, _, acc => .ok acc
  | k+1, i, acc =>
    if i ≥ stop then .ok acc
    else match v.wordBytes i with
      | .error e => .error e
      | .ok w =>
        match appendStored w acc with
        | .error e => .error e
        | .ok acc => renderWords v stop k (i + 1) (acc.push 10)

end L4Factoidal.Qlvr
