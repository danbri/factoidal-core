/-
L4Factoidal.Storage.Sbm11.Block — sorted quad permutations of wire version
11: rows, blocks (PRB1) and block metadata (PRM1)
(`docs/designissues/2026-10-11-shardborough-vs-qlever.md` sections 6.3 to
6.5; https://github.com/danbri/factoidal/issues/789).

## Rows and permutations

A quad is `(s, p, o, g)` of ids (`TermId`, `GraphId`; `g = 0` is the default
graph). A permutation stores each quad as a `Row` `(c0, c1, c2, g)`:

| Permutation | code | c0 | c1 | c2 |
| --- | ---: | --- | --- | --- |
| PSO | 0 | p | s | o |
| POS | 1 | p | o | s |
| SPO | 2 | s | p | o |
| OSP | 3 | o | s | p |

Rows are strictly increasing in the lexicographic order of `(c0, c1, c2, g)`
(`Row.lt`), so a permutation holds each quad once.

## PRB1 (`<perm>.prb1`)

    "PRB1"  version u8 = 1  perm u8
    block*  frame(c0) frame(c1) frame(c2) frame(g)    (`Column.frameBytes`)

## PRM1 (`<perm>.prm1`)

    "PRM1"  version u8 = 1  perm u8  blockCount u64  rowCount u64
    entry*  92 bytes per block:
            first row 4 × u64   last row 4 × u64   rows u32
            offset u64 (in PRB1)   len(c0) len(c1) len(c2) len(g)  4 × u32

## Admission

`prmAdmitted`: `perm < 4`; every block has at least one row and fewer than
`2^32`; `first ≤ last`; the last row of a block is below the first row of
the next (`Row.lt`): blocks are sorted and do not overlap; the first block
starts at byte 6 of PRB1 and every next block starts where the previous one
ends; every field inside its width. `decodePrm` checks the same predicate on
what it read and that `rowCount` is the sum of the blocks' rows.

`encodeBlock?` admits a non-empty, strictly increasing list of rows whose
ids are below `2^64`, with fewer than `2^32` rows. `decodeBlock m bytes`
cuts the four frames by the lengths of `m`, decodes each to `m.rows` ids
and checks that the rows are strictly increasing, that their count is
`m.rows` and that the first and last rows are `m.first` and `m.last`
(`BlockTheorems.decodeBlock_bounds`).

## Loops

Every recursive function here is a tail call with an accumulator or a count
`Nat` first. No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Column

namespace L4Factoidal.Storage.Sbm11.Block

open L4Factoidal (two32 two64)
open L4Factoidal.Storage.Sbm11.Column

/-! ## Rows -/

structure Row where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  g : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Lexicographic strict order on `(c0, c1, c2, g)`. -/
def Row.lt (a b : Row) : Bool :=
  if a.c0 != b.c0 then a.c0 < b.c0
  else if a.c1 != b.c1 then a.c1 < b.c1
  else if a.c2 != b.c2 then a.c2 < b.c2
  else a.g < b.g

def Row.le (a b : Row) : Bool := a == b || a.lt b

def Row.fits (r : Row) : Bool := r.c0 < two64 && r.c1 < two64 && r.c2 < two64 && r.g < two64

def sortedGo : Row → List Row → Bool
  | _, [] => true
  | prev, r :: rs => if prev.lt r then sortedGo r rs else false

def rowsSorted : List Row → Bool
  | [] => true
  | r :: rs => sortedGo r rs

def zipRows (a b c d : List Nat) : List Row :=
  List.zipWith (fun (p : Nat × Nat) (q : Nat × Nat) => Row.mk p.1 p.2 q.1 q.2) (List.zip a b) (List.zip c d)

/-! ## Blocks -/

structure BlockMeta where
  first : Row
  last : Row
  rows : Nat
  offset : Nat
  len0 : Nat
  len1 : Nat
  len2 : Nat
  len3 : Nat
  deriving DecidableEq, Repr, Inhabited

def BlockMeta.size (m : BlockMeta) : Nat := m.len0 + m.len1 + m.len2 + m.len3

/-- The bytes of a block: four frames. -/
def blockBytes (rows : List Row) : List UInt8 :=
  frameBytes (rows.map Row.c0) ++ frameBytes (rows.map Row.c1) ++
    frameBytes (rows.map Row.c2) ++ frameBytes (rows.map Row.g)

def blockAdmitted (rows : List Row) : Bool :=
  !rows.isEmpty && rowsSorted rows && rows.all Row.fits && decide (rows.length < two32) &&
    decide ((frameBytes (rows.map Row.c0)).length < two32) &&
    decide ((frameBytes (rows.map Row.c1)).length < two32) &&
    decide ((frameBytes (rows.map Row.c2)).length < two32) &&
    decide ((frameBytes (rows.map Row.g)).length < two32)

/-- The block at PRB1 offset `offset`: its PRM1 entry and its bytes. -/
def encodeBlock? (offset : Nat) (rows : List Row) : Option (BlockMeta × List UInt8) :=
  if blockAdmitted rows then
    some ({ first := rows.headD default, last := rows.getLastD default, rows := rows.length, offset,
            len0 := (frameBytes (rows.map Row.c0)).length, len1 := (frameBytes (rows.map Row.c1)).length,
            len2 := (frameBytes (rows.map Row.c2)).length, len3 := (frameBytes (rows.map Row.g)).length },
          blockBytes rows)
  else none

/-- One frame that is exactly `n` rows. -/
def decodeFrame (n : Nat) (f : List UInt8) : Option (List Nat) :=
  match decodeColumn n f with
  | some (c, []) => some c
  | _ => none

def blockOk (m : BlockMeta) (rows : List Row) : Bool :=
  rows.length == m.rows && rows.head? == some m.first && rows.getLast? == some m.last && rowsSorted rows

/-- The rows of a block from its PRM1 entry and its bytes. -/
def decodeBlock (m : BlockMeta) (bs : List UInt8) : Option (List Row) :=
  if bs.length != m.size then none
  else
    let bs1 := bs.drop m.len0
    let bs2 := bs1.drop m.len1
    let bs3 := bs2.drop m.len2
    match decodeFrame m.rows (bs.take m.len0), decodeFrame m.rows (bs1.take m.len1),
      decodeFrame m.rows (bs2.take m.len2), decodeFrame m.rows bs3 with
    | some c0, some c1, some c2, some g =>
      let rows := zipRows c0 c1 c2 g
      if blockOk m rows then some rows else none
    | _, _, _, _ => none

/-! ## PRM1 -/

def prbHeaderBytes : Nat := 6

def prbHeader (perm : Nat) : List UInt8 := [80, 82, 66, 49, 1, perm.toUInt8]

def prmMagic : List UInt8 := [80, 82, 77, 49, 1]

def prmHeaderBytes : Nat := 22

def prmEntryBytes : Nat := 92

def rowBytes (r : Row) : List UInt8 := put64 r.c0 ++ put64 r.c1 ++ put64 r.c2 ++ put64 r.g

def getRow (bs : List UInt8) : Option (Row × List UInt8) := do
  let (a, r1) ← get64 bs
  let (b, r2) ← get64 r1
  let (c, r3) ← get64 r2
  let (d, r4) ← get64 r3
  some (⟨a, b, c, d⟩, r4)

def entryBytes (m : BlockMeta) : List UInt8 :=
  rowBytes m.first ++ rowBytes m.last ++ put32 m.rows ++ put64 m.offset ++
    put32 m.len0 ++ put32 m.len1 ++ put32 m.len2 ++ put32 m.len3

def getEntry (bs : List UInt8) : Option (BlockMeta × List UInt8) := do
  let (first, r1) ← getRow bs
  let (last, r2) ← getRow r1
  let (rows, r3) ← get32 r2
  let (offset, r4) ← get64 r3
  let (len0, r5) ← get32 r4
  let (len1, r6) ← get32 r5
  let (len2, r7) ← get32 r6
  let (len3, r8) ← get32 r7
  some ({ first, last, rows, offset, len0, len1, len2, len3 }, r8)

def metaFits (m : BlockMeta) : Bool :=
  m.first.fits && m.last.fits && decide (0 < m.rows) && decide (m.rows < two32) &&
    decide (m.offset < two64) && decide (m.len0 < two32) && decide (m.len1 < two32) &&
    decide (m.len2 < two32) && decide (m.len3 < two32) && m.first.le m.last

/-- Every entry fits, the blocks are sorted without overlap, and they are
    contiguous in PRB1 from byte `off`. -/
def chainGo : Nat → List BlockMeta → Bool
  | _, [] => true
  | off, m :: ms =>
    if metaFits m && m.offset == off then
      match ms with
      | [] => true
      | n :: _ => if m.last.lt n.first then chainGo (off + m.size) ms else false
    else false

def rowSumGo : List BlockMeta → Nat → Nat
  | [], acc => acc
  | m :: ms, acc => rowSumGo ms (acc + m.rows)

def rowSum (ms : List BlockMeta) : Nat := rowSumGo ms 0

def prmAdmitted (perm : Nat) (ms : List BlockMeta) : Bool :=
  decide (perm < 4) && chainGo prbHeaderBytes ms && decide (ms.length < two64) &&
    decide (rowSum ms < two64)

def prmBytes (perm : Nat) (ms : List BlockMeta) : List UInt8 :=
  prmMagic ++ [perm.toUInt8] ++ put64 ms.length ++ put64 (rowSum ms) ++ (ms.map entryBytes).flatten

def encodePrm? (perm : Nat) (ms : List BlockMeta) : Option (List UInt8) :=
  if prmAdmitted perm ms then some (prmBytes perm ms) else none

def getEntriesGo : Nat → List UInt8 → List BlockMeta → Option (List BlockMeta × List UInt8)
  | 0, bs, acc => some (acc.reverse, bs)
  | n + 1, bs, acc =>
    match getEntry bs with
    | none => none
    | some (m, rest) => getEntriesGo n rest (m :: acc)

/-- A PRM1 file: its permutation code and its entries. -/
def decodePrm (bs : List UInt8) : Option (Nat × List BlockMeta) :=
  match bs with
  | 80 :: 82 :: 77 :: 49 :: 1 :: p :: rest =>
    match get64 rest with
    | none => none
    | some (count, r1) =>
      match get64 r1 with
      | none => none
      | some (total, r2) =>
        match getEntriesGo count r2 [] with
        | some (ms, []) =>
          if prmAdmitted p.toNat ms && total == rowSum ms then some (p.toNat, ms) else none
        | _ => none
  | _ => none

/-! ## The runtime block decoder -/

/-- Four decoded columns of one block. -/
structure Cols where
  c0 : Array Nat
  c1 : Array Nat
  c2 : Array Nat
  g : Array Nat
  deriving Inhabited

def Cols.size (c : Cols) : Nat := c.c0.size

def Cols.row (c : Cols) (i : Nat) : Row := ⟨c.c0[i]!, c.c1[i]!, c.c2[i]!, c.g[i]!⟩

def colsSortedGo (c : Cols) : Nat → Nat → Bool
  | 0, _ => true
  | f + 1, i => if i + 1 < c.size then (if (c.row i).lt (c.row (i + 1)) then colsSortedGo c f (i + 1) else false) else true

/-- The frames of a block at offset `base` of `b` (the block's bytes, or a
    whole PRB1 file with `base = m.offset`): the columns, after the checks
    of `decodeBlock`. -/
def decodeBlockAt (b : ByteArray) (m : BlockMeta) (base : Nat) : Except String Cols := do
  let frame (k off len : Nat) : Except String (Array Nat) :=
    match decodeColumnAt b m.rows off with
    | some (c, j) =>
      if j == off + len && c.size == m.rows then .ok c
      else .error s!"block at {m.offset}: frame {k} does not end at its length"
    | none => .error s!"block at {m.offset}: frame {k} does not decode"
  if base + m.size > b.size then throw s!"block at {m.offset}: {m.size} bytes past the end"
  let c0 ← frame 0 base m.len0
  let c1 ← frame 1 (base + m.len0) m.len1
  let c2 ← frame 2 (base + m.len0 + m.len1) m.len2
  let g ← frame 3 (base + m.len0 + m.len1 + m.len2) m.len3
  let cols : Cols := ⟨c0, c1, c2, g⟩
  if m.rows == 0 then throw s!"block at {m.offset}: no rows"
  if cols.row 0 != m.first then throw s!"block at {m.offset}: first row differs from PRM1"
  if cols.row (m.rows - 1) != m.last then throw s!"block at {m.offset}: last row differs from PRM1"
  if !colsSortedGo cols m.rows 0 then throw s!"block at {m.offset}: rows not strictly increasing"
  pure cols

/-! ## Unit tests -/

private def rs : List Row := [⟨1, 2, 3, 0⟩, ⟨1, 2, 4, 0⟩, ⟨1, 5, 4, 0⟩, ⟨7, 0, 0, 0⟩]

#guard rowsSorted rs
#guard !rowsSorted [⟨1, 2, 3, 0⟩, ⟨1, 2, 3, 0⟩]
#guard match encodeBlock? 6 rs with
  | some (m, bs) => decodeBlock m bs == some rs && m.first == ⟨1, 2, 3, 0⟩ && m.last == ⟨7, 0, 0, 0⟩
  | none => false
#guard encodeBlock? 6 [] == none
#guard encodeBlock? 6 [⟨1, 2, 3, 0⟩, ⟨1, 2, 3, 0⟩] == none
-- a PRM1 entry whose first row is not the block's first row is refused
#guard match encodeBlock? 6 rs with
  | some (m, bs) => decodeBlock { m with first := ⟨1, 2, 3, 1⟩ } bs == none
  | none => false
#guard match encodeBlock? 6 rs with
  | some (m, bs) =>
    match decodeBlockAt ⟨bs.toArray⟩ m 0 with
    | .ok c => (List.range c.size).map c.row == rs
    | .error _ => false
  | none => false
#guard match encodeBlock? 6 rs with
  | some (m, bs) =>
    match decodeBlockAt ⟨bs.toArray⟩ { m with last := ⟨7, 0, 0, 1⟩ } 0 with
    | .ok _ => false
    | .error _ => true
  | none => false
#guard match encodeBlock? 6 rs, encodeBlock? 0 [⟨8, 0, 0, 0⟩, ⟨9, 1, 1, 0⟩] with
  | some (m1, b1), some (m2, _) =>
    let m2 := { m2 with offset := 6 + b1.length }
    decodePrm (prmBytes 2 [m1, m2]) == some (2, [m1, m2]) &&
      (encodePrm? 2 [m1, m2]).isSome &&
      -- overlapping or unordered blocks are refused
      (encodePrm? 2 [m2, m1]).isNone &&
      decodePrm (prmBytes 2 [m2, m1]) == none &&
      -- a gap in PRB1 is refused
      (encodePrm? 2 [m1, { m2 with offset := m2.offset + 1 }]).isNone
  | _, _ => false

end L4Factoidal.Storage.Sbm11.Block
