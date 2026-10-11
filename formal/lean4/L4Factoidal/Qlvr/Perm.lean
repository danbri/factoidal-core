/-
L4Factoidal.Qlvr.Perm — QLever permutation files: the trailing block
metadata, the `.meta` relation array, and column frames (Factoidal/qlvr,
https://github.com/danbri/factoidal/issues/778).

Format record: docs/designissues/2026-10-11-qlever-index-format.md, section 3.

A permutation file is

    [ column frames, at the offsets the block metadata gives, in any order ]
    [ IndexMetaData serialization ]
    [ i64 start offset of the IndexMetaData serialization ]   (last 8 bytes)

`IndexMetaData` (`index/IndexMetaData.h:137-172`): `u64` magic 2^64 - 3,
`u64` version 2, string name, vector of block metadata, `i64` offsetAfter,
`u64` totalElements, `u64` numDistinctCol0. Block metadata
(`index/CompressedRelationMetadata.h:182-205`): vector of
`{i64 offsetInFile, u64 compressedSize}`, `u64` numRows, 4 Ids first
triple, 4 Ids last triple, optional vector of graph Ids, `bool`, `u64`
blockIndex. A vector or string is a `u64` count then the elements; an
optional is a byte 0/1 then the value.

Each column of a block is one zstd frame of `numRows` little-endian 8-byte
Ids (`decodeColumn`, through `L4Factoidal.Codec.Zstd`).

## Loops

The block and relation loops are `for` loops in `Except` over a count that
is first checked against the bytes that remain, so a corrupt count cannot
make the loop longer than the input. They are per block (67 in the largest
file of the instance), not per row.
-/
import L4Factoidal.Codec.Zstd
import L4Factoidal.Qlvr.Id
import L4Factoidal.Qlvr.Vocab

namespace L4Factoidal.Qlvr

open L4Factoidal.Codec.Zstd (word64)

/-- `IndexMetaData` magic (`IndexMetaData.h:46-47`). -/
def metaMagic : UInt64 := 0xFFFFFFFFFFFFFFFD
def metaVersion : UInt64 := 2

/-- The `u64` at `p`, or an error naming `what` when fewer than 8 bytes remain. -/
def rd64 (d : ByteArray) (p : Nat) (what : String) : Except String UInt64 :=
  if p + 8 ≤ d.size then .ok (word64 d p)
  else .error s!"{what}: needs 8 bytes at offset {p}, buffer has {d.size}"

/-- One column frame of a block. -/
structure ColumnRef where
  offset : Nat
  size : Nat
  deriving Repr, Inhabited, BEq

structure BlockMeta where
  cols : Array ColumnRef
  rows : Nat
  /-- col0, col1, col2, graph -/
  first : Array Id
  last : Array Id
  graphs : Option (Array Id)
  dupGraphs : Bool
  index : Nat
  deriving Repr, Inhabited

structure PermMeta where
  name : String
  blocks : Array BlockMeta
  totalElements : Nat
  distinctCol0 : Nat
  deriving Repr, Inhabited

/-- The four Ids of a triple (col0, col1, col2, graph) at `p`. -/
def readTriple (d : ByteArray) (p : Nat) (what : String) : Except String (Array Id) := do
  let a ← rd64 d p what
  let b ← rd64 d (p + 8) what
  let c ← rd64 d (p + 16) what
  let g ← rd64 d (p + 24) what
  pure #[⟨a⟩, ⟨b⟩, ⟨c⟩, ⟨g⟩]

/-- One block metadata record at `p`; returns it and the next position. -/
def readBlockMeta (d : ByteArray) (p : Nat) (fileSize : Nat) : Except String (BlockMeta × Nat) := do
  let ncol := (← rd64 d p "block: column count").toNat
  if ncol * 16 + 8 > d.size - min p d.size then throw s!"block at {p}: {ncol} columns exceed the metadata"
  let mut cols : Array ColumnRef := #[]
  let mut q := p + 8
  for _ in [0:ncol] do
    let off := (← rd64 d q "block: column offset").toNat
    let sz := (← rd64 d (q + 8) "block: column size").toNat
    if off >= 2 ^ 63 || off + sz > fileSize then throw s!"block at {p}: column frame {off}+{sz} outside the file"
    cols := cols.push ⟨off, sz⟩
    q := q + 16
  let rows := (← rd64 d q "block: numRows").toNat
  let first ← readTriple d (q + 8) "block: firstTriple"
  let last ← readTriple d (q + 40) "block: lastTriple"
  q := q + 72
  if q ≥ d.size then throw "block: graphInfo flag missing"
  let present := d.get! q
  q := q + 1
  let mut graphs : Option (Array Id) := none
  if present == 1 then
    let ng := (← rd64 d q "block: graph count").toNat
    if ng * 8 > d.size - min (q + 8) d.size then throw s!"block at {p}: {ng} graphs exceed the metadata"
    q := q + 8
    let mut gs : Array Id := #[]
    for _ in [0:ng] do
      gs := gs.push ⟨← rd64 d q "block: graph Id"⟩
      q := q + 8
    graphs := some gs
  else if present != 0 then throw s!"block at {p}: graphInfo flag {present}"
  if q ≥ d.size then throw "block: duplicates flag missing"
  let dup := d.get! q != 0
  let idx := (← rd64 d (q + 1) "block: blockIndex").toNat
  pure ({ cols, rows, first, last, graphs, dupGraphs := dup, index := idx }, q + 9)

/-- Parse the `IndexMetaData` serialization. `d` holds bytes
    `[start, fileSize - 8)` of the permutation file. -/
def parsePermMeta (d : ByteArray) (fileSize : Nat) : Except String PermMeta := do
  let magic ← rd64 d 0 "metadata: magic"
  if magic != metaMagic then throw s!"metadata: magic {magic}, want {metaMagic}"
  let ver ← rd64 d 8 "metadata: version"
  if ver != metaVersion then throw s!"metadata: version {ver}, want {metaVersion}"
  let nlen := (← rd64 d 16 "metadata: name length").toNat
  if 24 + nlen > d.size then throw "metadata: name exceeds the metadata"
  let name := (String.fromUTF8? (d.extract 24 (24 + nlen))).getD ""
  let mut p := 24 + nlen
  let nb := (← rd64 d p "metadata: block count").toNat
  -- every block record has at least 8 + 8 + 64 + 1 + 1 + 8 = 90 bytes
  if nb * 90 > d.size - min (p + 8) d.size then throw s!"metadata: {nb} blocks exceed the metadata"
  p := p + 8
  let mut blocks : Array BlockMeta := #[]
  for i in [0:nb] do
    let (b, q) ← readBlockMeta d p fileSize
    if b.index != i then throw s!"metadata: block {i} has blockIndex {b.index}"
    if b.first.size != 4 || b.last.size != 4 then throw "metadata: bad triple"
    if i > 0 then
      let prev := blocks[i-1]!
      if (prev.last.getD 0 default).bits > (b.first.getD 0 default).bits then
        throw s!"metadata: block {i} starts before block {i-1} ends (col0)"
    blocks := blocks.push b
    p := q
  let _offsetAfter ← rd64 d p "metadata: offsetAfter"
  let total := (← rd64 d (p + 8) "metadata: totalElements").toNat
  let distinct := (← rd64 d (p + 16) "metadata: numDistinctCol0").toNat
  if p + 24 != d.size then throw s!"metadata: {d.size - (p + 24)} bytes left after the metadata"
  pure { name, blocks, totalElements := total, distinctCol0 := distinct }

/-- The start offset of the metadata from the last 8 bytes of the file. -/
def metaStart (lastEight : ByteArray) (fileSize : Nat) : Except String Nat := do
  let s := (← rd64 lastEight 0 "permutation: trailing offset").toNat
  if s >= 2 ^ 63 || s + 8 > fileSize then throw s!"permutation: metadata start {s} outside the file ({fileSize} bytes)"
  pure s

/-- One entry of a `.meta` file (`CompressedRelationMetadata.h:252-258`). -/
structure Relation where
  col0 : Id
  rows : Nat
  offsetInBlock : UInt64
  deriving Repr, Inhabited

/-- Parse a `.meta` file: 32-byte entries, then the MmapVector trailer. -/
def parseRelations (d : ByteArray) : Except String (Array Relation) := do
  let (n, bytesize) ← parseMmapTrailer d ".meta"
  if bytesize != 32 * n then throw s!".meta: {n} entries but bytesize {bytesize}"
  let mut out : Array Relation := #[]
  for i in [0:n] do
    let p := 32 * i
    out := out.push { col0 := ⟨word64 d p⟩, rows := (word64 d (p + 8)).toNat,
                      offsetInBlock := word64 d (p + 24) }
  pure out

/-- Decompress one column frame: exactly `8 * rows` bytes of Ids. -/
def decodeColumn (frame : ByteArray) (rows : Nat) : Except String ByteArray := do
  let out ← L4Factoidal.Codec.Zstd.decompress frame (8 * rows)
  if out.size != 8 * rows then throw s!"column: {out.size} bytes, want {8 * rows}"
  pure out

/-- Id `i` of a decoded column. -/
@[inline] def colId (c : ByteArray) (i : Nat) : Id := ⟨word64 c (8 * i)⟩

/-- Does the block's col0 range contain `x`? -/
def BlockMeta.covers (b : BlockMeta) (x : Id) : Bool :=
  (b.first.getD 0 default).bits ≤ x.bits && x.bits ≤ (b.last.getD 0 default).bits

end L4Factoidal.Qlvr
