import L4Factoidal.Codec.Inflate

/-!
# WOFF 1.0 to sfnt

WOFF File Format 1.0 (W3C Recommendation, 2012): an sfnt font (TrueType or CFF-flavoured
OpenType) whose tables are each compressed with zlib, behind a 44-byte header and a table
directory of 20 bytes for each table. `toSfnt` gives back the sfnt that the font reader
(`SfntProfile.Font.read`, with the font safety policy) reads: its offset table, its table
records sorted by tag as the WOFF directory has them, and each table at a four-byte
boundary. WOFF 1.0 is still a common web font format; a face offered only as WOFF 1.0 was
not read before. WOFF2 (Brotli and transformed tables) is read by `Woff2.toSfnt`.

Font bytes are hostile input. Every size is checked against the input and against
`maxSfntBytes` before anything is made; each table is inflated to exactly the length the
directory gives (`Codec.inflateAt` stops at that limit); a table that is larger compressed
than whole, or that runs past the file, is a refusal. Metadata and private data are left out:
the sfnt has no place for them.
-/
namespace L4Factoidal.Rendering.Woff

/-- The largest sfnt made from a WOFF file: 16 MiB (a web font with every CJK glyph is
about 10 MiB). -/
def maxSfntBytes : Nat := 16777216

/-- The most tables of a WOFF file (an sfnt has about 20). -/
def maxTables : Nat := 256

/-- The first four bytes of a WOFF 1.0 file: `wOFF`. -/
def isWoff (b : ByteArray) : Bool :=
  b.size ≥ 4 && b.get! 0 == 0x77 && b.get! 1 == 0x4F && b.get! 2 == 0x46 && b.get! 3 == 0x46

private def u16 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat*256+(b.get! (i+1)).toNat
private def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i*65536+u16 b (i+2)

private def push16 (out : ByteArray) (v : Nat) : ByteArray :=
  (out.push (v/256%256).toUInt8).push (v%256).toUInt8
private def push32 (out : ByteArray) (v : Nat) : ByteArray :=
  push16 (push16 out (v/65536%65536)) (v%65536)

/-- One entry of the table directory. -/
structure Entry where
  tag : Nat
  offset : Nat
  compLength : Nat
  origLength : Nat
  checksum : Nat

/-- The largest power of two not above `n` (at least 1), and its exponent: the search fields
of an sfnt offset table (OpenType, "Table directory"). -/
def searchPower (n : Nat) : Nat × Nat := Id.run do
  let mut p := 1
  let mut e := 0
  for _ in [0:16] do
    if p*2 ≤ n then
      p := p*2
      e := e+1
  return (p,e)

/-- Padding to the next multiple of four. -/
def pad4 (n : Nat) : Nat := (n+3)/4*4

theorem pad4_ge (n : Nat) : n ≤ pad4 n := by unfold pad4; omega
theorem pad4_mod (n : Nat) : pad4 n % 4 = 0 := by unfold pad4; omega

/-- The table's bytes: stored, or inflated from zlib to exactly `origLength`. -/
def tableData (b : ByteArray) (e : Entry) : Except String ByteArray := do
  if e.offset+e.compLength > b.size then throw "WOFF table runs past the end of the file"
  if e.compLength > e.origLength then throw "WOFF table is larger compressed than whole"
  let raw := b.extract e.offset (e.offset+e.compLength)
  if e.compLength == e.origLength then return raw
  -- RFC 1950: a two-byte zlib header, deflate data, an Adler-32 that is not checked here
  -- (the sfnt's own checksums are not checked by the reader either).
  if raw.size < 2 then throw "WOFF table has no zlib header"
  let cmf := (raw.get! 0).toNat
  let flg := (raw.get! 1).toNat
  if cmf%16 != 8 || (cmf*256+flg)%31 != 0 || flg &&& 32 != 0 then throw "WOFF table zlib header is not valid"
  let (out,_) ← Codec.inflateAt raw 2 e.origLength
  if out.size != e.origLength then throw "WOFF table inflates to another length than its directory gives"
  return out

/-- The sfnt of a WOFF 1.0 file. -/
def toSfnt (b : ByteArray) : Except String ByteArray := do
  if b.size < 44 || !isWoff b then throw "not a WOFF 1.0 file"
  let flavor := u32 b 4
  let numTables := u16 b 12
  if numTables == 0 || numTables > maxTables then throw "WOFF table count is not valid"
  if 44+numTables*20 > b.size then throw "WOFF table directory runs past the end of the file"
  let mut entries : Array Entry := #[]
  let mut total := 12+16*numTables
  for i in [0:numTables] do
    let at_ := 44+i*20
    let e : Entry := ⟨u32 b at_,u32 b (at_+4),u32 b (at_+8),u32 b (at_+12),u32 b (at_+16)⟩
    if let some last := entries.back? then
      if e.tag ≤ last.tag then throw "WOFF table directory is not sorted by tag"
    total := total+pad4 e.origLength
    if total > maxSfntBytes then throw s!"WOFF font exceeds {maxSfntBytes} bytes"
    entries := entries.push e
  -- The offset table and the table records.
  let (power,exponent) := searchPower numTables
  let mut out := ByteArray.emptyWithCapacity total
  out := push32 out flavor
  out := push16 out numTables
  out := push16 out (power*16)
  out := push16 out exponent
  out := push16 out (numTables*16-power*16)
  let mut offset := 12+16*numTables
  for e in entries do
    out := push32 (push32 (push32 (push32 out e.tag) e.checksum) offset) e.origLength
    offset := offset+pad4 e.origLength
  -- The tables, each at a four-byte boundary.
  for e in entries do
    let data ← tableData b e
    out := out ++ data
    for _ in [0:pad4 data.size-data.size] do out := out.push 0
  if out.size != total then throw "WOFF font: the sfnt made has another size than its tables give"
  return out

/-- Bytes as the font reader takes them: a WOFF 1.0 file as its sfnt, anything else as it is. -/
def sfntOf (b : ByteArray) : Except String ByteArray :=
  if isWoff b then toSfnt b else .ok b

/-- Bytes that are not WOFF pass through unchanged. -/
theorem sfntOf_other (b : ByteArray) (h : isWoff b = false) : sfntOf b = .ok b := by
  simp [sfntOf, h]

-- The search fields: a power of two not above the count (for a count of at least 1).
#guard searchPower 1 == (1,0) && searchPower 2 == (2,1) && searchPower 13 == (8,3) && searchPower 16 == (16,4)
#guard pad4 0 == 0 && pad4 1 == 4 && pad4 4 == 4 && pad4 5 == 8

/-! Checks on small files made here: a stored table and a compressed one round-trip. -/
private def woffOf (flavor : Nat) (tables : List (Nat × ByteArray × ByteArray)) : ByteArray := Id.run do
  -- tables: tag, the whole table, the bytes stored in the file (whole or zlib)
  let n := tables.length
  let mut offset := 44+20*n
  let mut dir := ByteArray.empty
  let mut body := ByteArray.empty
  for (tag,whole,stored) in tables do
    dir := push32 (push32 (push32 (push32 (push32 dir tag) offset) stored.size) whole.size) 0
    body := body ++ stored
    for _ in [0:pad4 stored.size-stored.size] do body := body.push 0
    offset := offset+pad4 stored.size
  -- signature, flavour, length, table count, reserved, sfnt size, major and minor version
  let head := push32 (push32 (push16 (push16 (push32 (push32 (push32 ByteArray.empty 0x774F4646) flavor) offset) n) 0) 0) 0
  -- version, metadata and private fields: zero
  let head := push32 (push32 (push32 (push32 (push32 head 0) 0) 0) 0) 0
  return head ++ dir ++ body
-- "abc" twenty times as a zlib stream (14 bytes, made with zlib level 9).
private def abc60 : ByteArray := ByteArray.mk #[120,218,75,76,74,78,36,23,1,0,188,190,22,249]
private def abc60Whole : ByteArray := (String.join (List.replicate 20 "abc")).toUTF8
private def sample : ByteArray := woffOf 0x00010000
  [(0x636D6170,"abc".toUTF8,"abc".toUTF8),(0x676C7966,abc60Whole,abc60)]
#guard isWoff sample && (woffOf 0 []).size == 44
#guard match toSfnt sample with
  | .ok s => s.size == 12+32+4+60 && u32 s 0 == 0x00010000 && u16 s 4 == 2 && u32 s 12 == 0x636D6170 &&
      u32 s 20 == 44 && u32 s 24 == 3 && u32 s 36 == 48 && u32 s 40 == 60 &&
      (s.extract 44 47).toList == "abc".toUTF8.toList && s.get! 47 == 0 && (s.extract 48 108).toList == abc60Whole.toList
  | .error _ => false
-- Hostile input: unsorted tags, a table past the end, a table larger compressed, no tables.
#guard (toSfnt (woffOf 0 [(2,"a".toUTF8,"a".toUTF8),(1,"b".toUTF8,"b".toUTF8)])).toOption.isNone
#guard (toSfnt ((woffOf 0 [(1,"abcd".toUTF8,"abcd".toUTF8)]).extract 0 66)).toOption.isNone
#guard (toSfnt (woffOf 0 [(1,"ab".toUTF8,"abcd".toUTF8)])).toOption.isNone
-- A compressed table that inflates to another length than its directory says.
#guard (toSfnt (woffOf 0 [(1,(String.join (List.replicate 21 "abc")).toUTF8,abc60)])).toOption.isNone
#guard (toSfnt (woffOf 0 [])).toOption.isNone
#guard (sfntOf "true".toUTF8).toOption.map (·.toList) == some "true".toUTF8.toList

end L4Factoidal.Rendering.Woff
