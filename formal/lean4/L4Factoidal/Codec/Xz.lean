/-
L4Factoidal.Codec.Xz — the xz file format: read a stream (or several), and
write one.

Spec: "The .xz File Format", Lasse Collin, version 1.0.4 (2009-08-27):
section 2 (container: stream header, blocks, index, stream footer), 3
(block header), 4 (index), 5.3.1 (LZMA2 filter), and the check types of
section 3.1.1. The LZMA2 data itself is `Codec.Lzma`.

## What is read

* any number of concatenated streams, with stream padding (zero words)
  between them;
* any number of blocks per stream, each with the LZMA2 filter alone (the
  filter chain of the files `xz` writes by default). A block that names
  another filter (BCJ, delta) is `unsupported`, because this module does
  not have it;
* the checks `none`, CRC32, CRC64 and SHA-256, each verified over the
  block's uncompressed data. A reserved check type is `unsupported`;
* the index, whose records must say what the blocks were, and the footer,
  whose backward size and flags must say what the index and header were.

Every CRC in the container is checked, and so are the zero padding bytes.

## What is written

`xz` writes one block of LZMA2 chunks that are all uncompressed (control
bytes 1 and 2, at most 65536 bytes each), with a CRC64 check. The output is
a valid stream that any xz reader reads back to the input; it is not
smaller than the input. Writing a compressing LZMA2 encoder is a separate
piece of work, and nothing here needs it: an RML-IO target compressed as
`rml:tarxz` is read back by `unxz`.
-/
import L4Factoidal.Codec.Crc32
import L4Factoidal.Codec.Lzma
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Codec

/-! ## CRC-64 -/

/-- One table entry of CRC-64/XZ (ECMA-182, reflected polynomial
    0xC96C5795D7870F42). -/
def crc64Entry (n : Nat) : UInt64 := Id.run do
  let mut c : UInt64 := UInt64.ofNat n
  for _ in [0:8] do
    c := if c &&& 1 == 1 then (0xC96C5795D7870F42 : UInt64) ^^^ (c >>> (1 : UInt64)) else c >>> (1 : UInt64)
  return c

def crc64Table : Array UInt64 := (Array.range 256).map crc64Entry

/-- The CRC-64/XZ of a byte array: initial value and final XOR all ones. -/
def crc64 (b : ByteArray) : UInt64 := Id.run do
  let mut c : UInt64 := (0xFFFFFFFFFFFFFFFF : UInt64)
  for x in b.toList do
    c := crc64Table[((c ^^^ x.toUInt64) &&& 0xFF).toNat]! ^^^ (c >>> (8 : UInt64))
  return c ^^^ (0xFFFFFFFFFFFFFFFF : UInt64)

-- The standard check value: CRC-64/XZ("123456789") = 0x995DC9BBDF1939FA.
#guard crc64 "123456789".toUTF8 == 0x995DC9BBDF1939FA
#guard crc64 ByteArray.empty == 0
#guard crc64 "123456789".toUTF8 != crc64 "123456780".toUTF8

/-! ## Errors -/

/-- A file this module cannot read because it has no code for a feature of
    the format, or because the file is not a valid xz file. -/
inductive XzError where
  | unsupported (what : String)
  | corrupt (msg : String)

private def corrupt {α : Type} (m : String) : Except XzError α := .error (.corrupt m)

private def lift {α : Type} (r : Except String α) : Except XzError α :=
  match r with
  | .ok a => .ok a
  | .error m => .error (.corrupt m)

/-! ## Reading -/

private def u8 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat

private def le32At (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| ((b.get! (i + 1)).toUInt32 <<< (8 : UInt32)) |||
  ((b.get! (i + 2)).toUInt32 <<< (16 : UInt32)) ||| ((b.get! (i + 3)).toUInt32 <<< (24 : UInt32))

private def le64At (b : ByteArray) (i : Nat) : UInt64 :=
  (le32At b i).toUInt64 ||| ((le32At b (i + 4)).toUInt64 <<< (32 : UInt64))

/-- A "multibyte integer" (section 1.2): seven bits per byte, low group
    first, the top bit set on every byte but the last, at most nine bytes.
    The value and the index after it. -/
private def varint (b : ByteArray) (i : Nat) : Option (Nat × Nat) := Id.run do
  let mut v : Nat := 0
  let mut j := i
  for k in [0:9] do
    if j ≥ b.size then return none
    let x := u8 b j
    v := v + ((x &&& 0x7F) <<< (7 * k))
    j := j + 1
    if x &&& 0x80 == 0 then
      -- the last byte of a multibyte integer is not zero unless it is the only one
      if x == 0 && k > 0 then return none
      return some (v, j)
  return none

private def allZero (b : ByteArray) (i n : Nat) : Bool :=
  (List.range n).all (fun k => b.get! (i + k) == 0)

/-- The size of the check field for a check type. -/
private def checkSize (t : Nat) : Except XzError Nat :=
  if t == 0 then .ok 0
  else if t == 1 then .ok 4
  else if t == 4 then .ok 8
  else if t == 10 then .ok 32
  else .error (.unsupported s!"the xz check type {t}")

/-- Check a block's uncompressed data against its check field. -/
private def verifyCheck (t : Nat) (check : ByteArray) (data : ByteArray) : Except XzError Unit :=
  if t == 0 then .ok ()
  else if t == 1 then
    if le32At check 0 == crc32 data then .ok () else corrupt "a block's CRC32 does not match its data"
  else if t == 4 then
    if le64At check 0 == crc64 data then .ok () else corrupt "a block's CRC64 does not match its data"
  else
    if check == L4Factoidal.Crypto.sha256 data then .ok ()
    else corrupt "a block's SHA-256 does not match its data"

/-- One block at `p`: its uncompressed data, the unpadded size (header,
    compressed data and check) for the index, and the index after it. -/
private def readBlock (b : ByteArray) (p checkType : Nat)
    : Except XzError (ByteArray × Nat × Nat) := do
  let hsize := (u8 b p + 1) * 4
  if p + hsize > b.size then corrupt "a block header is truncated"
  if le32At b (p + hsize - 4) != crc32 (b.extract p (p + hsize - 4)) then
    corrupt "a block header's CRC32 does not match"
  let flags := u8 b (p + 1)
  if flags &&& 0x3C != 0 then corrupt "a block header sets reserved flag bits"
  let nFilters := (flags &&& 3) + 1
  let mut q := p + 2
  let mut compField : Option Nat := none
  let mut uncField : Option Nat := none
  if flags &&& 0x40 != 0 then
    match varint b q with
    | some (v, j) => compField := some v; q := j
    | none => corrupt "a block header's compressed size is not a valid integer"
  if flags &&& 0x80 != 0 then
    match varint b q with
    | some (v, j) => uncField := some v; q := j
    | none => corrupt "a block header's uncompressed size is not a valid integer"
  if nFilters != 1 then .error (.unsupported "an xz block with a filter chain of several filters")
  let some (fid, q1) := varint b q | corrupt "a filter ID is not a valid integer"
  let some (psize, q2) := varint b q1 | corrupt "a filter's property size is not a valid integer"
  if fid != 0x21 then .error (.unsupported s!"the xz filter {fid}")
  if psize != 1 || q2 + 1 > p + hsize - 4 then corrupt "the LZMA2 filter has the wrong property size"
  if u8 b q2 > 40 then corrupt "the LZMA2 dictionary size is out of range"
  let q3 := q2 + 1
  if !allZero b q3 (p + hsize - 4 - q3) then corrupt "a block header's padding is not zero"
  let dataStart := p + hsize
  let (data, dataEnd) ← lift (Lzma.lzma2Decode b dataStart)
  let compSize := dataEnd - dataStart
  if compField.any (· != compSize) then corrupt "a block's compressed size is not what its header says"
  if uncField.any (· != data.size) then corrupt "a block's uncompressed size is not what its header says"
  let pad := (4 - (hsize + compSize) % 4) % 4
  if dataEnd + pad > b.size then corrupt "a block is truncated"
  if !allZero b dataEnd pad then corrupt "a block's padding is not zero"
  let cs ← checkSize checkType
  let checkStart := dataEnd + pad
  if checkStart + cs > b.size then corrupt "a block's check is truncated"
  verifyCheck checkType (b.extract checkStart (checkStart + cs)) data
  return (data, hsize + compSize + cs, checkStart + cs)

/-- One stream at `pos`: its data and the index after its footer. -/
private def readStream (b : ByteArray) (pos : Nat) : Except XzError (ByteArray × Nat) := do
  if pos + 12 > b.size then corrupt "an xz stream header is truncated"
  if b.extract pos (pos + 6) != ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] then
    corrupt "this is not an xz stream (the magic bytes are wrong)"
  if u8 b (pos + 6) != 0 || u8 b (pos + 7) &&& 0xF0 != 0 then
    corrupt "the xz stream flags set reserved bits"
  let checkType := u8 b (pos + 7) &&& 0x0F
  if le32At b (pos + 8) != crc32 (b.extract (pos + 6) (pos + 8)) then
    corrupt "the xz stream header's CRC32 does not match"
  let mut p := pos + 12
  let mut out := ByteArray.empty
  let mut records : List (Nat × Nat) := []
  let mut sawIndex := false
  for _ in [0:b.size + 1] do
    if sawIndex then break
    if p ≥ b.size then corrupt "an xz stream has no index"
    if u8 b p == 0 then sawIndex := true
    else
      let (data, unpadded, next) ← readBlock b p checkType
      out := out ++ data
      records := records ++ [(unpadded, data.size)]
      p := next
  -- the index
  let indexStart := p
  let some (count, q0) := varint b (p + 1) | corrupt "the xz index's record count is not a valid integer"
  if count != records.length then corrupt "the xz index counts other blocks than the stream has"
  let mut q := q0
  for (unpadded, unc) in records do
    let some (u, q1) := varint b q | corrupt "an xz index record is not a valid integer"
    let some (v, q2) := varint b q1 | corrupt "an xz index record is not a valid integer"
    if u != unpadded || v != unc then corrupt "an xz index record does not match its block"
    q := q2
  let pad := (4 - (q - indexStart) % 4) % 4
  if q + pad + 4 > b.size then corrupt "the xz index is truncated"
  if !allZero b q pad then corrupt "the xz index's padding is not zero"
  let indexEnd := q + pad
  if le32At b indexEnd != crc32 (b.extract indexStart indexEnd) then
    corrupt "the xz index's CRC32 does not match"
  -- the footer
  let f := indexEnd + 4
  if f + 12 > b.size then corrupt "the xz stream footer is truncated"
  if le32At b f != crc32 (b.extract (f + 4) (f + 10)) then
    corrupt "the xz stream footer's CRC32 does not match"
  if (le32At b (f + 4)).toNat != (indexEnd + 4 - indexStart) / 4 - 1 then
    corrupt "the xz stream footer's backward size is not the size of the index"
  if b.extract (f + 8) (f + 10) != b.extract (pos + 6) (pos + 8) then
    corrupt "the xz stream footer's flags differ from the header's"
  if b.extract (f + 10) (f + 12) != ByteArray.mk #[0x59, 0x5A] then
    corrupt "the xz stream footer's magic bytes are wrong"
  return (out, f + 12)

/-- Read an xz file: its streams one after the other, with zero padding
    (a multiple of four bytes) allowed between them and after the last. -/
def unxz (b : ByteArray) : Except XzError ByteArray := do
  if b.isEmpty then corrupt "an empty file is not an xz file"
  let mut pos := 0
  let mut out := ByteArray.empty
  let mut streams := 0
  for _ in [0:b.size + 1] do
    if pos ≥ b.size then break
    if pos + 4 ≤ b.size && allZero b pos 4 && streams > 0 then pos := pos + 4
    else
      let (d, next) ← readStream b pos
      out := out ++ d
      pos := next
      streams := streams + 1
  return out

/-! ## Writing -/

private def le32 (n : UInt32) : ByteArray :=
  ByteArray.mk #[n.toUInt8, (n >>> (8 : UInt32)).toUInt8, (n >>> (16 : UInt32)).toUInt8,
                 (n >>> (24 : UInt32)).toUInt8]

private def le64 (n : UInt64) : ByteArray :=
  le32 n.toUInt32 ++ le32 (n >>> (32 : UInt64)).toUInt32

private def varintBytes (n : Nat) : ByteArray := Id.run do
  let mut v := n
  let mut out := ByteArray.empty
  for _ in [0:9] do
    if v < 0x80 then
      return out.push v.toUInt8
    out := out.push (v % 128 + 128).toUInt8
    v := v / 128
  return out

/-- LZMA2 data of uncompressed chunks of at most 65536 bytes. -/
private def lzma2Stored (data : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut i := 0
  let mut first := true
  for _ in [0:data.size + 1] do
    if i ≥ data.size then break
    let n := min 65536 (data.size - i)
    out := out.push (if first then 1 else 2)
    out := out.push ((n - 1) / 256).toUInt8
    out := out.push ((n - 1) % 256).toUInt8
    out := out ++ data.extract i (i + n)
    i := i + n
    first := false
  return out.push 0

/-- An xz stream holding `data` in one block of uncompressed LZMA2 chunks,
    with a CRC64 check; no block at all for empty data. -/
def xz (data : ByteArray) : ByteArray :=
  let flags := ByteArray.mk #[0, 4]
  let header := ByteArray.mk #[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00] ++ flags ++ le32 (crc32 flags)
  let blockHeaderBody := ByteArray.mk #[2, 0, 0x21, 1, 0, 0, 0, 0]
  let blockHeader := blockHeaderBody ++ le32 (crc32 blockHeaderBody)
  let lz := lzma2Stored data
  let pad := ByteArray.mk (Array.replicate ((4 - (blockHeader.size + lz.size) % 4) % 4) 0)
  let block := blockHeader ++ lz ++ pad ++ le64 (crc64 data)
  let unpadded := blockHeader.size + lz.size + 8
  let records :=
    if data.isEmpty then ByteArray.empty else varintBytes unpadded ++ varintBytes data.size
  let indexBody := ByteArray.mk #[0] ++ varintBytes (if data.isEmpty then 0 else 1) ++ records
  let indexPad := ByteArray.mk (Array.replicate ((4 - indexBody.size % 4) % 4) 0)
  let index := (indexBody ++ indexPad)
  let index := index ++ le32 (crc32 index)
  let footerBody := le32 (UInt32.ofNat (index.size / 4 - 1)) ++ flags
  let footer := le32 (crc32 footerBody) ++ footerBody ++ ByteArray.mk #[0x59, 0x5A]
  header ++ (if data.isEmpty then ByteArray.empty else block) ++ index ++ footer

end L4Factoidal.Codec
