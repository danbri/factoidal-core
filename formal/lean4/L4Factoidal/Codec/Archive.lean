/-
L4Factoidal.Codec.Archive — gzip (RFC 1952), zip (PKWARE APPNOTE) and
tar (POSIX ustar), enough to read the single document an RML source is
compressed into, and to write one.

## Scope

* gzip: one member; header flags FEXTRA, FNAME, FCOMMENT and FHCRC are
  skipped; the CRC-32 and the length in the trailer are checked.
* zip: the first entry of the central directory; stored (0) and deflated
  (8) entries; the CRC-32 and sizes are checked. The central directory is
  read, not the local headers alone, because a writer that streams puts
  the sizes in a data descriptor after the data.
* tar: the first regular file; pax extended headers (`x`, `g`) are
  skipped; the header checksum is checked.

A format outside these (a second compression method, a multi-volume zip,
a sparse tar entry) is an error with a message.

The writers emit what the readers read and what other tools accept:
`gzip` and `zipSingle` wrap the stored-block DEFLATE of `Inflate`, and
`tarSingle` is a plain ustar archive with its two zero blocks.
-/
import L4Factoidal.Codec.Inflate

namespace L4Factoidal.Codec

private def u16 (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat + 256 * (b.get! (i + 1)).toNat

private def u32 (b : ByteArray) (i : Nat) : Nat :=
  u16 b i + 65536 * u16 b (i + 2)

private def le16 (n : Nat) : ByteArray := ByteArray.mk #[(n % 256).toUInt8, (n / 256 % 256).toUInt8]
private def le32 (n : Nat) : ByteArray := le16 (n % 65536) ++ le16 (n / 65536 % 65536)

private def have' (b : ByteArray) (i n : Nat) : Bool := i + n ≤ b.size

/-! ## gzip -/

/-- Skip a zero-terminated string starting at `i`; the index after it. -/
private def skipZ (b : ByteArray) (i : Nat) : Option Nat := Id.run do
  let mut j := i
  for _ in [0:b.size] do
    if j ≥ b.size then return none
    if b.get! j == 0 then return some (j + 1)
    j := j + 1
  return none

def gunzip (b : ByteArray) : Except String ByteArray := do
  if b.size < 18 then throw "too short to be a gzip file"
  if b.get! 0 != 0x1f || b.get! 1 != 0x8b then throw "not a gzip file (bad magic)"
  if b.get! 2 != 8 then throw "gzip compression method is not deflate"
  let flg := (b.get! 3).toNat
  let mut i := 10
  if flg &&& 4 != 0 then
    if !have' b i 2 then throw "truncated gzip header"
    i := i + 2 + u16 b i
  if flg &&& 8 != 0 then
    match skipZ b i with
    | some j => i := j
    | none => throw "unterminated gzip file name"
  if flg &&& 16 != 0 then
    match skipZ b i with
    | some j => i := j
    | none => throw "unterminated gzip comment"
  if flg &&& 2 != 0 then i := i + 2
  let (out, endAt) ← inflateAt b i
  if !have' b endAt 8 then throw "truncated gzip trailer"
  if u32 b endAt != (crc32 out).toNat then throw "gzip CRC-32 mismatch"
  if u32 b (endAt + 4) != out.size % 4294967296 then throw "gzip length mismatch"
  pure out

/-- A gzip file with stored blocks. -/
def gzip (b : ByteArray) : ByteArray :=
  ByteArray.mk #[0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 0xff] ++ deflateStored b ++
    le32 (crc32 b).toNat ++ le32 (b.size % 4294967296)

/-! ## zip -/

private def findEocd (b : ByteArray) : Option Nat := Id.run do
  if b.size < 22 then return none
  let mut i := b.size - 22
  for _ in [0:min (b.size - 21) 65558] do
    if u32 b i == 0x06054b50 then return some i
    if i == 0 then return none
    i := i - 1
  return none

/-- The first entry of a zip archive: its name and its bytes. -/
def unzipFirst (b : ByteArray) : Except String (String × ByteArray) := do
  let eocd ← match findEocd b with
    | some i => pure i
    | none => throw "not a zip archive (no end of central directory)"
  if u16 b (eocd + 10) == 0 then throw "the zip archive has no entries"
  let cd := u32 b (eocd + 16)
  if !have' b cd 46 || u32 b cd != 0x02014b50 then throw "bad zip central directory"
  let method := u16 b (cd + 10)
  let crc := u32 b (cd + 16)
  let csize := u32 b (cd + 20)
  let usize := u32 b (cd + 24)
  let nlen := u16 b (cd + 28)
  let loc := u32 b (cd + 42)
  if !have' b (cd + 46) nlen then throw "truncated zip central directory"
  let name := String.fromUTF8! (b.extract (cd + 46) (cd + 46 + nlen))
  if !have' b loc 30 || u32 b loc != 0x04034b50 then throw "bad zip local header"
  let start := loc + 30 + u16 b (loc + 26) + u16 b (loc + 28)
  if !have' b start csize then throw "zip entry runs past the end of the file"
  let raw := b.extract start (start + csize)
  let data ← match method with
    | 0 => pure raw
    | 8 => inflate raw
    | m => throw s!"zip compression method {m} is not supported"
  if data.size != usize then throw "zip entry size mismatch"
  if (crc32 data).toNat != crc then throw "zip CRC-32 mismatch"
  pure (name, data)

/-- A zip archive of one deflated (stored-block) entry. -/
def zipSingle (name : String) (data : ByteArray) : ByteArray :=
  let nameB := name.toUTF8
  let comp := deflateStored data
  let crc := (crc32 data).toNat
  let local' := le32 0x04034b50 ++ le16 20 ++ le16 0 ++ le16 8 ++ le16 0 ++ le16 33 ++
    le32 crc ++ le32 comp.size ++ le32 data.size ++ le16 nameB.size ++ le16 0 ++ nameB ++ comp
  let cdir := le32 0x02014b50 ++ le16 20 ++ le16 20 ++ le16 0 ++ le16 8 ++ le16 0 ++ le16 33 ++
    le32 crc ++ le32 comp.size ++ le32 data.size ++ le16 nameB.size ++ le16 0 ++ le16 0 ++
    le16 0 ++ le16 0 ++ le32 0 ++ le32 0 ++ nameB
  local' ++ cdir ++
    le32 0x06054b50 ++ le16 0 ++ le16 0 ++ le16 1 ++ le16 1 ++ le32 cdir.size ++ le32 local'.size ++ le16 0

/-! ## tar -/

private def tarString (b : ByteArray) (i n : Nat) : String :=
  let bs := (b.extract i (i + n)).toList.takeWhile (· != 0)
  String.fromUTF8! (ByteArray.mk bs.toArray)

private def octal (b : ByteArray) (i n : Nat) : Option Nat :=
  let ds := (b.extract i (i + n)).toList.filter (fun c => c != 0 && c != 32)
  ds.foldl (fun acc c => acc.bind (fun a =>
    if 48 ≤ c.toNat && c.toNat ≤ 55 then some (a * 8 + (c.toNat - 48)) else none)) (some 0)

private def tarChecksum (b : ByteArray) (at' : Nat) : Nat :=
  ((List.range 512).map (fun i =>
    if 148 ≤ i && i < 156 then 32 else (b.get! (at' + i)).toNat)).foldl (· + ·) 0

/-- The first regular file of a tar archive: its name and bytes. -/
def untarFirst (b : ByteArray) : Except String (String × ByteArray) := do
  let mut i := 0
  for _ in [0:b.size / 512 + 1] do
    if !have' b i 512 then throw "no regular file in the tar archive"
    if (b.extract i (i + 512)).toList.all (· == 0) then throw "no regular file in the tar archive"
    let size ← match octal b (i + 124) 12 with
      | some s => pure s
      | none => throw "bad tar entry size"
    let stored ← match octal b (i + 148) 8 with
      | some s => pure s
      | none => throw "bad tar checksum field"
    if stored != tarChecksum b i then throw "tar header checksum mismatch"
    let typ := b.get! (i + 156)
    let dataAt := i + 512
    if !have' b dataAt size then throw "tar entry runs past the end of the file"
    if typ == 0 || typ == 48 then
      return (tarString b i 100, b.extract dataAt (dataAt + size))
    i := dataAt + (size + 511) / 512 * 512
  throw "no regular file in the tar archive"

private def octalField (n digits : Nat) : ByteArray :=
  let s := (Nat.toDigits 8 n)
  let padded := List.replicate (digits - s.length) '0' ++ s
  ByteArray.mk ((padded.map (fun c => c.toNat.toUInt8)).toArray) |>.push 0

/-- A ustar archive of one file. -/
def tarSingle (name : String) (data : ByteArray) : ByteArray := Id.run do
  let nameB := name.toUTF8
  let mut h := ByteArray.mk (Array.replicate 512 0)
  let put (h : ByteArray) (at' : Nat) (v : ByteArray) : ByteArray := Id.run do
    let mut h := h
    for j in [0:v.size] do h := h.set! (at' + j) (v.get! j)
    pure h
  h := put h 0 (nameB.extract 0 (min 100 nameB.size))
  h := put h 100 (octalField 0o644 7)
  h := put h 108 (octalField 0 7)
  h := put h 116 (octalField 0 7)
  h := put h 124 (octalField data.size 11)
  h := put h 136 (octalField 0 11)
  h := put h 148 (ByteArray.mk #[32, 32, 32, 32, 32, 32, 32, 32])
  h := h.set! 156 48
  h := put h 257 (ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0, 0x30, 0x30])
  let sum := tarChecksum h 0
  h := put h 148 (octalField sum 6 |>.push 32)
  let pad := (512 - data.size % 512) % 512
  pure (h ++ data ++ ByteArray.mk (Array.replicate (pad + 1024) 0))

/-! ## Build-time checks

The gzip, zip and tar vectors were written by `gzip`, `zip` and `tar` on
the text "hello gzip\n" and are checked here byte for byte. -/

private def bytes (xs : List Nat) : ByteArray := ByteArray.mk (xs.map UInt8.ofNat).toArray

private def sample : ByteArray := "hello gzip\n".toUTF8


private def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - 48 else c.toNat - 87

private def ofHex (s : String) : ByteArray :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (hexVal a * 16 + hexVal b) :: go rest
    | _ => []
  ByteArray.mk (go s.toList).toArray

-- Archives written by the real `gzip -9 -n`, `zip -X` and `tar --format=ustar`.
private def realGz : ByteArray := ofHex "1f8b0800000000000203cb48cdc9c95748afca2ce00200397c63560b000000"
private def realZip : ByteArray := ofHex "504b03040a000000000072154a5d397c63560b0000000b00000005000000612e74787468656c6c6f20677a69700a504b01021e030a000000000072154a5d397c63560b0000000b000000050000000000000001000000a48100000000612e747874504b05060000000001000100330000002e0000000000"
private def realTar : ByteArray := ofHex "612e7478740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000303030303634340030303030303030003030303030303000303030303030303030313300313532363233323331333000303130353634002030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007573746172003030726f6f7400000000000000000000000000000000000000000000000000000000726f6f740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068656c6c6f20677a69700a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"

#guard (gunzip realGz).toOption == some sample
#guard (unzipFirst realZip).toOption == some ("a.txt", sample)
#guard (untarFirst realTar).toOption == some ("a.txt", sample)

-- The writers, read back by the readers.
#guard (gunzip (gzip sample)).toOption == some sample
#guard (gunzip (gzip ByteArray.empty)).toOption == some ByteArray.empty
#guard (unzipFirst (zipSingle "a.txt" sample)).toOption == some ("a.txt", sample)
#guard (untarFirst (tarSingle "a.txt" sample)).toOption == some ("a.txt", sample)
-- Corruption is an error: a flipped payload byte fails the checksum.
#guard (gunzip ((gzip sample).set! 15 0x00)).toOption.isNone
#guard (unzipFirst ((zipSingle "a.txt" sample).set! 36 0x00)).toOption.isNone
#guard (untarFirst ((tarSingle "a.txt" sample).set! 1 0x00)).toOption.isNone
-- Not archives at all.
#guard (gunzip sample).toOption.isNone
#guard (unzipFirst sample).toOption.isNone
#guard (untarFirst sample).toOption.isNone
#guard (untarFirst ByteArray.empty).toOption.isNone
-- A tar with only the end-of-archive blocks has no file.
#guard (untarFirst (ByteArray.mk (Array.replicate 1024 0))).toOption.isNone

end L4Factoidal.Codec
