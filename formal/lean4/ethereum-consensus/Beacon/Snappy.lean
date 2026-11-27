/-!
# Raw Snappy block decompression

The official consensus test vectors are stored as raw Snappy blocks
(`*.ssz_snappy`). This is a repository-owned decoder for that container
format, written from the Snappy format description (preamble varint, then
literal and copy elements). It is test-harness support: no consensus rule
depends on it.

Bounds: the output never exceeds the declared length, which is refused above
`maxOutput`; the element loop runs at most once per input byte.
-/

namespace Beacon.Snappy

/-- Largest declared output accepted (256 MiB). -/
def maxOutput : Nat := 268435456

/-- Little-endian base-128 varint at `pos`; at most five bytes are read. -/
def readVarint (src : ByteArray) : Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _ => none
  | fuel + 1, pos, shift, acc =>
    if pos < src.size then
      let b := src[pos]!.toNat
      let acc := acc + (b % 128) * 2 ^ shift
      if b < 128 then some (acc, pos + 1) else readVarint src fuel (pos + 1) (shift + 7) acc
    else none

def leAt (src : ByteArray) (pos width : Nat) : Nat :=
  (List.range width).foldl (fun acc i => acc + src[pos + i]!.toNat * 256 ^ i) 0

/-- Append `len` bytes starting `offset` bytes back; ranges may overlap. -/
def copyBack (out : ByteArray) (offset : Nat) : Nat → ByteArray
  | 0 => out
  | len + 1 => copyBack (out.push out[out.size - offset]!) offset len

def decompress (src : ByteArray) : Except String ByteArray := do
  let some (declared, start) := readVarint src 5 0 0 0
    | throw "snappy: bad preamble"
  if declared > maxOutput then throw "snappy: declared length above limit"
  let mut out := ByteArray.emptyWithCapacity declared
  let mut pos := start
  for _ in [0:src.size] do
    if pos ≥ src.size then break
    let tag := src[pos]!.toNat
    let kind := tag % 4
    if kind == 0 then
      let small := tag / 4
      let extra := if small < 60 then 0 else small - 59
      if pos + 1 + extra > src.size then throw "snappy: truncated literal length"
      let len := if small < 60 then small + 1 else leAt src (pos + 1) extra + 1
      let from_ := pos + 1 + extra
      if from_ + len > src.size then throw "snappy: truncated literal"
      if out.size + len > declared then throw "snappy: output longer than declared"
      out := out ++ src.extract from_ (from_ + len)
      pos := from_ + len
    else
      let (len, offset, used) :=
        if kind == 1 then ((tag / 4) % 8 + 4, (tag / 32) * 256 + (if pos + 1 < src.size then src[pos + 1]!.toNat else 0), 2)
        else if kind == 2 then (tag / 4 + 1, (if pos + 2 < src.size then leAt src (pos + 1) 2 else 0), 3)
        else (tag / 4 + 1, (if pos + 4 < src.size then leAt src (pos + 1) 4 else 0), 5)
      if pos + used > src.size then throw "snappy: truncated copy"
      if offset == 0 || offset > out.size then throw "snappy: bad copy offset"
      if out.size + len > declared then throw "snappy: output longer than declared"
      out := copyBack out offset len
      pos := pos + used
  if pos != src.size then throw "snappy: trailing input"
  if out.size != declared then throw "snappy: length mismatch"
  return out

end Beacon.Snappy
