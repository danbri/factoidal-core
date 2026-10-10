/-
L4Factoidal.Codec.Crc32 — the CRC-32 of ISO 3309, as gzip (RFC 1952
section 8) and zip (APPNOTE 4.4.7) use it: reflected polynomial
0xEDB88320, initial value and final XOR 0xFFFFFFFF.

The table is computed, not typed in, so the only constant is the
polynomial.
-/

namespace L4Factoidal.Codec

/-- One table entry: eight shift-and-xor steps over the byte. -/
def crc32Entry (n : Nat) : UInt32 := Id.run do
  let mut c : UInt32 := UInt32.ofNat n
  for _ in [0:8] do
    c := if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
  return c

def crc32Table : Array UInt32 := (Array.range 256).map crc32Entry

/-- The CRC-32 of a byte array. -/
def crc32 (b : ByteArray) : UInt32 := Id.run do
  let mut c : UInt32 := (0xFFFFFFFF : UInt32)
  for x in b.toList do
    c := crc32Table[((c ^^^ x.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)
  return c ^^^ (0xFFFFFFFF : UInt32)

-- The standard check value: CRC-32("123456789") = 0xCBF43926.
#guard crc32 "123456789".toUTF8 == 0xCBF43926
#guard crc32 ByteArray.empty == 0
#guard crc32 "a".toUTF8 == 0xE8B7BE43
#guard crc32 "123456789".toUTF8 != crc32 "123456780".toUTF8

end L4Factoidal.Codec
