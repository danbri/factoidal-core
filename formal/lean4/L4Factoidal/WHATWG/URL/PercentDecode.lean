/- WHATWG URL §1.3, percent-decoding a byte sequence. This operation does
not require any character encoding tables. -/
namespace L4Factoidal.WHATWG.URL

/-- The value of an ASCII hex digit byte, or `none`. -/
def hexValue? (b : UInt8) : Option Nat :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b.toNat - 0x30)
  else if 0x41 ≤ b && b ≤ 0x46 then some (b.toNat - 0x41 + 10)
  else if 0x61 ≤ b && b ≤ 0x66 then some (b.toNat - 0x61 + 10)
  else none

/-- percent-decode a byte sequence (section 1.3): `%` followed by two ASCII
hex digits is the byte they name; every other byte is itself. -/
def percentDecode (input : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut i := 0
  for _ in [0:input.size] do
    if h : i < input.size then
      let b := input[i]
      match (if b == 0x25 then (input[i + 1]?.bind hexValue?, input[i + 2]?.bind hexValue?)
             else (none, none)) with
      | (some hi, some lo) =>
        out := out.push (hi * 16 + lo).toUInt8
        i := i + 3
      | _ =>
        out := out.push b
        i := i + 1
  return out

end L4Factoidal.WHATWG.URL
