/- Shared ASCII hexadecimal digit decoding.
   RFC 3986 §2.1 HEXDIG, RFC 8259 §7, XSD 1.1 Part 2 §3.3.15.
   This primitive knows nothing about escaping, Unicode scalar validity,
   percent encoding, whitespace, padding or canonical output case.
   Those are consumer policies. No imports or additional trust assumptions. -/
namespace L4Factoidal.Encoding.Hex

/-- Both ASCII cases are accepted; every other character is rejected.
    Zero is a valid digit, so failure has its own `Option` constructor. -/
def digitValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

end L4Factoidal.Encoding.Hex
