/- Independent finite arithmetic observations from CPython float operations.
   binary64 uses native double operations; binary32 rounds inputs and outputs
   with struct.pack/unpack('>f'). These 62 chosen vectors are observations,
   not a proof of all IEEE rounding cases (particularly double-rounding edges).
   Special-value branches are tested by SPARQL.ArithmeticTests and theorems. -/
import L4Factoidal.Fn.Arithmetic

namespace L4Factoidal.Fn.ArithmeticOracleTests
open XSD Arithmetic

private def vectors : List (Bool × Op × String × String × Nat) := [
  (false, .add, "0.10000000149011612", "0.20000000298023224", 0x3E99999A),
  (false, .add, "1.5", "-2.0", 0xBF000000),
  (false, .add, "1.0", "3.0", 0x40800000),
  (false, .add, "16777216.0", "1.0", 0x4B800000),
  (false, .add, "16777216.0", "3.0", 0x4B800002),
  (false, .add, "0.0", "-0.0", 0x0),
  (false, .add, "1.401298464324817e-45", "2.0", 0x40000000),
  (false, .add, "3.4028234663852886e+38", "2.0", 0x7F7FFFFF),
  (false, .sub, "0.10000000149011612", "0.20000000298023224", 0xBDCCCCCD),
  (false, .sub, "1.5", "-2.0", 0x40600000),
  (false, .sub, "1.0", "3.0", 0xC0000000),
  (false, .sub, "16777216.0", "1.0", 0x4B7FFFFF),
  (false, .sub, "16777216.0", "3.0", 0x4B7FFFFD),
  (false, .sub, "0.0", "-0.0", 0x0),
  (false, .sub, "1.401298464324817e-45", "2.0", 0xC0000000),
  (false, .sub, "3.4028234663852886e+38", "2.0", 0x7F7FFFFF),
  (false, .mul, "0.10000000149011612", "0.20000000298023224", 0x3CA3D70B),
  (false, .mul, "1.5", "-2.0", 0xC0400000),
  (false, .mul, "1.0", "3.0", 0x40400000),
  (false, .mul, "16777216.0", "1.0", 0x4B800000),
  (false, .mul, "16777216.0", "3.0", 0x4C400000),
  (false, .mul, "0.0", "-0.0", 0x80000000),
  (false, .mul, "1.401298464324817e-45", "2.0", 0x2),
  (false, .mul, "3.4028234663852886e+38", "2.0", 0x7F800000),
  (false, .div, "0.10000000149011612", "0.20000000298023224", 0x3F000000),
  (false, .div, "1.5", "-2.0", 0xBF400000),
  (false, .div, "1.0", "3.0", 0x3EAAAAAB),
  (false, .div, "16777216.0", "1.0", 0x4B800000),
  (false, .div, "16777216.0", "3.0", 0x4AAAAAAB),
  (false, .div, "1.401298464324817e-45", "2.0", 0x0),
  (false, .div, "3.4028234663852886e+38", "2.0", 0x7EFFFFFF),
  (true, .add, "0.1", "0.2", 0x3FD3333333333334),
  (true, .add, "1.5", "-2.0", 0xBFE0000000000000),
  (true, .add, "1.0", "3.0", 0x4010000000000000),
  (true, .add, "16777216.0", "1.0", 0x4170000010000000),
  (true, .add, "16777216.0", "3.0", 0x4170000030000000),
  (true, .add, "0.0", "-0.0", 0x0),
  (true, .add, "5e-324", "2.0", 0x4000000000000000),
  (true, .add, "1.7976931348623157e+308", "2.0", 0x7FEFFFFFFFFFFFFF),
  (true, .sub, "0.1", "0.2", 0xBFB999999999999A),
  (true, .sub, "1.5", "-2.0", 0x400C000000000000),
  (true, .sub, "1.0", "3.0", 0xC000000000000000),
  (true, .sub, "16777216.0", "1.0", 0x416FFFFFE0000000),
  (true, .sub, "16777216.0", "3.0", 0x416FFFFFA0000000),
  (true, .sub, "0.0", "-0.0", 0x0),
  (true, .sub, "5e-324", "2.0", 0xC000000000000000),
  (true, .sub, "1.7976931348623157e+308", "2.0", 0x7FEFFFFFFFFFFFFF),
  (true, .mul, "0.1", "0.2", 0x3F947AE147AE147C),
  (true, .mul, "1.5", "-2.0", 0xC008000000000000),
  (true, .mul, "1.0", "3.0", 0x4008000000000000),
  (true, .mul, "16777216.0", "1.0", 0x4170000000000000),
  (true, .mul, "16777216.0", "3.0", 0x4188000000000000),
  (true, .mul, "0.0", "-0.0", 0x8000000000000000),
  (true, .mul, "5e-324", "2.0", 0x2),
  (true, .mul, "1.7976931348623157e+308", "2.0", 0x7FF0000000000000),
  (true, .div, "0.1", "0.2", 0x3FE0000000000000),
  (true, .div, "1.5", "-2.0", 0xBFE8000000000000),
  (true, .div, "1.0", "3.0", 0x3FD5555555555555),
  (true, .div, "16777216.0", "1.0", 0x4170000000000000),
  (true, .div, "16777216.0", "3.0", 0x4155555555555555),
  (true, .div, "5e-324", "2.0", 0x0),
  (true, .div, "1.7976931348623157e+308", "2.0", 0x7FDFFFFFFFFFFFFF)
]

private def check (row : Bool × Op × String × String × Nat) : Bool := Id.run do
  let (double, op, a, b, expected) := row
  let some pa := parseLexical a | return false
  let some pb := parseLexical b | return false
  let x := if double then canonDouble pa else canonFloat pa
  let y := if double then canonDouble pb else canonFloat pb
  let result := calculate double op x y
  return (if double then (fvalToBits64 result).toNat else (fvalToBits32 result).toNat) == expected

#guard vectors.length == 62
#guard vectors.all check

end L4Factoidal.Fn.ArithmeticOracleTests
