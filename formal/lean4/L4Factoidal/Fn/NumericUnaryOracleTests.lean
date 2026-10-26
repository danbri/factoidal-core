/- Independent finite unary observations: 40 binary inputs × 3 operations.
   CPython struct.pack/unpack selects binary32/64 inputs, Decimal.from_float
   reads their exact value, then to_integral_value uses ROUND_FLOOR,
   ROUND_CEILING, or ROUND_HALF_DOWN for negatives / ROUND_HALF_UP otherwise.
   struct.pack encodes the expected result, including signed zero. This is
   a finite oracle corpus, not a universal IEEE correctness proof. -/
import L4Factoidal.Fn.NumericUnary

namespace L4Factoidal.Fn.NumericUnaryOracleTests
open XSD

private def vectors : List (Bool × String × Nat × Nat × Nat) := [
  (false, "-0.0", 0x80000000, 0x80000000, 0x80000000),
  (false, "0.0", 0x0, 0x0, 0x0),
  (false, "-0.10000000149011612", 0xBF800000, 0x80000000, 0x80000000),
  (false, "0.10000000149011612", 0x0, 0x3F800000, 0x0),
  (false, "-0.5", 0xBF800000, 0x80000000, 0x80000000),
  (false, "0.5", 0x0, 0x3F800000, 0x3F800000),
  (false, "-1.5", 0xC0000000, 0xBF800000, 0xBF800000),
  (false, "1.5", 0x3F800000, 0x40000000, 0x40000000),
  (false, "-2.5", 0xC0400000, 0xC0000000, 0xC0000000),
  (false, "2.5", 0x40000000, 0x40400000, 0x40400000),
  (false, "0.5", 0x0, 0x3F800000, 0x3F800000),
  (false, "-0.5", 0xBF800000, 0x80000000, 0x80000000),
  (false, "0.5", 0x0, 0x3F800000, 0x3F800000),
  (false, "-0.5", 0xBF800000, 0x80000000, 0x80000000),
  (false, "16777216.0", 0x4B800000, 0x4B800000, 0x4B800000),
  (false, "9007199254740992.0", 0x5A000000, 0x5A000000, 0x5A000000),
  (false, "1.401298464324817e-45", 0x0, 0x3F800000, 0x0),
  (false, "-1.401298464324817e-45", 0xBF800000, 0x80000000, 0x80000000),
  (false, "3.4028234663852886e+38", 0x7F7FFFFF, 0x7F7FFFFF, 0x7F7FFFFF),
  (false, "-3.4028234663852886e+38", 0xFF7FFFFF, 0xFF7FFFFF, 0xFF7FFFFF),
  (true, "-0.0", 0x8000000000000000, 0x8000000000000000, 0x8000000000000000),
  (true, "0.0", 0x0, 0x0, 0x0),
  (true, "-0.1", 0xBFF0000000000000, 0x8000000000000000, 0x8000000000000000),
  (true, "0.1", 0x0, 0x3FF0000000000000, 0x0),
  (true, "-0.5", 0xBFF0000000000000, 0x8000000000000000, 0x8000000000000000),
  (true, "0.5", 0x0, 0x3FF0000000000000, 0x3FF0000000000000),
  (true, "-1.5", 0xC000000000000000, 0xBFF0000000000000, 0xBFF0000000000000),
  (true, "1.5", 0x3FF0000000000000, 0x4000000000000000, 0x4000000000000000),
  (true, "-2.5", 0xC008000000000000, 0xC000000000000000, 0xC000000000000000),
  (true, "2.5", 0x4000000000000000, 0x4008000000000000, 0x4008000000000000),
  (true, "0.49999999999999994", 0x0, 0x3FF0000000000000, 0x0),
  (true, "-0.5000000000000001", 0xBFF0000000000000, 0x8000000000000000, 0xBFF0000000000000),
  (true, "0.499999999", 0x0, 0x3FF0000000000000, 0x0),
  (true, "-0.50000001", 0xBFF0000000000000, 0x8000000000000000, 0xBFF0000000000000),
  (true, "16777217.0", 0x4170000010000000, 0x4170000010000000, 0x4170000010000000),
  (true, "9007199254740991.0", 0x433FFFFFFFFFFFFF, 0x433FFFFFFFFFFFFF, 0x433FFFFFFFFFFFFF),
  (true, "5e-324", 0x0, 0x3FF0000000000000, 0x0),
  (true, "-5e-324", 0xBFF0000000000000, 0x8000000000000000, 0x8000000000000000),
  (true, "1.7976931348623157e+308", 0x7FEFFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFF),
  (true, "-1.7976931348623157e+308", 0xFFEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF)]

private def checkVector (v : Bool × String × Nat × Nat × Nat) : Bool :=
  let (double, source, floorBits, ceilingBits, nearestBits) := v
  let input := XSD.lexicalFor .xsd10 (if double then .double else .float) source
  let f := match input with | some (.flt f) | some (.dbl f) => some f | _ => none
  match f with
  | none => false
  | some f =>
      [(Rounding.Mode.floor, floorBits), (.ceiling, ceilingBits), (.nearest, nearestBits)].all
        fun (mode, expected) =>
          let result := NumericUnary.integralFloating double mode f
          (if double then (fvalToBits64 result).toNat else (fvalToBits32 result).toNat) == expected

#guard vectors.length == 40
#guard vectors.all checkVector

end L4Factoidal.Fn.NumericUnaryOracleTests
