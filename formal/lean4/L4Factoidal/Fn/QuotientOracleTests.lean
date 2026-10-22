/- F&O §6.2.5–6: 24 finite observations from CPython math.fmod and
   math.trunc(a / b), with struct binary32/64 input/result rounding.
   Tests compare remainder bit patterns (including signed zero) and quotient
   integers. Finite vectors are observations, not a proof of all IEEE cases.
   RIF.NumericTests covers special values and the actual dispatch adapters. -/
import L4Factoidal.Fn.Arithmetic

namespace L4Factoidal.Fn.QuotientOracleTests
open XSD Arithmetic

private def vectors : List (Bool × String × String × Nat × Int) := [
  (false, "5.0", "2.0", 0x3F800000, 2),
  (false, "-5.0", "2.0", 0xBF800000, -2),
  (false, "5.0", "-2.0", 0x3F800000, -2),
  (false, "-5.0", "-2.0", 0xBF800000, 2),
  (false, "4.5", "1.2000000476837158", 0x3F666664, 3),
  (false, "-4.5", "1.2000000476837158", 0xBF666664, -3),
  (false, "1.0", "3.0", 0x3F800000, 0),
  (false, "0.10000000149011612", "0.029999999329447746", 0x3C23D70E, 3),
  (false, "-0.0", "2.0", 0x80000000, 0),
  (false, "0.0", "-2.0", 0x0, 0),
  (false, "123.0", "6.0", 0x40400000, 20),
  (false, "1.0000000200408773e+20", "3.0", 0x40000000, 33333333268354826240),
  (true, "5.0", "2.0", 0x3FF0000000000000, 2),
  (true, "-5.0", "2.0", 0xBFF0000000000000, -2),
  (true, "5.0", "-2.0", 0x3FF0000000000000, -2),
  (true, "-5.0", "-2.0", 0xBFF0000000000000, 2),
  (true, "4.5", "1.2", 0x3FECCCCCCCCCCCCE, 3),
  (true, "-4.5", "1.2", 0xBFECCCCCCCCCCCCE, -3),
  (true, "1.0", "3.0", 0x3FF0000000000000, 0),
  (true, "0.1", "0.03", 0x3F847AE147AE1480, 3),
  (true, "-0.0", "2.0", 0x8000000000000000, 0),
  (true, "0.0", "-2.0", 0x0, 0),
  (true, "123.0", "6.0", 0x4008000000000000, 20),
  (true, "1e+20", "3.0", 0x3FF0000000000000, 33333333333333331968)
]

private def check (row : Bool × String × String × Nat × Int) : Bool := Id.run do
  let (double, a, b, bits, quotient) := row
  let some pa := parseLexical a | return false
  let some pb := parseLexical b | return false
  let x := if double then canonDouble pa else canonFloat pa
  let y := if double then canonDouble pb else canonFloat pb
  let r := floatingMod double x y
  let observed := if double then (fvalToBits64 r).toNat else (fvalToBits32 r).toNat
  return observed == bits && floatingIntegerDivide double x y == some quotient

#guard vectors.length == 24
#guard vectors.all check

end L4Factoidal.Fn.QuotientOracleTests
