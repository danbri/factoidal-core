import EVMCleanroom.Precompiles.Secp256k1Point
import EVMCleanroom.Precompiles.ScalarMul
namespace Probe
open EVMCleanroom.Precompiles EVMCleanroom.Precompiles.Secp256k1 EVMCleanroom.Precompiles.Secp256k1.Fast

@[inline] def addG (table : Array Aff) (d : Int) (flip : Bool) (acc : Pt) : Pt :=
  if d = 0 then acc else madd acc (table.getD (d.natAbs / 2) affZero) (flip != decide (d < 0))
@[inline] def addQ (table : Array Pt) (d : Int) (flip : Bool) (acc : Pt) : Pt :=
  if d = 0 then acc else padd acc (table.getD (d.natAbs / 2) infinity) (flip != decide (d < 0))
def mainLoop (gT lgT : Array Aff) (qT lqT : Array Pt) (d1 d2 d3 d4 : Array Int) (f1 f2 f3 f4 : Bool) : Nat → Pt → Pt
  | 0, acc => acc
  | i+1, acc =>
    mainLoop gT lgT qT lqT d1 d2 d3 d4 f1 f2 f3 f4 i
      (addQ lqT (d4.getD i 0) f4 (addQ qT (d3.getD i 0) f3
        (addG lgT (d2.getD i 0) f2 (addG gT (d1.getD i 0) f1 (dbl acc)))))
