import EVMCleanroom.Precompiles.Secp256k1Point
import EVMCleanroom.Precompiles.ScalarMul
namespace Probe
open EVMCleanroom.Precompiles EVMCleanroom.Precompiles.Secp256k1 EVMCleanroom.Precompiles.Secp256k1.Fast

@[inline] def addG (table : Array Aff) (d : Int) (flip : Bool) (acc : Pt) : Pt :=
  if d = 0 then acc else madd acc (table.getD (d.natAbs / 2) affZero) (flip != decide (d < 0))
@[inline] def addQ (table : Array Pt) (d : Int) (flip : Bool) (acc : Pt) : Pt :=
  if d = 0 then acc else padd acc (table.getD (d.natAbs / 2) infinity) (flip != decide (d < 0))
