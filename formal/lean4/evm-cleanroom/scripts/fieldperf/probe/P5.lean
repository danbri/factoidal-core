import EVMCleanroom.Precompiles.Secp256k1Point
import EVMCleanroom.Precompiles.ScalarMul
namespace Probe
open EVMCleanroom.Precompiles EVMCleanroom.Precompiles.Secp256k1 EVMCleanroom.Precompiles.Secp256k1.Fast

def step (acc : Pt) : Pt := dbl acc
