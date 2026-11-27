import EVMCleanroom.Precompiles.Montgomery

/-! # The BLS12-381 base field on six limbs, in Montgomery form -/

namespace EVMCleanroom.Precompiles.BLS12381

def baseField : Mont384 where
  n := ⟨0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624, 0x64774b84f38512bf, 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a⟩
  inv := 0x89f3fffcfffcfffd
  one := ⟨0x760900000002fffd, 0xebf4000bc40c0002, 0x5f48985753c758ba, 0x77ce585370525745, 0x5c071a97a256ec6d, 0x15f65ec3fa80e493⟩
  r2 := ⟨0xf4df1f341c341746, 0xa76e6a609d104f1, 0x8de5476c4c95b6d5, 0x67eb88a9939d83c0, 0x9a793e85b519952d, 0x11988fe592cae3aa⟩

end EVMCleanroom.Precompiles.BLS12381
