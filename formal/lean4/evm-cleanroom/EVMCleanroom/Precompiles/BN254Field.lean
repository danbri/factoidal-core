import EVMCleanroom.Precompiles.Montgomery

/-! # The alt_bn128 base field on four limbs, in Montgomery form -/

namespace EVMCleanroom.Precompiles.BN254

def baseField : Mont256 where
  n := ⟨0x3c208c16d87cfd47, 0x97816a916871ca8d, 0xb85045b68181585d, 0x30644e72e131a029⟩
  inv := 0x87d20782e4866389
  one := ⟨0xd35d438dc58f0d9d, 0xa78eb28f5c70b3d, 0x666ea36f7879462c, 0xe0a77c19a07df2f⟩
  r2 := ⟨0xf32cfc5b538afa89, 0xb5e71911d44501fb, 0x47ab1eff0a417ff6, 0x6d89f71cab8351f⟩

end EVMCleanroom.Precompiles.BN254
