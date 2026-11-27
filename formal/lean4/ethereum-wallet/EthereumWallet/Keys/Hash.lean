import EVMCleanroom.Keccak

/-
The one place the key modules reach Keccak-256. The implementation is the
repository's `EVMCleanroom.Keccak` (pure Lean, checked against published vectors,
not proved equal to an independent model). Change this file to switch.
-/

namespace EthereumWallet.Keys

/-- Keccak-256 (Ethereum's, suffix 0x01) of a byte string: 32 bytes. -/
def keccak256 (b : ByteArray) : ByteArray :=
  ByteArray.mk (EVMCleanroom.Keccak.digest (EVMCleanroom.ByteView.ofArray b.data)).toArray

/-- Kind: size.
    Says: the digest is 32 bytes.
    Does not say: anything about the digest's value. -/
theorem keccak256_size (b : ByteArray) : (keccak256 b).size = 32 := by
  simp [keccak256, ByteArray.size]

end EthereumWallet.Keys
