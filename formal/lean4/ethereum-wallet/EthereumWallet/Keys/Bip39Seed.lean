import EthereumWallet.Keys.Bip39
import EthereumWallet.Keys.Pbkdf2

/-!
# BIP-39: mnemonic to seed

`PBKDF2-HMAC-SHA512(password = mnemonic, salt = "mnemonic" ‖ passphrase, c = 2048, dkLen = 64)`.

BIP-39 applies Unicode NFKD to both strings first. English mnemonics are ASCII, where
NFKD changes nothing; `seed` therefore accepts ASCII only and refuses anything else with
`notAscii`, and `seedOfNormalized` takes bytes the caller has already normalised.
BIP-39 derives a seed from any sentence, valid or not; check with `Bip39.parse` first
when the sentence must be a real mnemonic.
-/

namespace EthereumWallet.Keys.Bip39

def seedIterations : Nat := 2048

/-- All bytes below 0x80. -/
def isAscii (b : ByteArray) : Bool := b.foldl (fun ok x => ok && x < 128) true

/-- The 64-byte seed for a mnemonic and passphrase given as NFKD-normalised UTF-8. -/
def seedOfNormalized (_ : SecretRisk) (mnemonic passphrase : ByteArray) : ByteArray :=
  Pbkdf2.raw (HmacKey.ofSha512 mnemonic).mac512 64 ("mnemonic".toUTF8 ++ passphrase)
    seedIterations 64

/-- The 64-byte seed for an ASCII mnemonic and ASCII passphrase. -/
def seed (risk : SecretRisk) (mnemonic passphrase : String) : Except Error ByteArray :=
  if isAscii mnemonic.toUTF8 && isAscii passphrase.toUTF8 then
    .ok (seedOfNormalized risk mnemonic.toUTF8 passphrase.toUTF8)
  else .error .notAscii

/-- Kind: refusal.
    Says: a mnemonic or passphrase with a non-ASCII byte is refused, never hashed as it is.
    Does not say: that ASCII input needs no other preparation by the caller. -/
theorem seed_not_ascii (risk : SecretRisk) (mnemonic passphrase : String)
    (h : (isAscii mnemonic.toUTF8 && isAscii passphrase.toUTF8) = false) :
    seed risk mnemonic passphrase = .error .notAscii := by
  unfold seed
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- Kind: equality with the checked form.
    Says: the seed is what the bounds-checked PBKDF2 returns for 2048 rounds and 64 bytes. -/
theorem seedOfNormalized_eq (risk : SecretRisk) (mnemonic passphrase : ByteArray) :
    Pbkdf2.hmacSha512 risk mnemonic ("mnemonic".toUTF8 ++ passphrase) 2048 64
      = .ok (seedOfNormalized risk mnemonic passphrase) := by
  rfl

end EthereumWallet.Keys.Bip39

open EthereumWallet.Keys.Bip39 in
#print axioms seed_not_ascii
open EthereumWallet.Keys.Bip39 in
#print axioms seedOfNormalized_eq
