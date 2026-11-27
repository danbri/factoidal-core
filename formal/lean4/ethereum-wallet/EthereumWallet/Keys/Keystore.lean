import L4Factoidal.Crypto.Hmac
import EthereumWallet.Keys.Hash
import EthereumWallet.Keys.Pbkdf2
import EthereumWallet.Keys.Scrypt
import EthereumWallet.Keys.Aes

/-
Web3 Secret Storage, version 3 (the keystore JSON of geth and others): the
record, key derivation, the MAC check, decryption and encryption. JSON text is
handled in `KeystoreJson`.

Order of work in `decrypt`: header checks (version, cipher, IV length), KDF
parameter checks, key derivation, MAC check, and only then AES. A MAC mismatch
is answered before any AES work (`decryptWithKey_mac_mismatch`,
`decrypt_mac_mismatch`), and an `.ok` answer implies the MAC matched
(`decrypt_ok_mac`).

Randomness: `encrypt` takes the salt and the IV as inputs; the host supplies OS
random bytes. Wrong lengths are refused (IV exactly 16 bytes; salt at least
`minSaltBytes` = 16, geth writes 32). Nothing here generates random bytes, and
nothing here can tell whether an IV or salt was used before: that is the
caller's duty.

Short secrets: geth's vectors "31_byte_key" and "30_byte_key" hold ciphertexts
shorter than 32 bytes. `decrypt` returns the plaintext bytes exactly as they
are; a caller that wants a 32-byte private key left-pads with zeros.
`encrypt` takes secrets of 1 to `maxSecretBytes` bytes.

## Constant time and secret lifetime (this half: scrypt, AES, keystore)

* Not constant-time: AES uses a table S-box indexed by secret bytes and
  data-dependent branches in `xtime`; scrypt indexes memory by
  password-dependent values (by design); the pure SHA-256/HMAC/PBKDF2 and
  Keccak are fixed-width word code with no secret-dependent branches at source
  level, but nothing was measured and the compiler is trusted.
* No `Nat` holds a secret here: `Nat`s are sizes, counts, parameters, the
  public CTR counter, and scrypt's index `j` (secret-dependent, used as an
  array offset).
* The MAC comparison is `L4Factoidal.Crypto.ctEqBytes`: at source level its
  time depends only on the length. The compiled code was not examined.
* Lifetime: the password, derived key, AES key schedule, keystream and
  plaintext are ordinary immutable Lean heap objects. They live until the
  runtime frees them, are never zeroised, and may be copied by the runtime.
  A caller must not keep them longer than the operation needs, and must not
  log them. Errors carry no secret bytes.
-/

namespace EthereumWallet.Keys

open L4Factoidal.Crypto (ctEqBytes ctDiffFrom)

/-- The key-derivation part of a keystore. -/
inductive Kdf where
  | scrypt (n r p dkLen : Nat) (salt : ByteArray)
  | pbkdf2 (c dkLen : Nat) (prf : String) (salt : ByteArray)
  /-- A KDF name this code does not implement; kept so that a file can be read
      and refused by `decrypt`, not by the reader. -/
  | other (name : String)

/-- A version 3 keystore. `address` and `id` are carried as text, unchecked. -/
structure Keystore where
  version : Nat := 3
  cipher : String := "aes-128-ctr"
  iv : ByteArray
  ciphertext : ByteArray
  kdf : Kdf
  mac : ByteArray
  address : Option String := none
  id : Option String := none

inductive KeystoreError where
  | unsupportedVersion
  | unsupportedCipher
  | unsupportedKdf
  | unsupportedPrf
  | badIvLength
  /-- `dklen` below 32 (the MAC needs bytes 16 to 32) or above `scryptMaxDkLen`. -/
  | badDkLen
  | badSaltLength
  | badSecretLength
  /-- PBKDF2 iteration count zero or above `pbkdf2MaxIterations`. -/
  | badIterations
  | scrypt (e : ScryptError)
  | macMismatch
  | internal
  /-- The text is not a keystore (`KeystoreJson`). -/
  | json (what : String)
  deriving Repr, BEq, DecidableEq

/-- The largest PBKDF2 iteration count accepted (a work bound; geth writes 262144). -/
def pbkdf2MaxIterations : Nat := 16777216

/-- The shortest salt `encrypt` accepts, in bytes. -/
def minSaltBytes : Nat := 16

/-- The longest secret `encrypt` accepts, in bytes. -/
def maxSecretBytes : Nat := 64

/-- geth's standard scrypt parameters (N = 2^18, r = 8, p = 1): 256 MiB. -/
def Kdf.scryptStandard (salt : ByteArray) : Kdf := .scrypt 262144 8 1 32 salt

/-- geth's light scrypt parameters (N = 2^12, r = 8, p = 6): 4 MiB. -/
def Kdf.scryptLight (salt : ByteArray) : Kdf := .scrypt 4096 8 6 32 salt

/-- Derive the key. Parameter checks come before any derivation work. -/
def deriveKey (kdf : Kdf) (password : ByteArray) : Except KeystoreError ByteArray :=
  match kdf with
  | .scrypt n r p dkLen salt =>
    match (ScryptParams.mk n r p dkLen).check with
    | .error e => .error (.scrypt e)
    | .ok () =>
      if dkLen < 32 then .error .badDkLen
      else
        match Keys.scrypt password salt ⟨n, r, p, dkLen⟩ with
        | .error e => .error (.scrypt e)
        | .ok dk => .ok dk
  | .pbkdf2 c dkLen prf salt =>
    if prf ≠ "hmac-sha256" then .error .unsupportedPrf
    else if dkLen < 32 ∨ scryptMaxDkLen < dkLen then .error .badDkLen
    else if c = 0 ∨ pbkdf2MaxIterations < c then .error .badIterations
    else
      -- Prepared-key PBKDF2 (`HmacKey.mac256_eq`: the same HMAC, two compressions a round).
      let dk := Pbkdf2.raw (HmacKey.ofSha256 password).mac256 32 salt c dkLen
      if dk.size = dkLen then .ok dk else .error .internal
  | .other _ => .error .unsupportedKdf

/-- The keystore MAC: Keccak-256 of bytes 16 to 32 of the derived key, then the ciphertext. -/
def macOf (dk ciphertext : ByteArray) : ByteArray :=
  keccak256 (dk.extract 16 32 ++ ciphertext)

/-- Version, cipher and IV length. -/
def checkHeader (ks : Keystore) : Except KeystoreError Unit :=
  if ks.version ≠ 3 then .error .unsupportedVersion
  else if ks.cipher ≠ "aes-128-ctr" then .error .unsupportedCipher
  else if ks.iv.size ≠ 16 then .error .badIvLength
  else .ok ()

/-- MAC check, then AES-128-CTR under the first 16 bytes of the derived key.
    The MAC is compared before any AES work. -/
def decryptWithKey (dk : ByteArray) (ks : Keystore) : Except KeystoreError ByteArray :=
  if ctEqBytes (macOf dk ks.ciphertext) ks.mac then
    match aes128Ctr (dk.extract 0 16) ks.iv ks.ciphertext with
    | .ok plain => .ok plain
    | .error .badIvLength => .error .badIvLength
    | .error .badKeyLength => .error .internal
  else .error .macMismatch

/-- Decrypt a keystore with a password. -/
def decrypt (ks : Keystore) (password : ByteArray) : Except KeystoreError ByteArray :=
  match checkHeader ks with
  | .error e => .error e
  | .ok () =>
    match deriveKey ks.kdf password with
    | .error e => .error e
    | .ok dk => decryptWithKey dk ks

/-- Encrypt under an already derived key. -/
def encryptWithKey (dk secret iv : ByteArray) (kdf : Kdf)
    (address id : Option String := none) : Except KeystoreError Keystore :=
  match aes128Ctr (dk.extract 0 16) iv secret with
  | .ok ciphertext =>
    .ok { iv := iv, ciphertext := ciphertext, kdf := kdf, mac := macOf dk ciphertext,
          address := address, id := id }
  | .error .badIvLength => .error .badIvLength
  | .error .badKeyLength => .error .internal

/-- The salt of a KDF description, if it has one. -/
def Kdf.salt? : Kdf → Option ByteArray
  | .scrypt _ _ _ _ salt => some salt
  | .pbkdf2 _ _ _ salt => some salt
  | .other _ => none

/-- Make a keystore. `iv` (16 bytes) and the salt inside `kdf` (at least
    `minSaltBytes`) must be fresh OS random bytes supplied by the host. -/
def encrypt (secret password iv : ByteArray) (kdf : Kdf)
    (address id : Option String := none) : Except KeystoreError Keystore :=
  if secret.size = 0 ∨ maxSecretBytes < secret.size then .error .badSecretLength
  else if iv.size ≠ 16 then .error .badIvLength
  else
    match kdf.salt? with
    | none => .error .unsupportedKdf
    | some salt =>
      if salt.size < minSaltBytes then .error .badSaltLength
      else
        match deriveKey kdf password with
        | .error e => .error e
        | .ok dk => encryptWithKey dk secret iv kdf address id

/-! ## Theorems -/

/-- Kind: authentication before decryption.
    Says: when the MAC comparison fails, `decryptWithKey` answers
    `.error .macMismatch`; the AES branch is not taken, so no plaintext exists.
    Does not say: that Keccak-256 or the comparison resist forgery. -/
theorem decryptWithKey_mac_mismatch (dk : ByteArray) (ks : Keystore)
    (h : ctEqBytes (macOf dk ks.ciphertext) ks.mac = false) :
    decryptWithKey dk ks = .error .macMismatch := by
  simp [decryptWithKey, h]

/-- Kind: authentication before decryption.
    Says: for a keystore that passes the header checks and whose key derives,
    a failed MAC comparison makes `decrypt` answer `.error .macMismatch`
    (a wrong password, or a changed ciphertext, MAC or KDF field).
    Does not say: that a wrong password always fails the MAC (that rests on
    Keccak-256 and the KDF, which are tested, not proved). -/
theorem decrypt_mac_mismatch (ks : Keystore) (password dk : ByteArray)
    (hh : checkHeader ks = .ok ()) (hk : deriveKey ks.kdf password = .ok dk)
    (h : ctEqBytes (macOf dk ks.ciphertext) ks.mac = false) :
    decrypt ks password = .error .macMismatch := by
  simp [decrypt, hh, hk, decryptWithKey_mac_mismatch dk ks h]

/-- Kind: authentication before decryption.
    Says: every `.ok` answer of `decrypt` comes with a derived key whose MAC
    over the ciphertext compared equal to the stored MAC.
    Does not say: that the plaintext is the one originally encrypted (that
    needs collision resistance, which is assumed, not proved). -/
theorem decrypt_ok_mac (ks : Keystore) (password plain : ByteArray)
    (h : decrypt ks password = .ok plain) :
    ∃ dk, deriveKey ks.kdf password = .ok dk ∧
      ctEqBytes (macOf dk ks.ciphertext) ks.mac = true := by
  unfold decrypt at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i dk hk
      refine ⟨dk, hk, ?_⟩
      cases hm : ctEqBytes (macOf dk ks.ciphertext) ks.mac with
      | true => rfl
      | false => rw [decryptWithKey_mac_mismatch dk ks hm] at h; cases h

/-- Kind: refusal.
    Says: a version other than 3 is refused before any other work.
    Does not say: anything about version 3 files. -/
theorem decrypt_refuses_version (ks : Keystore) (password : ByteArray) (h : ks.version ≠ 3) :
    decrypt ks password = .error .unsupportedVersion := by
  simp [decrypt, checkHeader, h]

/-- Kind: refusal.
    Says: a version 3 file with a cipher other than `aes-128-ctr` is refused.
    Does not say: anything else. -/
theorem decrypt_refuses_cipher (ks : Keystore) (password : ByteArray) (hv : ks.version = 3)
    (h : ks.cipher ≠ "aes-128-ctr") : decrypt ks password = .error .unsupportedCipher := by
  simp [decrypt, checkHeader, hv, h]

/-- Kind: refusal.
    Says: with version and cipher accepted, an IV that is not 16 bytes is
    refused before key derivation.
    Does not say: anything else. -/
theorem decrypt_refuses_iv (ks : Keystore) (password : ByteArray) (hv : ks.version = 3)
    (hc : ks.cipher = "aes-128-ctr") (h : ks.iv.size ≠ 16) :
    decrypt ks password = .error .badIvLength := by
  simp [decrypt, checkHeader, hv, hc, h]

/-- Kind: refusal.
    Says: an unknown KDF name derives no key.
    Does not say: anything else. -/
theorem deriveKey_refuses_other (name : String) (password : ByteArray) :
    deriveKey (.other name) password = .error .unsupportedKdf := rfl

/-- Kind: refusal.
    Says: PBKDF2 with a PRF other than `hmac-sha256` derives no key.
    Does not say: anything else. -/
theorem deriveKey_refuses_prf (c dkLen : Nat) (prf : String) (salt password : ByteArray)
    (h : prf ≠ "hmac-sha256") :
    deriveKey (.pbkdf2 c dkLen prf salt) password = .error .unsupportedPrf := by
  simp [deriveKey, h]

/-- Kind: refusal.
    Says: PBKDF2 with `dklen` below 32 derives no key.
    Does not say: anything else. -/
theorem deriveKey_pbkdf2_refuses_dkLen (c dkLen : Nat) (salt password : ByteArray)
    (h : dkLen < 32) :
    deriveKey (.pbkdf2 c dkLen "hmac-sha256" salt) password = .error .badDkLen := by
  simp [deriveKey, h]

/-- Kind: refusal.
    Says: PBKDF2 with an accepted `dklen` and an iteration count of zero or
    above `pbkdf2MaxIterations` derives no key (a work bound).
    Does not say: how long an accepted count takes. -/
theorem deriveKey_pbkdf2_refuses_iterations (c dkLen : Nat) (salt password : ByteArray)
    (hd : ¬(dkLen < 32 ∨ scryptMaxDkLen < dkLen)) (h : c = 0 ∨ pbkdf2MaxIterations < c) :
    deriveKey (.pbkdf2 c dkLen "hmac-sha256" salt) password = .error .badIterations := by
  simp only [deriveKey, ne_eq, not_true_eq_false, if_false, if_neg hd, if_pos h]

/-- Kind: resource refusal.
    Says: a failed scrypt parameter check is `deriveKey`'s answer, before any
    derivation work.
    Does not say: which check failed. -/
theorem deriveKey_scrypt_check_error (n r p dkLen : Nat) (salt password : ByteArray)
    (e : ScryptError) (h : (ScryptParams.mk n r p dkLen).check = .error e) :
    deriveKey (.scrypt n r p dkLen salt) password = .error (.scrypt e) := by
  simp [deriveKey, h]

/-- Kind: resource refusal.
    Says: scrypt parameters needing more than `scryptMaxBytes` derive no key:
    the answer is `.error (.scrypt .memoryLimit)`, before any allocation.
    Does not say: that the limit suits a given machine. -/
theorem deriveKey_scrypt_over_limit (n r p dkLen : Nat) (salt password : ByteArray)
    (h : scryptMaxBytes < 128 * r * n + 128 * r * p) :
    deriveKey (.scrypt n r p dkLen salt) password = .error (.scrypt .memoryLimit) :=
  deriveKey_scrypt_check_error n r p dkLen salt password .memoryLimit
    (check_over_limit _ (by simpa [ScryptParams.memoryBytes] using h))

/-- Kind: refusal.
    Says: scrypt with accepted cost parameters and `dklen` below 32 derives no key.
    Does not say: anything else. -/
theorem deriveKey_scrypt_refuses_dkLen (n r p dkLen : Nat) (salt password : ByteArray)
    (hc : (ScryptParams.mk n r p dkLen).check = .ok ()) (h : dkLen < 32) :
    deriveKey (.scrypt n r p dkLen salt) password = .error .badDkLen := by
  simp [deriveKey, hc, h]

/-- Kind: resource refusal.
    Says: `decrypt` on an accepted header with over-limit scrypt parameters
    answers `.error (.scrypt .memoryLimit)`.
    Does not say: anything about parameters within the limit. -/
theorem decrypt_scrypt_over_limit (ks : Keystore) (password salt : ByteArray) (n r p dkLen : Nat)
    (hh : checkHeader ks = .ok ()) (hk : ks.kdf = .scrypt n r p dkLen salt)
    (h : scryptMaxBytes < 128 * r * n + 128 * r * p) :
    decrypt ks password = .error (.scrypt .memoryLimit) := by
  simp [decrypt, hh, hk, deriveKey_scrypt_over_limit n r p dkLen salt password h]

theorem ctDiffFrom_self (a : ByteArray) (n i : Nat) (acc : UInt8) :
    ctDiffFrom a a n i acc = acc := by
  induction n generalizing i acc with
  | zero => rfl
  | succ k ih => simp [ctDiffFrom, ih]

/-- Kind: algebra.
    Says: `ctEqBytes` answers `true` on equal byte strings.
    Does not say: that it answers `false` on all unequal ones (not needed here). -/
theorem ctEqBytes_self (a : ByteArray) : ctEqBytes a a = true := by
  simp [ctEqBytes, ctDiffFrom_self]

/-- Kind: round trip.
    Says: a keystore made by `encryptWithKey` under a derived key decrypts under
    the same key to the same secret: the MAC it stored matches, and CTR undoes
    itself.
    Does not say: that `deriveKey` gives the same key twice (it is a function,
    so it does, for the same KDF description and password), nor anything about
    the JSON text. -/
theorem decryptWithKey_encryptWithKey (dk secret iv : ByteArray) (kdf : Kdf)
    (address id : Option String) (ks : Keystore)
    (h : encryptWithKey dk secret iv kdf address id = .ok ks) :
    decryptWithKey dk ks = .ok secret := by
  unfold encryptWithKey at h
  split at h
  · rename_i ct hct
    cases h
    simp [decryptWithKey, ctEqBytes_self, aes128Ctr_involutive _ _ _ _ hct]
  · cases h
  · cases h

/-- Kind: refusal.
    Says: `encrypt` refuses an IV that is not 16 bytes, for an accepted secret length.
    Does not say: that a 16-byte IV is fresh. -/
theorem encrypt_refuses_iv (secret password iv : ByteArray) (kdf : Kdf)
    (address id : Option String)
    (hs : ¬(secret.size = 0 ∨ maxSecretBytes < secret.size)) (h : iv.size ≠ 16) :
    encrypt secret password iv kdf address id = .error .badIvLength := by
  simp only [encrypt, if_neg hs, if_pos h]

/-- Kind: refusal.
    Says: `encrypt` refuses an empty secret or one above `maxSecretBytes`.
    Does not say: anything else. -/
theorem encrypt_refuses_secret (secret password iv : ByteArray) (kdf : Kdf)
    (address id : Option String) (h : secret.size = 0 ∨ maxSecretBytes < secret.size) :
    encrypt secret password iv kdf address id = .error .badSecretLength := by
  simp only [encrypt, if_pos h]

end EthereumWallet.Keys
