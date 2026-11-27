import L4Factoidal.Crypto.Hmac
import EthereumWallet.Keys.Bytes
import EthereumWallet.Keys.Hash
import EthereumWallet.Keys.Pbkdf2
import EthereumWallet.Keys.Scrypt
import EthereumWallet.Keys.Risk

/-
Web3 Secret Storage, version 3 (the keystore JSON of geth and others): the
record, key derivation, the MAC check, and decryption and encryption through a
cipher supplied from outside. JSON text is handled in `KeystoreJson`.

## The cipher is not implemented here

A version 3 keystore encrypts the secret with a 128-bit block cipher in counter
mode (`"cipher": "aes-128-ctr"`). This package does not contain that cipher,
and no file in the repository may: the repository's rule
(`skills/aes-hardware-only`, gate `tools/aes-gate.py`) is that the only such
cipher code allowed is verified assembly using the CPU's own instructions. A
table-based or other hand-written version, in Lean or any language, leaks the
key through cache timing however many test vectors it passes.

So the cipher is a parameter, `CtrCipher`: a provider handed in by the caller.
The only instance in the tree is `CtrCipher.unavailable`, which refuses.

What works without a provider: reading and writing the JSON, every parameter
check, both key-derivation functions (scrypt and PBKDF2-HMAC-SHA-256), the
Keccak MAC, and so `verifyPassword`: it says whether a password is the
keystore's password.

What needs a provider: recovering the plaintext (`decrypt`) and making a new
keystore (`encrypt`). With `CtrCipher.unavailable` both answer
`.error .cipherUnavailable` (`decrypt_unavailable`, `encrypt_unavailable`,
`decrypt_unavailable_never_ok`). Where a provider can come from is an open
decision for the owner: on JavaScript hosts, the host's WebCrypto, as content
encryption for JWE and XML Encryption already does; natively, refused until a
verified hardware implementation of this mode exists or the owner decides
otherwise.

## Order of work

`decrypt`: header checks (version, cipher name, IV length), KDF parameter
checks, key derivation, MAC check, and only then the cipher. A MAC mismatch is
answered `.error .macMismatch` whatever the provider is, so the provider is not
consulted (`decryptWithKey_mac_mismatch`, `decrypt_mac_mismatch`), and an `.ok`
answer implies the MAC matched (`decrypt_ok_mac`). A provider's answer is
checked for length (`cipherMisbehaved`); nothing else about a provider is, or
can be, checked here.

Randomness: `encrypt` takes the salt and the IV as inputs; the host supplies OS
random bytes. Wrong lengths are refused (IV exactly 16 bytes; salt at least
`minSaltBytes` = 16, geth writes 32). Nothing here generates random bytes, and
nothing here can tell whether an IV or salt was used before: that is the
caller's duty.

Short secrets: geth's vectors "31_byte_key" and "30_byte_key" hold ciphertexts
shorter than 32 bytes. `decrypt` returns the provider's bytes exactly as they
are; a caller that wants a 32-byte private key left-pads with zeros.
`encrypt` takes secrets of 1 to `maxSecretBytes` bytes.

## Constant time and secret lifetime (this half: scrypt, PBKDF2, keystore)

Every function here that takes a password or a derived key takes the risk
token of `Risk.lean` (`SecretRisk`), because none of the following is shown.

* Not constant-time: scrypt indexes memory by password-dependent values (by
  design); the pure SHA-256/HMAC/PBKDF2 and Keccak are fixed-width word code
  with no secret-dependent branches at source level, but nothing was measured
  and the compiler is trusted.
* No `Nat` holds a secret here: `Nat`s are sizes, counts, parameters, and
  scrypt's index `j` (secret-dependent, used as an array offset).
* The MAC comparison is `L4Factoidal.Crypto.ctEqBytes`: at source level its
  time depends only on the length. The compiled code was not examined.
* Lifetime: the password, the derived key and whatever a provider returns are
  ordinary immutable Lean heap objects. They live until the runtime frees
  them, are never zeroised, and may be copied by the runtime. The first 16
  bytes of the derived key are handed to the provider. A caller must not keep
  them longer than the operation needs, and must not log them. Errors carry
  no secret bytes.
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
  /-- No provider for the keystore's cipher: nothing is decrypted or encrypted. -/
  | cipherUnavailable
  /-- The provider declined this call. -/
  | cipherRefused
  /-- The provider returned bytes of the wrong length. -/
  | cipherMisbehaved
  | internal
  /-- The text is not a keystore (`KeystoreJson`). -/
  | json (what : String)
  deriving Repr, BEq, DecidableEq

/-- The keystore's cipher (128-bit key, 16-byte initial counter block, counter
    mode), supplied from outside this package. `apply key iv data` gives the
    data combined with the keystream, or `none` when the provider declines.
    Nothing in the tree implements one; see the note at the top of this file. -/
structure CtrCipher where
  name : String
  available : Bool
  apply : (key iv data : ByteArray) → Option ByteArray

/-- The only provider in the tree: it has no cipher and refuses. -/
def CtrCipher.unavailable : CtrCipher :=
  { name := "none", available := false, apply := fun _ _ _ => none }

/-- The largest PBKDF2 iteration count accepted (a work bound; geth writes 262144). -/
def pbkdf2MaxIterations : Nat := 2097152

/-- The largest PBKDF2 `dklen` accepted: only bytes 0 to 32 of the key are ever used, and
    each further 32 bytes costs the whole iteration count again. -/
def pbkdf2MaxDkLen : Nat := 64

/-- The shortest salt `encrypt` accepts, in bytes. -/
def minSaltBytes : Nat := 16

/-- The longest secret `encrypt` accepts, in bytes. -/
def maxSecretBytes : Nat := 64

/-- geth's standard scrypt parameters (N = 2^18, r = 8, p = 1): 256 MiB. -/
def Kdf.scryptStandard (salt : ByteArray) : Kdf := .scrypt 262144 8 1 32 salt

/-- geth's light scrypt parameters (N = 2^12, r = 8, p = 6): 4 MiB. -/
def Kdf.scryptLight (salt : ByteArray) : Kdf := .scrypt 4096 8 6 32 salt

/-- Derive the key. Parameter checks come before any derivation work. -/
def deriveKey (risk : SecretRisk) (kdf : Kdf) (password : ByteArray) :
    Except KeystoreError ByteArray :=
  match kdf with
  | .scrypt n r p dkLen salt =>
    match (ScryptParams.mk n r p dkLen).check with
    | .error e => .error (.scrypt e)
    | .ok () =>
      if dkLen < 32 then .error .badDkLen
      else
        match Keys.scrypt risk password salt ⟨n, r, p, dkLen⟩ with
        | .error e => .error (.scrypt e)
        | .ok dk => .ok dk
  | .pbkdf2 c dkLen prf salt =>
    if prf ≠ "hmac-sha256" then .error .unsupportedPrf
    else if dkLen < 32 ∨ pbkdf2MaxDkLen < dkLen then .error .badDkLen
    else if c = 0 ∨ pbkdf2MaxIterations < c then .error .badIterations
    else
      -- Prepared-key PBKDF2 (`HmacKey.mac256_eq`: the same HMAC, the two pads made once).
      let dk := Pbkdf2.raw (HmacKey.ofSha256 password).mac256 32 salt c dkLen
      if dk.size = dkLen then .ok dk else .error .internal
  | .other _ => .error .unsupportedKdf

/-- The keystore MAC: Keccak-256 of bytes 16 to 32 of the derived key, then the ciphertext. -/
def macOf (dk ciphertext : ByteArray) : ByteArray :=
  keccak256 (dk.extract 16 32 ++ ciphertext)

/-- The MAC of the derived key over the stored ciphertext compares equal to the stored MAC. -/
def macMatches (dk : ByteArray) (ks : Keystore) : Bool :=
  ctEqBytes (macOf dk ks.ciphertext) ks.mac

/-- Version, cipher name and IV length. -/
def checkHeader (ks : Keystore) : Except KeystoreError Unit :=
  if ks.version ≠ 3 then .error .unsupportedVersion
  else if ks.cipher ≠ "aes-128-ctr" then .error .unsupportedCipher
  else if ks.iv.size ≠ 16 then .error .badIvLength
  else .ok ()

/-- One call of the provider, with its answer checked for length. -/
def applyCipher (cipher : CtrCipher) (key iv data : ByteArray) : Except KeystoreError ByteArray :=
  if cipher.available = false then .error .cipherUnavailable
  else
    match cipher.apply key iv data with
    | none => .error .cipherRefused
    | some out => if out.size = data.size then .ok out else .error .cipherMisbehaved

/-- MAC check, then the provider under the first 16 bytes of the derived key.
    The MAC is compared before the provider is consulted. -/
def decryptWithKey (_ : SecretRisk) (cipher : CtrCipher) (dk : ByteArray) (ks : Keystore) :
    Except KeystoreError ByteArray :=
  if macMatches dk ks = true then applyCipher cipher (dk.extract 0 16) ks.iv ks.ciphertext
  else .error .macMismatch

/-- Is `password` the keystore's password? Header checks, key derivation and
    the MAC comparison; no cipher is needed. -/
def verifyPassword (risk : SecretRisk) (ks : Keystore) (password : ByteArray) :
    Except KeystoreError Unit :=
  match checkHeader ks with
  | .error e => .error e
  | .ok () =>
    match deriveKey risk ks.kdf password with
    | .error e => .error e
    | .ok dk => if macMatches dk ks = true then .ok () else .error .macMismatch

/-- Decrypt a keystore with a password, through the given provider. -/
def decrypt (risk : SecretRisk) (cipher : CtrCipher) (ks : Keystore) (password : ByteArray) :
    Except KeystoreError ByteArray :=
  match checkHeader ks with
  | .error e => .error e
  | .ok () =>
    match deriveKey risk ks.kdf password with
    | .error e => .error e
    | .ok dk => decryptWithKey risk cipher dk ks

/-- Encrypt under an already derived key, through the given provider. -/
def encryptWithKey (_ : SecretRisk) (cipher : CtrCipher) (dk secret iv : ByteArray) (kdf : Kdf)
    (address id : Option String := none) : Except KeystoreError Keystore :=
  match applyCipher cipher (dk.extract 0 16) iv secret with
  | .ok ciphertext =>
    .ok { iv := iv, ciphertext := ciphertext, kdf := kdf, mac := macOf dk ciphertext,
          address := address, id := id }
  | .error e => .error e

/-- The salt of a KDF description, if it has one. -/
def Kdf.salt? : Kdf → Option ByteArray
  | .scrypt _ _ _ _ salt => some salt
  | .pbkdf2 _ _ _ salt => some salt
  | .other _ => none

/-- Make a keystore, through the given provider. `iv` (16 bytes) and the salt
    inside `kdf` (at least `minSaltBytes`) must be fresh OS random bytes
    supplied by the host. Without a provider the refusal comes first, before
    any key derivation. -/
def encrypt (risk : SecretRisk) (cipher : CtrCipher) (secret password iv : ByteArray) (kdf : Kdf)
    (address id : Option String := none) : Except KeystoreError Keystore :=
  if cipher.available = false then .error .cipherUnavailable
  else if secret.size = 0 ∨ maxSecretBytes < secret.size then .error .badSecretLength
  else if iv.size ≠ 16 then .error .badIvLength
  else
    match kdf.salt? with
    | none => .error .unsupportedKdf
    | some salt =>
      if salt.size < minSaltBytes then .error .badSaltLength
      else
        match deriveKey risk kdf password with
        | .error e => .error e
        | .ok dk => encryptWithKey risk cipher dk secret iv kdf address id

/-! ## Theorems -/

/-- Kind: authentication before decryption.
    Says: when the MAC comparison fails, `decryptWithKey` answers
    `.error .macMismatch` for every provider, so the provider is not consulted
    and no plaintext exists.
    Does not say: that Keccak-256 or the comparison resist forgery. -/
theorem decryptWithKey_mac_mismatch (risk : SecretRisk) (cipher : CtrCipher) (dk : ByteArray)
    (ks : Keystore) (h : macMatches dk ks = false) :
    decryptWithKey risk cipher dk ks = .error .macMismatch := by
  unfold decryptWithKey
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- Kind: authentication before decryption.
    Says: for a keystore that passes the header checks and whose key derives,
    a failed MAC comparison makes `decrypt` answer `.error .macMismatch`, for
    every provider (a wrong password, or a changed ciphertext, MAC or KDF field).
    Does not say: that a wrong password always fails the MAC (that rests on
    Keccak-256 and the KDF, which are tested, not proved). -/
theorem decrypt_mac_mismatch (risk : SecretRisk) (cipher : CtrCipher) (ks : Keystore)
    (password dk : ByteArray)
    (hh : checkHeader ks = .ok ()) (hk : deriveKey risk ks.kdf password = .ok dk)
    (h : macMatches dk ks = false) :
    decrypt risk cipher ks password = .error .macMismatch := by
  simp [decrypt, hh, hk, decryptWithKey_mac_mismatch risk cipher dk ks h]

/-- Kind: authentication before decryption.
    Says: every `.ok` answer of `decrypt` comes with an accepted header and a
    derived key whose MAC over the ciphertext compared equal to the stored MAC.
    Does not say: that the plaintext is the one originally encrypted (that
    needs collision resistance and a correct provider, neither proved). -/
theorem decrypt_ok_mac (risk : SecretRisk) (cipher : CtrCipher) (ks : Keystore)
    (password plain : ByteArray) (h : decrypt risk cipher ks password = .ok plain) :
    checkHeader ks = .ok () ∧
      ∃ dk, deriveKey risk ks.kdf password = .ok dk ∧ macMatches dk ks = true := by
  cases hh : checkHeader ks with
  | error e => simp [decrypt, hh] at h
  | ok u =>
    cases u
    refine ⟨rfl, ?_⟩
    cases hk : deriveKey risk ks.kdf password with
    | error e => simp [decrypt, hh, hk] at h
    | ok dk =>
      refine ⟨dk, rfl, ?_⟩
      cases hm : macMatches dk ks with
      | true => rfl
      | false => simp [decrypt, hh, hk, decryptWithKey_mac_mismatch risk cipher dk ks hm] at h

/-- Kind: password check.
    Says: for an accepted header and a derived key, `verifyPassword` answers
    `.ok ()` exactly when the MAC comparison succeeds.
    Does not say: that only the right password makes it succeed (tested). -/
theorem verifyPassword_ok_iff (risk : SecretRisk) (ks : Keystore) (password dk : ByteArray)
    (hh : checkHeader ks = .ok ()) (hk : deriveKey risk ks.kdf password = .ok dk) :
    verifyPassword risk ks password = .ok () ↔ macMatches dk ks = true := by
  cases hm : macMatches dk ks <;> simp [verifyPassword, hh, hk, hm]

/-- Kind: password check.
    Says: under the same conditions a failed MAC comparison is `.error .macMismatch`.
    Does not say: anything else. -/
theorem verifyPassword_mac_mismatch (risk : SecretRisk) (ks : Keystore) (password dk : ByteArray)
    (hh : checkHeader ks = .ok ()) (hk : deriveKey risk ks.kdf password = .ok dk)
    (h : macMatches dk ks = false) :
    verifyPassword risk ks password = .error .macMismatch := by
  simp [verifyPassword, hh, hk, h]

/-- Kind: agreement.
    Says: whenever `decrypt` answers `.ok`, with any provider, `verifyPassword`
    accepts the same password.
    Does not say: the converse (it needs a provider that answers). -/
theorem decrypt_ok_verifyPassword (risk : SecretRisk) (cipher : CtrCipher) (ks : Keystore)
    (password plain : ByteArray) (h : decrypt risk cipher ks password = .ok plain) :
    verifyPassword risk ks password = .ok () := by
  have ⟨hh, dk, hk, hm⟩ := decrypt_ok_mac risk cipher ks password plain h
  exact (verifyPassword_ok_iff risk ks password dk hh hk).mpr hm

/-- Kind: refusal (no cipher in the tree).
    Says: with `CtrCipher.unavailable`, `decryptWithKey` answers
    `.error .cipherUnavailable` when the MAC matches and `.error .macMismatch`
    when it does not.
    Does not say: anything about other providers. -/
theorem decryptWithKey_unavailable (risk : SecretRisk) (dk : ByteArray) (ks : Keystore) :
    decryptWithKey risk CtrCipher.unavailable dk ks =
      if macMatches dk ks = true then .error .cipherUnavailable else .error .macMismatch := by
  cases hm : macMatches dk ks <;>
    simp [decryptWithKey, applyCipher, CtrCipher.unavailable, hm]

/-- Kind: refusal (no cipher in the tree).
    Says: with `CtrCipher.unavailable`, a keystore whose header, key derivation
    and MAC all pass is answered `.error .cipherUnavailable`.
    Does not say: anything about other providers. -/
theorem decrypt_unavailable (risk : SecretRisk) (ks : Keystore) (password dk : ByteArray)
    (hh : checkHeader ks = .ok ()) (hk : deriveKey risk ks.kdf password = .ok dk)
    (hm : macMatches dk ks = true) :
    decrypt risk CtrCipher.unavailable ks password = .error .cipherUnavailable := by
  simp [decrypt, hh, hk, decryptWithKey_unavailable, hm]

/-- Kind: refusal (no cipher in the tree).
    Says: with `CtrCipher.unavailable`, `decrypt` never answers `.ok`: no
    plaintext is produced by the code in this repository.
    Does not say: which error is given (see `decrypt_unavailable`,
    `decrypt_unavailable_passed`). -/
theorem decrypt_unavailable_never_ok (risk : SecretRisk) (ks : Keystore)
    (password plain : ByteArray) :
    decrypt risk CtrCipher.unavailable ks password ≠ .ok plain := by
  intro h
  have ⟨hh, dk, hk, hm⟩ := decrypt_ok_mac risk CtrCipher.unavailable ks password plain h
  rw [decrypt_unavailable risk ks password dk hh hk hm] at h
  cases h

theorem checkHeader_ne_cipherUnavailable (ks : Keystore) :
    checkHeader ks ≠ .error .cipherUnavailable := by
  unfold checkHeader
  by_cases h1 : ks.version ≠ 3
  · rw [if_pos h1]; intro h; cases h
  · rw [if_neg h1]
    by_cases h2 : ks.cipher ≠ "aes-128-ctr"
    · rw [if_pos h2]; intro h; cases h
    · rw [if_neg h2]
      by_cases h3 : ks.iv.size ≠ 16
      · rw [if_pos h3]; intro h; cases h
      · rw [if_neg h3]; intro h; cases h

theorem deriveKey_ne_cipherUnavailable (risk : SecretRisk) (kdf : Kdf) (password : ByteArray) :
    deriveKey risk kdf password ≠ .error .cipherUnavailable := by
  cases kdf with
  | scrypt n r p dkLen salt =>
    cases hc : (ScryptParams.mk n r p dkLen).check with
    | error e => simp [deriveKey, hc]
    | ok u =>
      cases u
      by_cases hd : dkLen < 32
      · simp [deriveKey, hc, hd]
      · cases hs : Keys.scrypt risk password salt ⟨n, r, p, dkLen⟩ <;>
          simp [deriveKey, hc, hd, hs]
  | pbkdf2 c dkLen prf salt =>
    by_cases h1 : prf ≠ "hmac-sha256"
    · simp [deriveKey, h1]
    · by_cases h2 : dkLen < 32 ∨ pbkdf2MaxDkLen < dkLen
      · simp only [deriveKey, if_neg h1, if_pos h2]; intro h; cases h
      · by_cases h3 : c = 0 ∨ pbkdf2MaxIterations < c
        · simp only [deriveKey, if_neg h1, if_neg h2, if_pos h3]; intro h; cases h
        · simp only [deriveKey, if_neg h1, if_neg h2, if_neg h3]
          by_cases h4 : (Pbkdf2.raw (HmacKey.ofSha256 password).mac256 32 salt c dkLen).size = dkLen
          · rw [if_pos h4]; intro h; cases h
          · rw [if_neg h4]; intro h; cases h
  | other name => intro h; cases h

/-- Kind: refusal (no cipher in the tree), converse.
    Says: with `CtrCipher.unavailable`, the answer `.error .cipherUnavailable`
    is given only when the header was accepted, the key derived and the MAC
    matched: it is given exactly to a correct password on a well-formed keystore.
    Does not say: that a matching MAC proves the password (tested, not proved). -/
theorem decrypt_unavailable_passed (risk : SecretRisk) (ks : Keystore) (password : ByteArray)
    (h : decrypt risk CtrCipher.unavailable ks password = .error .cipherUnavailable) :
    checkHeader ks = .ok () ∧
      ∃ dk, deriveKey risk ks.kdf password = .ok dk ∧ macMatches dk ks = true := by
  cases hh : checkHeader ks with
  | error e =>
    have : e = .cipherUnavailable := by simpa [decrypt, hh] using h
    rw [this] at hh
    exact absurd hh (checkHeader_ne_cipherUnavailable ks)
  | ok u =>
    cases u
    refine ⟨rfl, ?_⟩
    cases hk : deriveKey risk ks.kdf password with
    | error e =>
      have : e = .cipherUnavailable := by simpa [decrypt, hh, hk] using h
      rw [this] at hk
      exact absurd hk (deriveKey_ne_cipherUnavailable risk ks.kdf password)
    | ok dk =>
      refine ⟨dk, rfl, ?_⟩
      cases hm : macMatches dk ks with
      | true => rfl
      | false => simp [decrypt, hh, hk, decryptWithKey_mac_mismatch risk _ dk ks hm] at h

/-- Kind: refusal (no cipher in the tree).
    Says: with `CtrCipher.unavailable`, `encrypt` answers
    `.error .cipherUnavailable` for every input, before any key derivation.
    Does not say: anything about other providers. -/
theorem encrypt_unavailable (risk : SecretRisk) (secret password iv : ByteArray) (kdf : Kdf)
    (address id : Option String) :
    encrypt risk CtrCipher.unavailable secret password iv kdf address id
      = .error .cipherUnavailable := by
  simp [encrypt, CtrCipher.unavailable]

/-- Kind: refusal.
    Says: a provider that is not available yields `.error .cipherUnavailable`
    from `applyCipher`; its `apply` is not called.
    Does not say: anything else. -/
theorem applyCipher_unavailable (cipher : CtrCipher) (key iv data : ByteArray)
    (h : cipher.available = false) :
    applyCipher cipher key iv data = .error .cipherUnavailable := by
  unfold applyCipher
  rw [if_pos h]

/-- Kind: provider check.
    Says: an `.ok` from `applyCipher` means the provider was available,
    answered, and its answer has the length of the data.
    Does not say: that the answer is the right cipher's output. -/
theorem applyCipher_ok (cipher : CtrCipher) (key iv data out : ByteArray)
    (h : applyCipher cipher key iv data = .ok out) :
    cipher.available = true ∧ cipher.apply key iv data = some out ∧ out.size = data.size := by
  unfold applyCipher at h
  by_cases ha : cipher.available = false
  · rw [if_pos ha] at h; cases h
  · rw [if_neg ha] at h
    cases hc : cipher.apply key iv data with
    | none => rw [hc] at h; cases h
    | some o =>
      rw [hc] at h
      by_cases hs : o.size = data.size
      · have ho : o = out := by simpa [hs] using h
        subst ho
        exact ⟨by simpa using ha, rfl, hs⟩
      · simp [hs] at h

/-- Kind: refusal.
    Says: a version other than 3 is refused before any other work.
    Does not say: anything about version 3 files. -/
theorem decrypt_refuses_version (risk : SecretRisk) (cipher : CtrCipher) (ks : Keystore)
    (password : ByteArray) (h : ks.version ≠ 3) :
    decrypt risk cipher ks password = .error .unsupportedVersion := by
  simp [decrypt, checkHeader, h]

/-- Kind: refusal.
    Says: a version 3 file with a cipher name other than `aes-128-ctr` is refused.
    Does not say: anything else. -/
theorem decrypt_refuses_cipher (risk : SecretRisk) (cipher : CtrCipher) (ks : Keystore)
    (password : ByteArray) (hv : ks.version = 3)
    (h : ks.cipher ≠ "aes-128-ctr") :
    decrypt risk cipher ks password = .error .unsupportedCipher := by
  simp [decrypt, checkHeader, hv, h]

/-- Kind: refusal.
    Says: with version and cipher name accepted, an IV that is not 16 bytes is
    refused before key derivation.
    Does not say: anything else. -/
theorem decrypt_refuses_iv (risk : SecretRisk) (cipher : CtrCipher) (ks : Keystore)
    (password : ByteArray) (hv : ks.version = 3)
    (hc : ks.cipher = "aes-128-ctr") (h : ks.iv.size ≠ 16) :
    decrypt risk cipher ks password = .error .badIvLength := by
  simp [decrypt, checkHeader, hv, hc, h]

/-- Kind: refusal.
    Says: an unknown KDF name derives no key.
    Does not say: anything else. -/
theorem deriveKey_refuses_other (risk : SecretRisk) (name : String) (password : ByteArray) :
    deriveKey risk (.other name) password = .error .unsupportedKdf := rfl

/-- Kind: refusal.
    Says: PBKDF2 with a PRF other than `hmac-sha256` derives no key.
    Does not say: anything else. -/
theorem deriveKey_refuses_prf (risk : SecretRisk) (c dkLen : Nat) (prf : String)
    (salt password : ByteArray) (h : prf ≠ "hmac-sha256") :
    deriveKey risk (.pbkdf2 c dkLen prf salt) password = .error .unsupportedPrf := by
  simp [deriveKey, h]

/-- Kind: refusal.
    Says: PBKDF2 with `dklen` below 32 derives no key.
    Does not say: anything else. -/
theorem deriveKey_pbkdf2_refuses_dkLen (risk : SecretRisk) (c dkLen : Nat)
    (salt password : ByteArray) (h : dkLen < 32) :
    deriveKey risk (.pbkdf2 c dkLen "hmac-sha256" salt) password = .error .badDkLen := by
  simp [deriveKey, h]

/-- Kind: refusal.
    Says: PBKDF2 with an accepted `dklen` and an iteration count of zero or
    above `pbkdf2MaxIterations` derives no key (a work bound).
    Does not say: how long an accepted count takes. -/
theorem deriveKey_pbkdf2_refuses_iterations (risk : SecretRisk) (c dkLen : Nat)
    (salt password : ByteArray)
    (hd : ¬(dkLen < 32 ∨ pbkdf2MaxDkLen < dkLen)) (h : c = 0 ∨ pbkdf2MaxIterations < c) :
    deriveKey risk (.pbkdf2 c dkLen "hmac-sha256" salt) password = .error .badIterations := by
  simp only [deriveKey, ne_eq, not_true_eq_false, if_false, if_neg hd, if_pos h]

/-- Kind: resource refusal.
    Says: a failed scrypt parameter check is `deriveKey`'s answer, before any
    derivation work.
    Does not say: which check failed. -/
theorem deriveKey_scrypt_check_error (risk : SecretRisk) (n r p dkLen : Nat)
    (salt password : ByteArray)
    (e : ScryptError) (h : (ScryptParams.mk n r p dkLen).check = .error e) :
    deriveKey risk (.scrypt n r p dkLen salt) password = .error (.scrypt e) := by
  simp [deriveKey, h]

/-- Kind: resource refusal.
    Says: scrypt parameters needing more than `scryptMaxBytes` derive no key:
    the answer is `.error (.scrypt .memoryLimit)`, before any allocation.
    Does not say: that the limit suits a given machine. -/
theorem deriveKey_scrypt_over_limit (risk : SecretRisk) (n r p dkLen : Nat)
    (salt password : ByteArray)
    (h : scryptMaxBytes < 128 * r * n + 128 * r * p) :
    deriveKey risk (.scrypt n r p dkLen salt) password = .error (.scrypt .memoryLimit) :=
  deriveKey_scrypt_check_error risk n r p dkLen salt password .memoryLimit
    (check_over_limit _ (by simpa [ScryptParams.memoryBytes] using h))

/-- Kind: refusal.
    Says: scrypt with accepted cost parameters and `dklen` below 32 derives no key.
    Does not say: anything else. -/
theorem deriveKey_scrypt_refuses_dkLen (risk : SecretRisk) (n r p dkLen : Nat)
    (salt password : ByteArray)
    (hc : (ScryptParams.mk n r p dkLen).check = .ok ()) (h : dkLen < 32) :
    deriveKey risk (.scrypt n r p dkLen salt) password = .error .badDkLen := by
  simp [deriveKey, hc, h]

/-- Kind: resource refusal.
    Says: `decrypt` on an accepted header with over-limit scrypt parameters
    answers `.error (.scrypt .memoryLimit)`, for every provider.
    Does not say: anything about parameters within the limit. -/
theorem decrypt_scrypt_over_limit (risk : SecretRisk) (cipher : CtrCipher) (ks : Keystore)
    (password salt : ByteArray) (n r p dkLen : Nat)
    (hh : checkHeader ks = .ok ()) (hk : ks.kdf = .scrypt n r p dkLen salt)
    (h : scryptMaxBytes < 128 * r * n + 128 * r * p) :
    decrypt risk cipher ks password = .error (.scrypt .memoryLimit) := by
  simp [decrypt, hh, hk, deriveKey_scrypt_over_limit risk n r p dkLen salt password h]

/-- Kind: resource refusal.
    Says: the same for `verifyPassword`.
    Does not say: anything about parameters within the limit. -/
theorem verifyPassword_scrypt_over_limit (risk : SecretRisk) (ks : Keystore)
    (password salt : ByteArray) (n r p dkLen : Nat)
    (hh : checkHeader ks = .ok ()) (hk : ks.kdf = .scrypt n r p dkLen salt)
    (h : scryptMaxBytes < 128 * r * n + 128 * r * p) :
    verifyPassword risk ks password = .error (.scrypt .memoryLimit) := by
  simp [verifyPassword, hh, hk, deriveKey_scrypt_over_limit risk n r p dkLen salt password h]

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

/-- Kind: round trip, conditional on the provider.
    Says: IF the provider undoes itself (applying it to its own length-keeping
    output under the same key and IV gives the input back, as a counter-mode
    cipher does), then a keystore made by `encryptWithKey` under a derived key
    decrypts under the same key to the same secret: the MAC it stored matches.
    Does not say: that any provider has that property. No provider in the tree
    does (`CtrCipher.unavailable` never answers), so in the tree this theorem
    is about the plumbing only; nor does it say anything about the JSON text. -/
theorem decryptWithKey_encryptWithKey (risk : SecretRisk) (cipher : CtrCipher)
    (hinv : ∀ key iv data out : ByteArray, cipher.apply key iv data = some out →
      out.size = data.size → cipher.apply key iv out = some data)
    (dk secret iv : ByteArray) (kdf : Kdf)
    (address id : Option String) (ks : Keystore)
    (h : encryptWithKey risk cipher dk secret iv kdf address id = .ok ks) :
    decryptWithKey risk cipher dk ks = .ok secret := by
  cases hx : applyCipher cipher (dk.extract 0 16) iv secret with
  | error e => simp [encryptWithKey, hx] at h
  | ok ct =>
    simp only [encryptWithKey, hx] at h
    cases h
    have ⟨ha, hap, hsz⟩ := applyCipher_ok cipher _ _ _ _ hx
    have hback := hinv _ _ _ _ hap hsz
    simp [decryptWithKey, macMatches, ctEqBytes_self, applyCipher, ha, hback, hsz]

/-- Kind: refusal.
    Says: with an available provider, `encrypt` refuses an IV that is not 16
    bytes, for an accepted secret length.
    Does not say: that a 16-byte IV is fresh. -/
theorem encrypt_refuses_iv (risk : SecretRisk) (cipher : CtrCipher) (secret password iv : ByteArray)
    (kdf : Kdf) (address id : Option String) (ha : cipher.available = true)
    (hs : ¬(secret.size = 0 ∨ maxSecretBytes < secret.size)) (h : iv.size ≠ 16) :
    encrypt risk cipher secret password iv kdf address id = .error .badIvLength := by
  unfold encrypt
  rw [if_neg (by simp [ha]), if_neg hs, if_pos h]

/-- Kind: refusal.
    Says: with an available provider, `encrypt` refuses an empty secret or one
    above `maxSecretBytes`.
    Does not say: anything else. -/
theorem encrypt_refuses_secret (risk : SecretRisk) (cipher : CtrCipher)
    (secret password iv : ByteArray) (kdf : Kdf)
    (address id : Option String) (ha : cipher.available = true)
    (h : secret.size = 0 ∨ maxSecretBytes < secret.size) :
    encrypt risk cipher secret password iv kdf address id = .error .badSecretLength := by
  unfold encrypt
  rw [if_neg (by simp [ha]), if_pos h]

end EthereumWallet.Keys
