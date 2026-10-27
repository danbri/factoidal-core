/-
L4Factoidal.Crypto.Aead — an authenticated encryption scheme with associated
data (AEAD, RFC 5116), as a PARAMETER.

XML Encryption 1.1 and JWE take their AES-GCM through this structure, so
the code that builds and reads `EncryptedData` or a JWE compact
serialisation never names an implementation. Two instances are planned
(https://github.com/danbri/factoidal/issues/677 and
https://github.com/danbri/factoidal/issues/1081):

  * native x86-64: HACL* Vale AES-GCM, `Crypto/AesGcmNative.lean`
    (`AesGcmNative.nativeOps`);
  * JavaScript hosts: WebCrypto `SubtleCrypto`, through the host's
    request-and-resume step (`skills/crypto-policy/SKILL.md`, section "AES
    through WebCrypto"). Not in this module.

This module is pure: no `@[extern]`, no `IO`. The decisions that belong to
the protocol (which algorithm, which key and IV lengths, what to do on a
failure) stay with the caller; an `AeadOps` only runs the cipher.

## Contract an instance must meet

  * `encrypt key iv aad plain` → `.ok (ciphertext || tag)`, where the tag is
    `tagBytes` long and appended (the layout of RFC 5116 section 5.1, XML
    Encryption 1.1 section 5.2.4 and JWE's `ciphertext` plus `tag`), or
    `.error msg` on any refusal.
  * `decrypt key iv aad (ciphertext || tag)` → `.ok plain` only when the tag
    authenticates; `.error msg` otherwise. An instance gives no plaintext for
    a failed tag, and gives the same kind of answer for a refused length, a
    failed tag and an unavailable cipher: no plaintext.
  * `available = false` means every call answers `.error`. That is a fact an
    instance states about itself; the theorem `unavailable_encrypt` below
    proves it for the refusing instance, and the native instance is checked
    at run time by `lake exe l4crypto-probe` (section `aes-gcm`), because the
    native functions are `opaque`.
-/

namespace L4Factoidal.Crypto.Aead

/-- One AEAD: its name, the key and IV lengths in bytes it accepts, its tag
length in bytes, whether this build can run it, and the two operations. -/
structure AeadOps where
  name : String
  keyLengths : List Nat
  ivLengths : List Nat
  tagBytes : Nat
  available : Bool
  encrypt : (key iv aad plain : ByteArray) → Except String ByteArray
  decrypt : (key iv aad ctWithTag : ByteArray) → Except String ByteArray

/-- An AEAD this build cannot run: every call answers `.error msg`. The
message names the reason and its tracking issue. -/
def AeadOps.unavailable (name : String) (keyLengths ivLengths : List Nat)
    (tagBytes : Nat) (msg : String) : AeadOps where
  name := name
  keyLengths := keyLengths
  ivLengths := ivLengths
  tagBytes := tagBytes
  available := false
  encrypt := fun _ _ _ _ => .error msg
  decrypt := fun _ _ _ _ => .error msg

theorem unavailable_encrypt (name : String) (ks is : List Nat) (t : Nat) (msg : String)
    (key iv aad plain : ByteArray) :
    (AeadOps.unavailable name ks is t msg).encrypt key iv aad plain = .error msg := rfl

theorem unavailable_decrypt (name : String) (ks is : List Nat) (t : Nat) (msg : String)
    (key iv aad ct : ByteArray) :
    (AeadOps.unavailable name ks is t msg).decrypt key iv aad ct = .error msg := rfl

theorem unavailable_available (name : String) (ks is : List Nat) (t : Nat) (msg : String) :
    (AeadOps.unavailable name ks is t msg).available = false := rfl

/-- The lengths an instance states it accepts, as one test. A caller (XML
Encryption, JWE) checks this before it calls the instance, so the refusal of
a wrong length is decided in Lean, the same on every host. -/
def AeadOps.accepts (ops : AeadOps) (key iv : ByteArray) : Bool :=
  ops.keyLengths.contains key.size && ops.ivLengths.contains iv.size

end L4Factoidal.Crypto.Aead
