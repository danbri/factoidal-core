/-
L4Factoidal.Crypto.AesGcmNative — AES-128-GCM and AES-256-GCM on native
x86-64 executables, through HACL*'s EverCrypt AEAD over the Vale verified
assembly. A member of the tree's `@[extern]` crypto family
(`Crypto/Ed25519.lean`, `Crypto/SHA2Native.lean`, `Crypto/P256Native.lean`,
`Crypto/RsaNative.lean`, `Crypto/ChaChaPoly.lean` are the others).

Issue: https://github.com/danbri/factoidal/issues/677 (AES-GCM).
Consumers to come: XML Encryption 1.1 and JWE,
https://github.com/danbri/factoidal/issues/1081. They take AES as a
PARAMETER (`Crypto/Aead.lean`, `AeadOps`); `nativeOps` below is the native
instance, and a WebCrypto instance serves the JavaScript hosts.

## Owner decision

Owner, 2026-10-27, verbatim: "Ok for now: “My proposal is HACL* Vale on
x86-64 and a refusal on other CPU”". So:

  * x86-64 Linux and macOS executables link `EverCrypt_AEAD.c` and the Vale
    `aesgcm-x86_64-{linux,darwin}.S` of the pinned HACL* distribution
    (cryspen/hacl-packages 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2,
    `third_party/hacl/PROVENANCE.md`). At run time the CPU must have AES-NI,
    PCLMULQDQ, AVX, SSE and MOVBE (the five features EverCrypt tests); a CPU
    without them refuses.
  * Every other target, the wasm32 module included, compiles
    `ffi/hacl_aesgcm.c` to stubs: `available = false` and every call is
    refused with `refusalMessage`, which names issue 677. On JavaScript
    hosts AES is WebCrypto (`skills/crypto-policy/SKILL.md`, section "AES
    through WebCrypto"), never this module.

## Trust statement

`encryptRaw`, `decryptRaw` and `availableRaw` are `opaque`s: Lean knows
their TYPE and nothing about their VALUE. NO THEOREM IN THIS TREE DEPENDS ON
WHAT THEY COMPUTE.

What is trusted:

  * AES-GCM as implemented by Vale (x86-64 assembly proved functionally
    correct against an F* specification of AES and GCM, and free of
    secret-dependent branches and memory accesses, by Project Everest), and
    EverCrypt's agile AEAD layer around it (KaRaMeL-extracted C), both
    vendored unmodified.
  * `EverCrypt_AutoConfig2.c` with the Vale `cpuid` assembly, for the CPU
    feature test.
  * `ffi/hacl_aesgcm.c`: length checks, the choice of algorithm by key
    length, one pointer offset for the `ciphertext || tag` split, a
    `memset` of the output on a failed tag. No AES or GCM arithmetic, no tag
    comparison.
  * `ffi/hacl_vale_config/config.h`: the HACL* CMake configuration header,
    filled in by hand (`HACL_CAN_COMPILE_VALE` on x86-64 only).

What is NOT checked here:

  * IV REUSE. Two encryptions under one (key, IV) pair destroy GCM's
    confidentiality and authentication. This module holds no state; the
    protocol layer that makes IVs owns that rule.
  * AES-192-GCM. XML Encryption 1.1 lists `aes192-gcm` and JWE lists
    `A192GCM`; EverCrypt has no AES-192, so a 24-byte key is refused.
  * IV lengths other than 12 bytes and tags shorter than 16 bytes. XML
    Encryption 1.1 (section 5.2.4) and JWE (RFC 7518 section 5.3) use a
    96-bit IV and a 128-bit tag only.

A `#guard` cannot check any of this, because the interpreter cannot call an
`@[extern]`. `lake exe l4crypto-probe`, section `aes-gcm`, runs the
McGrew–Viega GCM test cases 1–4 and 13–16 and the Wycheproof
`aes_gcm_test.json` vectors with 96-bit IVs and 128- and 256-bit keys.
-/
import L4Factoidal.Crypto.Aead

namespace L4Factoidal.Crypto.AesGcmNative

open L4Factoidal.Crypto.Aead

/-- The tracking issue, named by every refusal. -/
def issueUrl : String := "https://github.com/danbri/factoidal/issues/677"

/-- IV length in bytes: 96 bits (NIST SP 800-38D section 5.2.1.1). -/
def ivBytes : Nat := 12

/-- Tag length in bytes: 128 bits. -/
def tagBytes : Nat := 16

/-- Key lengths in bytes: AES-128 and AES-256. -/
def keyLengths : List Nat := [16, 32]

/-- `true` when this executable has the Vale AES-GCM AND the CPU has the
instructions it needs. Always `false` off x86-64 and in the wasm module. -/
@[extern "l4_hacl_aesgcm_available"]
opaque availableRaw (u : Unit) : Bool

/-- Raw encrypt: `ciphertext || tag`, or the EMPTY `ByteArray` on a
refusal. Prefer `aesGcmEncrypt?`. -/
@[extern "l4_hacl_aesgcm_encrypt"]
opaque encryptRaw (key : @& ByteArray) (iv : @& ByteArray) (aad : @& ByteArray)
    (plain : @& ByteArray) : ByteArray

/-- Raw decrypt: `plaintext || status`, where `status` (the last byte) is
`1` for an authenticated decryption and `0` for a failed tag; or the EMPTY
`ByteArray` on a refusal. Prefer `aesGcmDecrypt?`. -/
@[extern "l4_hacl_aesgcm_decrypt"]
opaque decryptRaw (key : @& ByteArray) (iv : @& ByteArray) (aad : @& ByteArray)
    (ct : @& ByteArray) : ByteArray

/-- Whether native AES-GCM runs here (see `availableRaw`). -/
def available : Bool := availableRaw ()

/-- The lengths this module accepts, decided in Lean. -/
def lengthsOk (key iv : ByteArray) : Bool :=
  keyLengths.contains key.size && iv.size == ivBytes

/-- AES-GCM encryption (NIST SP 800-38D): `some (ciphertext || tag)`, 16 bytes
longer than `plain`, when the key is 16 or 32 bytes, the IV is 12 bytes and
`available`; `none` otherwise. -/
def aesGcmEncrypt? (key iv aad plain : ByteArray) : Option ByteArray :=
  if !lengthsOk key iv || !available then none
  else
    let out := encryptRaw key iv aad plain
    if out.size = plain.size + tagBytes then some out else none

/-- AES-GCM authenticated decryption: `some plain` only when the tag
authenticates; `none` on a refused length, on a failed tag and when not
`available`. The caller cannot tell these apart, because none of them gives a
plaintext. -/
def aesGcmDecrypt? (key iv aad ctWithTag : ByteArray) : Option ByteArray :=
  if !lengthsOk key iv || ctWithTag.size < tagBytes || !available then none
  else
    let raw := decryptRaw key iv aad ctWithTag
    let n := ctWithTag.size - tagBytes
    if raw.size ≠ n + 1 then none
    else if raw.get! n ≠ 1 then none
    else some (raw.extract 0 n)

/-- The refusal on a target without native AES-GCM. -/
def refusalMessage : String :=
  "AES-GCM is not available in this executable: native AES-GCM is HACL* Vale " ++
  "assembly for x86-64 only, and it needs a CPU with AES-NI, PCLMULQDQ, AVX, SSE " ++
  "and MOVBE; on other CPUs AES is refused. JavaScript hosts use WebCrypto. " ++
  s!"See {issueUrl}"

/-- The native instance of `AeadOps`. When `available` is false this IS
`AeadOps.unavailable` (every call answers `refusalMessage`). -/
def nativeOps : AeadOps :=
  if available then
    { name := "AES-GCM (HACL* Vale, x86-64)"
      keyLengths := keyLengths
      ivLengths := [ivBytes]
      tagBytes := tagBytes
      available := true
      encrypt := fun key iv aad plain =>
        if !lengthsOk key iv then
          .error "AES-GCM: refused: the key must be 16 or 32 bytes and the IV 12 bytes"
        else match aesGcmEncrypt? key iv aad plain with
          | some out => .ok out
          | none => .error "AES-GCM: encryption refused"
      decrypt := fun key iv aad ct =>
        match aesGcmDecrypt? key iv aad ct with
        | some p => .ok p
        | none => .error "AES-GCM: decryption failed" }
  else
    AeadOps.unavailable "AES-GCM (HACL* Vale, x86-64)" keyLengths [ivBytes] tagBytes
      refusalMessage

end L4Factoidal.Crypto.AesGcmNative
