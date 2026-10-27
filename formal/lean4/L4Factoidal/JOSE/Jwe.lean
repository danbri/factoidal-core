/-
L4Factoidal.JOSE.Jwe — JSON Web Encryption (RFC 7516), Compact
Serialization, decryption and encryption, with an algorithm allowlist that
is decided before any key is read
(https://github.com/danbri/factoidal/issues/1085; design record
`docs/designissues/2026-10-27-xml-encryption-and-jwe.md`, section "JWE
profile").

## The allowlist, before the key

`jwePreKey` splits the five parts, decodes and parses the protected header,
and then decides from fixed tables, in this order:

  * `crit` present: refused. This module understands no extension, and RFC
    7516 §4.1.13 (by reference to RFC 7515 §4.1.11) requires a recipient to
    reject a JWE whose `crit` names one it does not understand.
  * `zip` present: refused. Compression before encryption makes the
    ciphertext length depend on the plaintext; with attacker-chosen content
    beside a secret that is the CRIME and BREACH compression side channel.
  * `alg` in `RSA-OAEP`, `RSA-OAEP-256`, `ECDH-ES`, `ECDH-ES+A128KW`,
    `ECDH-ES+A256KW`, `A128KW`, `A256KW`, `dir`. Every other value is
    refused, `RSA1_5` (Bleichenbacher 1998) and the `PBES2-*` family
    included (`keyAlg_refused`).
  * `enc` in `A128GCM`, `A256GCM`, `A128CBC-HS256`, `A256CBC-HS512`.

The key, the cipher and the RSA, P-256 and X25519 operations are not
arguments of `jwePreKey`. `decrypt_independent_of_key_before_key_stage`
states that a token refused there gives the same answer for every key,
every cipher and every set of primitives; it is the JWE form of
`JOSE.verify_independent_of_key_before_key_stage`.

## One error after the allowlist

After the allowlist every failure is `Err.decryptionFailed`, with no
reason: a wrong key type, a bad part encoding, an `epk` off the curve, a
failed key unwrap, a wrong CEK length, a MAC or tag mismatch, a refusal by
the host's cipher. The post-key stage returns `Fail`, which has no refusal
constructor, so `decrypt_refused_only_pre_key` holds by the types: a
`.refused` answer always comes from the allowlist stage.

RFC 7516 §11.5: an RSA-OAEP decryption that fails, or gives a CEK of the
wrong length, continues with a substitute CEK (`substituteCek`, an HMAC of
the private exponent and the encrypted key), so the failure shows only at
the content tag, the same as a tag failure.

## AES is a request

Every AES operation is a `CipherCall.Req` answered by a `Cipher`
(`Crypto/CipherCall.lean`). `.need r` from the cipher reaches the caller
unchanged (`Fail.need`, `Err.need`); the wasm op returns it to the host,
which answers with WebCrypto and calls again. The CBC-HMAC algorithms
(RFC 7518 §5.2.2.2) check the MAC in Lean BEFORE the decryption request,
in constant time (`Crypto.ctEqBytes`); `cbc_mac_failure_makes_no_request`
states that a MAC failure gives `failed` for every cipher, so no request is
made.

## Primitives as a parameter

RSA, P-256 ECDH and X25519 arrive in a `Prims` record, as the signature
primitives of `JOSE/Jws.lean` arrive in `Verifiers`. The theorems hold for
every record; `nativePrims` is the HACL* instance, and `JOSE/JweTests.lean`
checks the structure with stubs.

## ECDH-ES (RFC 7518 §4.6)

`epk` is a public P-256 or X25519 key (`JweKey.parseEpk?`); the HACL*
operations refuse a point off the curve. The Concat KDF AlgorithmID is the
`enc` value for direct `ECDH-ES` and the `alg` value for the key-wrapping
forms (§4.6.2); `apu` and `apv` are base64url header members, empty when
absent.

## Nested JWT (RFC 7519 §5.2)

`decryptThenVerify` decrypts, requires `cty` `JWT`, and gives the inner JWS
to `JOSE.verifyCompact`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.JOSE.Jws
import L4Factoidal.JOSE.JweKey
import L4Factoidal.Crypto.CipherCall
import L4Factoidal.Crypto.RsaOaep
import L4Factoidal.Crypto.P256Native
import L4Factoidal.Crypto.X25519
import L4Factoidal.Crypto.ConcatKdf
import L4Factoidal.Crypto.Hmac
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.JOSE.Jwe

open L4Factoidal.JSON
open L4Factoidal.JOSE.JweKey
open L4Factoidal.Crypto
open L4Factoidal.Crypto.CipherCall (Cipher Req Op)

/-! ## Algorithms -/

/-- The key management algorithms (RFC 7518 §4.1) this module accepts. -/
inductive KeyAlg where
  | rsaOaep
  | rsaOaep256
  | ecdhEs
  | ecdhEsA128kw
  | ecdhEsA256kw
  | a128kw
  | a256kw
  | dir
  deriving DecidableEq, Repr, BEq

def KeyAlg.name : KeyAlg → String
  | .rsaOaep => "RSA-OAEP"
  | .rsaOaep256 => "RSA-OAEP-256"
  | .ecdhEs => "ECDH-ES"
  | .ecdhEsA128kw => "ECDH-ES+A128KW"
  | .ecdhEsA256kw => "ECDH-ES+A256KW"
  | .a128kw => "A128KW"
  | .a256kw => "A256KW"
  | .dir => "dir"

/-- **The `alg` allowlist.** A closed match with a `none` default. -/
def keyAlgOfString? : String → Option KeyAlg
  | "RSA-OAEP" => some .rsaOaep
  | "RSA-OAEP-256" => some .rsaOaep256
  | "ECDH-ES" => some .ecdhEs
  | "ECDH-ES+A128KW" => some .ecdhEsA128kw
  | "ECDH-ES+A256KW" => some .ecdhEsA256kw
  | "A128KW" => some .a128kw
  | "A256KW" => some .a256kw
  | "dir" => some .dir
  | _ => none

/-- The content encryption algorithms (RFC 7518 §5.1) this module accepts. -/
inductive EncAlg where
  | a128gcm
  | a256gcm
  | a128cbcHs256
  | a256cbcHs512
  deriving DecidableEq, Repr, BEq

def EncAlg.name : EncAlg → String
  | .a128gcm => "A128GCM"
  | .a256gcm => "A256GCM"
  | .a128cbcHs256 => "A128CBC-HS256"
  | .a256cbcHs512 => "A256CBC-HS512"

/-- **The `enc` allowlist.** -/
def encAlgOfString? : String → Option EncAlg
  | "A128GCM" => some .a128gcm
  | "A256GCM" => some .a256gcm
  | "A128CBC-HS256" => some .a128cbcHs256
  | "A256CBC-HS512" => some .a256cbcHs512
  | _ => none

/-- CEK length in octets (RFC 7518 §5.2.3, §5.2.5, §5.3). -/
def EncAlg.cekBytes : EncAlg → Nat
  | .a128gcm => 16
  | .a256gcm => 32
  | .a128cbcHs256 => 32
  | .a256cbcHs512 => 64

/-- IV length in octets: 96 bits for GCM (RFC 7518 §5.3), 128 for CBC
(§5.2.2.1). -/
def EncAlg.ivBytes : EncAlg → Nat
  | .a128gcm | .a256gcm => 12
  | .a128cbcHs256 | .a256cbcHs512 => 16

/-- Authentication tag length in octets: 16, except 32 for `A256CBC-HS512`
(RFC 7518 §5.2.5). -/
def EncAlg.tagBytes : EncAlg → Nat
  | .a256cbcHs512 => 32
  | _ => 16

def EncAlg.isCbc : EncAlg → Bool
  | .a128cbcHs256 | .a256cbcHs512 => true
  | _ => false

/-! ## Compact serialisation and the stage before the key -/

/-- The five parts of a JWE Compact Serialization (RFC 7516 §7.1), still
base64url, and the Additional Authenticated Data
`ASCII(BASE64URL(UTF8(JWE Protected Header)))` (§5.1 step 14). -/
structure Compact where
  headerB64 : String
  ekB64 : String
  ivB64 : String
  ctB64 : String
  tagB64 : String
  aad : ByteArray

/-- The refusals decided from the token alone, before any key is read. -/
inductive Refusal where
  | notFiveParts
  | headerNotBase64Url
  | headerNotUtf8
  | headerNotJson
  | headerNotObject
  | criticalHeaderUnsupported
  | compressionRefused
  | algMissing
  | algNotAllowed (alg : String)
  | encMissing
  | encNotAllowed (enc : String)
  deriving DecidableEq, Repr, BEq

def Refusal.message : Refusal → String
  | .notFiveParts => "a JWE compact serialization has five parts"
  | .headerNotBase64Url => "the protected header is not base64url"
  | .headerNotUtf8 => "the protected header is not UTF-8"
  | .headerNotJson => "the protected header is not JSON"
  | .headerNotObject => "the protected header is not a JSON object"
  | .criticalHeaderUnsupported => "crit is refused: no JWE extension is understood"
  | .compressionRefused => "zip is refused (compression side channel)"
  | .algMissing => "the protected header has no alg"
  | .algNotAllowed a => s!"alg \"{a}\" is not allowed"
  | .encMissing => "the protected header has no enc"
  | .encNotAllowed e => s!"enc \"{e}\" is not allowed"

/-- The protected header and the two algorithms it names. -/
structure Header where
  alg : KeyAlg
  enc : EncAlg
  json : Json

/-- RFC 7516 §7.1: exactly five parts. The header, the IV and the tag are
never empty; the encrypted key is empty for `dir` and `ECDH-ES`, and the
ciphertext is empty for an empty plaintext under GCM. -/
def splitCompact? (token : String) : Option Compact :=
  match token.splitOn "." with
  | [h, k, i, c, t] =>
      if h.isEmpty || i.isEmpty || t.isEmpty then none
      else some { headerB64 := h, ekB64 := k, ivB64 := i, ctB64 := c, tagB64 := t,
                  aad := h.toUTF8 }
  | _ => none

/-- Split, decode, parse, check `crit` and `zip`, resolve `alg` and `enc`
against the allowlists. THE KEY IS NOT AN ARGUMENT. -/
def jwePreKey (token : String) : Except Refusal (Compact × Header) :=
  match splitCompact? token with
  | none => .error .notFiveParts
  | some c =>
      match Base64Url.decode c.headerB64 with
      | none => .error .headerNotBase64Url
      | some raw =>
          match String.fromUTF8? raw with
          | none => .error .headerNotUtf8
          | some text =>
              match parseJson? text with
              | none => .error .headerNotJson
              | some j =>
                  match j with
                  | .object _ =>
                      if (j.field? "crit").isSome then .error .criticalHeaderUnsupported
                      else if (j.field? "zip").isSome then .error .compressionRefused
                      else
                        match j.getString? "alg" with
                        | none => .error .algMissing
                        | some a =>
                            match keyAlgOfString? a with
                            | none => .error (.algNotAllowed a)
                            | some alg =>
                                match j.getString? "enc" with
                                | none => .error .encMissing
                                | some e =>
                                    match encAlgOfString? e with
                                    | none => .error (.encNotAllowed e)
                                    | some enc => .ok (c, { alg := alg, enc := enc, json := j })
                  | _ => .error .headerNotObject

/-! ## Primitives -/

/-- The public-key primitives, supplied by the caller.

  * `rsaPub n e x`, `rsaPriv n d x` — `x^e mod n`, `x^d mod n`
    (`RsaOaep.RsaOp`).
  * `p256Ecdh theirXY sk` — the 32-octet shared secret `Z`, refusing a
    point off the curve; `p256Public sk` — the 64-octet `x || y`.
  * `x25519Dh scalar point`, `x25519Public scalar` — RFC 7748, with the
    all-zero check of §6.1. -/
structure Prims where
  rsaPub : RsaOaep.RsaOp
  rsaPriv : RsaOaep.RsaOp
  p256Ecdh : ByteArray → ByteArray → Option ByteArray
  p256Public : ByteArray → Option ByteArray
  x25519Dh : ByteArray → ByteArray → Option ByteArray
  x25519Public : ByteArray → Option ByteArray

/-- The HACL* instance. -/
def nativePrims : Prims where
  rsaPub := Rsa.rsaPublicOp
  rsaPriv := RsaOaep.rsaPrivateOp
  p256Ecdh := P256.p256Ecdh
  p256Public := P256.p256SecretToPublic
  x25519Dh := X25519.dh?
  x25519Public := X25519.publicKey?

/-! ## The stage after the key -/

/-- A failure after the allowlist stage: one opaque failure, or a cipher
request the host has not answered yet. There is no refusal constructor. -/
inductive Fail where
  | failed
  | need (req : Req)

abbrev Post := Except Fail

/-- Run one cipher request. A refusal becomes `failed`; `.need` passes
through unchanged. -/
def runCipher (C : Cipher) (r : Req) : Post ByteArray :=
  match C.call r with
  | .ok b => .ok b
  | .error .refused => .error .failed
  | .error (.need q) => .error (.need q)

def guardP (b : Bool) : Post Unit := if b then .ok () else .error .failed

def someP {α : Type} : Option α → Post α
  | some a => .ok a
  | none => .error .failed

/-- `AL` of RFC 7518 §5.2.2.1: the AAD length in BITS as a 64-bit
big-endian integer. -/
def al64 (aad : ByteArray) : ByteArray :=
  let n := aad.size * 8
  ⟨#[(n / 72057594037927936 % 256).toUInt8, (n / 281474976710656 % 256).toUInt8,
     (n / 1099511627776 % 256).toUInt8, (n / 4294967296 % 256).toUInt8,
     (n / 16777216 % 256).toUInt8, (n / 65536 % 256).toUInt8,
     (n / 256 % 256).toUInt8, (n % 256).toUInt8]⟩

/-- The CBC-HMAC tag of RFC 7518 §5.2.2.1 steps 5 and 6: the HMAC over
`A || IV || E || AL`, truncated to `T_LEN` (16 octets with SHA-256, 32 with
SHA-512). -/
def cbcTag (enc : EncAlg) (macKey aad iv ct : ByteArray) : ByteArray :=
  let m := aad ++ iv ++ ct ++ al64 aad
  match enc with
  | .a256cbcHs512 => (hmacSha512 macKey m).extract 0 32
  | _ => (hmacSha256 macKey m).extract 0 16

/-- `MAC_KEY` and `ENC_KEY` of RFC 7518 §5.2.2.1 step 1: the first and the
second half of the CEK. -/
def splitCbcKey (cek : ByteArray) : ByteArray × ByteArray :=
  let half := cek.size / 2
  (cek.extract 0 half, cek.extract half cek.size)

/-- Content decryption (RFC 7516 §5.2 step 16). For CBC-HMAC, the MAC is
checked first and only a MAC that matches leads to the decryption request
(RFC 7518 §5.2.2.2 step 4). -/
def contentDecrypt (C : Cipher) (enc : EncAlg) (cek iv aad ct tag : ByteArray) :
    Post ByteArray := do
  guardP (cek.size == enc.cekBytes && iv.size == enc.ivBytes && tag.size == enc.tagBytes)
  if enc.isCbc then
    let (macKey, encKey) := splitCbcKey cek
    guardP (ctEqBytes (cbcTag enc macKey aad iv ct) tag)
    runCipher C { op := .cbcDecrypt, key := encKey, iv := iv, data := ct }
  else
    runCipher C { op := .gcmDecrypt, key := cek, iv := iv, aad := aad, data := ct ++ tag }

/-- Content encryption (RFC 7516 §5.1 step 15): the ciphertext and the tag. -/
def contentEncrypt (C : Cipher) (enc : EncAlg) (cek iv aad pt : ByteArray) :
    Post (ByteArray × ByteArray) := do
  guardP (cek.size == enc.cekBytes && iv.size == enc.ivBytes)
  if enc.isCbc then
    let (macKey, encKey) := splitCbcKey cek
    let ct ← runCipher C { op := .cbcEncrypt, key := encKey, iv := iv, data := pt }
    pure (ct, cbcTag enc macKey aad iv ct)
  else
    let out ← runCipher C { op := .gcmEncrypt, key := cek, iv := iv, aad := aad, data := pt }
    guardP (out.size ≥ 16)
    pure (out.extract 0 (out.size - 16), out.extract (out.size - 16) out.size)

/-- A header member holding base64url octets; absent is empty (RFC 7518
§4.6.1.2 and §4.6.1.3 for `apu` and `apv`). -/
def headerOctets? (j : Json) (name : String) : Option ByteArray :=
  match j.field? name with
  | none => some ByteArray.empty
  | some (.string s) => Base64Url.decode s
  | some _ => none

/-- The Concat KDF AlgorithmID (RFC 7518 §4.6.2): `enc` for direct
key agreement, `alg` for key agreement with key wrapping. -/
def kdfAlgId (alg : KeyAlg) (enc : EncAlg) : ByteArray :=
  if alg == .ecdhEs then enc.name.toUTF8 else alg.name.toUTF8

/-- keydatalen in bits: the CEK for direct key agreement, the KEK for the
key-wrapping forms. -/
def kdfBits (alg : KeyAlg) (enc : EncAlg) : Nat :=
  match alg with
  | .ecdhEsA128kw => 128
  | .ecdhEsA256kw => 256
  | _ => enc.cekBytes * 8

/-- The ECDH-ES shared secret of the recipient's key and the header's `epk`.
The curves must agree. -/
def agree (P : Prims) (k : DecKey) (e : Epk) : Option ByteArray :=
  match k, e with
  | .ec d, .ec x y => P.p256Ecdh (x ++ y) d
  | .x25519 d, .x25519 x => P.x25519Dh d x
  | _, _ => none

/-- The key the KDF derives from the header and the recipient's key. -/
def derive (P : Prims) (k : DecKey) (h : Header) : Option ByteArray := do
  let epkJson ← h.json.field? "epk"
  let e ← parseEpk? epkJson
  let apu ← headerOctets? h.json "apu"
  let apv ← headerOctets? h.json "apv"
  let z ← agree P k e
  ConcatKdf.jweDerive? z (kdfAlgId h.alg h.enc) apu apv (kdfBits h.alg h.enc)

/-- The CEK used when RSA-OAEP decryption fails or gives a CEK of the wrong
length (RFC 7516 §11.5): an HMAC of the private exponent and the encrypted
key, so the failure shows only at the content tag. -/
def substituteCek (d ek : ByteArray) (len : Nat) : ByteArray :=
  (hmacSha512 d ("JWE substitute CEK".toUTF8 ++ ek)).extract 0 len

/-- AES Key Unwrap of the CEK; the result must be the CEK length. -/
def unwrapCek (C : Cipher) (kek ek : ByteArray) (len : Nat) : Post ByteArray := do
  let cek ← runCipher C { op := .kwUnwrap, key := kek, data := ek }
  guardP (cek.size == len)
  pure cek

/-- The CEK (RFC 7516 §5.2 steps 9 to 11). -/
def recoverCek (P : Prims) (C : Cipher) (k : DecKey) (h : Header) (ek : ByteArray) :
    Post ByteArray :=
  let n := h.enc.cekBytes
  let oaep (H : RsaOaep.OaepHash) (nn d : ByteArray) : Post ByteArray :=
    match RsaOaep.oaepDecrypt H P.rsaPriv nn d ek ByteArray.empty with
    | some cek => if cek.size == n then .ok cek else .ok (substituteCek d ek n)
    | none => .ok (substituteCek d ek n)
  match h.alg, k with
  | .rsaOaep, .rsa nn d => oaep RsaOaep.oaepSha1 nn d
  | .rsaOaep256, .rsa nn d => oaep RsaOaep.oaepSha256 nn d
  | .dir, .oct key => do
      guardP (ek.size == 0 && key.size == n)
      pure key
  | .a128kw, .oct kek => do
      guardP (kek.size == 16)
      unwrapCek C kek ek n
  | .a256kw, .oct kek => do
      guardP (kek.size == 32)
      unwrapCek C kek ek n
  | .ecdhEs, _ => do
      guardP (ek.size == 0)
      someP (derive P k h)
  | .ecdhEsA128kw, _ => do
      let kek ← someP (derive P k h)
      unwrapCek C kek ek n
  | .ecdhEsA256kw, _ => do
      let kek ← someP (derive P k h)
      unwrapCek C kek ek n
  | _, _ => .error .failed

/-- Everything after the allowlist stage. -/
def afterKey (P : Prims) (C : Cipher) (k : DecKey) (c : Compact) (h : Header) :
    Post ByteArray := do
  let ek ← someP (Base64Url.decode c.ekB64)
  let iv ← someP (Base64Url.decode c.ivB64)
  let ct ← someP (Base64Url.decode c.ctB64)
  let tag ← someP (Base64Url.decode c.tagB64)
  let cek ← recoverCek P C k h ek
  contentDecrypt C h.enc cek iv c.aad ct tag

/-! ## Decryption -/

/-- Why a token gave no plaintext. -/
inductive Err where
  /-- Refused by the allowlist stage, before any key was read. -/
  | refused (r : Refusal)
  /-- Every failure after the allowlist stage, with no reason. -/
  | decryptionFailed
  /-- The cipher needs the host to answer this request first. -/
  | need (req : Req)

def Fail.toErr : Fail → Err
  | .failed => .decryptionFailed
  | .need r => .need r

/-- Decrypt a JWE Compact Serialization: the protected header and the
plaintext. -/
def decrypt (P : Prims) (C : Cipher) (k : DecKey) (token : String) :
    Except Err (Json × ByteArray) :=
  match jwePreKey token with
  | .error r => .error (.refused r)
  | .ok (c, h) =>
      match afterKey P C k c h with
      | .ok pt => .ok (h.json, pt)
      | .error f => .error f.toErr

/-! ## Encryption -/

/-- Why a token could not be made. Encryption has no secret input from an
attacker, so its errors carry a reason. -/
inductive EncErr where
  | invalid (msg : String)
  | refused
  | need (req : Req)

def Fail.toEncErr : Fail → EncErr
  | .failed => .refused
  | .need r => .need r

/-- Random octets one encryption takes, in this order: the CEK (not for
`dir` or direct `ECDH-ES`), the IV, then the OAEP seed (20 octets for
SHA-1, 32 for SHA-256) or the 32-octet ephemeral scalar of ECDH-ES. -/
def randomCekBytes (alg : KeyAlg) (enc : EncAlg) : Nat :=
  if alg == .dir || alg == .ecdhEs then 0 else enc.cekBytes

def randomAlgBytes : KeyAlg → Nat
  | .rsaOaep => 20
  | .rsaOaep256 => 32
  | .ecdhEs | .ecdhEsA128kw | .ecdhEsA256kw => 32
  | _ => 0

def randomBytesNeeded (alg : KeyAlg) (enc : EncAlg) : Nat :=
  randomCekBytes alg enc + enc.ivBytes + randomAlgBytes alg

/-- Header members the caller may not set: the encryptor writes them. -/
def reservedHeaderNames : List String := ["alg", "enc", "zip", "crit", "epk"]

/-- `(cek, encrypted key, epk)` for a sender. -/
def senderKeys (P : Prims) (C : Cipher) (alg : KeyAlg) (enc : EncAlg) (key : EncKey)
    (randCek randAlg apu apv : ByteArray) :
    Except EncErr (ByteArray × ByteArray × Option Epk) :=
  let n := enc.cekBytes
  let lift {α : Type} (p : Post α) : Except EncErr α :=
    match p with
    | .ok a => .ok a
    | .error f => .error f.toEncErr
  let wrap (kek cek : ByteArray) : Except EncErr ByteArray :=
    lift (runCipher C { op := .kwWrap, key := kek, data := cek })
  let ecdh : Except EncErr (ByteArray × Epk) :=
    match key with
    | .ec x y =>
        match P.p256Public randAlg, P.p256Ecdh (x ++ y) randAlg with
        | some pub, some z => .ok (z, .ec (pub.extract 0 32) (pub.extract 32 64))
        | _, _ => .error (.invalid "ECDH-ES on P-256 refused the key pair")
    | .x25519 x =>
        match P.x25519Public randAlg, P.x25519Dh randAlg x with
        | some pub, some z => .ok (z, .x25519 pub)
        | _, _ => .error (.invalid "ECDH-ES on X25519 refused the key pair")
    | _ => .error (.invalid s!"{alg.name} needs an EC P-256 or OKP X25519 key")
  let kdf (z : ByteArray) : Except EncErr ByteArray :=
    match ConcatKdf.jweDerive? z (kdfAlgId alg enc) apu apv (kdfBits alg enc) with
    | some k => .ok k
    | none => .error (.invalid "the Concat KDF refused its input")
  match alg, key with
  | .dir, .oct k =>
      if k.size == n then .ok (k, ByteArray.empty, none)
      else .error (.invalid s!"dir with {enc.name} needs a {n}-octet key")
  | .a128kw, .oct kek =>
      if kek.size == 16 then do
        let ek ← wrap kek randCek
        pure (randCek, ek, none)
      else .error (.invalid "A128KW needs a 16-octet key")
  | .a256kw, .oct kek =>
      if kek.size == 32 then do
        let ek ← wrap kek randCek
        pure (randCek, ek, none)
      else .error (.invalid "A256KW needs a 32-octet key")
  | .rsaOaep, .rsa nn e =>
      match RsaOaep.oaepEncrypt RsaOaep.oaepSha1 P.rsaPub nn e randCek ByteArray.empty randAlg with
      | some ek => .ok (randCek, ek, none)
      | none => .error (.invalid "RSA-OAEP encryption refused the key")
  | .rsaOaep256, .rsa nn e =>
      match RsaOaep.oaepEncrypt RsaOaep.oaepSha256 P.rsaPub nn e randCek ByteArray.empty randAlg with
      | some ek => .ok (randCek, ek, none)
      | none => .error (.invalid "RSA-OAEP-256 encryption refused the key")
  | .ecdhEs, _ => do
      let (z, epk) ← ecdh
      let cek ← kdf z
      pure (cek, ByteArray.empty, some epk)
  | .ecdhEsA128kw, _ | .ecdhEsA256kw, _ => do
      let (z, epk) ← ecdh
      let kek ← kdf z
      let ek ← wrap kek randCek
      pure (randCek, ek, some epk)
  | _, _ => .error (.invalid s!"{alg.name} does not take this key type")

/-- Encrypt to a JWE Compact Serialization. `rand` supplies
`randomBytesNeeded alg enc` octets from the host's random source; `extra`
are further protected header members (for example `kid`, `cty`, `apu`,
`apv`). -/
def encrypt (P : Prims) (C : Cipher) (rand : ByteArray) (alg : KeyAlg) (enc : EncAlg)
    (key : EncKey) (pt : ByteArray) (extra : List (String × Json)) :
    Except EncErr String := do
  let needed := randomBytesNeeded alg enc
  if rand.size < needed then
    throw (.invalid s!"{alg.name} with {enc.name} needs {needed} random octets, got {rand.size}")
  let names := extra.map (·.1)
  if names.any (reservedHeaderNames.contains ·) then
    throw (.invalid "extra header members may not set alg, enc, zip, crit or epk")
  if names.eraseDups.length != names.length then
    throw (.invalid "extra header members have a duplicate name")
  let extraJson := Json.object extra
  let apu ← match headerOctets? extraJson "apu" with
    | some b => pure b
    | none => throw (.invalid "apu is not base64url")
  let apv ← match headerOctets? extraJson "apv" with
    | some b => pure b
    | none => throw (.invalid "apv is not base64url")
  let c1 := randomCekBytes alg enc
  let randCek := rand.extract 0 c1
  let iv := rand.extract c1 (c1 + enc.ivBytes)
  let randAlg := rand.extract (c1 + enc.ivBytes) needed
  let (cek, ek, epk?) ← senderKeys P C alg enc key randCek randAlg apu apv
  let epkMember := match epk? with
    | some e => [("epk", e.toJson)]
    | none => []
  let header := Json.object ([("alg", .string alg.name), ("enc", .string enc.name)] ++
    epkMember ++ extra)
  let headerB64 := Base64Url.encodeUtf8 header.toString
  let aad := headerB64.toUTF8
  let (ct, tag) ← match contentEncrypt C enc cek iv aad pt with
    | .ok r => pure r
    | .error f => throw f.toEncErr
  pure (headerB64 ++ "." ++ Base64Url.encode ek ++ "." ++ Base64Url.encode iv ++ "." ++
    Base64Url.encode ct ++ "." ++ Base64Url.encode tag)

/-! ## Nested JWT (RFC 7519 §5.2) -/

/-- The outcome of decrypting a nested JWT. -/
inductive Nested where
  /-- The inner JWS verified; its payload (the JWT Claims Set octets). -/
  | verified (outer : Json) (payload : ByteArray)
  /-- The JWE did not declare `cty` `JWT`. -/
  | notNested
  /-- The plaintext was not a UTF-8 JWS compact serialization. -/
  | innerMalformed
  /-- The inner JWS did not verify. -/
  | innerRefused (o : JOSE.Outcome)

/-- `cty` names a nested JWT (RFC 7519 §5.2: "JWT"; media type names are
compared without regard to ASCII case, RFC 7515 §4.1.10). -/
def isJwtCty (h : Json) : Bool :=
  match h.getString? "cty" with
  | some s => s.toUpper == "JWT"
  | none => false

/-- Decrypt, then verify the inner JWS with `JOSE.verifyCompact`. -/
def decryptThenVerify (P : Prims) (C : Cipher) (k : DecKey) (V : JOSE.Verifiers)
    (vk : Jwk) (token : String) : Except Err Nested := do
  let (h, pt) ← decrypt P C k token
  if !isJwtCty h then return .notNested
  match String.fromUTF8? pt with
  | none => return .innerMalformed
  | some inner =>
      match JOSE.verifyCompact V vk inner with
      | .verified =>
          match JOSE.splitCompact? inner with
          | some jc =>
              match Base64Url.decode jc.payloadB64 with
              | some payload => return .verified h payload
              | none => return .innerMalformed
          | none => return .innerMalformed
      | o => return .innerRefused o

/-! ## Theorems -/

/-- A refusal decided before the key is the answer. -/
theorem decrypt_refuses_at_pre_key_stage (P : Prims) (C : Cipher) (k : DecKey)
    (token : String) {r : Refusal} (h : jwePreKey token = .error r) :
    decrypt P C k token = .error (.refused r) := by
  simp [decrypt, h]

/-- **A token refused by the allowlist stage gives the same answer for
every key, every cipher and every set of primitives.** No key is read, no
cipher request is made and no RSA or ECDH operation runs for it. -/
theorem decrypt_independent_of_key_before_key_stage
    (P₁ P₂ : Prims) (C₁ C₂ : Cipher) (k₁ k₂ : DecKey) (token : String) {r : Refusal}
    (h : jwePreKey token = .error r) :
    decrypt P₁ C₁ k₁ token = decrypt P₂ C₂ k₂ token := by
  rw [decrypt_refuses_at_pre_key_stage P₁ C₁ k₁ token h,
      decrypt_refuses_at_pre_key_stage P₂ C₂ k₂ token h]

/-- **A `.refused` answer always comes from the allowlist stage.** Every
failure after it is `decryptionFailed` or `need`. -/
theorem decrypt_refused_only_pre_key {P : Prims} {C : Cipher} {k : DecKey}
    {token : String} {r : Refusal} (h : decrypt P C k token = .error (.refused r)) :
    jwePreKey token = .error r := by
  unfold decrypt at h
  split at h
  · next r' hr => simp at h; rw [hr, h]
  · split at h
    · simp at h
    · next f _ => cases f <;> simp [Fail.toErr] at h

/-- **The `alg` values this module refuses**: RSAES-PKCS1-v1_5 (RFC 7518
§4.2), the PBES2 family (§4.8), AES-GCM key wrap (§4.7), `none` and case
variants of allowed names. -/
theorem keyAlg_refused :
    ∀ s ∈ ["RSA1_5", "PBES2-HS256+A128KW", "PBES2-HS384+A192KW", "PBES2-HS512+A256KW",
           "A128GCMKW", "A192GCMKW", "A256GCMKW", "A192KW", "ECDH-ES+A192KW",
           "none", "", "rsa-oaep", "DIR", "RSA-OAEP-384", "RSA-OAEP-512"],
      keyAlgOfString? s = none := by decide

/-- **The `enc` values this module refuses**: the 192-bit forms and every
name outside RFC 7518 §5.1. -/
theorem encAlg_refused :
    ∀ s ∈ ["A192GCM", "A192CBC-HS384", "a128gcm", "", "none", "A128CBC"],
      encAlgOfString? s = none := by decide

theorem keyAlg_roundTrip (a : KeyAlg) : keyAlgOfString? a.name = some a := by
  cases a <;> rfl

theorem encAlg_roundTrip (e : EncAlg) : encAlgOfString? e.name = some e := by
  cases e <;> rfl

/-- **A CBC-HMAC MAC failure makes no cipher request**: the answer is
`failed` for every cipher, so the decryption request is never formed. -/
theorem cbc_mac_failure_makes_no_request (C : Cipher) {enc : EncAlg}
    {cek iv aad ct tag : ByteArray} (hcbc : enc.isCbc = true)
    (hmac : ctEqBytes (cbcTag enc (splitCbcKey cek).1 aad iv ct) tag = false) :
    contentDecrypt C enc cek iv aad ct tag = .error .failed := by
  unfold contentDecrypt
  by_cases hl : (cek.size == enc.cekBytes && iv.size == enc.ivBytes && tag.size == enc.tagBytes) = true
  · simp only [guardP, hl, if_true, hcbc]
    simp [hmac, bind, Except.bind]
  · simp only [guardP, hl]
    simp [bind, Except.bind]

/-- A cipher's `.need` reaches the caller of `runCipher` unchanged. -/
theorem runCipher_need {C : Cipher} {r q : Req} (h : C.call r = .error (.need q)) :
    runCipher C r = .error (.need q) := by
  simp [runCipher, h]

/-- And `decrypt` passes a post-key `.need` through unchanged. -/
theorem decrypt_need {P : Prims} {C : Cipher} {k : DecKey} {token : String}
    {c : Compact} {h : Header} {q : Req}
    (hp : jwePreKey token = .ok (c, h)) (ha : afterKey P C k c h = .error (.need q)) :
    decrypt P C k token = .error (.need q) := by
  simp [decrypt, hp, ha, Fail.toErr]

end L4Factoidal.JOSE.Jwe
