/-
L4Factoidal.Crypto.WebCryptoKeys — the Web Cryptography API's algorithm logic for keys:
the registry of operations and algorithms, the key store behind opaque handles, the key
usages rules, extractability, the key formats (raw, JWK, SPKI, PKCS #8) and the error
of every refusal. The primitives are HACL*'s (`Crypto.WebHacl`); this module decides
everything around them.

Specifications: Web Cryptography Level 2 (W3C Editor's Draft): §14 SubtleCrypto, §18.4
"normalize an algorithm", §23 ECDSA, §24 ECDH, Ed25519 and X25519 (the secure curves
sections), §32 HMAC, §33 HKDF, §34 PBKDF2; "Modern Algorithms in the Web Cryptography
API" (WICG) for ChaCha20-Poly1305; RFC 5480 and RFC 5915 (EC keys in SPKI and PKCS #8),
RFC 8410 (Ed25519 and X25519 in SPKI and PKCS #8), RFC 7517, 7518 and 8037 (JWK), X.690
(DER). Record: docs/designissues/2026-11-09-hacl-web-crypto.md.

## Keys are handles

A CryptoKey's bytes live here, in the `KeyStore` of the page's session (`Hosts.WebApi`),
never in page JavaScript: the page holds a number. The only operation whose answer is
built from a key's own bytes is `exportKey` (and `wrapKey`, which exports and then
encrypts), and it refuses unless the key is extractable (`exportKey_extractable`); its
answer does not depend on the bytes of any non-extractable key (`exportKey_blind`).

No `partial`, no `sorry`, no `axiom`.
-/
import L4Factoidal.Crypto.WebHacl
import L4Factoidal.JOSE.Base64Url
import Std.Data.HashMap

namespace L4Factoidal.Crypto.WebCryptoKeys

open L4Factoidal.Crypto
open L4Factoidal.Crypto.WebHacl

/-! ## Errors -/

/-- The exceptions of the API: WebIDL's TypeError and the DOMException names of §14. -/
inductive Err where
  | typeError | notSupported | syntax | invalidAccess | data | operation | quota
  deriving DecidableEq, Repr, Inhabited

/-- The `web_api` answer code (`Hosts.WebApi`; prelude.js `apiError`). -/
def Err.code : Err → Int
  | .typeError => -20 | .operation => -22 | .notSupported => -23 | .syntax => -24
  | .invalidAccess => -25 | .data => -26 | .quota => -27

/-- The DOMException name (or `TypeError`) each code becomes in the page. -/
def Err.name : Err → String
  | .typeError => "TypeError" | .operation => "OperationError" | .notSupported => "NotSupportedError"
  | .syntax => "SyntaxError" | .invalidAccess => "InvalidAccessError" | .data => "DataError"
  | .quota => "QuotaExceededError"

def Err.all : List Err := [.typeError, .notSupported, .syntax, .invalidAccess, .data, .operation, .quota]

theorem Err.mem_all (e : Err) : e ∈ Err.all := by cases e <;> decide

/-- Distinct errors have distinct codes, so the page always sees the error Lean chose. -/
theorem Err.code_injective {a b : Err} (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Err.code] at h)

/-- Every code is negative: never a length, never an answer. -/
theorem Err.code_neg (e : Err) : e.code < 0 := by cases e <;> decide

abbrev Res := Except Err

/-! ## Usages, key types, algorithms -/

inductive Usage where
  | encrypt | decrypt | sign | verify | deriveKey | deriveBits | wrapKey | unwrapKey
  | encapsulateKey | encapsulateBits | decapsulateKey | decapsulateBits
  deriving DecidableEq, Repr, Inhabited

def Usage.name : Usage → String
  | .encrypt => "encrypt" | .decrypt => "decrypt" | .sign => "sign" | .verify => "verify"
  | .deriveKey => "deriveKey" | .deriveBits => "deriveBits" | .wrapKey => "wrapKey"
  | .unwrapKey => "unwrapKey" | .encapsulateKey => "encapsulateKey"
  | .encapsulateBits => "encapsulateBits" | .decapsulateKey => "decapsulateKey"
  | .decapsulateBits => "decapsulateBits"

def Usage.all : List Usage := [.encrypt, .decrypt, .sign, .verify, .deriveKey, .deriveBits, .wrapKey,
  .unwrapKey, .encapsulateKey, .encapsulateBits, .decapsulateKey, .decapsulateBits]

def Usage.ofName? (s : String) : Option Usage := Usage.all.find? (·.name == s)

inductive KeyType where
  | secret | publicKey | privateKey
  deriving DecidableEq, Repr, Inhabited

def KeyType.name : KeyType → String
  | .secret => "secret" | .publicKey => "public" | .privateKey => "private"

/-- The algorithms this engine has keys for. AES and RSA are not here: HACL* has no
portable AES (record, "What stays off"), and RSA keys are future work. -/
inductive Alg where
  | hmac | hkdf | pbkdf2 | ecdsa | ecdh | ed25519 | x25519 | chacha
  deriving DecidableEq, Repr, Inhabited

def Alg.name : Alg → String
  | .hmac => "HMAC" | .hkdf => "HKDF" | .pbkdf2 => "PBKDF2" | .ecdsa => "ECDSA" | .ecdh => "ECDH"
  | .ed25519 => "Ed25519" | .x25519 => "X25519" | .chacha => "ChaCha20-Poly1305"

/-- A key's `[[algorithm]]`. -/
structure KeyAlgo where
  alg : Alg
  hash : Option HashAlg := none
  /-- HMAC: the length in bits. -/
  length : Nat := 0
  /-- ECDSA, ECDH: the named curve (only "P-256" makes keys here). -/
  curve : String := ""
  deriving Inhabited

structure Key where
  type : KeyType
  extractable : Bool
  algo : KeyAlgo
  usages : List Usage
  /-- secret: the key bytes; private: the private scalar (P-256) or seed (Ed25519,
  X25519), 32 bytes; public: the public key (P-256 `x ‖ y`, 64 bytes; OKP, 32). -/
  material : ByteArray
  /-- private: the public key of the pair (P-256 `x ‖ y`; OKP 32 bytes). -/
  pub : ByteArray := ByteArray.empty
  deriving Inhabited

/-- The usages a key of this algorithm and type may have (§23-§34, and the modern
algorithms draft for ChaCha20-Poly1305). -/
def allowedUsages : Alg → KeyType → List Usage
  | .hmac, _ => [.sign, .verify]
  | .hkdf, _ | .pbkdf2, _ => [.deriveKey, .deriveBits]
  | .ecdsa, .privateKey | .ed25519, .privateKey => [.sign]
  | .ecdsa, _ | .ed25519, _ => [.verify]
  | .ecdh, .privateKey | .x25519, .privateKey => [.deriveKey, .deriveBits]
  | .ecdh, _ | .x25519, _ => []
  | .chacha, _ => [.encrypt, .decrypt, .wrapKey, .unwrapKey]

/-- The usage check of every import and generate step: SyntaxError when a usage is not
the algorithm's. -/
def checkUsages (allowed : List Usage) (us : List Usage) : Res Unit :=
  if us.all (allowed.contains ·) then .ok () else .error .syntax

def dedup (us : List Usage) : List Usage := us.foldl (fun acc u => if acc.contains u then acc else acc ++ [u]) []

/-! ## Arguments from the page

prelude.js sends an operation as `method, k₁, v₁, k₂, v₂, …`: the WebIDL conversions
done, nothing decided. Keys: `format`, `extractable`, `usages` (presence), `usage` (each
one, in order), `data`, `key`, `baseKey`, `wrappingKey`, `unwrappingKey`, `length`
(`null` or decimal), `a:<member>` (the normalized algorithm), `t:<member>` (a derived or
unwrapped key's algorithm), `j:<member>` (a JsonWebKey; `j:key_ops[]` each entry). -/

abbrev Args := Array (String × ByteArray)

def Args.get? (a : Args) (k : String) : Option ByteArray := (a.find? (·.1 == k)).map (·.2)
def Args.all (a : Args) (k : String) : List ByteArray := (a.toList.filter (·.1 == k)).map (·.2)
def Args.str? (a : Args) (k : String) : Option String := (a.get? k).bind String.fromUTF8?
def Args.has (a : Args) (k : String) : Bool := (a.get? k).isSome
def Args.nat? (a : Args) (k : String) : Option Nat := (a.str? k).bind String.toNat?
def Args.bool (a : Args) (k : String) : Bool := a.str? k == some "1"

/-- The pairs of a field list after the method name. -/
def pairsOf (fs : Array ByteArray) : Args := Id.run do
  let mut out : Args := #[]
  for i in [0:(fs.size - 1) / 2] do
    match String.fromUTF8? fs[2 * i + 1]! with
    | some k => out := out.push (k, fs[2 * i + 2]!)
    | none => pure ()
  return out

def usagesOf (a : Args) : Res (List Usage) :=
  (a.all "usage").foldlM (fun acc b => match (String.fromUTF8? b).bind Usage.ofName? with
    | some u => .ok (if acc.contains u then acc else acc ++ [u])
    | none => .error .typeError) []

/-- The members of the normalized algorithm (prefix `a:`) or of another dictionary. -/
def sub (a : Args) (pfx : String) : Args :=
  a.filterMap fun (k, v) => if k.startsWith pfx then some (String.ofList (k.toList.drop pfx.length), v) else none

/-! ## The registry (§18.4 "normalize an algorithm")

`normalizeSpec op name` is the registered algorithm for an operation and the members of
its dictionary type in WebIDL order (inherited members first, then lexicographic), each
with the conversion prelude.js makes: `h` HashAlgorithmIdentifier (normalized for
"digest"), `b` BufferSource (copied), `l` [EnforceRange] unsigned long, `o`
[EnforceRange] octet, `s` DOMString, `k` CryptoKey (its handle); `!` marks a required
member. NotSupportedError when the operation has no such algorithm. -/
def registered : List String :=
  ["AES-CTR", "AES-CBC", "AES-GCM", "AES-KW", "HMAC", "SHA-1", "SHA-256", "SHA-384", "SHA-512", "HKDF",
   "PBKDF2", "ECDSA", "ECDH", "RSASSA-PKCS1-v1_5", "RSA-PSS", "RSA-OAEP", "Ed25519", "X25519",
   "ChaCha20-Poly1305"]

def normalizeSpec (op name : String) : Res (String × List String) :=
  match (registered.find? (WebCrypto.asciiUpper · == WebCrypto.asciiUpper name)) with
  | none => .error .notSupported
  | some reg =>
    let r (ms : List String) : Res (String × List String) := .ok (reg, ms)
    match op, reg with
    | "digest", "SHA-1" | "digest", "SHA-256" | "digest", "SHA-384" | "digest", "SHA-512" => r []
    | "generateKey", "HMAC" | "importKey", "HMAC" | "get key length", "HMAC" => r ["hash:h!", "length:l"]
    | "generateKey", "ECDSA" | "generateKey", "ECDH" | "importKey", "ECDSA" | "importKey", "ECDH" =>
      r ["namedCurve:s!"]
    | "generateKey", "Ed25519" | "generateKey", "X25519" | "generateKey", "ChaCha20-Poly1305" => r []
    | "importKey", "HKDF" | "importKey", "PBKDF2" | "importKey", "Ed25519" | "importKey", "X25519"
    | "importKey", "ChaCha20-Poly1305" => r []
    | "get key length", "HKDF" | "get key length", "PBKDF2" | "get key length", "ChaCha20-Poly1305" => r []
    | "sign", "HMAC" | "verify", "HMAC" | "sign", "Ed25519" | "verify", "Ed25519" => r []
    | "sign", "ECDSA" | "verify", "ECDSA" => r ["hash:h!"]
    | "deriveBits", "HKDF" => r ["hash:h!", "info:b!", "salt:b!"]
    | "deriveBits", "PBKDF2" => r ["hash:h!", "iterations:l!", "salt:b!"]
    | "deriveBits", "ECDH" | "deriveBits", "X25519" => r ["public:k!"]
    | "encrypt", "ChaCha20-Poly1305" | "decrypt", "ChaCha20-Poly1305" => r ["additionalData:b", "iv:b!", "tagLength:o"]
    | _, _ => .error .notSupported

def algOf? (name : String) : Option Alg :=
  [Alg.hmac, .hkdf, .pbkdf2, .ecdsa, .ecdh, .ed25519, .x25519, .chacha].find? (·.name == name)

/-! ## The store -/

/-- The keys of a session, by handle. -/
structure KeyStore where
  keys : Std.HashMap Nat Key := {}
  next : Nat := 1
  deriving Inhabited

/-- At most this many keys at once in a session. -/
def maxKeys : Nat := 1 <<< 16

def KeyStore.add (s : KeyStore) (k : Key) : Res (KeyStore × Nat) :=
  if s.keys.size ≥ maxKeys then .error .quota else
  .ok ({ keys := s.keys.insert s.next k, next := s.next + 1 }, s.next)

def keyOf (s : KeyStore) (a : Args) (field : String) : Res Key :=
  match a.nat? field with
  | some h => match s.keys[h]? with | some k => .ok k | none => .error .typeError
  | none => .error .typeError

/-- The random bytes an operation needs, drawn by the caller (`Hosts.WebApi.randomBytes`,
the session's HMAC_DRBG) before the operation runs. -/
abbrev Rand := ByteArray

/-! ## Encodings: DER (X.690), SEC 1 points, base64url -/

/-- DER definite length octets, minimal (X.690 §10.1), for lengths below 2^16. -/
def derLen (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8]
  else if n < 256 then [0x81, n.toUInt8]
  else [0x82, (n / 256).toUInt8, (n % 256).toUInt8]

def tlv (tag : UInt8) (c : List UInt8) : List UInt8 := tag :: derLen c.length ++ c

/-- One DER TLV: tag, contents, the rest. Strict: minimal length octets only. -/
def readTlv : List UInt8 → Option (UInt8 × List UInt8 × List UInt8)
  | tag :: l0 :: rest =>
    if l0 < 128 then
      if l0.toNat ≤ rest.length then some (tag, rest.take l0.toNat, rest.drop l0.toNat) else none
    else if l0 == 0x81 then
      match rest with
      | l1 :: r => if l1 ≥ 128 && l1.toNat ≤ r.length then some (tag, r.take l1.toNat, r.drop l1.toNat) else none
      | [] => none
    else if l0 == 0x82 then
      match rest with
      | l1 :: l2 :: r =>
        let n := l1.toNat * 256 + l2.toNat
        if n ≥ 256 && n ≤ r.length then some (tag, r.take n, r.drop n) else none
      | _ => none
    else none
  | _ => none

/-- One TLV with the expected tag. -/
def expect (tag : UInt8) (b : List UInt8) : Option (List UInt8 × List UInt8) :=
  match readTlv b with
  | some (t, c, r) => if t == tag then some (c, r) else none
  | none => none

theorem toNat_toUInt8_of_lt {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

/-- DER round trip: reading what `tlv` wrote gives the tag, the contents and the rest. -/
theorem readTlv_tlv (tag : UInt8) (c rest : List UInt8) (h : c.length < 65536) :
    readTlv (tlv tag c ++ rest) = some (tag, c, rest) := by
  unfold tlv derLen
  by_cases h1 : c.length < 128
  · have hn := toNat_toUInt8_of_lt (n := c.length) (by omega)
    have hl : c.length.toUInt8 < 128 := by
      rw [UInt8.lt_iff_toNat_lt, hn]; exact h1
    rw [if_pos h1]
    show readTlv (tag :: c.length.toUInt8 :: (c ++ rest)) = _
    simp only [readTlv, hl, if_true, hn, List.length_append]
    simp
  · rw [if_neg h1]
    by_cases h2 : c.length < 256
    · have hn := toNat_toUInt8_of_lt (n := c.length) (by omega)
      rw [if_pos h2]
      show readTlv (tag :: 0x81 :: c.length.toUInt8 :: (c ++ rest)) = _
      have hge : c.length.toUInt8 ≥ 128 := by
        show (128 : UInt8) ≤ c.length.toUInt8
        rw [UInt8.le_iff_toNat_le, hn]; show 128 ≤ c.length; omega
      simp only [readTlv, hn, List.length_append]
      simp [hge]
    · rw [if_neg h2]
      have hn1 := toNat_toUInt8_of_lt (n := c.length / 256) (by omega)
      have hn2 := toNat_toUInt8_of_lt (n := c.length % 256) (by omega)
      have hsum : c.length / 256 * 256 + c.length % 256 = c.length := by omega
      show readTlv (tag :: 0x82 :: (c.length / 256).toUInt8 :: (c.length % 256).toUInt8 :: (c ++ rest)) = _
      simp only [readTlv, hn1, hn2, hsum, List.length_append]
      simp
      omega

def oidEcPublicKey : List UInt8 := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]
def oidP256 : List UInt8 := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]
def oidP384 : List UInt8 := [0x2b, 0x81, 0x04, 0x00, 0x22]
def oidP521 : List UInt8 := [0x2b, 0x81, 0x04, 0x00, 0x23]
def oidEd25519 : List UInt8 := [0x2b, 0x65, 0x70]
def oidX25519 : List UInt8 := [0x2b, 0x65, 0x6e]

def curveOfOid? (o : List UInt8) : Option String :=
  if o == oidP256 then some "P-256" else if o == oidP384 then some "P-384"
  else if o == oidP521 then some "P-521" else none

/-- An AlgorithmIdentifier: the OID and the parameters' TLV bytes (none when absent). -/
def readAlgId (c : List UInt8) : Option (List UInt8 × Option (List UInt8)) := do
  let (oid, r) ← expect 0x06 c
  if r.isEmpty then return (oid, none) else
  match readTlv r with
  | some (_, _, []) => return (oid, some r)
  | _ => none

/-- SubjectPublicKeyInfo (RFC 5280 §4.1): the algorithm and the BIT STRING's bytes. -/
def readSpki (b : List UInt8) : Option (List UInt8 × Option (List UInt8) × List UInt8) := do
  let (seq, rest) ← expect 0x30 b
  if !rest.isEmpty then none
  let (aid, r) ← expect 0x30 seq
  let (bits, r2) ← expect 0x03 r
  if !r2.isEmpty then none
  let (oid, params) ← readAlgId aid
  match bits with
  | 0 :: key => return (oid, params, key)
  | _ => none

/-- PrivateKeyInfo / OneAsymmetricKey (RFC 5208, RFC 5958): the algorithm and the
privateKey OCTET STRING's contents. Attributes and a v2 public key after it are allowed. -/
def readPkcs8 (b : List UInt8) : Option (List UInt8 × Option (List UInt8) × List UInt8) := do
  let (seq, rest) ← expect 0x30 b
  if !rest.isEmpty then none
  let (ver, r) ← expect 0x02 seq
  if ver != [0] && ver != [1] then none
  let (aid, r) ← expect 0x30 r
  let (pk, _) ← expect 0x04 r
  let (oid, params) ← readAlgId aid
  return (oid, params, pk)

def spkiOf (oid : List UInt8) (params : List UInt8) (key : List UInt8) : List UInt8 :=
  tlv 0x30 (tlv 0x30 (tlv 0x06 oid ++ params) ++ tlv 0x03 (0 :: key))

def pkcs8Of (oid : List UInt8) (params : List UInt8) (pk : List UInt8) : List UInt8 :=
  tlv 0x30 (tlv 0x02 [0] ++ tlv 0x30 (tlv 0x06 oid ++ params) ++ tlv 0x04 pk)

/-- SEC 1 §2.3.3 uncompressed point of a raw `x ‖ y`. -/
def uncompressed (xy : ByteArray) : ByteArray := ByteArray.mk #[4] ++ xy

/-- SEC 1 §2.3.4: a point (uncompressed or compressed) to a raw `x ‖ y` that HACL*
validated (on the curve, not infinity). -/
def decodePoint? (b : ByteArray) : Option ByteArray :=
  if b.size == 65 && b.get! 0 == 4 then
    let xy := b.extract 1 65
    if p256ValidPublic xy then some xy else none
  else if b.size == 33 && (b.get! 0 == 2 || b.get! 0 == 3) then p256Decompress? b
  else none

def b64 (b : ByteArray) : String := JOSE.Base64Url.encode b
def unb64? (s : String) : Option ByteArray := JOSE.Base64Url.decode s

/-- The encodings of the Ed25519 points of small order, with the sign bit cleared
(libsodium's `has_small_order` list, which includes the non-canonical encodings of
y = p - 1, p and p + 1). WebCrypto §Ed25519 verify: a small-order public key or R
verifies false. Public data: no constant-time need. -/
def ed25519SmallOrder : List (List UInt8) :=
  [ (1 : UInt8) :: List.replicate 31 0,
    0xec :: List.replicate 30 0xff ++ [0x7f],
    List.replicate 32 0,
    [0x26, 0xe8, 0x95, 0x8f, 0xc2, 0xb2, 0x27, 0xb0, 0x45, 0xc3, 0xf4, 0x89, 0xf2, 0xef, 0x98, 0xf0,
     0xd5, 0xdf, 0xac, 0x05, 0xd3, 0xc6, 0x33, 0x39, 0xb1, 0x38, 0x02, 0x88, 0x6d, 0x53, 0xfc, 0x05],
    [0xc7, 0x17, 0x6a, 0x70, 0x3d, 0x4d, 0xd8, 0x4f, 0xba, 0x3c, 0x0b, 0x76, 0x0d, 0x10, 0x67, 0x0f,
     0x2a, 0x20, 0x53, 0xfa, 0x2c, 0x39, 0xcc, 0xc6, 0x4e, 0xc7, 0xfd, 0x77, 0x92, 0xac, 0x03, 0x7a],
    0xed :: List.replicate 30 0xff ++ [0x7f],
    0xee :: List.replicate 30 0xff ++ [0x7f] ]

def ed25519IsSmallOrder (p : ByteArray) : Bool :=
  p.size == 32 &&
    let l := (p.toList.take 31) ++ [p.get! 31 &&& 0x7f]
    ed25519SmallOrder.contains l

/-! ## JWK (RFC 7517 §4, RFC 7518 §6, RFC 8037 §2) -/

/-- A member of a JWK answer: name and value. -/
inductive JwkVal where
  | str (s : String) | bool (b : Bool) | arr (xs : List String)

/-- The JsonWebKey members common to every import (§14.3.9 and each algorithm's import
steps): `use` against `expectUse` when there are usages, `key_ops` (no duplicates, and
every usage in it), and `ext` (DataError when false and the key is to be extractable). -/
def jwkCommon (j : Args) (us : List Usage) (extractable : Bool) (expectUse : String) : Res Unit := do
  if !us.isEmpty then
    if let some u := j.str? "use" then
      if u != expectUse then throw .data
  if j.has "key_ops" then
    let ops := (j.all "key_ops[]").filterMap String.fromUTF8?
    if (ops.eraseDups).length != ops.length then throw .data
    if !(us.all fun u => ops.contains u.name) then throw .data
  if j.str? "ext" == some "false" && extractable then throw .data

def jwkCommonOut (k : Key) : List (String × JwkVal) :=
  [("key_ops", .arr (k.usages.map (·.name))), ("ext", .bool k.extractable)]

/-! ## Import (§14.3.9, then each algorithm's "import key" steps, in their order) -/

/-- The key an import makes, before the generic steps (extractable and usages). -/
structure Made where
  type : KeyType
  algo : KeyAlgo
  material : ByteArray
  pub : ByteArray := ByteArray.empty

def okpOid : Alg → List UInt8
  | .ed25519 => oidEd25519 | _ => oidX25519

def okpPublic? : Alg → ByteArray → Option ByteArray
  | .ed25519, sk => ed25519Public? sk
  | _, sk => x25519Public? sk

/-- ECDSA and ECDH (§23.7, §24.4 "import key"). -/
def importEc (alg : Alg) (format : String) (data : ByteArray) (j : Args) (curve : String)
    (us : List Usage) (extractable : Bool) : Res Made := do
  let pubU := allowedUsages alg .publicKey
  let privU := allowedUsages alg .privateKey
  let useName := if alg == .ecdsa then "sig" else "enc"
  -- P-384 and P-521 are named curves of the API, but HACL* has only P-256.
  let haveCurve (c : String) : Res Unit :=
    if c == "P-256" then .ok () else if c == "P-384" || c == "P-521" then .error .notSupported else .error .data
  match format with
  | "spki" | "raw-public" | "raw" =>
    if format == "raw" || format == "raw-public" then
      if !(curve == "P-256" || curve == "P-384" || curve == "P-521") then throw .data
    checkUsages pubU us
    let point ← if format == "spki" then do
        let some (oid, params, key) := readSpki data.toList | throw .data
        if oid != oidEcPublicKey then throw .data
        let some p := params | throw .data
        let some (poid, _) := expect 0x06 p | throw .data
        let some c := curveOfOid? poid | throw .data
        haveCurve c
        if c != curve then throw .data
        pure (ByteArray.mk key.toArray)
      else do haveCurve curve; pure data
    let some xy := decodePoint? point | throw .data
    return { type := .publicKey, algo := { alg, curve }, material := xy }
  | "pkcs8" =>
    checkUsages privU us
    let some (oid, params, pk) := readPkcs8 data.toList | throw .data
    if oid != oidEcPublicKey then throw .data
    let some p := params | throw .data
    let some (poid, _) := expect 0x06 p | throw .data
    let some c := curveOfOid? poid | throw .data
    haveCurve c
    -- ECPrivateKey (RFC 5915 §3).
    let some (ecpk, rest) := expect 0x30 pk | throw .data
    if !rest.isEmpty then throw .data
    let some (ver, r) := expect 0x02 ecpk | throw .data
    if ver != [1] then throw .data
    let some (d, r) := expect 0x04 r | throw .data
    let r ← match expect 0xa0 r with
      | some (ps, r') =>
        match expect 0x06 ps with
        | some (o, []) => if o != poid then throw .data else pure r'
        | _ => throw .data
      | none => pure r
    let given ← match expect 0xa1 r with
      | some (pkb, _) =>
        match expect 0x03 pkb with
        | some (0 :: pt, []) => pure (some (ByteArray.mk pt.toArray))
        | _ => throw .data
      | none => pure none
    if c != curve then throw .data
    let d := ByteArray.mk d.toArray
    if d.size != 32 || !p256ValidPrivate d then throw .data
    let some xy := p256Public? d | throw .data
    if let some g := given then
      match decodePoint? g with
      | some gxy => if gxy != xy then throw .data
      | none => throw .data
    return { type := .privateKey, algo := { alg, curve }, material := d, pub := xy }
  | "jwk" =>
    let hasD := j.has "d"
    checkUsages (if hasD then privU else pubU) us
    if j.str? "kty" != some "EC" then throw .data
    jwkCommon j us extractable useName
    let some crv := j.str? "crv" | throw .data
    if crv != curve then throw .data
    haveCurve crv
    -- §23.7 jwk step 8.1: an `alg` that names another curve's ECDSA is a DataError; any
    -- other value names no curve and is not checked.
    if alg == .ecdsa then
      if let some a := j.str? "alg" then
        if a == "ES384" || a == "ES512" then throw .data
    let some x := (j.str? "x").bind unb64? | throw .data
    let some y := (j.str? "y").bind unb64? | throw .data
    if x.size != 32 || y.size != 32 then throw .data
    let xy := x ++ y
    if !p256ValidPublic xy then throw .data
    if hasD then
      let some d := (j.str? "d").bind unb64? | throw .data
      if d.size != 32 || !p256ValidPrivate d then throw .data
      let some pxy := p256Public? d | throw .data
      if pxy != xy then throw .data
      return { type := .privateKey, algo := { alg, curve }, material := d, pub := xy }
    return { type := .publicKey, algo := { alg, curve }, material := xy }
  | _ => throw .notSupported

/-- Ed25519 and X25519 (the secure curves "import key" steps). -/
def importOkp (alg : Alg) (format : String) (data : ByteArray) (j : Args) (us : List Usage)
    (extractable : Bool) : Res Made := do
  let pubU := allowedUsages alg .publicKey
  let privU := allowedUsages alg .privateKey
  match format with
  | "spki" =>
    checkUsages pubU us
    let some (oid, params, key) := readSpki data.toList | throw .data
    if oid != okpOid alg || params.isSome then throw .data
    if key.length != 32 then throw .data
    return { type := .publicKey, algo := { alg }, material := ByteArray.mk key.toArray }
  | "pkcs8" =>
    checkUsages privU us
    let some (oid, params, pk) := readPkcs8 data.toList | throw .data
    if oid != okpOid alg || params.isSome then throw .data
    let some (sk, []) := expect 0x04 pk | throw .data
    if sk.length != 32 then throw .data
    let sk := ByteArray.mk sk.toArray
    let some pub := okpPublic? alg sk | throw .data
    return { type := .privateKey, algo := { alg }, material := sk, pub }
  | "raw" | "raw-public" =>
    checkUsages pubU us
    if data.size != 32 then throw .data
    return { type := .publicKey, algo := { alg }, material := data }
  | "jwk" =>
    let hasD := j.has "d"
    checkUsages (if hasD then privU else pubU) us
    if j.str? "kty" != some "OKP" then throw .data
    if j.str? "crv" != some alg.name then throw .data
    if alg == .ed25519 then
      if let some a := j.str? "alg" then
        if a != "Ed25519" && a != "EdDSA" then throw .data
    jwkCommon j us extractable (if alg == .ed25519 then "sig" else "enc")
    let some x := (j.str? "x").bind unb64? | throw .data
    if x.size != 32 then throw .data
    if hasD then
      let some d := (j.str? "d").bind unb64? | throw .data
      if d.size != 32 then throw .data
      let some pub := okpPublic? alg d | throw .data
      if pub != x then throw .data
      return { type := .privateKey, algo := { alg }, material := d, pub }
    return { type := .publicKey, algo := { alg }, material := x }
  | _ => throw .notSupported

def hmacJwkAlg (h : HashAlg) : String :=
  match h with | .sha1 => "HS1" | .sha256 => "HS256" | .sha384 => "HS384" | .sha512 => "HS512"

/-- HMAC, HKDF, PBKDF2, ChaCha20-Poly1305 ("import key" of §32.6, §33.4, §34.4 and the
modern algorithms draft). -/
def importSecret (alg : Alg) (format : String) (data : ByteArray) (j : Args) (p : Args)
    (us : List Usage) (extractable : Bool) : Res Made := do
  -- HKDF and PBKDF2 (§33.4, §34.4) check the format first; HMAC (§32.6) the usages.
  if (alg == .hkdf || alg == .pbkdf2) && format != "raw" && format != "raw-secret" then throw .notSupported
  checkUsages (allowedUsages alg .secret) us
  match alg with
  | .hkdf | .pbkdf2 =>
    if extractable then throw .syntax
    return { type := .secret, algo := { alg }, material := data }
  | .hmac =>
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    let raw ← match format with
      | "raw" | "raw-secret" => pure data
      | "jwk" => do
        if j.str? "kty" != some "oct" then throw .data
        let some k := (j.str? "k").bind unb64? | throw .data
        if let some a := j.str? "alg" then
          if a != hmacJwkAlg h then throw .data
        jwkCommon j us extractable "sig"
        pure k
      | _ => throw .notSupported
    let bits := raw.size * 8
    if bits == 0 then throw .data
    let len ← match p.nat? "length" with
      | some l => if l > bits || l ≤ bits - 8 then throw .data else pure l
      | none => pure bits
    return { type := .secret, algo := { alg, hash := some h, length := len }, material := raw }
  | .chacha =>
    let raw ← match format with
      | "raw" | "raw-secret" => pure data
      | "jwk" => do
        if j.str? "kty" != some "oct" then throw .data
        let some k := (j.str? "k").bind unb64? | throw .data
        if let some a := j.str? "alg" then
          if a != "C20P" then throw .data
        jwkCommon j us extractable "enc"
        pure k
      | _ => throw .notSupported
    if raw.size != 32 then throw .data
    return { type := .secret, algo := { alg }, material := raw }
  | _ => throw .notSupported

/-- The algorithm's import steps. -/
def importMade (algName : String) (p : Args) (format : String) (data : ByteArray) (j : Args)
    (extractable : Bool) (us : List Usage) : Res Made :=
  match algOf? algName with
  | none => .error .notSupported
  | some alg =>
    match alg with
    | .ecdsa | .ecdh => importEc alg format data j ((p.str? "namedCurve").getD "") us extractable
    | .ed25519 | .x25519 => importOkp alg format data j us extractable
    | _ => importSecret alg format data j p us extractable

/-- §14.3.9 steps 10-11: a secret or private key with no usages is a SyntaxError; then
the key takes `extractable` and the usages. -/
def finishKey (m : Made) (extractable : Bool) (us : List Usage) : Res Key :=
  if (m.type == .secret || m.type == .privateKey) && us.isEmpty then .error .syntax
  else .ok { type := m.type, extractable, algo := m.algo, usages := us, material := m.material, pub := m.pub }

/-- §14.3.9 importKey after normalization. -/
def importKey (algName : String) (p : Args) (format : String) (data : ByteArray) (j : Args)
    (extractable : Bool) (us : List Usage) : Res Key :=
  importMade algName p format data j extractable us >>= fun m => finishKey m extractable us

/-! ## Export (§14.3.10, then each algorithm's "export key" steps) -/

inductive Exported where
  | bytes (b : ByteArray)
  | jwk (members : List (String × JwkVal))

/-- The export steps of `k`'s algorithm (no extractability check: `exportKey` makes it). -/
def exportBody (k : Key) (format : String) : Res Exported := do
  let alg := k.algo.alg
  match alg with
  | .ecdsa | .ecdh =>
    match format, k.type with
    | "spki", .publicKey => return .bytes (ByteArray.mk (spkiOf oidEcPublicKey (tlv 0x06 oidP256) (uncompressed k.material).toList).toArray)
    | "raw", .publicKey | "raw-public", .publicKey => return .bytes (uncompressed k.material)
    | "pkcs8", .privateKey =>
      let ec := tlv 0x30 (tlv 0x02 [1] ++ tlv 0x04 k.material.toList ++
        tlv 0xa1 (tlv 0x03 (0 :: (uncompressed k.pub).toList)))
      return .bytes (ByteArray.mk (pkcs8Of oidEcPublicKey (tlv 0x06 oidP256) ec).toArray)
    | "jwk", t =>
      let xy := if t == .privateKey then k.pub else k.material
      let base := [("kty", JwkVal.str "EC"), ("crv", .str k.algo.curve),
        ("x", .str (b64 (xy.extract 0 32))), ("y", .str (b64 (xy.extract 32 64)))]
      let d := if t == .privateKey then [("d", JwkVal.str (b64 k.material))] else []
      return .jwk (base ++ d ++ jwkCommonOut k)
    | "spki", _ | "raw", _ | "raw-public", _ | "pkcs8", _ => throw .invalidAccess
    | _, _ => throw .notSupported
  | .ed25519 | .x25519 =>
    match format, k.type with
    | "spki", .publicKey => return .bytes (ByteArray.mk (spkiOf (okpOid alg) [] k.material.toList).toArray)
    | "raw", .publicKey | "raw-public", .publicKey => return .bytes k.material
    | "pkcs8", .privateKey => return .bytes (ByteArray.mk (pkcs8Of (okpOid alg) [] (tlv 0x04 k.material.toList)).toArray)
    | "jwk", t =>
      let x := if t == .privateKey then k.pub else k.material
      let base := [("kty", JwkVal.str "OKP"), ("crv", .str alg.name), ("x", .str (b64 x))]
      let d := if t == .privateKey then [("d", JwkVal.str (b64 k.material))] else []
      let a := if alg == .ed25519 then [("alg", JwkVal.str "Ed25519")] else []
      return .jwk (base ++ d ++ a ++ jwkCommonOut k)
    | "spki", _ | "raw", _ | "raw-public", _ | "pkcs8", _ => throw .invalidAccess
    | _, _ => throw .notSupported
  | .hmac =>
    match format with
    | "raw" | "raw-secret" => return .bytes k.material
    | "jwk" =>
      let a := match k.algo.hash with | some h => [("alg", JwkVal.str (hmacJwkAlg h))] | none => []
      return .jwk ([("kty", JwkVal.str "oct"), ("k", .str (b64 k.material))] ++ a ++ jwkCommonOut k)
    | _ => throw .notSupported
  | .chacha =>
    match format with
    | "raw" | "raw-secret" => return .bytes k.material
    | "jwk" => return .jwk ([("kty", JwkVal.str "oct"), ("k", .str (b64 k.material)), ("alg", .str "C20P")] ++ jwkCommonOut k)
    | _ => throw .notSupported
  | .hkdf | .pbkdf2 => throw .notSupported

/-- §14.3.10 exportKey: InvalidAccessError unless the key is extractable; only then are
its bytes read (`exportKey_extractable`, `exportKey_blind`). -/
def exportKey (k : Key) (format : String) : Res Exported :=
  if k.extractable then exportBody k format else .error .invalidAccess

/-! ## Generate (§14.3.6) -/

/-- A fresh key or key pair from `rand` (the caller drew `randNeeded` bytes). -/
inductive Made2 where
  | one (k : Key)
  | pair (pub priv : Key)

/-- Random bytes generateKey needs: the HMAC key, or eight 32-byte candidates for a
P-256 scalar (a candidate is outside [1, n-1] with probability below 2^-32), or one
seed. -/
def randNeeded (algName : String) (p : Args) : Nat :=
  match algOf? algName with
  | some .hmac =>
    let blk := ((p.str? "hash").bind HashAlg.ofName? |>.map (·.block)).getD 64
    ((p.nat? "length").getD (blk * 8) + 7) / 8
  | some .ecdsa | some .ecdh => 256
  | some _ => 32
  | none => 0

def firstValidScalar (r : ByteArray) : Option ByteArray :=
  (List.range 8).findSome? fun i =>
    let c := r.extract (32 * i) (32 * i + 32)
    if p256ValidPrivate c then some c else none

def generateKey (algName : String) (p : Args) (extractable : Bool) (us : List Usage) (rand : Rand) :
    Res Made2 := do
  let some alg := algOf? algName | throw .notSupported
  match alg with
  | .hmac =>
    checkUsages (allowedUsages .hmac .secret) us
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    let len ← match p.nat? "length" with
      | some 0 => throw .operation
      | some l => pure l
      | none => pure (h.block * 8)
    let n := (len + 7) / 8
    if rand.size < n then throw .operation
    let bytes := rand.extract 0 n
    let bytes := if len % 8 == 0 then bytes else
      bytes.set! (n - 1) (bytes.get! (n - 1) &&& (0xFF <<< (8 - len % 8).toUInt8))
    if us.isEmpty then throw .syntax
    return .one { type := .secret, extractable, algo := { alg, hash := some h, length := len }, usages := us, material := bytes }
  | .chacha =>
    checkUsages (allowedUsages .chacha .secret) us
    if us.isEmpty then throw .syntax
    if rand.size < 32 then throw .operation
    return .one { type := .secret, extractable, algo := { alg }, usages := us, material := rand.extract 0 32 }
  | .ecdsa | .ecdh | .ed25519 | .x25519 =>
    checkUsages ((allowedUsages alg .publicKey) ++ (allowedUsages alg .privateKey)) us
    let curve := (p.str? "namedCurve").getD ""
    if alg == .ecdsa || alg == .ecdh then
      if curve == "P-384" || curve == "P-521" || curve != "P-256" then throw .notSupported
    let (sk, pub) ← match alg with
      | .ecdsa | .ecdh => do
        let some sk := firstValidScalar rand | throw .operation
        let some pub := p256Public? sk | throw .operation
        pure (sk, pub)
      | _ => do
        if rand.size < 32 then throw .operation
        let sk := rand.extract 0 32
        let some pub := okpPublic? alg sk | throw .operation
        pure (sk, pub)
    let algo : KeyAlgo := { alg, curve := if alg == .ecdsa || alg == .ecdh then curve else "" }
    let pubUs := us.filter (allowedUsages alg .publicKey).contains
    let privUs := us.filter (allowedUsages alg .privateKey).contains
    if privUs.isEmpty then throw .syntax
    return .pair { type := .publicKey, extractable := true, algo, usages := pubUs, material := pub }
      { type := .privateKey, extractable, algo, usages := privUs, material := sk, pub }
  | _ => throw .notSupported

/-! ## Sign, verify, derive, encrypt (§14.3.1-8) -/

/-- The checks every key operation makes first (§14.3.x, step "If the name member of
normalizedAlgorithm is not equal to the name attribute of the [[algorithm]] … or [[usages]]
does not contain …": InvalidAccessError). -/
def keyFor (k : Key) (algName : String) (u : Usage) : Res Unit :=
  if k.algo.alg.name != algName || !k.usages.contains u then .error .invalidAccess else .ok ()

def sign (algName : String) (p : Args) (k : Key) (data : ByteArray) (rand : Rand) : Res ByteArray := do
  keyFor k algName .sign
  match k.algo.alg with
  | .hmac =>
    let some h := k.algo.hash | throw .operation
    return (haclHash h).mac k.material data
  | .ecdsa =>
    if k.type != .privateKey then throw .invalidAccess
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    let e := p256MsgRep (hashFast h data)
    let sig := (List.range 8).findSome? fun i => p256Sign? k.material e (rand.extract (32 * i) (32 * i + 32))
    let some s := sig | throw .operation
    return s
  | .ed25519 =>
    if k.type != .privateKey then throw .invalidAccess
    let some s := ed25519Sign? k.material data | throw .operation
    return s
  | _ => throw .invalidAccess

def verify (algName : String) (p : Args) (k : Key) (sig data : ByteArray) : Res Bool := do
  keyFor k algName .verify
  match k.algo.alg with
  | .hmac =>
    let some h := k.algo.hash | throw .operation
    -- HACL*'s HMAC, then the constant-time comparison in C.
    return ctEq ((haclHash h).mac k.material data) sig
  | .ecdsa =>
    if k.type != .publicKey then throw .invalidAccess
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    return p256Verify k.material (p256MsgRep (hashFast h data)) sig
  | .ed25519 =>
    if k.type != .publicKey then throw .invalidAccess
    if ed25519IsSmallOrder k.material || (sig.size == 64 && ed25519IsSmallOrder (sig.extract 0 32)) then return false
    return ed25519Verify k.material data sig
  | _ => throw .invalidAccess

/-- The first `bits` bits of `secret` (the ECDH and X25519 truncation). -/
def truncateBits (secret : ByteArray) (bits : Nat) : ByteArray :=
  let n := (bits + 7) / 8
  let b := secret.extract 0 n
  if bits % 8 == 0 then b else b.set! (n - 1) (b.get! (n - 1) &&& (0xFF <<< (8 - bits % 8).toUInt8))

/-- deriveBits (§14.3.8 and the algorithms' "derive bits"). `length` is `none` for null. -/
def deriveBits (algName : String) (p : Args) (k : Key) (length : Option Nat) (store : KeyStore) : Res ByteArray := do
  keyFor k algName .deriveBits
  match k.algo.alg with
  | .hkdf =>
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    let some len := length | throw .operation
    if len % 8 != 0 then throw .operation
    let some out := WebCrypto.hkdf (haclHash h) k.material ((p.get? "salt").getD .empty)
      ((p.get? "info").getD .empty) (len / 8) | throw .operation
    return out
  | .pbkdf2 =>
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    let some len := length | throw .operation
    if len % 8 != 0 then throw .operation
    let it := (p.nat? "iterations").getD 0
    if it == 0 then throw .operation
    return WebCrypto.pbkdf2 (haclHash h) k.material ((p.get? "salt").getD .empty) it (len / 8)
  | .ecdh | .x25519 =>
    if k.type != .privateKey then throw .invalidAccess
    let pk ← keyOf store p "public"
    if pk.type != .publicKey || pk.algo.alg != k.algo.alg then throw .invalidAccess
    if k.algo.alg == .ecdh && pk.algo.curve != k.algo.curve then throw .invalidAccess
    let secret ← match k.algo.alg with
      | .ecdh => match p256Ecdh? pk.material k.material with | some s => pure s | none => throw .operation
      | _ => match x25519? k.material pk.material with | some s => pure s | none => throw .operation
    match length with
    | none => return secret
    | some len => if len > secret.size * 8 then throw .operation else return truncateBits secret len
  | _ => throw .invalidAccess

/-- "get key length" (§14.3.7 step 9) of a derived key's algorithm: `none` for null. -/
def keyLength (algName : String) (t : Args) : Res (Option Nat) := do
  match algOf? algName with
  | some .hmac =>
    let some h := (t.str? "hash").bind HashAlg.ofName? | throw .notSupported
    match t.nat? "length" with
    | some 0 => throw .typeError
    | some l => return some l
    | none => return some (h.block * 8)
  | some .hkdf | some .pbkdf2 => return none
  | some .chacha => return some 256
  | _ => throw .notSupported

/-- ChaCha20-Poly1305 (modern algorithms draft, "encrypt" and "decrypt"). -/
def crypt (enc : Bool) (algName : String) (p : Args) (k : Key) (data : ByteArray) : Res ByteArray := do
  keyFor k algName (if enc then .encrypt else .decrypt)
  match k.algo.alg with
  | .chacha =>
    let iv := (p.get? "iv").getD .empty
    if iv.size != 12 then throw .operation
    if let some t := p.nat? "tagLength" then
      if t != 128 then throw .operation
    let aad := (p.get? "additionalData").getD .empty
    if enc then
      let some c := chachaSeal? k.material iv aad data | throw .operation
      return c
    else
      if data.size < 16 then throw .operation
      let some m := chachaOpen? k.material iv aad data | throw .operation
      return m
  | _ => throw .invalidAccess

/-! ## Theorems: extractability and the usages rules -/

theorem exportKey_extractable {k : Key} {f : String} {e : Exported} (h : exportKey k f = .ok e) :
    k.extractable = true := by
  unfold exportKey at h
  cases hk : k.extractable
  · simp [hk] at h
  · rfl

/-- A key whose bytes are replaced: what an observer could not tell apart, if the API
leaked nothing of them. -/
def Key.blind (k : Key) : Key := { k with material := ByteArray.empty, pub := ByteArray.empty }

/-- Exporting a non-extractable key gives the same answer whatever its bytes: the
InvalidAccessError, and nothing else. -/
theorem exportKey_blind (k : Key) (f : String) (h : k.extractable = false) :
    exportKey k f = exportKey k.blind f := by
  have hb : k.blind.extractable = false := h
  unfold exportKey; rw [if_neg (by simp [h]), if_neg (by simp [hb])]

/-- The store with the bytes of every non-extractable key replaced. -/
def KeyStore.blind (st : KeyStore) : KeyStore :=
  { st with keys := st.keys.map fun _ k => if k.extractable then k else k.blind }

theorem keyOf_blind (st : KeyStore) (a : Args) (f : String) :
    keyOf st.blind a f = (keyOf st a f).map (fun k => if k.extractable then k else k.blind) := by
  unfold keyOf KeyStore.blind
  cases a.nat? f with
  | none => rfl
  | some h =>
    simp only [Std.HashMap.getElem?_map]
    cases st.keys[h]? <;> rfl

theorem checkUsages_ok {allowed us : List Usage} (h : checkUsages allowed us = .ok ()) :
    ∀ u ∈ us, u ∈ allowed := by
  unfold checkUsages at h
  split at h
  · rename_i hall; intro u hu
    have := List.all_eq_true.mp hall u hu
    simpa using this
  · cases h

theorem keyFor_of_bind {k : Key} {a : String} {u : Usage} {β : Type} {f : Unit → Res β} {x : β}
    (h : (keyFor k a u >>= f) = .ok x) : k.algo.alg.name = a ∧ k.usages.contains u = true := by
  unfold keyFor at h
  by_cases hc : (k.algo.alg.name != a || !k.usages.contains u) = true
  · rw [if_pos hc] at h; cases h
  · rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hc
    simp only [bne_eq_false_iff_eq, Bool.not_eq_false'] at hc
    exact hc

/-- Sign needs a key of the algorithm with the usage "sign". -/
theorem sign_usage {a : String} {p : Args} {k : Key} {d r : ByteArray} {out : ByteArray}
    (h : sign a p k d r = .ok out) : k.algo.alg.name = a ∧ k.usages.contains .sign = true :=
  keyFor_of_bind h

theorem verify_usage {a : String} {p : Args} {k : Key} {s d : ByteArray} {out : Bool}
    (h : verify a p k s d = .ok out) : k.algo.alg.name = a ∧ k.usages.contains .verify = true :=
  keyFor_of_bind h

theorem deriveBits_usage {a : String} {p : Args} {k : Key} {l : Option Nat} {s : KeyStore} {out : ByteArray}
    (h : deriveBits a p k l s = .ok out) : k.algo.alg.name = a ∧ k.usages.contains .deriveBits = true :=
  keyFor_of_bind h

theorem crypt_usage {e : Bool} {a : String} {p : Args} {k : Key} {d out : ByteArray}
    (h : crypt e a p k d = .ok out) :
    k.algo.alg.name = a ∧ k.usages.contains (if e then .encrypt else .decrypt) = true :=
  keyFor_of_bind h

theorem finishKey_ok {m : Made} {x : Bool} {us : List Usage} {k : Key} (h : finishKey m x us = .ok k) :
    k.usages = us ∧ k.extractable = x ∧ k.type = m.type ∧ (k.type ≠ .publicKey → us ≠ []) := by
  unfold finishKey at h
  split at h
  · cases h
  · rename_i hc
    cases h
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro hne hnil
    apply hc
    cases ht : m.type <;> simp_all

/-- An imported key has exactly the usages and extractability asked for, and a secret
or private one has a usage (§14.3.9 step 10). -/
theorem importKey_usages {n : String} {p : Args} {f : String} {d : ByteArray} {j : Args} {x : Bool}
    {us : List Usage} {k : Key} (h : importKey n p f d j x us = .ok k) :
    k.usages = us ∧ k.extractable = x ∧ (k.type ≠ .publicKey → us ≠ []) := by
  unfold importKey at h
  cases hm : importMade n p f d j x us with
  | error e => rw [hm] at h; cases h
  | ok m =>
    rw [hm] at h
    have := finishKey_ok h
    exact ⟨this.1, this.2.1, this.2.2.2⟩

/-! ## Checks (pure parts; the externs do not run in the interpreter) -/

#guard readTlv (tlv 0x30 (List.replicate 200 7) ++ [9]) == some (0x30, List.replicate 200 7, [9])
#guard readTlv [0x30, 0x81, 0x05, 1, 2, 3, 4, 5] == none  -- non-minimal length
#guard readTlv [0x30, 0x80] == none                        -- indefinite length
#guard (spkiOf oidEd25519 [] (List.replicate 32 0)).length == 44
#guard readSpki (spkiOf oidEd25519 [] (List.replicate 32 5)) == some (oidEd25519, none, List.replicate 32 5)
#guard (readPkcs8 (pkcs8Of oidX25519 [] (tlv 0x04 (List.replicate 32 1)))).map (·.2.2) == some (tlv 0x04 (List.replicate 32 1))
-- The WPT fixture's P-256 SPKI header (WebCryptoAPI/util/ec_key_fixtures.js).
#guard (spkiOf oidEcPublicKey (tlv 0x06 oidP256) (4 :: List.replicate 64 0)).take 27 ==
  [48, 89, 48, 19, 6, 7, 42, 134, 72, 206, 61, 2, 1, 6, 8, 42, 134, 72, 206, 61, 3, 1, 7, 3, 66, 0, 4]
#guard ed25519IsSmallOrder (ByteArray.mk ((List.replicate 32 (0 : UInt8)).set 31 0x80).toArray)
#guard !ed25519IsSmallOrder (ByteArray.mk (List.replicate 32 (9 : UInt8)).toArray)
#guard (normalizeSpec "deriveBits" "pbkdf2").toOption.map (·.1) == some "PBKDF2"
#guard (normalizeSpec "encrypt" "AES-GCM").isOk == false
#guard Usage.ofName? "decapsulateKey" == some .decapsulateKey
#guard truncateBits (ByteArray.mk #[0xff, 0xff]) 12 == ByteArray.mk #[0xff, 0xf0]
#guard Err.all.map Err.code == [-20, -23, -24, -25, -26, -22, -27]

end L4Factoidal.Crypto.WebCryptoKeys
