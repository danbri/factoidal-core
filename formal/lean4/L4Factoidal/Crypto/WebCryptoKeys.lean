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
(DER). Records: docs/designissues/2026-11-09-hacl-web-crypto.md and
2026-11-14-webcrypto.md (`supports`, `getPublicKey`, the usage and format theorems).

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
import L4Factoidal.JOSE.Pkcs1
import L4Factoidal.Crypto.OaepEncoding
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

/-- The algorithms this engine has keys for. AES is not here: HACL* has no portable AES
(record, "What stays off"). RSA keys are imported, never generated: HACL* has no prime
generation (`generateKey_rsa_refused`). -/
inductive Alg where
  | hmac | hkdf | pbkdf2 | ecdsa | ecdh | ed25519 | x25519 | chacha | rsaPkcs1 | rsaPss | rsaOaep
  deriving DecidableEq, Repr, Inhabited

def Alg.name : Alg → String
  | .hmac => "HMAC" | .hkdf => "HKDF" | .pbkdf2 => "PBKDF2" | .ecdsa => "ECDSA" | .ecdh => "ECDH"
  | .ed25519 => "Ed25519" | .x25519 => "X25519" | .chacha => "ChaCha20-Poly1305"
  | .rsaPkcs1 => "RSASSA-PKCS1-v1_5" | .rsaPss => "RSA-PSS" | .rsaOaep => "RSA-OAEP"

def Alg.isRsa (a : Alg) : Bool := a == .rsaPkcs1 || a == .rsaPss || a == .rsaOaep

/-- A key's `[[algorithm]]`. -/
structure KeyAlgo where
  alg : Alg
  hash : Option HashAlg := none
  /-- HMAC: the length in bits. -/
  length : Nat := 0
  /-- ECDSA, ECDH: the named curve (only "P-256" makes keys here). -/
  curve : String := ""
  /-- RSA: the modulus length in bits and the public exponent (big-endian). -/
  modulusLength : Nat := 0
  publicExponent : ByteArray := ByteArray.empty
  deriving Inhabited

/-- The parts of an RSA key (RFC 8017 §3), big-endian with no leading zero octet: `n` and
`e` always; the private parts empty in a public key. -/
structure RsaParts where
  n : ByteArray
  e : ByteArray
  d : ByteArray := ByteArray.empty
  p : ByteArray := ByteArray.empty
  q : ByteArray := ByteArray.empty
  dp : ByteArray := ByteArray.empty
  dq : ByteArray := ByteArray.empty
  qi : ByteArray := ByteArray.empty
  deriving Inhabited

/-- The public half of RSA parts. -/
def RsaParts.public (r : RsaParts) : RsaParts := { n := r.n, e := r.e }

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
  /-- RSA keys: their parts (`material` is then `d`, or `n` for a public key). -/
  rsa : Option RsaParts := none
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
  | .rsaPkcs1, .privateKey | .rsaPss, .privateKey => [.sign]
  | .rsaPkcs1, _ | .rsaPss, _ => [.verify]
  | .rsaOaep, .privateKey => [.decrypt, .unwrapKey]
  | .rsaOaep, _ => [.encrypt, .wrapKey]

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
   "ChaCha20-Poly1305", "AES-OCB", "Ed448", "X448", "ML-DSA-44", "ML-DSA-65", "ML-DSA-87",
   "ML-KEM-512", "ML-KEM-768", "ML-KEM-1024", "MLKEM768-P256", "MLKEM768-X25519", "MLKEM1024-P384",
   "KMAC128", "KMAC256", "SHA3-256", "SHA3-384", "SHA3-512", "cSHAKE128", "cSHAKE256"]

def normalizeSpec (op name : String) : Res (String × List String) :=
  match (registered.find? (WebCrypto.asciiUpper · == WebCrypto.asciiUpper name)) with
  | none => .error .notSupported
  | some reg =>
    let r (ms : List String) : Res (String × List String) := .ok (reg, ms)
    match op, reg with
    | "digest", "SHA-1" | "digest", "SHA-256" | "digest", "SHA-384" | "digest", "SHA-512" => r []
    -- SHA-3 and cSHAKE (modern algorithms draft): HACL*'s Hacl_Hash_SHA3 (`digestExt`).
    | "digest", "SHA3-256" | "digest", "SHA3-384" | "digest", "SHA3-512" => r []
    | "digest", "cSHAKE128" | "digest", "cSHAKE256" => r ["customization:b", "functionName:b", "outputLength:l!"]
    -- exportKey and getPublicKey take no parameters: registered for `supports` (the
    -- operations themselves read the key's own algorithm).
    | "exportKey", "HMAC" | "exportKey", "ECDSA" | "exportKey", "ECDH" | "exportKey", "Ed25519"
    | "exportKey", "X25519" | "exportKey", "ChaCha20-Poly1305" | "exportKey", "RSASSA-PKCS1-v1_5"
    | "exportKey", "RSA-PSS" | "exportKey", "RSA-OAEP" => r []
    | "getPublicKey", "ECDSA" | "getPublicKey", "ECDH" | "getPublicKey", "Ed25519" | "getPublicKey", "X25519"
    | "getPublicKey", "RSASSA-PKCS1-v1_5" | "getPublicKey", "RSA-PSS" | "getPublicKey", "RSA-OAEP" => r []
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
    | "generateKey", "RSASSA-PKCS1-v1_5" | "generateKey", "RSA-PSS" | "generateKey", "RSA-OAEP" =>
      r ["modulusLength:l!", "publicExponent:n!", "hash:h!"]
    | "importKey", "RSASSA-PKCS1-v1_5" | "importKey", "RSA-PSS" | "importKey", "RSA-OAEP" => r ["hash:h!"]
    | "sign", "RSASSA-PKCS1-v1_5" | "verify", "RSASSA-PKCS1-v1_5" => r []
    | "sign", "RSA-PSS" | "verify", "RSA-PSS" => r ["saltLength:l!"]
    | "encrypt", "RSA-OAEP" | "decrypt", "RSA-OAEP" => r ["label:b"]
    -- Algorithms this engine has no keys for (`refusedSpec?`): registered for generateKey,
    -- importKey and "get key length" only, so those operations make their checks of the
    -- arguments in the specification's order before they refuse (`generateRefusedErr`,
    -- `importRefusedErr`, `keyLength`). Every other operation refuses them at once.
    | "generateKey", "AES-CTR" | "generateKey", "AES-CBC" | "generateKey", "AES-GCM" | "generateKey", "AES-KW"
    | "generateKey", "AES-OCB" | "get key length", "AES-CTR" | "get key length", "AES-CBC"
    | "get key length", "AES-GCM" | "get key length", "AES-KW" | "get key length", "AES-OCB" => r ["length:l!"]
    | "generateKey", "KMAC128" | "generateKey", "KMAC256" => r ["length:l"]
    | "generateKey", "Ed448" | "generateKey", "X448" | "generateKey", "ML-DSA-44" | "generateKey", "ML-DSA-65"
    | "generateKey", "ML-DSA-87" | "generateKey", "ML-KEM-512" | "generateKey", "ML-KEM-768"
    | "generateKey", "ML-KEM-1024" | "generateKey", "MLKEM768-P256" | "generateKey", "MLKEM768-X25519"
    | "generateKey", "MLKEM1024-P384" => r []
    | "importKey", "AES-CTR" | "importKey", "AES-CBC" | "importKey", "AES-GCM" | "importKey", "AES-KW"
    | "importKey", "AES-OCB" | "importKey", "Ed448" | "importKey", "X448" => r []
    | _, _ => .error .notSupported

def algOf? (name : String) : Option Alg :=
  [Alg.hmac, .hkdf, .pbkdf2, .ecdsa, .ecdh, .ed25519, .x25519, .chacha, .rsaPkcs1, .rsaPss, .rsaOaep].find? (·.name == name)


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
  rsa : Option RsaParts := none

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

/-! ## Registered algorithms without keys here

AES (no portable AES in HACL*), Ed448 and X448, ML-DSA, ML-KEM and the hybrid KEMs, and
KMAC; and RSA for generateKey only (no prime generation in HACL*; imported RSA keys work). Each is refused with NotSupportedError, as before 2026-11-13; what
changed is the order: generateKey and importKey first make the checks of their arguments that
come before key generation or key import in the specification (usages: SyntaxError; parameters:
OperationError; key data: DataError), as an engine with the algorithm does. The functions below
return an `Err`, not a `Res`: they can make no key, by their type. No key bytes are read or
made on these paths. -/

/-- The usages of a registered algorithm without keys here: `pub` of a secret key (or of a
pair's public key), `priv` of a pair's private key. -/
structure RefusedSpec where
  pub : List Usage
  priv : List Usage
  pair : Bool

def refusedSpec? : String → Option RefusedSpec
  | "AES-CTR" | "AES-CBC" | "AES-GCM" | "AES-OCB" => some ⟨[.encrypt, .decrypt, .wrapKey, .unwrapKey], [], false⟩
  | "AES-KW" => some ⟨[.wrapKey, .unwrapKey], [], false⟩
  | "KMAC128" | "KMAC256" => some ⟨[.sign, .verify], [], false⟩
  | "RSASSA-PKCS1-v1_5" | "RSA-PSS" | "Ed448" | "ML-DSA-44" | "ML-DSA-65" | "ML-DSA-87" =>
    some ⟨[.verify], [.sign], true⟩
  | "RSA-OAEP" => some ⟨[.encrypt, .wrapKey], [.decrypt, .unwrapKey], true⟩
  | "X448" => some ⟨[], [.deriveKey, .deriveBits], true⟩
  | "ML-KEM-512" | "ML-KEM-768" | "ML-KEM-1024" | "MLKEM768-P256" | "MLKEM768-X25519" | "MLKEM1024-P384" =>
    some ⟨[.encapsulateBits, .encapsulateKey], [.decapsulateBits, .decapsulateKey], true⟩
  | _ => none

/-- AES key lengths in bits (§27-§30 "generate key" step 2, "get key length" step 1). -/
def aesLengthOk (n : Nat) : Bool := n == 128 || n == 192 || n == 256

/-- A generateKey parameter an engine with the algorithm would refuse with OperationError:
an AES length other than 128, 192 or 256; an RSA public exponent other than 3 or 65537 (the
exponents engines generate with; others are a generation failure). -/
def refusedBadParams (name : String) (p : Args) : Bool :=
  if name.startsWith "AES-" then !aesLengthOk ((p.nat? "length").getD 0)
  else if name.startsWith "RSA" then
    let e := ((p.get? "publicExponent").getD .empty).toList.dropWhile (· == 0)
    !(e == [1, 0, 1] || e == [3])
  else false

/-- generateKey of an algorithm without keys here: usages (SyntaxError), parameters
(OperationError), a key that would have no usage (SyntaxError), then NotSupportedError. -/
def generateRefusedErr (name : String) (p : Args) (us : List Usage) : Err :=
  match refusedSpec? name with
  | none => .notSupported
  | some r =>
    if !us.all ((r.pub ++ r.priv).contains ·) then .syntax
    else if refusedBadParams name p then .operation
    else if r.pair && us.all (fun u => !r.priv.contains u) then .syntax
    else if !r.pair && us.isEmpty then .syntax
    else .notSupported

/-- The SPKI and PKCS #8 OID and key size of Ed448 and X448 (RFC 8410). -/
def okp448? : String → Option (List UInt8 × Nat)
  | "Ed448" => some ([0x2b, 0x65, 0x71], 57)
  | "X448" => some ([0x2b, 0x65, 0x6f], 56)
  | _ => none

/-- importKey of an algorithm without keys here: the checks of the algorithm's "import key"
steps that need no key operation (usages, then the format's encoding and sizes, then the JWK
members), then a secret or private key with no usage (SyntaxError), then NotSupportedError. -/
def importRefusedErr (name : String) (format : String) (data : ByteArray) (j : Args) (extractable : Bool)
    (us : List Usage) : Err :=
  let checks : Res Bool := do
    let some r := refusedSpec? name | throw .notSupported
    if !r.pair then
      -- AES (§27-§30 "import key"): raw or jwk, 128, 192 or 256 bits.
      checkUsages r.pub us
      match format with
      | "raw" | "raw-secret" => if !aesLengthOk (data.size * 8) then throw .data
      | "jwk" =>
        if j.str? "kty" != some "oct" then throw .data
        let some k := (j.str? "k").bind unb64? | throw .data
        if !aesLengthOk (k.size * 8) then throw .data
        jwkCommon j us extractable "enc"
      | _ => throw .notSupported
      return true
    match okp448? name with
    | some (oid, size) =>
      match format with
      | "spki" =>
        checkUsages r.pub us
        let some (o, params, key) := readSpki data.toList | throw .data
        if o != oid || params.isSome || key.length != size then throw .data
        return false
      | "pkcs8" =>
        checkUsages r.priv us
        let some (o, params, pk) := readPkcs8 data.toList | throw .data
        if o != oid || params.isSome then throw .data
        let some (sk, []) := expect 0x04 pk | throw .data
        if sk.length != size then throw .data
        return true
      | "raw" | "raw-public" =>
        checkUsages r.pub us
        if data.size != size then throw .data
        return false
      | "jwk" =>
        let hasD := j.has "d"
        checkUsages (if hasD then r.priv else r.pub) us
        if j.str? "kty" != some "OKP" then throw .data
        if j.str? "crv" != some name then throw .data
        if name == "Ed448" then
          if let some a := j.str? "alg" then
            if a != "Ed448" && a != "EdDSA" then throw .data
        jwkCommon j us extractable (if name == "Ed448" then "sig" else "enc")
        let some x := (j.str? "x").bind unb64? | throw .data
        if x.size != size then throw .data
        if hasD then
          let some d := (j.str? "d").bind unb64? | throw .data
          if d.size != size then throw .data
        return hasD
      | _ => throw .notSupported
    | none => throw .notSupported
  match checks with
  | .error e => e
  | .ok needsUsage => if needsUsage && us.isEmpty then .syntax else .notSupported

/-! ## RSA keys (RFC 8017 Appendix A.1, RFC 5280 §4.1, RFC 7518 §6.3) -/

def oidRsaEncryption : List UInt8 := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01]

/-- A DER INTEGER's contents as a non-negative number: big-endian, no leading zero
octet. `none` for a negative or non-minimal encoding (X.690 §8.3.2). -/
def readUInt (c : List UInt8) : Option ByteArray :=
  match c with
  | [] => none
  | 0 :: [] => some ByteArray.empty
  | 0 :: b :: rest => if b < 0x80 then none else some (ByteArray.mk (b :: rest).toArray)
  | b :: rest => if b ≥ 0x80 then none else some (ByteArray.mk (b :: rest).toArray)

/-- The DER INTEGER contents of a non-negative big-endian number. -/
def uintContents (b : ByteArray) : List UInt8 :=
  match b.toList.dropWhile (· == 0) with
  | [] => [0]
  | x :: rest => if x ≥ 0x80 then 0 :: x :: rest else x :: rest

def derUInt (b : ByteArray) : List UInt8 := tlv 0x02 (uintContents b)

def stripZeros (b : ByteArray) : ByteArray := ByteArray.mk (b.toList.dropWhile (· == 0)).toArray

/-- Bit length of a big-endian number. -/
def bitLength (b : ByteArray) : Nat :=
  match b.toList.dropWhile (· == 0) with
  | [] => 0
  | x :: rest => rest.length * 8 + (Nat.log2 x.toNat + 1)

/-- A sequence of DER INTEGERs filling `c` exactly. -/
def readUInts (c : List UInt8) (n : Nat) : Option (List ByteArray) := Id.run do
  let mut rest := c
  let mut out : Array ByteArray := #[]
  for _ in [0:n] do
    match expect 0x02 rest with
    | some (v, r) =>
      match readUInt v with
      | some x => out := out.push x; rest := r
      | none => return none
    | none => return none
  if rest.isEmpty then return some out.toList else return none

def rsaPublicDer (r : RsaParts) : List UInt8 := tlv 0x30 (derUInt r.n ++ derUInt r.e)

def rsaPrivateDer (r : RsaParts) : List UInt8 :=
  tlv 0x30 (tlv 0x02 [0] ++ derUInt r.n ++ derUInt r.e ++ derUInt r.d ++ derUInt r.p ++ derUInt r.q ++
    derUInt r.dp ++ derUInt r.dq ++ derUInt r.qi)

/-- The RSA keys this engine can use: moduli of 1024 to 4096 bits whose octets fill
whole 64-bit limbs (HACL*'s Hacl_Bignum64), and an odd public exponent above 1. -/
def rsaUsable (r : RsaParts) : Bool :=
  r.n.size % 8 == 0 && 128 ≤ r.n.size && r.n.size ≤ 512 && r.n.size > 0 && r.n.get! (r.n.size - 1) % 2 == 1 &&
    r.e.size > 0 && r.e.size ≤ r.n.size && r.e.get! (r.e.size - 1) % 2 == 1 && bitLength r.e > 1

def rsaJwkAlg (alg : Alg) (h : HashAlg) : String :=
  match alg, h with
  | .rsaPkcs1, .sha1 => "RS1" | .rsaPkcs1, .sha256 => "RS256" | .rsaPkcs1, .sha384 => "RS384"
  | .rsaPkcs1, .sha512 => "RS512"
  | .rsaPss, .sha1 => "PS1" | .rsaPss, .sha256 => "PS256" | .rsaPss, .sha384 => "PS384" | .rsaPss, .sha512 => "PS512"
  | _, .sha1 => "RSA-OAEP" | _, .sha256 => "RSA-OAEP-256" | _, .sha384 => "RSA-OAEP-384" | _, .sha512 => "RSA-OAEP-512"

/-- RSASSA-PKCS1-v1_5, RSA-PSS, RSA-OAEP "import key" (§20.8, §21.8, §22.8). -/
def importRsa (alg : Alg) (format : String) (data : ByteArray) (j : Args) (p : Args) (us : List Usage)
    (extractable : Bool) : Res Made := do
  let pubU := allowedUsages alg .publicKey
  let privU := allowedUsages alg .privateKey
  let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
  let made := fun (t : KeyType) (r : RsaParts) => do
    if !rsaUsable r then throw .data
    -- HACL*'s PSS is SHA-2 only.
    if alg == .rsaPss && h == .sha1 then throw .notSupported
    let algo : KeyAlgo := { alg, hash := some h, modulusLength := bitLength r.n, publicExponent := r.e }
    pure ({ type := t, algo, material := if t == .privateKey then r.d else r.n, rsa := some r } : Made)
  match format with
  | "spki" =>
    checkUsages pubU us
    let some (oid, params, key) := readSpki data.toList | throw .data
    if oid != oidRsaEncryption then throw .data
    if let some ps := params then if ps != [0x05, 0x00] then throw .data
    let some (seq, []) := expect 0x30 key | throw .data
    let some [n, e] := readUInts seq 2 | throw .data
    made .publicKey { n, e }
  | "pkcs8" =>
    checkUsages privU us
    let some (oid, params, pk) := readPkcs8 data.toList | throw .data
    if oid != oidRsaEncryption then throw .data
    if let some ps := params then if ps != [0x05, 0x00] then throw .data
    let some (seq, []) := expect 0x30 pk | throw .data
    let some [v, n, e, d, p', q, dp, dq, qi] := readUInts seq 9 | throw .data
    if v.size != 0 then throw .data
    made .privateKey { n, e, d, p := p', q, dp, dq, qi }
  | "jwk" =>
    let hasD := j.has "d"
    checkUsages (if hasD then privU else pubU) us
    if j.str? "kty" != some "RSA" then throw .data
    if let some a := j.str? "alg" then
      if a != rsaJwkAlg alg h then throw .data
    jwkCommon j us extractable (if alg == .rsaOaep then "enc" else "sig")
    let b := fun (k : String) => match (j.str? k).bind unb64? with
      | some x => Except.ok (stripZeros x) | none => Except.error Err.data
    let n ← b "n"
    let e ← b "e"
    if hasD then
      if j.has "oth" then throw .notSupported
      made .privateKey { n, e, d := ← b "d", p := ← b "p", q := ← b "q", dp := ← b "dp", dq := ← b "dq", qi := ← b "qi" }
    else made .publicKey { n, e }
  | _ => throw .notSupported

/-- The algorithm's import steps. -/
def importMade (algName : String) (p : Args) (format : String) (data : ByteArray) (j : Args)
    (extractable : Bool) (us : List Usage) : Res Made :=
  match algOf? algName with
  | none => .error (importRefusedErr algName format data j extractable us)
  | some alg =>
    match alg with
    | .ecdsa | .ecdh => importEc alg format data j ((p.str? "namedCurve").getD "") us extractable
    | .ed25519 | .x25519 => importOkp alg format data j us extractable
    | .rsaPkcs1 | .rsaPss | .rsaOaep => importRsa alg format data j p us extractable
    | _ => importSecret alg format data j p us extractable

/-- §14.3.9 steps 10-11: a secret or private key with no usages is a SyntaxError; then
the key takes `extractable` and the usages. -/
def finishKey (m : Made) (extractable : Bool) (us : List Usage) : Res Key :=
  if (m.type == .secret || m.type == .privateKey) && us.isEmpty then .error .syntax
  else .ok { type := m.type, extractable, algo := m.algo, usages := us, material := m.material, pub := m.pub, rsa := m.rsa }

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
  | .rsaPkcs1 | .rsaPss | .rsaOaep =>
    let r := k.rsa.getD { n := k.material, e := k.algo.publicExponent }
    match format, k.type with
    | "spki", .publicKey =>
      return .bytes (ByteArray.mk (spkiOf oidRsaEncryption [0x05, 0x00] (rsaPublicDer r)).toArray)
    | "pkcs8", .privateKey =>
      return .bytes (ByteArray.mk (pkcs8Of oidRsaEncryption [0x05, 0x00] (rsaPrivateDer r)).toArray)
    | "jwk", t =>
      let base := [("kty", JwkVal.str "RSA"), ("n", .str (b64 r.n)), ("e", .str (b64 r.e))]
      let priv := if t == .privateKey then
          [("d", JwkVal.str (b64 r.d)), ("p", .str (b64 r.p)), ("q", .str (b64 r.q)), ("dp", .str (b64 r.dp)),
           ("dq", .str (b64 r.dq)), ("qi", .str (b64 r.qi))] else []
      let a := match k.algo.hash with | some h => [("alg", JwkVal.str (rsaJwkAlg alg h))] | none => []
      return .jwk (base ++ priv ++ a ++ jwkCommonOut k)
    | "spki", _ | "pkcs8", _ => throw .invalidAccess
    | _, _ => throw .notSupported
  | .hkdf | .pbkdf2 => throw .notSupported

/-- §14.3.10 exportKey: InvalidAccessError unless the key is extractable; only then are
its bytes read (`exportKey_extractable`, `exportKey_blind`). -/
def exportKey (k : Key) (format : String) : Res Exported :=
  -- §14.3.10 step 6 (an algorithm with no export: NotSupportedError) before step 7.
  if k.algo.alg == .hkdf || k.algo.alg == .pbkdf2 then .error .notSupported
  else if k.extractable then exportBody k format else .error .invalidAccess

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
  | some .rsaPkcs1 | some .rsaPss | some .rsaOaep => 0
  | some _ => 32
  | none => 0

def firstValidScalar (r : ByteArray) : Option ByteArray :=
  (List.range 8).findSome? fun i =>
    let c := r.extract (32 * i) (32 * i + 32)
    if p256ValidPrivate c then some c else none

def generateKey (algName : String) (p : Args) (extractable : Bool) (us : List Usage) (rand : Rand) :
    Res Made2 := do
  let some alg := algOf? algName | throw (generateRefusedErr algName p us)
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
  | .rsaPkcs1 | .rsaPss | .rsaOaep =>
    -- HACL* has no prime generation, so no RSA key is ever generated: the checks of the
    -- arguments in the specification's order (§20.7: usages, then an exponent other than
    -- 3 or 65537 fails the generation, then a pair with no private usage), then
    -- NotSupportedError. `generateRefusedErr` has type `Err`: it cannot make a key.
    throw (generateRefusedErr algName p us)
  | .ecdsa | .ecdh | .ed25519 | .x25519 =>
    checkUsages ((allowedUsages alg .publicKey) ++ (allowedUsages alg .privateKey)) us
    let curve := (p.str? "namedCurve").getD ""
    if alg == .ecdsa || alg == .ecdh then
      if curve != "P-256" && curve != "P-384" && curve != "P-521" then throw .notSupported
      -- §23.7 and §24.4: a private key with no usage is a SyntaxError; checked before P-384
      -- and P-521 are refused (no keys for them here), as an engine with them would.
      if us.all (fun u => !(allowedUsages alg .privateKey).contains u) then throw .syntax
      if curve != "P-256" then throw .notSupported
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

/-- The DER DigestInfo prefix of EMSA-PKCS1-v1_5 (RFC 8017 §9.2 note 1). -/
def digestInfo : HashAlg → List UInt8
  | .sha1 => JOSE.Pkcs1.sha1DigestInfo | .sha256 => JOSE.Pkcs1.sha256DigestInfo
  | .sha384 => JOSE.Pkcs1.sha384DigestInfo | .sha512 => JOSE.Pkcs1.sha512DigestInfo

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
  | .rsaPkcs1 =>
    if k.type != .privateKey then throw .invalidAccess
    let (some r, some h) := (k.rsa, k.algo.hash) | throw .operation
    let some em := JOSE.Pkcs1.emsaEncodeGen (digestInfo h) h.size (hashFast h data).toList r.n.size | throw .operation
    let some s := rsaPrivate? r.n r.d (ByteArray.mk em.toArray) | throw .operation
    return s
  | .rsaPss =>
    if k.type != .privateKey then throw .invalidAccess
    let (some r, some h) := (k.rsa, k.algo.hash) | throw .operation
    let sl := (p.nat? "saltLength").getD 0
    if rand.size < sl then throw .operation
    let some s := rsaPssSign? h r.n r.e r.d (rand.extract 0 sl) data | throw .operation
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
  | .rsaPkcs1 =>
    if k.type != .publicKey then throw .invalidAccess
    let (some r, some h) := (k.rsa, k.algo.hash) | throw .operation
    if sig.size != r.n.size then return false
    -- RFC 8017 §8.2.2: RSAVP1, then the encoding of the message compared at full length
    -- (public values: the signature and the message).
    match rsaPublic? r.n r.e sig, JOSE.Pkcs1.emsaEncodeGen (digestInfo h) h.size (hashFast h data).toList r.n.size with
    | some em, some want => return em.toList == want
    | _, _ => return false
  | .rsaPss =>
    if k.type != .publicKey then throw .invalidAccess
    let (some r, some h) := (k.rsa, k.algo.hash) | throw .operation
    return rsaPssVerify h r.n r.e ((p.nat? "saltLength").getD 0) sig data
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

/-- The errors `deriveBits` would give, without deriving: for a `deriveKey` whose derived
key's algorithm has no keys here (`refusedSpec?`), so that its refusal comes after the same
errors in the same order but no bits are computed only to be dropped (PBKDF2 at 100,000
iterations takes milliseconds). A derivation that would fail only inside the primitive (an
ECDH point HACL* refuses) is not seen here: the refusal answers instead. -/
def deriveBitsCheck (algName : String) (p : Args) (k : Key) (length : Option Nat) (store : KeyStore) : Res Unit := do
  keyFor k algName .deriveBits
  match k.algo.alg with
  | .hkdf =>
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    let some len := length | throw .operation
    if len % 8 != 0 || len / 8 > 255 * h.size then throw .operation
  | .pbkdf2 =>
    let some _ := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    let some len := length | throw .operation
    if len % 8 != 0 then throw .operation
    if (p.nat? "iterations").getD 0 == 0 then throw .operation
  | .ecdh | .x25519 =>
    if k.type != .privateKey then throw .invalidAccess
    let pk ← keyOf store p "public"
    if pk.type != .publicKey || pk.algo.alg != k.algo.alg then throw .invalidAccess
    if k.algo.alg == .ecdh && pk.algo.curve != k.algo.curve then throw .invalidAccess
    if let some len := length then
      if len > 256 then throw .operation
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
  | none =>
    -- AES (§27-§30 "get key length"): its length, which must be 128, 192 or 256. The key's
    -- import is then refused (`importRefusedErr`), after the derivation's own checks.
    if algName.startsWith "AES-" && (refusedSpec? algName).isSome then
      let some l := t.nat? "length" | throw .typeError
      if !aesLengthOk l then throw .operation
      return some l
    throw .notSupported
  | _ => throw .notSupported

/-- ChaCha20-Poly1305 (modern algorithms draft, "encrypt" and "decrypt"). -/
def crypt (enc : Bool) (algName : String) (p : Args) (k : Key) (data : ByteArray) (rand : Rand := .empty) :
    Res ByteArray := do
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
  | .rsaOaep =>
    -- §22.3/22.4: encrypt with a public key, decrypt with a private one; EME-OAEP is Lean's
    -- (`Crypto.RsaOaep`, with its single refusal for every decoding failure), RSAEP and
    -- RSADP are HACL*'s.
    let (some r, some h) := (k.rsa, k.algo.hash) | throw .operation
    let oh : RsaOaep.OaepHash := ⟨hashFast h, h.size⟩
    let label := ((p.get? "label").getD .empty).toList
    if enc then
      if k.type != .publicKey then throw .invalidAccess
      if rand.size < h.size then throw .operation
      let some em := RsaOaep.emeEncode oh r.n.size label data.toList (rand.extract 0 h.size).toList | throw .operation
      let some c := rsaPublic? r.n r.e (ByteArray.mk em.toArray) | throw .operation
      return c
    else
      if k.type != .privateKey then throw .invalidAccess
      if data.size != r.n.size then throw .operation
      let some em := rsaPrivate? r.n r.d data | throw .operation
      let some m := RsaOaep.emeDecode oh r.n.size label em.toList | throw .operation
      return ByteArray.mk m.toArray
  | _ => throw .invalidAccess

/-! ## Digests beyond SHA-1 and SHA-2: SHA-3 and cSHAKE (modern algorithms draft)

HACL*'s `Hacl_Hash_SHA3` (`WebHacl.sha3?`). There is no pure-Lean twin and no fallback: where
HACL* cannot answer, the digest is refused. -/

def sha3Of? : String → Option Sha3Alg
  | "SHA3-256" => some .sha3_256 | "SHA3-384" => some .sha3_384 | "SHA3-512" => some .sha3_512
  | "cSHAKE128" => some .shake128 | "cSHAKE256" => some .shake256
  | _ => none

/-- The output length in octets of a cSHAKE digest this engine can serve. cSHAKE with an
empty function name and an empty customization is SHAKE (SP 800-185 §3.3), which HACL* has.
With either one non-empty it is the Keccak sponge with another domain byte, which HACL*
does not expose at the pin: NotSupportedError, not an implementation of our own. A length
that is not whole octets, or above `maxXofBytes`, is an OperationError. -/
def cshakeLen (p : Args) : Res Nat := do
  if ((p.get? "functionName").getD .empty).size != 0 || ((p.get? "customization").getD .empty).size != 0 then
    throw .notSupported
  let some bits := p.nat? "outputLength" | throw .typeError
  if bits % 8 != 0 || bits / 8 > maxXofBytes then throw .operation
  return bits / 8

/-- `digest` of SHA3-256/384/512 and cSHAKE128/256 (`name` as registered). -/
def digestExt (name : String) (p : Args) (data : ByteArray) : Res ByteArray := do
  let some a := sha3Of? name | throw .notSupported
  let n ← match a.fixed with
    | some n => pure n
    | none => cshakeLen p
  match sha3? a n data with
  | some d => return d
  | none => throw .operation

/-- Kind: policy invariant (no cSHAKE of our own). Says: a cSHAKE digest asked with a
non-empty function name is refused with NotSupportedError, whatever the other arguments: no
bytes are computed. Does not say: anything of the empty-name case, which is HACL*'s SHAKE. -/
theorem cshakeLen_named_refused (p : Args) (h : ((p.get? "functionName").getD .empty).size ≠ 0) :
    cshakeLen p = .error .notSupported := by
  unfold cshakeLen
  simp [h]
  rfl

#guard sha3Of? "SHA3-384" == some .sha3_384
#guard sha3Of? "SHA-384" == none
#guard (cshakeLen #[("outputLength", "256".toUTF8)]).toOption == some 32
#guard (cshakeLen #[("outputLength", "0".toUTF8)]).toOption == some 0
#guard (cshakeLen #[("outputLength", "12".toUTF8)]).isOk == false
#guard (cshakeLen #[("outputLength", "256".toUTF8), ("customization", "x".toUTF8)]).isOk == false
-- A cSHAKE digest of no bits is the empty string, with no call to the primitive.
#guard (digestExt "cSHAKE128" #[("outputLength", "0".toUTF8)] "abc".toUTF8).toOption == some ByteArray.empty
#guard (digestExt "KMAC128" #[] .empty).isOk == false
#guard (normalizeSpec "digest" "sha3-256").toOption == some ("SHA3-256", [])
#guard (normalizeSpec "digest" "CSHAKE128").toOption.map (·.1) == some "cSHAKE128"
#guard (normalizeSpec "digest" "KMAC128").isOk == false
#guard (normalizeSpec "sign" "SHA3-256").isOk == false

/-! ## getPublicKey (modern algorithms draft): the public key of a private key -/

/-- The algorithms whose private keys carry their public key. -/
def Alg.hasPair : Alg → Bool
  | .ecdsa | .ecdh | .ed25519 | .x25519 | .rsaPkcs1 | .rsaPss | .rsaOaep => true
  | _ => false

/-- `getPublicKey(key, usages)`: NotSupportedError for an algorithm without key pairs,
InvalidAccessError unless the key is private, SyntaxError for a usage a public key of the
algorithm cannot have; then the pair's public key, extractable, with those usages. It is
built from the public parts the private key carries (`pub`, or RSA's `n` and `e`): no
primitive runs. -/
def getPublicKey (k : Key) (us : List Usage) : Res Key :=
  if !k.algo.alg.hasPair then .error .notSupported
  else if k.type != .privateKey then .error .invalidAccess
  else if !us.all ((allowedUsages k.algo.alg .publicKey).contains ·) then .error .syntax
  else .ok { type := .publicKey, extractable := true, algo := k.algo, usages := us,
             material := if k.algo.alg.isRsa then (k.rsa.map (·.n)).getD ByteArray.empty else k.pub,
             rsa := k.rsa.map RsaParts.public }

/-- A private key with its private bytes replaced: the scalar or seed (`material`) and the
private parts of an RSA key. Its public parts stay. -/
def Key.hidePrivate (k : Key) : Key := { k with material := ByteArray.empty, rsa := k.rsa.map RsaParts.public }

/-- Kind: security invariant (key material). Says: the key `getPublicKey` answers is the
same whatever the private bytes of the key it was given (the scalar, the seed, RSA's d, p, q
and CRT values): it is a function of the public parts only, so no private byte can reach the
page through it, extractable or not. Does not say: that the public parts stored with a
private key are the right ones for it (import and generate make them, by HACL*). -/
theorem getPublicKey_hidePrivate (k : Key) (us : List Usage) :
    getPublicKey k.hidePrivate us = getPublicKey k us := by
  unfold getPublicKey Key.hidePrivate
  cases hr : k.rsa <;> simp [RsaParts.public]

/-- Kind: API contract. Says: a key `getPublicKey` answers is public, extractable, has
exactly the usages asked for, each one a usage a public key of the algorithm may have, and
came from a private key. Does not say: which error a refusal is. -/
theorem getPublicKey_ok {k pk : Key} {us : List Usage} (h : getPublicKey k us = .ok pk) :
    pk.type = .publicKey ∧ pk.extractable = true ∧ pk.usages = us ∧ k.type = .privateKey ∧
      ∀ u ∈ us, u ∈ allowedUsages k.algo.alg .publicKey := by
  unfold getPublicKey at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hpriv
      split at h
      · cases h
      · rename_i hall
        cases h
        refine ⟨rfl, rfl, rfl, by simpa using hpriv, ?_⟩
        intro u hu
        have hall' : us.all ((allowedUsages k.algo.alg .publicKey).contains ·) = true := by simpa using hall
        simpa using List.all_eq_true.mp hall' u hu

/-! ## supports (modern algorithms draft `SubtleCrypto.supports`)

Whether an operation with these (already normalized) parameters can succeed here for some
key and data. It answers from the same tables the operations use and is truthful about what
this engine refuses: AES, P-384 and P-521, Ed448 and X448, ML-KEM, ML-DSA, KMAC and RSA key
generation are reported as not supported (`supports_refused`). -/

def hashOf (p : Args) : Option HashAlg := (p.str? "hash").bind HashAlg.ofName?

/-- importKey can make a key of this algorithm with these parameters (for some format). -/
def importSupported (algName : String) (p : Args) : Bool :=
  match algOf? algName with
  | some .hmac => (hashOf p).isSome && p.nat? "length" != some 0
  | some .ecdsa | some .ecdh => p.str? "namedCurve" == some "P-256"
  | some .rsaPss => match hashOf p with | some h => h != .sha1 | none => false
  | some .rsaPkcs1 | some .rsaOaep => (hashOf p).isSome
  | some _ => true
  | none => false

/-- deriveBits can succeed with these parameters and this length (`none` for null). -/
def deriveSupported (algName : String) (p : Args) (length : Option Nat) (store : KeyStore) : Bool :=
  match algOf? algName with
  | some .hkdf => match hashOf p, length with
    | some h, some len => len % 8 == 0 && len / 8 ≤ 255 * h.size
    | _, _ => false
  | some .pbkdf2 => match hashOf p, length with
    | some _, some len => len % 8 == 0 && (p.nat? "iterations").getD 0 != 0
    | _, _ => false
  | some .ecdh | some .x25519 =>
    match keyOf store p "public" with
    | .ok pk => pk.type == .publicKey && pk.algo.alg.name == algName &&
        (match length with | some len => len ≤ 256 | none => true)
    | .error _ => false
  | _ => false

/-- encrypt and decrypt (and so wrapKey and unwrapKey) can succeed with these parameters. -/
def cryptSupported (algName : String) (p : Args) : Bool :=
  match algOf? algName with
  | some .chacha => ((p.get? "iv").getD .empty).size == 12 &&
      (match p.nat? "tagLength" with | some t => t == 128 | none => true)
  | some .rsaOaep => true
  | _ => false

/-- `supports(operation, algorithm, lengthOrAdditionalAlgorithm)`, after prelude.js has
normalized `algorithm` for `op` (`p`, name `algName`) and, for deriveKey and unwrapKey, the
additional algorithm for importKey (`t`) and "get key length" (`g`). `length` is deriveBits'
length. -/
def supports (op algName : String) (p t g : Args) (length : Option Nat) (store : KeyStore) : Bool :=
  let tName := (t.str? "name").getD ""
  match op with
  | "digest" =>
    (HashAlg.ofName? algName).isSome ||
      (match sha3Of? algName with
       | some a => a.fixed.isSome || (cshakeLen p).isOk
       | none => false)
  | "generateKey" =>
    match algOf? algName with
    | some .hmac => (hashOf p).isSome && p.nat? "length" != some 0
    | some .ecdsa | some .ecdh => p.str? "namedCurve" == some "P-256"
    | some .ed25519 | some .x25519 | some .chacha => true
    -- RSA: keys are imported, never generated (no prime generation in HACL*).
    | _ => false
  | "importKey" => importSupported algName p
  | "exportKey" =>
    match algOf? algName with
    | some .hkdf | some .pbkdf2 | none => false
    | some _ => true
  | "getPublicKey" => match algOf? algName with | some a => a.hasPair | none => false
  | "sign" | "verify" =>
    match algOf? algName with
    | some .hmac | some .ed25519 | some .rsaPkcs1 | some .rsaPss => true
    | some .ecdsa => (hashOf p).isSome
    | _ => false
  | "encrypt" | "decrypt" | "wrapKey" => cryptSupported algName p
  | "unwrapKey" => cryptSupported algName p && importSupported tName t
  | "deriveBits" => deriveSupported algName p length store
  | "deriveKey" =>
    importSupported tName t &&
      (match keyLength tName (if g.isEmpty then t else g) with
       | .ok len => deriveSupported algName p len store
       | .error _ => false)
  -- encapsulateKey, encapsulateBits, decapsulateKey, decapsulateBits: no KEM here.
  | _ => false

/-- Kind: policy invariant (refused algorithms are never advertised). Says: for a name that
is not an algorithm with keys here (`algOf?` answers `none`: AES, Ed448, X448, ML-KEM, ML-DSA,
KMAC, …) and not a digest this engine has, `supports` answers false for every operation, all
parameters, every length and every additional algorithm. Does not say: that `true` answers
are always followed by success (an operation can still fail on its key or data), nor
anything of RSA generateKey, P-384 or P-521, which are refused inside algorithms that have
keys here (see the `#guard`s). -/
theorem supports_refused (op algName : String) (p t g : Args) (length : Option Nat) (store : KeyStore)
    (hk : algOf? algName = none) (hd : HashAlg.ofName? algName = none) (h3 : sha3Of? algName = none) :
    supports op algName p t g length store = false := by
  unfold supports importSupported deriveSupported cryptSupported
  simp only [hk, hd, h3]
  split <;> simp
  intro _
  split <;> rfl

#guard supports "generateKey" "HMAC" #[("hash", "SHA-256".toUTF8)] #[] #[] none {} == true
#guard supports "generateKey" "HMAC" #[("hash", "SHA-256".toUTF8), ("length", "0".toUTF8)] #[] #[] none {} == false
#guard supports "generateKey" "ECDH" #[("namedCurve", "P-256".toUTF8)] #[] #[] none {} == true
#guard supports "generateKey" "ECDH" #[("namedCurve", "P-51".toUTF8)] #[] #[] none {} == false
-- Truthful refusals: P-384 keys, RSA key generation, AES.
#guard supports "generateKey" "ECDSA" #[("namedCurve", "P-384".toUTF8)] #[] #[] none {} == false
#guard supports "generateKey" "RSA-OAEP" #[("hash", "SHA-256".toUTF8)] #[] #[] none {} == false
#guard supports "importKey" "RSA-OAEP" #[("hash", "SHA-256".toUTF8)] #[] #[] none {} == true
#guard supports "importKey" "RSA-PSS" #[("hash", "SHA-1".toUTF8)] #[] #[] none {} == false
#guard supports "generateKey" "AES-GCM" #[("length", "256".toUTF8)] #[] #[] none {} == false
#guard supports "encrypt" "AES-GCM" #[] #[] #[] none {} == false
#guard supports "digest" "SHA-256" #[] #[] #[] none {} == true
#guard supports "digest" "SHA3-512" #[] #[] #[] none {} == true
#guard supports "digest" "cSHAKE128" #[("outputLength", "256".toUTF8)] #[] #[] none {} == true
#guard supports "digest" "HMAC" #[] #[] #[] none {} == false
#guard supports "sign" "SHA-256" #[] #[] #[] none {} == false
#guard supports "encrypt" "ChaCha20-Poly1305" #[("iv", ByteArray.mk (Array.replicate 12 0))] #[] #[] none {} == true
#guard supports "encrypt" "ChaCha20-Poly1305" #[("iv", ByteArray.mk (Array.replicate 10 0)), ("tagLength", "128".toUTF8)] #[] #[] none {} == false
#guard supports "encrypt" "ChaCha20-Poly1305" #[("iv", ByteArray.mk (Array.replicate 12 0)), ("tagLength", "100".toUTF8)] #[] #[] none {} == false
-- HKDF: at most 255 blocks of the hash, whole octets, never a null length (WPT supports.https.any.js).
#guard supports "deriveBits" "HKDF" #[("hash", "SHA-256".toUTF8)] #[] #[] (some (255 * 256)) {} == true
#guard supports "deriveBits" "HKDF" #[("hash", "SHA-256".toUTF8)] #[] #[] (some (255 * 256 + 8)) {} == false
#guard supports "deriveBits" "HKDF" #[("hash", "SHA-256".toUTF8)] #[] #[] (some 11) {} == false
#guard supports "deriveBits" "HKDF" #[("hash", "SHA-256".toUTF8)] #[] #[] none {} == false
#guard supports "deriveBits" "PBKDF2" #[("hash", "SHA-256".toUTF8), ("iterations", "100000".toUTF8)] #[] #[] (some 256) {} == true
#guard supports "deriveKey" "HKDF" #[("hash", "SHA-256".toUTF8)]
  #[("name", "HMAC".toUTF8), ("hash", "SHA-256".toUTF8), ("length", "65288".toUTF8)] #[] none {} == false
#guard supports "deriveKey" "HKDF" #[("hash", "SHA-256".toUTF8)]
  #[("name", "HMAC".toUTF8), ("hash", "SHA-256".toUTF8)] #[] none {} == true
#guard supports "deriveKey" "HKDF" #[("hash", "SHA-256".toUTF8)]
  #[("name", "AES-GCM".toUTF8)] #[("name", "AES-GCM".toUTF8), ("length", "256".toUTF8)] none {} == false
#guard supports "getPublicKey" "Ed25519" #[] #[] #[] none {} == true
#guard supports "getPublicKey" "HMAC" #[] #[] #[] none {} == false
#guard supports "encapsulateBits" "ML-KEM-768" #[] #[] #[] none {} == false
#guard supports "GENERATEKEY" "HMAC" #[("hash", "SHA-256".toUTF8)] #[] #[] none {} == false

/-! ## Theorems: extractability and the usages rules -/

theorem exportKey_extractable {k : Key} {f : String} {e : Exported} (h : exportKey k f = .ok e) :
    k.extractable = true := by
  unfold exportKey at h
  split at h
  · cases h
  · cases hk : k.extractable
    · simp [hk] at h
    · rfl

/-- A key whose bytes are replaced: what an observer could not tell apart, if the API
leaked nothing of them. -/
def Key.blind (k : Key) : Key := { k with material := ByteArray.empty, pub := ByteArray.empty, rsa := k.rsa.map RsaParts.public }

/-- Exporting a non-extractable key gives the same answer whatever its bytes: the
InvalidAccessError, and nothing else. -/
theorem exportKey_blind (k : Key) (f : String) (h : k.extractable = false) :
    exportKey k f = exportKey k.blind f := by
  have hb : k.blind.extractable = false := h
  have ha : k.blind.algo = k.algo := rfl
  unfold exportKey; rw [ha]
  split
  · rfl
  · rw [if_neg (by simp [h]), if_neg (by simp [hb])]

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

/-! ### Usages are enforced before any primitive runs

The theorems above say a success had the usage. These say the converse in the strongest
form: without the usage (or with another algorithm's key) the answer IS the
InvalidAccessError, a constant, so it is not computed from any primitive's output: HACL* is
not called on that path, by the value of the function. -/

/-- Kind: security invariant (usages). Says: the check every key operation starts with
answers InvalidAccessError when the key lacks the usage. Does not say: that every operation
starts with this check; that is each operation's own theorem below. -/
theorem keyFor_no_usage {k : Key} {a : String} {u : Usage} (h : k.usages.contains u = false) :
    keyFor k a u = .error .invalidAccess := by
  unfold keyFor; rw [h]; simp

/-- Kind: security invariant (usages). Says: the same when the key is of another algorithm
than the one the operation names. Does not say: anything of a key of the right algorithm. -/
theorem keyFor_wrong_alg {k : Key} {a : String} {u : Usage} (h : k.algo.alg.name ≠ a) :
    keyFor k a u = .error .invalidAccess := by
  unfold keyFor; simp [h]

/-- Kind: security invariant (usages). Says: `sign` with a key that lacks "sign" answers
InvalidAccessError for every algorithm, parameter set, message and random input: the answer
is that constant, so no signing primitive ran. Does not say: anything of a key that has the
usage. -/
theorem sign_no_usage {a : String} {p : Args} {k : Key} {d r : ByteArray}
    (h : k.usages.contains .sign = false) : sign a p k d r = .error .invalidAccess := by
  unfold sign; rw [keyFor_no_usage h]; rfl

/-- Kind: security invariant (usages). Says: `verify` with a key that lacks "verify" is the
InvalidAccessError for all other arguments: no verification primitive ran. Does not say:
anything of a key that has the usage. -/
theorem verify_no_usage {a : String} {p : Args} {k : Key} {s d : ByteArray}
    (h : k.usages.contains .verify = false) : verify a p k s d = .error .invalidAccess := by
  unfold verify; rw [keyFor_no_usage h]; rfl

/-- Kind: security invariant (usages). Says: `deriveBits` with a key that lacks "deriveBits"
is the InvalidAccessError for all other arguments: no derivation ran. Does not say: anything
of deriveKey, which the API runs as deriveBits after its own check of "deriveKey"
(`Hosts.WebApi.subtle`). -/
theorem deriveBits_no_usage {a : String} {p : Args} {k : Key} {l : Option Nat} {s : KeyStore}
    (h : k.usages.contains .deriveBits = false) : deriveBits a p k l s = .error .invalidAccess := by
  unfold deriveBits; rw [keyFor_no_usage h]; rfl

/-- Kind: security invariant (usages). Says: encrypt needs "encrypt" and decrypt needs
"decrypt": without it the answer is InvalidAccessError and no cipher ran. Does not say:
anything of wrapKey and unwrapKey, which check "wrapKey" and "unwrapKey" themselves before
they call this (`Hosts.WebApi.subtle`). -/
theorem crypt_no_usage {e : Bool} {a : String} {p : Args} {k : Key} {d r : ByteArray}
    (h : k.usages.contains (if e then .encrypt else .decrypt) = false) :
    crypt e a p k d r = .error .invalidAccess := by
  unfold crypt; rw [keyFor_no_usage h]; rfl

/-- Kind: security invariant (usages). Says: an operation named for one algorithm never
runs on another algorithm's key (sign; the same proof serves the other operations through
`keyFor_wrong_alg`). Does not say: which algorithms a key can be made for. -/
theorem sign_wrong_alg {a : String} {p : Args} {k : Key} {d r : ByteArray}
    (h : k.algo.alg.name ≠ a) : sign a p k d r = .error .invalidAccess := by
  unfold sign; rw [keyFor_wrong_alg h]; rfl

/-! ### wrapKey reads a key only through exportKey -/

/-- wrapKey's first half (§14.3.11 steps 9-12): the bytes that will be encrypted are the
key's export in `format` (a JWK as the JSON text `jwkText` makes). -/
def wrapPlain (jwkText : List (String × JwkVal) → ByteArray) (k : Key) (format : String) : Res ByteArray :=
  (exportKey k format).map fun e => match e with | .bytes b => b | .jwk ms => jwkText ms

/-- Kind: security invariant (key material). Says: wrapKey gets bytes to encrypt only from
an extractable key. Does not say: anything of the wrapping key, which is used, not read. -/
theorem wrapPlain_extractable {j : List (String × JwkVal) → ByteArray} {k : Key} {f : String} {b : ByteArray}
    (h : wrapPlain j k f = .ok b) : k.extractable = true := by
  unfold wrapPlain at h
  cases he : exportKey k f with
  | error e => rw [he] at h; cases h
  | ok e => exact exportKey_extractable he

/-- Kind: security invariant (key material). Says: for a non-extractable key, what wrapKey
would encrypt does not depend on the key's bytes (it is the refusal). Does not say: that the
ciphertext of an extractable key hides it; that is the wrapping cipher's strength. -/
theorem wrapPlain_blind (j : List (String × JwkVal) → ByteArray) (k : Key) (f : String)
    (h : k.extractable = false) : wrapPlain j k f = wrapPlain j k.blind f := by
  unfold wrapPlain; rw [exportKey_blind k f h]

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

/-! ## Theorems: the key formats are read exactly

SPKI and PKCS #8 are DER. `readTlv_tlv` (above) is the round trip of one TLV. Here: reading
is exact (`tlv_of_readTlv`: what is accepted is the canonical encoding of what is answered,
so a non-minimal length, an indefinite length or a truncated value is refused, and no
accepted input has a second reading), the round trips of the two containers, and that an
accepted SPKI is exactly the canonical SPKI of its parts (no bytes skipped, none trailing).
JWK members are base64url: `unb64_b64`. -/

/-- Kind: round trip (DER). Says: `expect` reads back what `tlv` wrote with the same tag,
and answers the rest untouched. Hypothesis: contents shorter than 2^16. Does not say: what a
different tag gives (it is refused: see `expect`). -/
theorem expect_tlv (tag : UInt8) (c rest : List UInt8) (h : c.length < 65536) :
    expect tag (tlv tag c ++ rest) = some (c, rest) := by
  unfold expect; rw [readTlv_tlv tag c rest h]; simp

/-- Kind: round trip (DER). Says: `expect_tlv` with nothing after the TLV. Does not say:
more than `expect_tlv`. -/
theorem expect_tlv_nil (tag : UInt8) (c : List UInt8) (h : c.length < 65536) :
    expect tag (tlv tag c) = some (c, []) := by
  have := expect_tlv tag c [] h
  simpa using this

/-- Kind: size bound. Says: a TLV is at least as long as its contents. Does not say: how
much longer (2 to 4 octets). -/
theorem length_le_tlv (tag : UInt8) (c : List UInt8) : c.length ≤ (tlv tag c).length := by
  unfold tlv; simp; omega

/-- Kind: parser exactness (DER). Says: whatever `readTlv` accepts is the canonical encoding
(`tlv`, minimal length octets) of the tag and contents it answers, followed by the rest it
answers; and the contents are shorter than 2^16. So nothing is skipped or read twice, and an
input with a non-minimal, indefinite or over-long length is not accepted. Does not say:
anything of the contents' own structure. -/
theorem tlv_of_readTlv {b : List UInt8} {t : UInt8} {c r : List UInt8} (h : readTlv b = some (t, c, r)) :
    b = tlv t c ++ r ∧ c.length < 65536 := by
  match b, h with
  | tag :: l0 :: rest, h =>
    simp only [readTlv] at h
    split at h
    · rename_i h0
      split at h
      · rename_i h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hl : (rest.take l0.toNat).length = l0.toNat := by simp [List.length_take]; omega
        have hlt : l0.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using h0
        refine ⟨?_, by omega⟩
        unfold tlv derLen
        rw [hl, if_pos hlt]
        simp [List.take_append_drop]
      · cases h
    · split at h
      · rename_i h81
        have e81 : l0 = 0x81 := by simpa using h81
        subst e81
        split at h
        · rename_i l1 r'
          split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            obtain ⟨hge, hle⟩ := hc
            have hge' : 128 ≤ l1.toNat := by
              have : (128 : UInt8) ≤ l1 := hge
              simpa [UInt8.le_iff_toNat_le] using this
            have hl : (r'.take l1.toNat).length = l1.toNat := by simp [List.length_take]; omega
            have hlt : l1.toNat < 256 := l1.toNat_lt
            refine ⟨?_, by omega⟩
            unfold tlv derLen
            rw [hl, if_neg (by omega), if_pos hlt]
            simp [List.take_append_drop]
          · cases h
        · cases h
      · split at h
        · rename_i h82
          have e82 : l0 = 0x82 := by simpa using h82
          subst e82
          split at h
          · rename_i l1 l2 r'
            split at h
            · rename_i hc
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
              obtain ⟨hge, hle⟩ := hc
              have h1 : l1.toNat < 256 := l1.toNat_lt
              have h2 : l2.toNat < 256 := l2.toNat_lt
              have hl : (r'.take (l1.toNat * 256 + l2.toNat)).length = l1.toNat * 256 + l2.toNat := by
                simp [List.length_take]; omega
              have hd : (l1.toNat * 256 + l2.toNat) / 256 = l1.toNat := by omega
              have hm : (l1.toNat * 256 + l2.toNat) % 256 = l2.toNat := by omega
              refine ⟨?_, by omega⟩
              unfold tlv derLen
              rw [hl, if_neg (by omega), if_neg (by omega), hd, hm]
              simp [List.take_append_drop]
            · cases h
          · cases h
        · cases h
  | [_], h => simp [readTlv] at h
  | [], h => simp [readTlv] at h

/-- Kind: parser exactness. Says: `expect` accepts only the canonical encoding of the
contents it answers, with the tag asked for, followed by the rest it answers. Does not say:
anything of the contents' own structure. -/
theorem tlv_of_expect {tag : UInt8} {b c r : List UInt8} (h : expect tag b = some (c, r)) :
    b = tlv tag c ++ r ∧ c.length < 65536 := by
  unfold expect at h
  cases hr : readTlv b with
  | none => rw [hr] at h; cases h
  | some x =>
    obtain ⟨t, c', r'⟩ := x
    rw [hr] at h
    by_cases ht : (t == tag) = true
    · simp only [ht, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have e : t = tag := by simpa using ht
      subst e
      exact tlv_of_readTlv hr
    · simp [ht] at h

/-- Kind: round trip (SPKI, no algorithm parameters: Ed25519, X25519). Says: reading the
SubjectPublicKeyInfo `spkiOf` writes gives the OID and the key bytes back, with no
parameters. Hypothesis: the whole encoding is shorter than 2^16 octets (every key format
here is). Does not say: that the key bytes are a valid key. -/
theorem readSpki_spkiOf (oid key : List UInt8) (h : (spkiOf oid [] key).length < 65536) :
    readSpki (spkiOf oid [] key) = some (oid, none, key) := by
  unfold spkiOf at h ⊢
  simp only [List.append_nil] at h ⊢
  have h1 := Nat.lt_of_le_of_lt (length_le_tlv 0x30 _) h
  have h2 : (tlv 0x30 (tlv 0x06 oid)).length < 65536 := by
    simp only [List.length_append] at h1; omega
  have h3 : (tlv 0x03 (0 :: key)).length < 65536 := by
    simp only [List.length_append] at h1; omega
  have h5 := Nat.lt_of_le_of_lt (length_le_tlv 0x30 _) h2
  have h6 := Nat.lt_of_le_of_lt (length_le_tlv 0x06 _) h5
  have h7 := Nat.lt_of_le_of_lt (length_le_tlv 0x03 _) h3
  unfold readSpki
  simp only [expect_tlv_nil _ _ h1, expect_tlv _ _ _ h5, expect_tlv_nil _ _ h7, readAlgId,
    expect_tlv_nil _ _ h6, Option.bind_some, Option.bind_eq_bind]
  simp

/-- Kind: round trip (SPKI with algorithm parameters: the EC curve OID). Says: reading the
SubjectPublicKeyInfo `spkiOf` writes with one parameter TLV gives the OID, that TLV and the
key bytes back. Hypothesis: the whole encoding is shorter than 2^16 octets. Does not say:
that the parameters name a curve this engine has, or that the key bytes are a valid point. -/
theorem readSpki_spkiOf_params (oid key : List UInt8) (pt : UInt8) (pc : List UInt8)
    (h : (spkiOf oid (tlv pt pc) key).length < 65536) :
    readSpki (spkiOf oid (tlv pt pc) key) = some (oid, some (tlv pt pc), key) := by
  unfold spkiOf at h ⊢
  have h1 := Nat.lt_of_le_of_lt (length_le_tlv 0x30 _) h
  have h2 : (tlv 0x30 (tlv 0x06 oid ++ tlv pt pc)).length < 65536 := by
    simp only [List.length_append] at h1; omega
  have h3 : (tlv 0x03 (0 :: key)).length < 65536 := by
    simp only [List.length_append] at h1; omega
  have h4 := Nat.lt_of_le_of_lt (length_le_tlv 0x30 _) h2
  have h5 : (tlv 0x06 oid).length < 65536 := by simp only [List.length_append] at h4; omega
  have h5' : (tlv pt pc).length < 65536 := by simp only [List.length_append] at h4; omega
  have h6 := Nat.lt_of_le_of_lt (length_le_tlv 0x06 _) h5
  have h6' := Nat.lt_of_le_of_lt (length_le_tlv pt _) h5'
  have h7 := Nat.lt_of_le_of_lt (length_le_tlv 0x03 _) h3
  have hne : (tlv pt pc).isEmpty = false := by unfold tlv; rfl
  have hp : readTlv (tlv pt pc) = some (pt, pc, []) := by
    have := readTlv_tlv pt pc [] h6'
    simpa using this
  unfold readSpki
  simp only [expect_tlv_nil _ _ h1, expect_tlv _ _ _ h4, expect_tlv_nil _ _ h7, readAlgId,
    expect_tlv _ _ _ h6, Option.bind_some, Option.bind_eq_bind]
  simp [hne, hp]

/-- Kind: round trip (PKCS #8). Says: reading the PrivateKeyInfo `pkcs8Of` writes gives the
OID and the private key octets back (no parameters). Hypothesis: the whole encoding is
shorter than 2^16 octets. Does not say: the converse (PKCS #8 may carry attributes after the
key, which the reader accepts and does not return), nor anything of the key octets. -/
theorem readPkcs8_pkcs8Of (oid pk : List UInt8) (h : (pkcs8Of oid [] pk).length < 65536) :
    readPkcs8 (pkcs8Of oid [] pk) = some (oid, none, pk) := by
  unfold pkcs8Of at h ⊢
  simp only [List.append_nil, List.append_assoc] at h ⊢
  have h1 := Nat.lt_of_le_of_lt (length_le_tlv 0x30 _) h
  have h2 : (tlv 0x30 (tlv 0x06 oid)).length < 65536 := by
    simp only [List.length_append] at h1; omega
  have h3 : (tlv 0x04 pk).length < 65536 := by
    simp only [List.length_append] at h1; omega
  have h5 := Nat.lt_of_le_of_lt (length_le_tlv 0x30 _) h2
  have h6 := Nat.lt_of_le_of_lt (length_le_tlv 0x06 _) h5
  have h7 := Nat.lt_of_le_of_lt (length_le_tlv 0x04 _) h3
  have h0 : ([0] : List UInt8).length < 65536 := by decide
  unfold readPkcs8
  simp only [expect_tlv_nil _ _ h1, expect_tlv _ _ _ h0, expect_tlv _ _ _ h5, expect_tlv_nil _ _ h7,
    readAlgId, expect_tlv_nil _ _ h6, Option.bind_some, Option.bind_eq_bind]
  simp

/-- Kind: parser exactness (SPKI). Says: an input `readSpki` accepts is exactly the
canonical SubjectPublicKeyInfo of the OID, parameters and key bytes it answers: no byte of
the input is skipped and none trails. With `readSpki_spkiOf` this makes export after import
the identity on accepted SPKI bytes. Does not say: that the key bytes are a valid key (the
algorithm's import steps and HACL* check that). -/
theorem spkiOf_of_readSpki {b oid key : List UInt8} {params : Option (List UInt8)}
    (h : readSpki b = some (oid, params, key)) : b = spkiOf oid (params.getD []) key := by
  unfold readSpki at h
  cases h1 : expect 0x30 b with
  | none => simp [h1] at h
  | some x1 =>
    obtain ⟨seq, rest⟩ := x1
    simp only [h1, Option.bind_eq_bind, Option.bind_some] at h
    by_cases hre : rest.isEmpty = true
    · have hrest : rest = [] := by simpa using hre
      subst hrest
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases h2 : expect 0x30 seq with
      | none => simp [h2] at h
      | some x2 =>
        obtain ⟨aid, r⟩ := x2
        simp only [h2, Option.bind_some] at h
        cases h3 : expect 0x03 r with
        | none => simp [h3] at h
        | some x3 =>
          obtain ⟨bits, r2⟩ := x3
          simp only [h3, Option.bind_some] at h
          by_cases hr2 : r2.isEmpty = true
          · have hr2' : r2 = [] := by simpa using hr2
            subst hr2'
            simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false] at h
            cases h4 : readAlgId aid with
            | none => simp [h4] at h
            | some x4 =>
              obtain ⟨oid', params'⟩ := x4
              simp only [h4, Option.bind_some] at h
              split at h
              · rename_i key'
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                have e1 := (tlv_of_expect h1).1
                have e2 := (tlv_of_expect h2).1
                have e3 := (tlv_of_expect h3).1
                -- the AlgorithmIdentifier: the OID, then nothing or exactly one TLV
                have ea : aid = tlv 0x06 oid' ++ params'.getD [] := by
                  unfold readAlgId at h4
                  cases h5 : expect 0x06 aid with
                  | none => simp [h5] at h4
                  | some x5 =>
                    obtain ⟨o, ra⟩ := x5
                    simp only [h5, Option.bind_eq_bind, Option.bind_some] at h4
                    have e5 := (tlv_of_expect h5).1
                    by_cases hra : ra.isEmpty = true
                    · have : ra = [] := by simpa using hra
                      subst this
                      simp only [List.isEmpty_nil, if_true, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h4
                      obtain ⟨rfl, rfl⟩ := h4
                      simpa using e5
                    · simp only [hra, Bool.false_eq_true, if_false] at h4
                      split at h4
                      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h4
                        obtain ⟨rfl, rfl⟩ := h4
                        simpa using e5
                      · cases h4
                rw [e1, e2, e3, ea]
                unfold spkiOf
                simp
              · cases h
          · simp [hr2] at h
    · simp [hre] at h

/-- Kind: round trip (DER INTEGER, the RSA key parts). Says: reading the INTEGER contents
`uintContents` writes for a big-endian number gives the number back without leading zero
octets, for every byte string: a leading 0x00 is written exactly when the top bit is set, and
read back as such. Does not say: that other encodings are refused (they are, by `readUInt`'s
cases: empty, negative, or with a needless leading zero; tested by `#guard`). -/
theorem readUInt_uintContents (b : ByteArray) : readUInt (uintContents b) = some (stripZeros b) := by
  unfold uintContents stripZeros
  have hd : ∀ x rest, b.toList.dropWhile (· == 0) = x :: rest → x ≠ 0 := by
    intro x rest h
    have hne : b.toList.dropWhile (· == 0) ≠ [] := by rw [h]; simp
    have := List.head_dropWhile_not (· == (0 : UInt8)) hne
    simp only [h, List.head_cons] at this
    simpa using this
  generalize b.toList.dropWhile (· == 0) = l at hd
  match l, hd with
  | [], _ => rfl
  | x :: rest, hd =>
    have hx : x ≠ 0 := hd x rest rfl
    by_cases h80 : x ≥ 0x80
    · have hlt : ¬ x < 0x80 := by
        intro hlt
        have h1 : (128 : UInt8) ≤ x := h80
        rw [UInt8.le_iff_toNat_le] at h1
        rw [UInt8.lt_iff_toNat_lt] at hlt
        exact absurd h1 (by simpa using hlt)
      simp [h80, readUInt, hlt]
    · simp only [h80, if_false]
      match x, hx, h80 with
      | 0, hx, _ => exact absurd rfl hx
      | x, hx, h80 =>
        unfold readUInt
        split
        · rename_i heq; cases heq
        · rename_i heq; cases heq; exact absurd rfl hx
        · rename_i heq
          simp only [List.cons.injEq] at heq
          exact absurd heq.1 hx
        · rename_i b' rest' _ _ heq
          simp only [List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          simp [h80]

#guard readUInt [0x00, 0x7f] == none          -- a needless leading zero
#guard readUInt [0x80] == none                -- negative
#guard readUInt [] == none
#guard (readUInt [0x00, 0x80]).map (·.toList) == some [0x80]
#guard uintContents (ByteArray.mk #[0, 0, 0x80, 1]) == [0, 0x80, 1]
#guard uintContents (ByteArray.mk #[0, 0]) == [0]

/-- Kind: round trip (JWK octets). Says: decoding the base64url text a JWK export writes
for key bytes gives those bytes back (`k`, `x`, `y`, `d` and the RSA members). Rests on
`JOSE.Base64Url.decode_encode`. Does not say: that the whole JWK object survives the trip
through the page (prelude.js builds and reads the object; tested, not proved). -/
theorem unb64_b64 (b : ByteArray) : unb64? (b64 b) = some b := by
  unfold unb64? b64 JOSE.Base64Url.decode JOSE.Base64Url.encode
  simp [JOSE.Base64Url.decode_encode]

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
#guard (normalizeSpec "generateKey" "aes-gcm").toOption == some ("AES-GCM", ["length:l!"])
#guard (normalizeSpec "sign" "ML-DSA-44").isOk == false
/-- Kind: security invariant (refused algorithms, by type and by case). Says: for a name that
is not an algorithm this engine implements (`algOf?` answers `none`: AES, RSA, Ed448, X448,
ML-DSA, ML-KEM, KMAC and every unknown name), `generateKey` answers an error and nothing
else: no key is made and no random bytes are asked for. `generateRefusedErr` has type `Err`,
not `Res`, so it cannot be a key. Does not say: which error (the order of the checks is
tested by `#guard`s and WPT), nor anything of the implemented algorithms. -/
theorem generateKey_refused (algName : String) (p : Args) (extractable : Bool) (us : List Usage) (rand : Rand)
    (h : algOf? algName = none) :
    generateKey algName p extractable us rand = .error (generateRefusedErr algName p us) := by
  unfold generateKey
  rw [h]
  rfl

/-- Kind: security invariant (no RSA key generation). Says: `generateKey` of an RSA algorithm
answers an error and nothing else, for all parameters, usages and random input: no RSA key is
ever generated (HACL* has no prime generation, and none is written here). `randNeeded` asks
for no random bytes for it. Does not say: which error (the order of the checks is tested),
nor anything of imported RSA keys, which work. -/
theorem generateKey_rsa_refused (algName : String) (p : Args) (extractable : Bool) (us : List Usage) (rand : Rand)
    (a : Alg) (ha : algOf? algName = some a) (hr : a.isRsa = true) :
    generateKey algName p extractable us rand = .error (generateRefusedErr algName p us) ∧
      randNeeded algName p = 0 := by
  unfold generateKey randNeeded
  rw [ha]
  cases a <;> simp [Alg.isRsa] at hr <;> exact ⟨rfl, rfl⟩

/-- Kind: security invariant (refused algorithms). Says: for a name that is not an algorithm
this engine implements, the import steps answer an error and nothing else: no key is made
from the key data, whatever the format and the data. Does not say: which error. -/
theorem importMade_refused (algName : String) (p : Args) (format : String) (data : ByteArray) (j : Args)
    (extractable : Bool) (us : List Usage) (h : algOf? algName = none) :
    importMade algName p format data j extractable us =
      .error (importRefusedErr algName format data j extractable us) := by
  unfold importMade
  rw [h]

#guard generateRefusedErr "AES-GCM" #[("length", "128".toUTF8)] [.sign] == .syntax
#guard generateRefusedErr "AES-GCM" #[("length", "64".toUTF8)] [] == .operation
#guard generateRefusedErr "AES-GCM" #[("length", "128".toUTF8)] [] == .syntax
#guard generateRefusedErr "AES-GCM" #[("length", "256".toUTF8)] [.encrypt] == .notSupported
#guard generateRefusedErr "RSA-OAEP" #[("publicExponent", ByteArray.mk #[1, 0, 0])] [.decrypt] == .operation
#guard generateRefusedErr "RSA-OAEP" #[("publicExponent", ByteArray.mk #[1, 0, 1])] [.encrypt] == .syntax
#guard generateRefusedErr "ML-KEM-768" #[] [.decapsulateKey] == .notSupported
#guard generateRefusedErr "ML-KEM-768" #[] [.sign] == .syntax
#guard generateRefusedErr "HMAC" #[] [.sign] == .notSupported
#guard importRefusedErr "AES-CBC" "raw" (ByteArray.mk (Array.replicate 16 0)) #[] false [.sign] == .syntax
#guard importRefusedErr "AES-CBC" "raw" (ByteArray.mk (Array.replicate 15 0)) #[] false [.encrypt] == .data
#guard importRefusedErr "AES-CBC" "raw" (ByteArray.mk (Array.replicate 16 0)) #[] false [] == .syntax
#guard importRefusedErr "AES-CBC" "raw" (ByteArray.mk (Array.replicate 32 0)) #[] false [.encrypt] == .notSupported
#guard importRefusedErr "Ed448" "raw" (ByteArray.mk (Array.replicate 57 0)) #[] false [.sign] == .syntax
#guard importRefusedErr "Ed448" "raw" (ByteArray.mk (Array.replicate 56 0)) #[] false [.verify] == .data
#guard importRefusedErr "Ed448" "raw" (ByteArray.mk (Array.replicate 57 0)) #[] false [.verify] == .notSupported
#guard (keyLength "AES-KW" #[("length", "192".toUTF8)]).toOption == some (some 192)
#guard (keyLength "AES-KW" #[("length", "100".toUTF8)]).isOk == false
#guard Usage.ofName? "decapsulateKey" == some .decapsulateKey
#guard truncateBits (ByteArray.mk #[0xff, 0xff]) 12 == ByteArray.mk #[0xff, 0xf0]
#guard Err.all.map Err.code == [-20, -23, -24, -25, -26, -22, -27]

end L4Factoidal.Crypto.WebCryptoKeys
