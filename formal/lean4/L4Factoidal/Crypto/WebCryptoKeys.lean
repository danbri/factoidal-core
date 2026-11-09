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
import L4Factoidal.JOSE.Pkcs1
import L4Factoidal.Crypto.RsaOaep
import Std.Data.HashMap
import Std.Data.HashSet

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
  | hmac | hkdf | pbkdf2 | ecdsa | ecdh | ed25519 | x25519 | chacha | rsaPkcs1 | rsaPss | rsaOaep
  | aesCtr | aesCbc | aesGcm | aesKw
  deriving DecidableEq, Repr, Inhabited

def Alg.name : Alg → String
  | .hmac => "HMAC" | .hkdf => "HKDF" | .pbkdf2 => "PBKDF2" | .ecdsa => "ECDSA" | .ecdh => "ECDH"
  | .ed25519 => "Ed25519" | .x25519 => "X25519" | .chacha => "ChaCha20-Poly1305"
  | .rsaPkcs1 => "RSASSA-PKCS1-v1_5" | .rsaPss => "RSA-PSS" | .rsaOaep => "RSA-OAEP"
  | .aesCtr => "AES-CTR" | .aesCbc => "AES-CBC" | .aesGcm => "AES-GCM" | .aesKw => "AES-KW"

def Alg.isAes (a : Alg) : Bool := a == .aesCtr || a == .aesCbc || a == .aesGcm || a == .aesKw

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
`e` always (public); the private parts `Secret`s, empty in a public key. -/
structure RsaParts where
  n : ByteArray
  e : ByteArray
  d : Secret := Secret.empty
  p : Secret := Secret.empty
  q : Secret := Secret.empty
  dp : Secret := Secret.empty
  dq : Secret := Secret.empty
  qi : Secret := Secret.empty
  deriving Inhabited

/-- The public half of RSA parts. -/
def RsaParts.public (r : RsaParts) : RsaParts := { n := r.n, e := r.e }

structure Key where
  type : KeyType
  extractable : Bool
  algo : KeyAlgo
  usages : List Usage
  /-- secret: the key bytes; private: the private scalar (P-256) or seed (Ed25519,
  X25519), 32 bytes, or RSA's `d`; public: empty. A `Secret`: only `WebHacl`'s primitives
  and the export of an extractable key read it. -/
  secret : Secret := Secret.empty
  /-- public: the public key (P-256 `x ‖ y`, 64 bytes; OKP, 32; RSA `n`); private: the
  public key of the pair; secret: empty. Public bytes. -/
  pub : ByteArray := ByteArray.empty
  /-- RSA keys: their parts (`secret` is then `d`, and `pub` is `n`). -/
  rsa : Option RsaParts := none
  /-- On the Hub: the browser's CryptoKey that holds this key (a number in the host's
  table); Lean then holds no key bytes at all (`secret` is empty). -/
  host : Option Nat := none
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
  | .aesKw, _ => [.wrapKey, .unwrapKey]
  | .aesCtr, _ | .aesCbc, _ | .aesGcm, _ => [.encrypt, .decrypt, .wrapKey, .unwrapKey]

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

def normalizeSpec (op name : String) (host : Bool := false) : Res (String × List String) :=
  match (registered.find? (WebCrypto.asciiUpper · == WebCrypto.asciiUpper name)) with
  | none => .error .notSupported
  | some reg =>
    let r (ms : List String) : Res (String × List String) := .ok (reg, ms)
    -- AES is registered only where the browser does the primitives (the Hub, `host`):
    -- HACL* has no portable AES (record, section 9).
    let aes := host && (reg == "AES-CTR" || reg == "AES-CBC" || reg == "AES-GCM" || reg == "AES-KW")
    if aes then
      match op with
      | "generateKey" | "get key length" => r ["length:l!"]
      | "importKey" => r []
      | "encrypt" | "decrypt" =>
        match reg with
        | "AES-CTR" => r ["counter:b!", "length:o!"]
        | "AES-CBC" => r ["iv:b!"]
        | "AES-GCM" => r ["additionalData:b", "iv:b!", "tagLength:o"]
        | _ => .error .notSupported
      | "wrapKey" | "unwrapKey" => if reg == "AES-KW" then r [] else .error .notSupported
      | _ => .error .notSupported
    else
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
    | "generateKey", "RSASSA-PKCS1-v1_5" | "generateKey", "RSA-PSS" | "generateKey", "RSA-OAEP" =>
      r ["modulusLength:l!", "publicExponent:n!", "hash:h!"]
    | "importKey", "RSASSA-PKCS1-v1_5" | "importKey", "RSA-PSS" | "importKey", "RSA-OAEP" => r ["hash:h!"]
    | "sign", "RSASSA-PKCS1-v1_5" | "verify", "RSASSA-PKCS1-v1_5" => r []
    | "sign", "RSA-PSS" | "verify", "RSA-PSS" => r ["saltLength:l!"]
    | "encrypt", "RSA-OAEP" | "decrypt", "RSA-OAEP" => r ["label:b"]
    | _, _ => .error .notSupported

def algOf? (name : String) : Option Alg :=
  [Alg.hmac, .hkdf, .pbkdf2, .ecdsa, .ecdh, .ed25519, .x25519, .chacha, .rsaPkcs1, .rsaPss, .rsaOaep,
   .aesCtr, .aesCbc, .aesGcm, .aesKw].find? (·.name == name)

/-! ## The store -/

/-- The keys of a session, by handle. -/
structure KeyStore where
  keys : Std.HashMap Nat Key := {}
  next : Nat := 1
  /-- The bytes the keys hold (`Key.footprint`), so a page cannot fill memory with keys. -/
  bytes : Nat := 0
  deriving Inhabited

/-- At most this many keys at once in a session. -/
def maxKeys : Nat := 1 <<< 16

/-- At most this many bytes of keys at once in a session (256 MiB): QuotaExceededError
beyond (cryptosec finding F4: 65,536 keys of 64 MiB each were allowed). -/
def maxStoreBytes : Nat := 1 <<< 28

def RsaParts.footprint (r : RsaParts) : Nat :=
  r.n.size + r.e.size + r.d.size + r.p.size + r.q.size + r.dp.size + r.dq.size + r.qi.size

/-- The bytes a key holds in the store. -/
def Key.footprint (k : Key) : Nat :=
  k.secret.size + k.pub.size + (k.rsa.map RsaParts.footprint).getD 0 + k.algo.publicExponent.size

def KeyStore.add (s : KeyStore) (k : Key) : Res (KeyStore × Nat) :=
  if s.keys.size ≥ maxKeys || s.bytes + k.footprint > maxStoreBytes then .error .quota else
  .ok ({ keys := s.keys.insert s.next k, next := s.next + 1, bytes := s.bytes + k.footprint }, s.next)

/-- The key a handle names. A handle the store gave out once but no longer holds (the page's
CryptoKey was collected and the key dropped) is an InvalidAccessError; a number it never
gave out a TypeError (no CryptoKey of the page can carry one). -/
def keyOf (s : KeyStore) (a : Args) (field : String) : Res Key :=
  match a.nat? field with
  | some h => match s.keys[h]? with
    | some k => .ok k
    | none => if h < s.next then .error .invalidAccess else .error .typeError
  | none => .error .typeError

/-! ### Handles: given out once, never again -/

/-- Every handle in the store was given out: it is below `next`. -/
def KeyStore.Wf (s : KeyStore) : Prop := ∀ h, h ∈ s.keys → h < s.next

theorem KeyStore.wf_empty : ({} : KeyStore).Wf := by
  intro h hh; simp at hh

/-- `add` gives the handle `next` and moves `next` on by one. -/
theorem KeyStore.add_handle {s s' : KeyStore} {k : Key} {h : Nat} (e : s.add k = .ok (s', h)) :
    h = s.next ∧ s'.next = s.next + 1 ∧ s'.keys = s.keys.insert s.next k := by
  unfold KeyStore.add at e
  split at e
  · cases e
  · simp only [Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨rfl, rfl, rfl⟩

/-- A handle `add` gives was not in the store: a fresh handle never names an older key. -/
theorem KeyStore.add_fresh {s s' : KeyStore} {k : Key} {h : Nat} (wf : s.Wf) (e : s.add k = .ok (s', h)) :
    h ∉ s.keys := by
  obtain ⟨rfl, -, -⟩ := KeyStore.add_handle e
  intro hm; exact Nat.lt_irrefl _ (wf _ hm)

theorem KeyStore.add_wf {s s' : KeyStore} {k : Key} {h : Nat} (wf : s.Wf) (e : s.add k = .ok (s', h)) : s'.Wf := by
  obtain ⟨-, hn, hk⟩ := KeyStore.add_handle e
  intro x hx
  rw [hk, Std.HashMap.mem_insert] at hx
  rw [hn]
  rcases hx with hx | hx
  · have : s.next = x := by simpa using hx
    omega
  · have := wf x hx; omega

/-- Dropping a key keeps `next`: its handle is not given out again. -/
theorem KeyStore.erase_wf {s : KeyStore} (wf : s.Wf) (h : Nat) : ({ s with keys := s.keys.erase h } : KeyStore).Wf := by
  intro x hx
  rw [Std.HashMap.mem_erase] at hx
  exact wf x hx.2

/-- An operation on a handle that was dropped fails with InvalidAccessError. -/
theorem keyOf_dropped {s : KeyStore} {a : Args} {f : String} {h : Nat} (ha : a.nat? f = some h)
    (hlt : h < s.next) (hn : h ∉ s.keys) : keyOf s a f = .error .invalidAccess := by
  unfold keyOf
  rw [ha]
  have : s.keys[h]? = none := Std.HashMap.getElem?_eq_none hn
  simp [this, hlt]

/-- Copy key `h` of the store `src` into the store `dst` (a structured clone of a CryptoKey
into another session): the copy gets `dst`'s next handle, whatever `h` is, so no handle
number crosses between sessions. -/
def KeyStore.cloneInto (src dst : KeyStore) (h : Nat) : Res (KeyStore × Nat) := do
  let some k := src.keys[h]? | throw (if h < src.next then .invalidAccess else .typeError)
  dst.add k

/-- The copy's handle is the receiving store's next one: no number of the sending session. -/
theorem KeyStore.cloneInto_handle {src dst dst' : KeyStore} {h h' : Nat} (e : src.cloneInto dst h = .ok (dst', h')) :
    h' = dst.next := by
  unfold KeyStore.cloneInto at e
  cases hk : src.keys[h]? with
  | none => simp [hk] at e
  | some k => simp only [hk] at e; exact (KeyStore.add_handle e).1

/-- A clone is the same key: never more extractable, never more usages (exactly the same). -/
theorem KeyStore.cloneInto_same {src dst dst' : KeyStore} {h h' : Nat} (e : src.cloneInto dst h = .ok (dst', h')) :
    ∃ k, src.keys[h]? = some k ∧ dst'.keys[h']? = some k := by
  unfold KeyStore.cloneInto at e
  cases hk : src.keys[h]? with
  | none => simp [hk] at e
  | some k =>
    simp only [hk] at e
    obtain ⟨rfl, -, hkeys⟩ := KeyStore.add_handle e
    exact ⟨k, rfl, by rw [hkeys]; simp⟩

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

/-- DER canonical uniqueness: what `readTlv` accepts is exactly `tlv` of what it answers. -/
theorem readTlv_eq_tlv {b : List UInt8} {t : UInt8} {c r : List UInt8} (h : readTlv b = some (t, c, r)) :
    b = tlv t c ++ r := by
  match b, h with
  | tag :: l0 :: rest, h =>
    simp only [readTlv] at h
    by_cases h0 : l0 < 128
    · rw [if_pos h0] at h
      split at h
      · rename_i hle
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hl : (rest.take l0.toNat).length = l0.toNat := by simp; omega
        have h0' : l0.toNat < 128 := by rw [UInt8.lt_iff_toNat_lt] at h0; exact h0
        simp only [tlv, derLen, hl, if_pos h0', List.cons_append]
        simp [Nat.toUInt8, UInt8.ofNat]
      · cases h
    · rw [if_neg h0] at h
      by_cases h1 : l0 == 0x81
      · rw [if_pos h1] at h
        have e1 : l0 = 0x81 := by simpa using h1
        match rest, h with
        | l1 :: r', h =>
          simp only at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hl : (r'.take l1.toNat).length = l1.toNat := by simp; omega
            have hge : 128 ≤ l1.toNat := by have := hc.1; exact (UInt8.le_iff_toNat_le.mp this)
            have hlt : l1.toNat < 256 := l1.toNat_lt
            simp only [tlv, derLen, hl, e1, List.cons_append]
            rw [if_neg (by omega), if_pos hlt]
            simp [Nat.toUInt8, UInt8.ofNat]
          · cases h
      · rw [if_neg h1] at h
        by_cases h2 : l0 == 0x82
        · rw [if_pos h2] at h
          have e2 : l0 = 0x82 := by simpa using h2
          match rest, h with
          | l1 :: l2 :: r', h =>
            simp only at h
            split at h
            · rename_i hc
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              have hl : (r'.take (l1.toNat * 256 + l2.toNat)).length = l1.toNat * 256 + l2.toNat := by simp; omega
              have b1 : l1.toNat < 256 := l1.toNat_lt
              have b2 : l2.toNat < 256 := l2.toNat_lt
              simp only [tlv, derLen, hl, e2, List.cons_append]
              rw [if_neg (by omega), if_neg (by omega)]
              have q1 : (l1.toNat * 256 + l2.toNat) / 256 = l1.toNat := by omega
              have q2 : (l1.toNat * 256 + l2.toNat) % 256 = l2.toNat := by omega
              rw [q1, q2]
              simp [Nat.toUInt8, UInt8.ofNat]
            · cases h
        · rw [if_neg h2] at h; cases h

theorem expect_eq_tlv {tag : UInt8} {b c r : List UInt8} (h : expect tag b = some (c, r)) : b = tlv tag c ++ r := by
  unfold expect at h
  split at h
  · rename_i t c' r' hr
    split at h
    · rename_i ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : t = tag := by simpa using ht
      subst this; exact readTlv_eq_tlv hr
    · cases h
  · cases h

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

theorem readAlgId_eq {c oid : List UInt8} {p : Option (List UInt8)} (h : readAlgId c = some (oid, p)) :
    c = tlv 0x06 oid ++ p.getD [] := by
  unfold readAlgId at h
  cases he : expect 0x06 c with
  | none => simp [he] at h
  | some x =>
    obtain ⟨o, r⟩ := x
    have hc := expect_eq_tlv he
    simp only [he, Option.bind_eq_bind, Option.bind_some] at h
    by_cases hr : r.isEmpty
    · simp only [hr, if_true, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp at hr; subst hr; simpa using hc
    · simp only [hr, Bool.false_eq_true, if_false] at h
      split at h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; simpa using hc
      · cases h

/-- PrivateKeyInfo / OneAsymmetricKey (RFC 5208, RFC 5958): the algorithm and the
privateKey OCTET STRING's contents. After it only `[0]` attributes, and in a v2 key a
`[1]` public key, are allowed, and nothing else (cryptosec finding F8: any bytes were
accepted there, so one key had many encodings). -/
def readPkcs8 (b : List UInt8) : Option (List UInt8 × Option (List UInt8) × List UInt8) := do
  let (seq, rest) ← expect 0x30 b
  if !rest.isEmpty then none
  let (ver, r) ← expect 0x02 seq
  if ver != [0] && ver != [1] then none
  let (aid, r) ← expect 0x30 r
  let (pk, r) ← expect 0x04 r
  let r := match readTlv r with | some (t, _, r') => if t == 0xa0 then r' else r | none => r
  let r := if ver == [1] then
      (match readTlv r with | some (t, _, r') => if t == 0x81 || t == 0xa1 then r' else r | none => r)
    else r
  if !r.isEmpty then none
  let (oid, params) ← readAlgId aid
  return (oid, params, pk)

def spkiOf (oid : List UInt8) (params : List UInt8) (key : List UInt8) : List UInt8 :=
  tlv 0x30 (tlv 0x30 (tlv 0x06 oid ++ params) ++ tlv 0x03 (0 :: key))

/-- SPKI canonical uniqueness: an SPKI the reader accepts is the one `spkiOf` writes for what it
read, so one key has one SPKI encoding. -/
theorem readSpki_eq {b oid key : List UInt8} {p : Option (List UInt8)} (h : readSpki b = some (oid, p, key)) :
    b = spkiOf oid (p.getD []) key := by
  unfold readSpki at h
  cases h1 : expect 0x30 b with
  | none => simp [h1] at h
  | some x1 =>
    obtain ⟨seq, rest⟩ := x1
    simp only [h1, Option.bind_eq_bind, Option.bind_some] at h
    by_cases hr : rest.isEmpty
    · simp only [hr, Bool.not_true, Bool.false_eq_true, if_false] at h
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
          by_cases hr2 : r2.isEmpty
          · simp only [hr2, Bool.not_true, Bool.false_eq_true, if_false] at h
            cases h4 : readAlgId aid with
            | none => simp [h4] at h
            | some x4 =>
              obtain ⟨o, pp⟩ := x4
              simp only [h4, Option.bind_some] at h
              split at h
              · rename_i k
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                have e1 := expect_eq_tlv h1; have e2 := expect_eq_tlv h2; have e3 := expect_eq_tlv h3
                have e4 := readAlgId_eq h4
                simp at hr hr2; subst hr hr2
                simp only [List.append_nil] at e1 e3
                rw [e1, e2, e3, e4]; simp [spkiOf]
              · cases h
          · simp [hr2] at h
    · simp [hr] at h

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

/-! ## P-256 point check in Lean (public values only) -/

def p256P : Nat := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
def p256B : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

def natOfBytes (b : ByteArray) : Nat := b.foldl (fun n x => n * 256 + x.toNat) 0

/-- SEC 1 §3.2.2.1 for a raw P-256 public key `x ‖ y`: both coordinates below p and the
point on y² = x³ − 3x + b (an affine point is never the point at infinity). The values are
public, so Lean computes it itself; on the Hub this is Lean's own check before the host
imports a key (natively HACL*'s `p256ValidPublic` makes it). -/
def p256OnCurve (xy : ByteArray) : Bool :=
  xy.size == 64 &&
    let x := natOfBytes (xy.extract 0 32)
    let y := natOfBytes (xy.extract 32 64)
    x < p256P && y < p256P && (y * y) % p256P == (x * x * x + 3 * (p256P - x) + p256B) % p256P

def p256N : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- `0 < d < n` for a P-256 private scalar (FIPS 186-4 §B.4). On the Hub, Lean checks it
before the host imports the key (natively HACL*'s constant-time `p256ValidPrivate` does).
This comparison is not constant time; the page that imports a key already holds its bytes. -/
def p256ScalarOk (d : ByteArray) : Bool :=
  d.size == 32 && let x := natOfBytes d; 0 < x && x < p256N

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

/-- No string twice, in one pass over a hash set. -/
def noDups (xs : List String) : Bool :=
  (xs.foldl (fun (acc : Option (Std.HashSet String)) x => acc.bind fun seen =>
    if seen.contains x then none else some (seen.insert x)) (some {})).isSome

/-- The JsonWebKey members common to every import (§14.3.9 and each algorithm's import
steps): `use` against `expectUse` when there are usages, `key_ops` (no duplicates, and
every usage in it), and `ext` (DataError when false and the key is to be extractable). -/
def jwkCommon (j : Args) (us : List Usage) (extractable : Bool) (expectUse : String) : Res Unit := do
  if !us.isEmpty then
    if let some u := j.str? "use" then
      if u != expectUse then throw .data
  if j.has "key_ops" then
    let ops := (j.all "key_ops[]").filterMap String.fromUTF8?
    -- Duplicates, in one pass (`List.eraseDups` is quadratic: 4,000 entries took 165 ms in
    -- BubblePopJS, half a million would take most of an hour; cryptosec finding F3).
    if !(noDups ops) then throw .data
    if !(us.all fun u => ops.contains u.name) then throw .data
  if j.str? "ext" == some "false" && extractable then throw .data

def jwkCommonOut (k : Key) : List (String × JwkVal) :=
  [("key_ops", .arr (k.usages.map (·.name))), ("ext", .bool k.extractable)]

/-! ## Import (§14.3.9, then each algorithm's "import key" steps, in their order) -/

/-- The key an import makes, before the generic steps (extractable and usages). -/
structure Made where
  type : KeyType
  algo : KeyAlgo
  secret : Secret := Secret.empty
  pub : ByteArray := ByteArray.empty
  rsa : Option RsaParts := none

def okpOid : Alg → List UInt8
  | .ed25519 => oidEd25519 | _ => oidX25519

def okpPublic? : Alg → ByteArray → Option ByteArray
  | .ed25519, sk => ed25519Public? sk
  | _, sk => x25519Public? sk

/-- The point of an EC SPKI (§23.7, §24.4 "import key", spki steps): DataError unless the
algorithm is id-ecPublicKey with a named curve; NotSupportedError for P-384 and P-521
(HACL* has only P-256); DataError when the OID's curve is not the namedCurve asked for. -/
def ecSpkiPoint (data : ByteArray) (curve : String) : Res ByteArray :=
  match readSpki data.toList with
  | some (oid, some p, key) =>
    if oid = oidEcPublicKey then
      match expect 0x06 p with
      | some (poid, _) =>
        match curveOfOid? poid with
        | some c =>
          if c = "P-256" then (if c = curve then .ok (ByteArray.mk key.toArray) else .error .data)
          else if c = "P-384" ∨ c = "P-521" then .error .notSupported else .error .data
        | none => .error .data
      | none => .error .data
    else .error .data
  | _ => .error .data

/-- An EC SPKI is read only when its curve OID names the namedCurve the page asked for. -/
theorem import_curve_matches_oid {data : ByteArray} {curve : String} {pt : ByteArray}
    (h : ecSpkiPoint data curve = .ok pt) :
    ∃ p key poid rest, readSpki data.toList = some (oidEcPublicKey, some p, key) ∧
      expect 0x06 p = some (poid, rest) ∧ curveOfOid? poid = some curve ∧ curve = "P-256" ∧
      pt = ByteArray.mk key.toArray := by
  unfold ecSpkiPoint at h
  split at h
  · rename_i oid p key hs
    split at h
    · rename_i ho
      split at h
      · rename_i poid rest he
        split at h
        · rename_i c hc
          split at h
          · rename_i h256
            split at h
            · rename_i hcur
              cases h; subst ho; subst hcur
              exact ⟨p, key, poid, rest, hs, he, hc, h256, rfl⟩
            · cases h
          · split at h <;> cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- Every point `decodePoint?` gives passed HACL*'s check: `p256ValidPublic` (on the curve,
not infinity, coordinates below p), or HACL*'s decompression, which checks the same. -/
theorem decodePoint?_valid {b xy : ByteArray} (h : decodePoint? b = some xy) :
    p256ValidPublic xy = true ∨ p256Decompress? b = some xy := by
  unfold decodePoint? at h
  split at h
  · simp only at h
    split at h
    · rename_i hv; cases h; exact Or.inl hv
    · cases h
  · split at h
    · exact Or.inr h
    · cases h

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
    let point ← if format == "spki" then ecSpkiPoint data curve else do haveCurve curve; pure data
    let some xy := decodePoint? point | throw .data
    return { type := .publicKey, algo := { alg, curve }, pub := xy }
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
    -- RFC 5915: then only the optional [1] public key; nothing after it.
    let given ← match expect 0xa1 r with
      | some (pkb, rest) =>
        if !rest.isEmpty then throw .data
        match expect 0x03 pkb with
        | some (0 :: pt, []) => pure (some (ByteArray.mk pt.toArray))
        | _ => throw .data
      | none => if r.isEmpty then pure none else throw .data
    if c != curve then throw .data
    let d := ByteArray.mk d.toArray
    if d.size != 32 || !p256ValidPrivate d then throw .data
    let some xy := p256Public? d | throw .data
    if let some g := given then
      match decodePoint? g with
      | some gxy => if gxy != xy then throw .data
      | none => throw .data
    return { type := .privateKey, algo := { alg, curve }, secret := Secret.ofBytes d, pub := xy }
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
      return { type := .privateKey, algo := { alg, curve }, secret := Secret.ofBytes d, pub := xy }
    return { type := .publicKey, algo := { alg, curve }, pub := xy }
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
    return { type := .publicKey, algo := { alg }, pub := ByteArray.mk key.toArray }
  | "pkcs8" =>
    checkUsages privU us
    let some (oid, params, pk) := readPkcs8 data.toList | throw .data
    if oid != okpOid alg || params.isSome then throw .data
    let some (sk, []) := expect 0x04 pk | throw .data
    if sk.length != 32 then throw .data
    let sk := ByteArray.mk sk.toArray
    let some pub := okpPublic? alg sk | throw .data
    return { type := .privateKey, algo := { alg }, secret := Secret.ofBytes sk, pub }
  | "raw" | "raw-public" =>
    checkUsages pubU us
    if data.size != 32 then throw .data
    return { type := .publicKey, algo := { alg }, pub := data }
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
      return { type := .privateKey, algo := { alg }, secret := Secret.ofBytes d, pub }
    return { type := .publicKey, algo := { alg }, pub := x }
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
    return { type := .secret, algo := { alg }, secret := Secret.ofBytes data }
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
    return { type := .secret, algo := { alg, hash := some h, length := len }, secret := Secret.ofBytes raw }
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
    return { type := .secret, algo := { alg }, secret := Secret.ofBytes raw }
  | _ => throw .notSupported

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

def rsaPrivateDer (n e d p q dp dq qi : ByteArray) : List UInt8 :=
  tlv 0x30 (tlv 0x02 [0] ++ derUInt n ++ derUInt e ++ derUInt d ++ derUInt p ++ derUInt q ++
    derUInt dp ++ derUInt dq ++ derUInt qi)

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
    pure ({ type := t, algo, secret := if t == .privateKey then r.d else Secret.empty, pub := r.n, rsa := some r } : Made)
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
    let sec := Secret.ofBytes
    made .privateKey { n, e, d := sec d, p := sec p', q := sec q, dp := sec dp, dq := sec dq, qi := sec qi }
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
      let sec := Secret.ofBytes
      let (d, p, q, dp, dq, qi) := (← b "d", ← b "p", ← b "q", ← b "dp", ← b "dq", ← b "qi")
      made .privateKey { n, e, d := sec d, p := sec p, q := sec q, dp := sec dp, dq := sec dq, qi := sec qi }
    else made .publicKey { n, e }
  | _ => throw .notSupported

/-- The largest SPKI or PKCS #8 key read (16 KiB: an RSA-4096 PKCS #8 key is about 2.4
KiB). The DER reader works on a `List UInt8`; a 64 MiB argument made a list of 64 million
cells (cryptosec finding F3). -/
def maxDerKey : Nat := 16384

/-- The algorithm's import steps. -/
def importMade (algName : String) (p : Args) (format : String) (data : ByteArray) (j : Args)
    (extractable : Bool) (us : List Usage) : Res Made :=
  match algOf? algName with
  | none => .error .notSupported
  | some alg =>
    if (format == "spki" || format == "pkcs8") && data.size > maxDerKey then .error .data else
    match alg with
    | .ecdsa | .ecdh => importEc alg format data j ((p.str? "namedCurve").getD "") us extractable
    | .ed25519 | .x25519 => importOkp alg format data j us extractable
    | .rsaPkcs1 | .rsaPss | .rsaOaep => importRsa alg format data j p us extractable
    | _ => importSecret alg format data j p us extractable

/-- §14.3.9 steps 10-11: a secret or private key with no usages is a SyntaxError; then
the key takes `extractable` and the usages. -/
def finishKey (m : Made) (extractable : Bool) (us : List Usage) : Res Key :=
  if (m.type == .secret || m.type == .privateKey) && us.isEmpty then .error .syntax
  else .ok { type := m.type, extractable, algo := m.algo, usages := us, secret := m.secret, pub := m.pub, rsa := m.rsa }

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
    | "spki", .publicKey => return .bytes (ByteArray.mk (spkiOf oidEcPublicKey (tlv 0x06 oidP256) (uncompressed k.pub).toList).toArray)
    | "raw", .publicKey | "raw-public", .publicKey => return .bytes (uncompressed k.pub)
    | "pkcs8", .privateKey =>
      let ec := tlv 0x30 (tlv 0x02 [1] ++ tlv 0x04 k.secret.revealForExport.toList ++
        tlv 0xa1 (tlv 0x03 (0 :: (uncompressed k.pub).toList)))
      return .bytes (ByteArray.mk (pkcs8Of oidEcPublicKey (tlv 0x06 oidP256) ec).toArray)
    | "jwk", t =>
      let xy := k.pub
      let base := [("kty", JwkVal.str "EC"), ("crv", .str k.algo.curve),
        ("x", .str (b64 (xy.extract 0 32))), ("y", .str (b64 (xy.extract 32 64)))]
      let d := if t == .privateKey then [("d", JwkVal.str (b64 k.secret.revealForExport))] else []
      return .jwk (base ++ d ++ jwkCommonOut k)
    | "spki", _ | "raw", _ | "raw-public", _ | "pkcs8", _ => throw .invalidAccess
    | _, _ => throw .notSupported
  | .ed25519 | .x25519 =>
    match format, k.type with
    | "spki", .publicKey => return .bytes (ByteArray.mk (spkiOf (okpOid alg) [] k.pub.toList).toArray)
    | "raw", .publicKey | "raw-public", .publicKey => return .bytes k.pub
    | "pkcs8", .privateKey => return .bytes (ByteArray.mk (pkcs8Of (okpOid alg) [] (tlv 0x04 k.secret.revealForExport.toList)).toArray)
    | "jwk", t =>
      let x := k.pub
      let base := [("kty", JwkVal.str "OKP"), ("crv", .str alg.name), ("x", .str (b64 x))]
      let d := if t == .privateKey then [("d", JwkVal.str (b64 k.secret.revealForExport))] else []
      let a := if alg == .ed25519 then [("alg", JwkVal.str "Ed25519")] else []
      return .jwk (base ++ d ++ a ++ jwkCommonOut k)
    | "spki", _ | "raw", _ | "raw-public", _ | "pkcs8", _ => throw .invalidAccess
    | _, _ => throw .notSupported
  | .hmac =>
    match format with
    | "raw" | "raw-secret" => return .bytes k.secret.revealForExport
    | "jwk" =>
      let a := match k.algo.hash with | some h => [("alg", JwkVal.str (hmacJwkAlg h))] | none => []
      return .jwk ([("kty", JwkVal.str "oct"), ("k", .str (b64 k.secret.revealForExport))] ++ a ++ jwkCommonOut k)
    | _ => throw .notSupported
  | .chacha =>
    match format with
    | "raw" | "raw-secret" => return .bytes k.secret.revealForExport
    | "jwk" => return .jwk ([("kty", JwkVal.str "oct"), ("k", .str (b64 k.secret.revealForExport)), ("alg", .str "C20P")] ++ jwkCommonOut k)
    | _ => throw .notSupported
  | .rsaPkcs1 | .rsaPss | .rsaOaep =>
    let r := k.rsa.getD { n := k.pub, e := k.algo.publicExponent }
    match format, k.type with
    | "spki", .publicKey =>
      return .bytes (ByteArray.mk (spkiOf oidRsaEncryption [0x05, 0x00] (rsaPublicDer r)).toArray)
    | "pkcs8", .privateKey =>
      return .bytes (ByteArray.mk (pkcs8Of oidRsaEncryption [0x05, 0x00] (rsaPrivateDer r.n r.e
        r.d.revealForExport r.p.revealForExport r.q.revealForExport r.dp.revealForExport r.dq.revealForExport
        r.qi.revealForExport)).toArray)
    | "jwk", t =>
      let base := [("kty", JwkVal.str "RSA"), ("n", .str (b64 r.n)), ("e", .str (b64 r.e))]
      let priv := if t == .privateKey then
          [("d", JwkVal.str (b64 r.d.revealForExport)), ("p", .str (b64 r.p.revealForExport)),
           ("q", .str (b64 r.q.revealForExport)), ("dp", .str (b64 r.dp.revealForExport)),
           ("dq", .str (b64 r.dq.revealForExport)), ("qi", .str (b64 r.qi.revealForExport))] else []
      let a := match k.algo.hash with | some h => [("alg", JwkVal.str (rsaJwkAlg alg h))] | none => []
      return .jwk (base ++ priv ++ a ++ jwkCommonOut k)
    | "spki", _ | "pkcs8", _ => throw .invalidAccess
    | _, _ => throw .notSupported
  | .hkdf | .pbkdf2 => throw .notSupported
  | .aesCtr | .aesCbc | .aesGcm | .aesKw => throw .notSupported

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
    return .one { type := .secret, extractable, algo := { alg, hash := some h, length := len }, usages := us, secret := Secret.ofBytes bytes }
  | .chacha =>
    checkUsages (allowedUsages .chacha .secret) us
    if us.isEmpty then throw .syntax
    if rand.size < 32 then throw .operation
    return .one { type := .secret, extractable, algo := { alg }, usages := us, secret := Secret.ofBytes (rand.extract 0 32) }
  | .rsaPkcs1 | .rsaPss | .rsaOaep =>
    checkUsages ((allowedUsages alg .publicKey) ++ (allowedUsages alg .privateKey)) us
    -- §20.7 step 2 "generate an RSA key pair": an exponent other than 3 or 65537, or a
    -- modulus length this engine could never make, fails the generation (OperationError).
    let e := stripZeros ((p.get? "publicExponent").getD .empty)
    let ml := (p.nat? "modulusLength").getD 0
    if !(e.toList == [3] || e.toList == [1, 0, 1]) || ml < 1024 || ml > 4096 || ml % 64 != 0 then throw .operation
    -- HACL* has no prime generation: a valid request is not supported here.
    throw .notSupported
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
    return .pair { type := .publicKey, extractable := true, algo, usages := pubUs, pub }
      { type := .privateKey, extractable, algo, usages := privUs, secret := Secret.ofBytes sk, pub }
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
    return k.secret.hmac h data
  | .ecdsa =>
    if k.type != .privateKey then throw .invalidAccess
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    -- The hedged RFC 6979 nonce (`Secret.ecdsaSign?`): `rand` is its additional data.
    let some s := k.secret.ecdsaSign? h (hashFast h data) (rand.extract 0 32) | throw .operation
    return s
  | .ed25519 =>
    if k.type != .privateKey then throw .invalidAccess
    let some s := k.secret.ed25519Sign? data | throw .operation
    return s
  | .rsaPkcs1 =>
    if k.type != .privateKey then throw .invalidAccess
    let (some r, some h) := (k.rsa, k.algo.hash) | throw .operation
    let some em := JOSE.Pkcs1.emsaEncodeGen (digestInfo h) h.size (hashFast h data).toList r.n.size | throw .operation
    let some s := Secret.rsaPrivate? r.n r.d (ByteArray.mk em.toArray) | throw .operation
    return s
  | .rsaPss =>
    if k.type != .privateKey then throw .invalidAccess
    let (some r, some h) := (k.rsa, k.algo.hash) | throw .operation
    let sl := (p.nat? "saltLength").getD 0
    if rand.size < sl then throw .operation
    let some s := Secret.rsaPssSign? h r.n r.e r.d (rand.extract 0 sl) data | throw .operation
    return s
  | _ => throw .invalidAccess

def verify (algName : String) (p : Args) (k : Key) (sig data : ByteArray) : Res Bool := do
  keyFor k algName .verify
  match k.algo.alg with
  | .hmac =>
    let some h := k.algo.hash | throw .operation
    -- HACL*'s HMAC, then the constant-time comparison in C.
    return ctEq (k.secret.hmac h data) sig
  | .ecdsa =>
    if k.type != .publicKey then throw .invalidAccess
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    return p256Verify k.pub (p256MsgRep (hashFast h data)) sig
  | .ed25519 =>
    if k.type != .publicKey then throw .invalidAccess
    if ed25519IsSmallOrder k.pub || (sig.size == 64 && ed25519IsSmallOrder (sig.extract 0 32)) then return false
    return ed25519Verify k.pub data sig
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
    let some out := k.secret.hkdf h ((p.get? "salt").getD .empty)
      ((p.get? "info").getD .empty) (len / 8) | throw .operation
    return out
  | .pbkdf2 =>
    let some h := (p.str? "hash").bind HashAlg.ofName? | throw .notSupported
    let some len := length | throw .operation
    if len % 8 != 0 then throw .operation
    let it := (p.nat? "iterations").getD 0
    if it == 0 then throw .operation
    return k.secret.pbkdf2 h ((p.get? "salt").getD .empty) it (len / 8)
  | .ecdh | .x25519 =>
    if k.type != .privateKey then throw .invalidAccess
    let pk ← keyOf store p "public"
    if pk.type != .publicKey || pk.algo.alg != k.algo.alg then throw .invalidAccess
    if k.algo.alg == .ecdh && pk.algo.curve != k.algo.curve then throw .invalidAccess
    let secret ← match k.algo.alg with
      | .ecdh => match Secret.p256Ecdh? pk.pub k.secret with | some s => pure s | none => throw .operation
      | _ => match k.secret.x25519? pk.pub with | some s => pure s | none => throw .operation
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
      let some c := k.secret.chachaSeal? iv aad data | throw .operation
      return c
    else
      if data.size < 16 then throw .operation
      let some m := k.secret.chachaOpen? iv aad data | throw .operation
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
      let some em := Secret.rsaPrivate? r.n r.d data | throw .operation
      let some m := RsaOaep.emeDecode oh r.n.size label em.toList | throw .operation
      return ByteArray.mk m.toArray
  | _ => throw .invalidAccess

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
def Key.blind (k : Key) : Key := { k with secret := Secret.empty, rsa := k.rsa.map RsaParts.public }

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
    cases st.keys[h]? with
    | some k => rfl
    | none => simp only [Option.map_none]; split <;> rfl

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

/-! ## Noninterference: a key's secret bytes reach an answer only through its usages

`k'` is `k` with other secret bytes (its `secret`, and RSA's private parts) and nothing else
changed. The theorems below say that an operation whose usage the key lacks answers the
same for `k` and `k'`, and so does exportKey for a key that is not extractable: the bytes
do not influence the answer, its error or its absence. The declassification policy
(record, "Noninterference") is the converse: bytes reach answers only through
  * exportKey, and wrapKey's export, of an extractable key (the bytes themselves);
  * an operation with a usage the key has: sign, verify (HMAC), encrypt, decrypt,
    deriveBits, deriveKey, wrapKey (as the wrapping key), unwrapKey (as the unwrapping key),
    whose answers are the primitive's outputs;
  * lengths, which are public. -/

/-- `k'` differs from `k` at most in its secret bytes. -/
structure Key.SameButSecret (k k' : Key) : Prop where
  type : k'.type = k.type
  extractable : k'.extractable = k.extractable
  algo : k'.algo = k.algo
  usages : k'.usages = k.usages
  pub : k'.pub = k.pub
  rsaPub : k'.rsa.map RsaParts.public = k.rsa.map RsaParts.public

theorem keyFor_lacks {k : Key} {a : String} {u : Usage} (hu : k.usages.contains u = false) :
    keyFor k a u = .error .invalidAccess := by
  unfold keyFor; rw [if_pos (by simp only [hu, Bool.not_false, Bool.or_true])]

theorem keyFor_same {k k' : Key} (hs : k.SameButSecret k') (a : String) (u : Usage) : keyFor k' a u = keyFor k a u := by
  unfold keyFor; rw [hs.algo, hs.usages]

theorem sign_ni {k k' : Key} (hs : k.SameButSecret k') (hu : k.usages.contains .sign = false)
    (a : String) (p : Args) (d r : ByteArray) : sign a p k' d r = sign a p k d r := by
  have h1 : keyFor k a .sign = .error .invalidAccess := keyFor_lacks hu
  have h2 : keyFor k' a .sign = .error .invalidAccess := by rw [keyFor_same hs]; exact h1
  unfold sign; rw [h1, h2]; rfl

theorem verify_ni {k k' : Key} (hs : k.SameButSecret k') (hu : k.usages.contains .verify = false)
    (a : String) (p : Args) (sig d : ByteArray) : verify a p k' sig d = verify a p k sig d := by
  have h1 : keyFor k a .verify = .error .invalidAccess := keyFor_lacks hu
  have h2 : keyFor k' a .verify = .error .invalidAccess := by rw [keyFor_same hs]; exact h1
  unfold verify; rw [h1, h2]; rfl

theorem crypt_ni {k k' : Key} (hs : k.SameButSecret k') (e : Bool)
    (hu : k.usages.contains (if e then .encrypt else .decrypt) = false)
    (a : String) (p : Args) (d r : ByteArray) : crypt e a p k' d r = crypt e a p k d r := by
  have h1 : keyFor k a (if e then .encrypt else .decrypt) = .error .invalidAccess := keyFor_lacks hu
  have h2 : keyFor k' a (if e then .encrypt else .decrypt) = .error .invalidAccess := by rw [keyFor_same hs]; exact h1
  unfold crypt; rw [h1, h2]; rfl

theorem deriveBits_ni {k k' : Key} (hs : k.SameButSecret k') (hu : k.usages.contains .deriveBits = false)
    (a : String) (p : Args) (len : Option Nat) (st : KeyStore) : deriveBits a p k' len st = deriveBits a p k len st := by
  have h1 : keyFor k a .deriveBits = .error .invalidAccess := keyFor_lacks hu
  have h2 : keyFor k' a .deriveBits = .error .invalidAccess := by rw [keyFor_same hs]; exact h1
  unfold deriveBits; rw [h1, h2]; rfl

theorem exportKey_ni {k k' : Key} (hs : k.SameButSecret k') (hx : k.extractable = false) (f : String) :
    exportKey k' f = exportKey k f := by
  have hx' : k'.extractable = false := by rw [hs.extractable]; exact hx
  unfold exportKey; rw [hs.algo, hx, hx']; simp

/-! ## Algorithms: a key is used only with its own algorithm -/

/-- Each key operation that answers ran on a key of the algorithm the page named (and with
the operation's usage): `sign_usage`, `verify_usage`, `deriveBits_usage`, `crypt_usage`.
Within the operation the branch is chosen by the KEY's algorithm (`match k.algo.alg`), so
the name the page gave and the key's algorithm are one. -/
theorem op_algo_matches {a : String} {p : Args} {k : Key} {d r out : ByteArray}
    (h : sign a p k d r = .ok out) : k.algo.alg.name = a := (sign_usage h).1

/-- `Alg.name` is injective: one name, one algorithm (so `op_algo_matches` pins the key's
algorithm to the registered one). -/
theorem Alg.name_injective {a b : Alg} (h : a.name = b.name) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Alg.name] at h)

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
-- The WPT fixture's P-256 key (WebCryptoAPI/util/ec_key_fixtures.js), and off-curve and
-- out-of-range variants.
#guard p256OnCurve ((unb64? "0hCwpvnZ8BKGgFi0P6T0cQGFQ7ugDJJQ35JXwqyuXdE").getD .empty ++ (unb64? "zgN1UtSBRQzjm00QlXAbF1v6s0uObAmeGPHBmDWDYeg").getD .empty)
#guard !p256OnCurve ((unb64? "0hCwpvnZ8BKGgFi0P6T0cQGFQ7ugDJJQ35JXwqyuXdE").getD .empty ++ (unb64? "zgN1UtSBRQzjm00QlXAbF1v6s0uObAmeGPHBmDWDYeE").getD .empty)
#guard !p256OnCurve (ByteArray.mk (Array.replicate 64 0))
#guard !p256OnCurve (ByteArray.mk (Array.replicate 32 0xff) ++ (unb64? "zgN1UtSBRQzjm00QlXAbF1v6s0uObAmeGPHBmDWDYeg").getD .empty)
#guard ed25519IsSmallOrder (ByteArray.mk ((List.replicate 32 (0 : UInt8)).set 31 0x80).toArray)
#guard !ed25519IsSmallOrder (ByteArray.mk (List.replicate 32 (9 : UInt8)).toArray)
#guard (normalizeSpec "deriveBits" "pbkdf2").toOption.map (·.1) == some "PBKDF2"
#guard (normalizeSpec "encrypt" "AES-GCM").isOk == false
#guard Usage.ofName? "decapsulateKey" == some .decapsulateKey
#guard truncateBits (ByteArray.mk #[0xff, 0xff]) 12 == ByteArray.mk #[0xff, 0xf0]
#guard Err.all.map Err.code == [-20, -23, -24, -25, -26, -22, -27]
-- PKCS #8 is read strictly (cryptosec F8): attributes and a v2 public key only, nothing else.
#guard (readPkcs8 (tlv 0x30 (tlv 0x02 [0] ++ tlv 0x30 (tlv 0x06 oidX25519) ++ tlv 0x04 (tlv 0x04 (List.replicate 32 1))))).isSome
#guard (readPkcs8 (tlv 0x30 (tlv 0x02 [0] ++ tlv 0x30 (tlv 0x06 oidX25519) ++ tlv 0x04 (tlv 0x04 (List.replicate 32 1)) ++ [0x05, 0x00]))).isNone
#guard (readPkcs8 (tlv 0x30 (tlv 0x02 [0] ++ tlv 0x30 (tlv 0x06 oidX25519) ++ tlv 0x04 (tlv 0x04 (List.replicate 32 1)) ++ tlv 0xa0 []))).isSome
#guard (readPkcs8 (tlv 0x30 (tlv 0x02 [0] ++ tlv 0x30 (tlv 0x06 oidX25519) ++ tlv 0x04 (tlv 0x04 (List.replicate 32 1)) ++ tlv 0x81 [0]))).isNone
#guard (readPkcs8 (tlv 0x30 (tlv 0x02 [1] ++ tlv 0x30 (tlv 0x06 oidX25519) ++ tlv 0x04 (tlv 0x04 (List.replicate 32 1)) ++ tlv 0x81 [0]))).isSome
#guard noDups ["sign", "verify", "x"] && !noDups ["sign", "x", "sign"]

end L4Factoidal.Crypto.WebCryptoKeys
