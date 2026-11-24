/-
L4Factoidal.XML.Enc — XML Encryption Syntax and Processing Version 1.1
(W3C Recommendation 11 April 2013, https://www.w3.org/TR/xmlenc-core1/):
decryption and encryption in one fixed profile
(https://github.com/danbri/factoidal/issues/1084; design record
`docs/designissues/2026-10-27-xml-encryption-and-jwe.md`, section "XML
Encryption 1.1 profile").

## What is accepted

Everything below is an allowlist. Any other algorithm, element or form is
refused, with a message that names it. Nothing is skipped.

  * `xenc:EncryptedData` with `Type` Element or Content (§3.1; another or no
    `Type` is refused by `decrypt`). `decryptOctets` gives the plaintext
    octets of a document element `EncryptedData` with any or no `Type`
    (§4.4 step 3: data that is not an element or element content goes to
    the application as octets). Children: `xenc:EncryptionMethod` (required here),
    optional `ds:KeyInfo`, `xenc:CipherData` holding `xenc:CipherValue`
    (`xenc:CipherReference` is refused: no retrieval), nothing else.
  * Data encryption (§5.2): `xmlenc11#aes128-gcm`, `xmlenc11#aes256-gcm`.
    `xmlenc#aes128-cbc` and `xmlenc#aes256-cbc` only when the caller sets
    `Opts.allowCbc`, because CBC without a MAC is malleable (Jager and
    Somorovsky, "How to Break XML Encryption", CCS 2011). AES-192 is
    refused (the cipher interface has 128 and 256-bit keys only).
  * `ds:KeyInfo` of `EncryptedData`: one `xenc:EncryptedKey`, one
    `ds:RetrievalMethod` whose `Type` is `xmlenc#EncryptedKey` and whose
    `URI` is `#id` of exactly one `xenc:EncryptedKey` in the same document
    (no transforms, no remote retrieval), one `xenc:AgreementMethod`
    (direct key agreement), one `xenc11:DerivedKey` (§5.4.3), or one
    `ds:KeyName` that names a caller's symmetric key. `decryptWrapped` (SAML `EncryptedElementType`) also
    takes the one `EncryptedKey` sibling when `KeyInfo` is absent.
  * Key transport (§5.5): `xmlenc#rsa-oaep-mgf1p` (MGF1 with SHA-1) and
    `xmlenc11#rsa-oaep` (MGF1 with the hash of `xenc11:MGF`: `mgf1sha1`,
    `mgf1sha224`, `mgf1sha256`, `mgf1sha384` or `mgf1sha512`; default
    `mgf1sha1`), each with the `ds:DigestMethod` SHA-1 (the default),
    SHA-224, SHA-256, SHA-384 or SHA-512, and an optional
    `xenc:OAEPparams` label (§5.5.2). The digest and the MGF1 hash are
    independent (`OaepDigest`, `oaepHashOf`).
    `xmlenc#rsa-1_5` is refused (Bleichenbacher, CRYPTO 1998). The RSA key
    is the caller's key named by `ds:KeyName` in the `EncryptedKey`'s
    `KeyInfo`, or the caller's only RSA key. `ds:X509Data` and
    `ds:KeyValue` beside it are hints this code does not read: the key is
    always the caller's.
  * Key wrap (§5.6): `xmlenc#kw-aes128`, `xmlenc#kw-aes256`, with a key
    encryption key named by `ds:KeyName`, the caller's only symmetric key
    of that size, or one derived by an `xenc:AgreementMethod`.
  * Key agreement (§5.4.1, §5.6): `xmlenc11#ECDH-ES` on P-256 (originator
    key `dsig11:ECKeyValue` with `NamedCurve` `urn:oid:1.2.840.10045.3.1.7`
    and an uncompressed point) or X25519, and
    `http://www.w3.org/2021/04/xmldsig-more#x25519` (RFC 9231 §2.6.2) on
    X25519 (originator key `dsig11:DEREncodedKeyValue`, the RFC 8410
    SubjectPublicKeyInfo); key derivation `xmlenc11#ConcatKDF` with the
    `ds:DigestMethod` SHA-256 (§5.4.1), or `xmlenc11#pbkdf2` (§5.4.2) with a
    `Specified` salt, an `IterationCount` of at most
    `Opts.maxPbkdf2Iterations`, a `KeyLength` equal to the length of the key
    it makes, and the PRF HMAC-SHA-1, -256, -384 or -512 (`Prims.pbkdf2`,
    HACL* HMAC); no `KA-Nonce`. The recipient key is named by
    `ds:KeyName` in `xenc:RecipientKeyInfo`, or is the caller's only key on
    that curve.
  * Finite-field Diffie-Hellman key agreement `xmlenc11#dh-es` (§5.6.3):
    originator key `xenc:DHKeyValue` (§5.6.1); the recipient key is a
    `DhKey` (`p`, `g`, `q`, `x`); the originator's domain parameters, when
    given, must be the key's; the public value is checked (`[2, p - 2]`,
    `y^q mod p = 1`) before the private value is used; `Z = y^x mod p` by
    HACL* (`Dh.modExp`); then Concat KDF or PBKDF2 as above. Primes of 2048
    to 4096 bits; 1024 bits only with `Opts.dh1024`. The legacy
    `xmlenc#dh` (§5.6.2, its own key derivation) is refused.
  * Derived keys (§5.4.3): `xenc11:DerivedKey` in `ds:KeyInfo` of
    `EncryptedData` (the content key) or of `EncryptedKey` (the key
    encryption key of AES Key Wrap), with one `xenc11:KeyDerivationMethod`
    (the Concat KDF or PBKDF2 of the key agreement list above) and an
    optional `xenc11:MasterKeyName` naming the caller's symmetric master
    key (else the caller's only symmetric key). `xenc:ReferenceList` and
    `xenc11:DerivedKeyName` are read as labels only. The master key is the
    shared secret `Z` of §5.4.1, or the password of §5.4.2.

## Decryption (§4.4)

Each `EncryptedData` is replaced by its plaintext, parsed in the context of
the namespace bindings in force on the element's parent (§4.4 step 3.4,
"the cleartext octet sequence ... in the context of the parent's
namespaces"): the octets are UTF-8, are wrapped in one element that
declares those bindings, and are parsed with `parseXML`. So the plaintext
is checked like any document: no document type declaration (it cannot hold
one), only the predefined entities, every prefix bound, and element nesting
at most `Opts.maxDepth` counted from the document element. A plaintext that
holds an `EncryptedData` is refused (one level of decryption). At most
`Opts.maxEncrypted` `EncryptedData` per document.

Every failure after the structure check (a key that does not decrypt, an
authentication tag that fails, a wrong key length, padding, a plaintext that
is not UTF-8 or not well-formed) is the one value `Failure.decryptFailed`
with the one message `decryptionError`, so the caller learns nothing about
which step failed (the padding and format oracles of Jager and Somorovsky).

## AES through a cipher

Every AES operation is a `CipherCall.Req` given to the caller's `Cipher`
(`Crypto/CipherCall.lean`): natively `nativeCipher`, on the wasm surface
`replayCipher answers`, which answers `.need req` for a request the host
has not answered yet. `Failure.need` carries that request unchanged to the
top. RSA, P-256 and X25519 are `Prims` (HACL*: `nativePrims`).

AES-CBC decryption uses two requests, because the host's CBC (WebCrypto
`AES-CBC`) removes PKCS #7 padding only, while XML Encryption §5.2 pads
with arbitrary octets and a final length octet (ISO 10126): first the
encryption of the empty message with the last ciphertext block as IV (one
block of PKCS #7 padding, under that chaining value), then the decryption
of the ciphertext with that block appended. The host removes the padding
block; this code removes the §5.2 padding.

## Encryption

`encryptNode` makes an `EncryptedData` (AES-GCM, IV first, tag last) with
one `EncryptedKey` (RSA-OAEP; ECDH-ES or X25519 key agreement and AES Key
Wrap; AES Key Wrap under a named key; or AES Key Wrap under an
`xenc11:DerivedKey` from a named symmetric master key, §5.4.3). A key
agreement or a derived key uses Concat KDF (§5.4.1) or PBKDF2 (§5.4.2) with
a specified salt (`EncryptSpec.kdf`). The content key, the IV, the OAEP
seed, the ephemeral private key and the PBKDF2 salt are octets the caller
gives (`rand`); nothing here reads a clock or a random source.

## Loops

Each walk over the tree recurses once per level of element nesting, which
the caller bounds (the plaintext nesting is checked here); each walk over
siblings, octets or characters is a tail call with an accumulator.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.DSig
import L4Factoidal.XML.Parser
import L4Factoidal.Crypto.CipherCall
import L4Factoidal.Crypto.RsaOaepChecked
import L4Factoidal.Crypto.WebHacl
import L4Factoidal.Crypto.P256Native
import L4Factoidal.Crypto.X25519
import L4Factoidal.Crypto.DhNative
import L4Factoidal.Risk
import L4Factoidal.Crypto.ConcatKdf

namespace L4Factoidal.XML.Enc

open L4Factoidal.XML
open L4Factoidal.XML.DSig
open L4Factoidal.XML.Canonical (Scope nsDecls extendScope rootScope escText escAttr isNsDeclName)
open L4Factoidal.Crypto
open L4Factoidal.Crypto.CipherCall

/-! ## Names -/

def xencNs : String := "http://www.w3.org/2001/04/xmlenc#"
def xenc11Ns : String := "http://www.w3.org/2009/xmlenc11#"
def dsig11Ns : String := "http://www.w3.org/2009/xmldsig11#"

def typeElement : String := xencNs ++ "Element"
def typeContent : String := xencNs ++ "Content"
def typeEncryptedKey : String := xencNs ++ "EncryptedKey"

def aes128Gcm : String := xenc11Ns ++ "aes128-gcm"
def aes192Gcm : String := xenc11Ns ++ "aes192-gcm"
def aes256Gcm : String := xenc11Ns ++ "aes256-gcm"
def aes128Cbc : String := xencNs ++ "aes128-cbc"
def aes192Cbc : String := xencNs ++ "aes192-cbc"
def aes256Cbc : String := xencNs ++ "aes256-cbc"
def rsaOaepMgf1p : String := xencNs ++ "rsa-oaep-mgf1p"
def rsaOaep11 : String := xenc11Ns ++ "rsa-oaep"
def rsa15 : String := xencNs ++ "rsa-1_5"
def kwAes128 : String := xencNs ++ "kw-aes128"
def kwAes192 : String := xencNs ++ "kw-aes192"
def kwAes256 : String := xencNs ++ "kw-aes256"
def ecdhEs : String := xenc11Ns ++ "ECDH-ES"
def dhEs : String := xenc11Ns ++ "dh-es"
def x25519Agreement : String := "http://www.w3.org/2021/04/xmldsig-more#x25519"
def concatKdfAlg : String := xenc11Ns ++ "ConcatKDF"
def pbkdf2Alg : String := xenc11Ns ++ "pbkdf2"
def hmacSha1Prf : String := "http://www.w3.org/2000/09/xmldsig#hmac-sha1"
def hmacSha256Prf : String := "http://www.w3.org/2001/04/xmldsig-more#hmac-sha256"
def hmacSha384Prf : String := "http://www.w3.org/2001/04/xmldsig-more#hmac-sha384"
def hmacSha512Prf : String := "http://www.w3.org/2001/04/xmldsig-more#hmac-sha512"
def sha1Digest : String := "http://www.w3.org/2000/09/xmldsig#sha1"
def sha256Digest : String := xencNs ++ "sha256"
def mgf1Sha1 : String := xenc11Ns ++ "mgf1sha1"
def mgf1Sha256 : String := xenc11Ns ++ "mgf1sha256"
def p256Oid : String := "urn:oid:1.2.840.10045.3.1.7"

/-- The one message of every decryption failure after the structure check. -/
def decryptionError : String := "XML decryption failed"

/-- The AES-CBC refusal. -/
def cbcRefusal : String :=
  "AES-CBC data encryption is refused unless the caller allows it (allowCbc): CBC without a " ++
  "MAC is malleable (Jager and Somorovsky, CCS 2011)"

/-! ## Primitives, keys, options, failures -/

/-- A label hash or an MGF1 hash for RSA-OAEP (§5.5.2). -/
inductive OaepDigest where
  | sha1 | sha224 | sha256 | sha384 | sha512
  deriving BEq, Repr, DecidableEq

/-- HACL* on native and Wasm. Every refusal stays a refusal. -/
def OaepDigest.hacl? : OaepDigest → ByteArray → Option ByteArray
  | .sha1 => WebHacl.hash? .sha1
  | .sha224 => WebHacl.sha224ForXml?
  | .sha256 => WebHacl.hash? .sha256
  | .sha384 => WebHacl.hash? .sha384
  | .sha512 => WebHacl.hash? .sha512

/-- The public-key and OAEP digest primitives: HACL* natively (`nativePrims`), any
functions in a test. -/
structure Prims where
  /-- `c^d mod n` (`RsaOaep.RsaOp`, arguments `n d c`). -/
  rsaPrivate : RsaOaep.RsaOp
  /-- `m^e mod n` (arguments `n e m`). -/
  rsaPublic : RsaOaep.RsaOp
  /-- P-256 ECDH: their raw `x || y`, our scalar, to the 32-octet `Z`. -/
  p256Ecdh : ByteArray → ByteArray → Option ByteArray
  /-- P-256: scalar to raw `x || y`. -/
  p256Public : ByteArray → Option ByteArray
  /-- X25519: our scalar, their u-coordinate, to `Z` (RFC 7748 §6.1 checked). -/
  x25519 : ByteArray → ByteArray → Option ByteArray
  /-- X25519: scalar to public u-coordinate. -/
  x25519Public : ByteArray → Option ByteArray
  /-- Both OAEP hashes use the checked backend, including MGF1 on the seed. -/
  oaepDigest : OaepDigest → ByteArray → Option ByteArray := OaepDigest.hacl?
  /-- PBKDF2 (RFC 8018 §5.2) with HMAC over the hash `a`: password, salt,
  iteration count, key length in octets. HACL* HMAC by default
  (`WebHacl.haclHash`); `pbkdf2_native_eq_spec` relates it to the pure function. -/
  pbkdf2 : WebHacl.HashAlg → ByteArray → ByteArray → Nat → Nat → ByteArray :=
    fun a => WebCrypto.pbkdf2 (WebHacl.haclHash a)
  /-- Finite-field Diffie-Hellman: `p x y` to `y^x mod p` as `|p|` octets
  (HACL* `Hacl_Bignum64_mod_exp_consttime`, `Dh.modExp`). -/
  dhModExp : ByteArray → ByteArray → ByteArray → Option ByteArray := Dh.modExp

/-- HACL* (`RsaOaep.rsaPrivateOp`, `Rsa.rsaPublicOp`, `P256`, `X25519`). -/
def nativePrims : Prims where
  rsaPrivate := RsaOaep.rsaPrivateOp
  rsaPublic := Rsa.rsaPublicOp
  p256Ecdh := P256.p256Ecdh
  p256Public := P256.p256SecretToPublic
  x25519 := X25519.dh?
  x25519Public := X25519.publicKey?

inductive Curve where
  | p256
  | x25519
  deriving BEq, DecidableEq, Repr

/-- An RSA private key: modulus, private exponent; `e` for encryption to it. -/
structure RsaKey where
  kid : Option String := none
  n : ByteArray
  e : ByteArray := ByteArray.empty
  d : ByteArray

/-- A P-256 or X25519 private key (the scalar). -/
structure EcKey where
  kid : Option String := none
  curve : Curve
  d : ByteArray

/-- A symmetric key: a key encryption key, or a content key named by
`ds:KeyName`. -/
structure SymKey where
  kid : Option String := none
  k : ByteArray

/-- A finite-field Diffie-Hellman private key (§5.6.1): the prime `p`, the
generator `g`, the order `q` of the subgroup `g` generates, and the private
value `x`, each a big-endian number. -/
structure DhKey where
  kid : Option String := none
  p : ByteArray
  g : ByteArray
  q : ByteArray
  x : ByteArray

/-- The caller's keys. -/
structure Keys where
  rsa : List RsaKey := []
  ec : List EcKey := []
  sym : List SymKey := []
  dh : List DhKey := []

def Keys.isEmpty (k : Keys) : Bool := k.rsa.isEmpty && k.ec.isEmpty && k.sym.isEmpty && k.dh.isEmpty

structure Opts where
  /-- Accept `aes128-cbc` and `aes256-cbc` data encryption. -/
  allowCbc : Bool := false
  /-- The deepest element nesting of a decrypted document. -/
  maxDepth : Nat := 32
  /-- The most `EncryptedData` elements decrypted in one document. -/
  maxEncrypted : Nat := 16
  /-- The largest PBKDF2 `IterationCount` (§5.4.2) accepted. Each iteration is
  one HMAC; a larger count is refused before any key is used, so a document
  cannot make the reader do unbounded work. -/
  maxPbkdf2Iterations : Nat := 1000000
  /-- Accept a Diffie-Hellman prime of 1024 to 2047 bits (`xmlenc11#dh-es`).
  Only `Risk.dangerouslyAccept .dh1024Agreement` makes the token. -/
  dh1024 : Option (Risk.Accepted .dh1024Agreement) := none

/-- Why a decryption or encryption gives no document. -/
inductive Failure where
  /-- A structure or allowlist refusal, before any key is used: the message
  names the rule. -/
  | refused (msg : String)
  /-- Every failure after the structure check: `decryptionError`. -/
  | decryptFailed
  /-- The cipher needs the host to answer this request (replay mode). -/
  | need (req : Req)
  deriving Inhabited

def Failure.message : Failure → String
  | .refused m => m
  | .decryptFailed => decryptionError
  | .need r => s!"an AES request ({r.op.name}) is not answered yet"

abbrev M := Except Failure

def refuse {α : Type} (m : String) : M α := .error (.refused m)

/-- One cipher call: a refusal is the decryption failure; a need is carried
up unchanged. -/
def ccall (c : Cipher) (r : Req) : M ByteArray :=
  match c.call r with
  | .ok b => .ok b
  | .error .refused => .error .decryptFailed
  | .error (.need q) => .error (.need q)

/-- A cipher refusal during encryption is a refusal with a message. -/
def ccallEnc (c : Cipher) (r : Req) : M ByteArray :=
  match c.call r with
  | .ok b => .ok b
  | .error .refused => refuse s!"the AES operation {r.op.name} was refused"
  | .error (.need q) => .error (.need q)

/-! ## Octets and text, as loops -/

def hexNib? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- `xs:hexBinary` (either case) to octets; a tail call per octet. -/
def hexLoop : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | [_], _ => none
  | a :: b :: rest, acc =>
      match hexNib? a, hexNib? b with
      | some x, some y => hexLoop rest (acc.push (x * 16 + y).toUInt8)
      | _, _ => none

def hexBytes? (s : String) : Option ByteArray := hexLoop s.toList ByteArray.empty

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexOfLoop (b : ByteArray) : (fuel i : Nat) → String → String
  | 0, _, acc => acc
  | f + 1, i, acc =>
      if h : i < b.size then
        let x := b[i].toNat
        hexOfLoop b f (i + 1) ((acc.push (hexDigit (x / 16))).push (hexDigit (x % 16)))
      else acc

def hexOf (b : ByteArray) : String := hexOfLoop b b.size 0 ""

def b64Digit (n : Nat) : Char :=
  if n < 26 then Char.ofNat (65 + n)
  else if n < 52 then Char.ofNat (71 + n)
  else if n < 62 then Char.ofNat (n - 4)
  else if n == 62 then '+' else '/'

/-- RFC 4648 §4 base64 with padding; a tail call per three octets. -/
def b64Loop (b : ByteArray) : (fuel i : Nat) → String → String
  | 0, _, acc => acc
  | f + 1, i, acc =>
      let g (j : Nat) : Nat := (b.get! j).toNat
      if i + 3 ≤ b.size then
        let x := g i * 65536 + g (i + 1) * 256 + g (i + 2)
        b64Loop b f (i + 3)
          ((((acc.push (b64Digit (x / 262144 % 64))).push (b64Digit (x / 4096 % 64))).push
            (b64Digit (x / 64 % 64))).push (b64Digit (x % 64)))
      else if i + 2 = b.size then
        let x := g i * 65536 + g (i + 1) * 256
        (((acc.push (b64Digit (x / 262144 % 64))).push (b64Digit (x / 4096 % 64))).push
          (b64Digit (x / 64 % 64))).push '='
      else if i + 1 = b.size then
        let x := g i * 65536
        (((acc.push (b64Digit (x / 262144 % 64))).push (b64Digit (x / 4096 % 64))).push '=').push '='
      else acc

def base64 (b : ByteArray) : String := b64Loop b (b.size / 3 + 1) 0 ""

/-- Base64 text (either alphabet, whitespace ignored) to octets. -/
def base64Decode? (s : String) : Option ByteArray :=
  (L4Factoidal.VC.Multibase.base64FlexDecode (String.ofList (s.toList.filter (!isXmlWs ·)))).map
    fun bs => ⟨bs.toArray⟩

/-- Is the element nesting of `cs` at most `maxD`, starting at depth `d`?
The scan of `SAML.nestingOk`: `<` not followed by `/`, `!` or `?` opens a
level, `</` and `/>` close one; markup in a comment or CDATA section can
only make the count larger. A tail call per character. -/
def nestingWithin (maxD : Nat) : List Char → Nat → Bool
  | [], _ => true
  | '<' :: '/' :: rest, d => nestingWithin maxD rest (d - 1)
  | '/' :: '>' :: rest, d => nestingWithin maxD rest (d - 1)
  | '<' :: c :: rest, d =>
      if c == '!' || c == '?' then nestingWithin maxD rest d
      else if d + 1 > maxD then false else nestingWithin maxD rest (d + 1)
  | _ :: rest, d => nestingWithin maxD rest d

/-! ## Serialization (for plaintext and for the op output) -/

def attrsText (as : List Attribute) : String :=
  as.foldl (fun acc a => acc ++ " " ++ a.name ++ "=\"" ++ escAttr a.value ++ "\"") ""

mutual

/-- Append the text of a node to `acc`. -/
def serNode (acc : String) : Node → String
  | .text t => acc ++ escText t
  | .cdata t => acc ++ escText t
  | .comment b => acc ++ "<!--" ++ b ++ "-->"
  | .pi t d => acc ++ "<?" ++ t ++ (if d.isEmpty then "" else " " ++ d) ++ "?>"
  | .element t attrs kids =>
      serNodes (acc ++ "<" ++ t ++ attrsText attrs ++ ">") kids ++ "</" ++ t ++ ">"

/-- `serNode` over siblings; a tail call per sibling. -/
def serNodes (acc : String) : List Node → String
  | [] => acc
  | n :: ns => serNodes (serNode acc n) ns

end

/-- A document as UTF-8 XML text, with no XML declaration. Comments and
processing instructions outside the document element are kept, each on
its own line. -/
def serializeDocument (d : Document) : String :=
  let pro := d.prolog.foldl (fun acc n => serNode acc n ++ "\n") ""
  let body := serNode pro d.root
  d.epilog.foldl (fun acc n => serNode (acc ++ "\n") n) body

/-! ## Reading the encrypted structure -/

def isEncData (e : El) : Bool := e.is xencNs "EncryptedData"
def isEncKey (e : El) : Bool := e.is xencNs "EncryptedKey"

/-- An `EncryptedData` or `EncryptedKey`, read. -/
structure EncParts where
  method : El
  keyInfo : Option El
  cipherValue : ByteArray

def cipherValueOf (cd : El) : M ByteArray :=
  if !cd.elementOnly then refuse "xenc:CipherData has unexpected content"
  else match cd.children with
  | [v] =>
      if v.is xencNs "CipherReference" then
        refuse "xenc:CipherReference is not supported: only xenc:CipherValue"
      else if !v.is xencNs "CipherValue" then refuse "xenc:CipherData must hold xenc:CipherValue"
      else match v.text? >>= base64Decode? with
        | some b => .ok b
        | none => refuse "xenc:CipherValue is not base64"
  | _ => refuse "xenc:CipherData must hold one xenc:CipherValue"

/-- The children of an `EncryptedType` element: `EncryptionMethod`,
optional `ds:KeyInfo`, `CipherData`, then only elements `extraOk` accepts. -/
def encParts (e : El) (extraOk : El → Bool) : M EncParts := do
  if !e.elementOnly then refuse s!"xenc:{e.lname} has unexpected content"
  match e.children with
  | [] => refuse s!"xenc:{e.lname} is empty"
  | m :: rest =>
      if !m.is xencNs "EncryptionMethod" then
        refuse s!"xenc:{e.lname} must begin with xenc:EncryptionMethod"
      let (ki, rest) := match rest with
        | k :: r => if k.is dsNs "KeyInfo" then (some k, r) else (none, rest)
        | [] => (none, [])
      match rest with
      | [] => refuse s!"xenc:{e.lname} has no xenc:CipherData"
      | cd :: tail =>
          if !cd.is xencNs "CipherData" then refuse s!"xenc:{e.lname} has no xenc:CipherData"
          if !tail.all extraOk then refuse s!"xenc:{e.lname} has an unsupported child"
          let cv ← cipherValueOf cd
          pure { method := m, keyInfo := ki, cipherValue := cv }

/-- The data encryption algorithm and its key length in octets. -/
inductive DataAlg where
  | gcm (len : Nat)
  | cbc (len : Nat)

def DataAlg.keyLen : DataAlg → Nat
  | .gcm l => l
  | .cbc l => l

def DataAlg.uri : DataAlg → String
  | .gcm 16 => aes128Gcm
  | .gcm _ => aes256Gcm
  | .cbc 16 => aes128Cbc
  | .cbc _ => aes256Cbc

def dataAlgOf (opts : Opts) (m : El) : M DataAlg :=
  if !(m.elementOnly && m.children.isEmpty) then
    refuse "the data encryption method must have no parameters"
  else match m.attr? "Algorithm" with
  | none => refuse "xenc:EncryptionMethod has no Algorithm"
  | some u =>
      if u == aes128Gcm then .ok (.gcm 16)
      else if u == aes256Gcm then .ok (.gcm 32)
      else if u == aes128Cbc || u == aes256Cbc then
        if opts.allowCbc then .ok (.cbc (if u == aes128Cbc then 16 else 32)) else refuse cbcRefusal
      else if u == aes192Gcm || u == aes192Cbc then refuse "AES-192 is not supported"
      else refuse s!"the data encryption algorithm {u} is not supported"

/-- The pure specification used by the hash-record equations and build-time tests. -/
def OaepDigest.fn : OaepDigest → ByteArray → ByteArray
  | .sha1 => L4Factoidal.Crypto.sha1
  | .sha224 => L4Factoidal.Crypto.sha224
  | .sha256 => L4Factoidal.Crypto.sha256
  | .sha384 => L4Factoidal.Crypto.sha384
  | .sha512 => L4Factoidal.Crypto.sha512

/-- The output length in octets. -/
def OaepDigest.len : OaepDigest → Nat
  | .sha1 => 20 | .sha224 => 28 | .sha256 => 32 | .sha384 => 48 | .sha512 => 64

def Prims.oaepProvider (p : Prims) (d : OaepDigest) : RsaOaep.DigestProvider :=
  { size := d.len, run := p.oaepDigest d }

/-- The digest method identifiers: §5.7 of XML Encryption 1.1 (SHA-1,
SHA-256, SHA-384, SHA-512) and SHA-224 of RFC 6931 §2.1.2, which XML
Signature 1.1 also lists. -/
def OaepDigest.digestUri : OaepDigest → String
  | .sha1 => sha1Digest
  | .sha224 => "http://www.w3.org/2001/04/xmldsig-more#sha224"
  | .sha256 => sha256Digest
  | .sha384 => "http://www.w3.org/2001/04/xmldsig-more#sha384"
  | .sha512 => xencNs ++ "sha512"

/-- The MGF identifiers of §5.5.2: `xmlenc11#mgf1sha1` and the SHA-2 ones. -/
def OaepDigest.mgfUri : OaepDigest → String
  | .sha1 => mgf1Sha1
  | .sha224 => xenc11Ns ++ "mgf1sha224"
  | .sha256 => mgf1Sha256
  | .sha384 => xenc11Ns ++ "mgf1sha384"
  | .sha512 => xenc11Ns ++ "mgf1sha512"

def OaepDigest.all : List OaepDigest := [.sha1, .sha224, .sha256, .sha384, .sha512]

def OaepDigest.ofDigestUri? (u : String) : Option OaepDigest :=
  OaepDigest.all.find? (·.digestUri == u)

def OaepDigest.ofMgfUri? (u : String) : Option OaepDigest :=
  OaepDigest.all.find? (·.mgfUri == u)

/-- The OAEP hashes of a label digest and an MGF1 hash. -/
def oaepHashOf (digest mgf : OaepDigest) : RsaOaep.OaepHash :=
  { hash := digest.fn, hLen := digest.len, mgfHash := mgf.fn, mgfLen := mgf.len }

/-- With the same hash for the digest and MGF1, `oaepHashOf` is the OAEP
instance JWE uses (`RSA-OAEP` is SHA-1, `RSA-OAEP-256` is SHA-256). So the
XML Encryption 1.0 algorithm `rsa-oaep-mgf1p` with its default digest, and
XML Encryption 1.1 `rsa-oaep` with SHA-256 and `mgf1sha256`, are the same
function as the two JWE algorithms. -/
theorem oaepHashOf_sha1 : oaepHashOf .sha1 .sha1 = RsaOaep.oaepSha1 := rfl

theorem oaepHashOf_sha256 : oaepHashOf .sha256 .sha256 = RsaOaep.oaepSha256 := rfl

/-- The key encryption algorithm of an `EncryptedKey`. -/
inductive KeyAlg where
  | oaep (digest mgf : OaepDigest) (label : ByteArray)
  | kw (len : Nat)

def KeyAlg.oaepHash (sha256 : Bool) : RsaOaep.OaepHash :=
  if sha256 then RsaOaep.oaepSha256 else RsaOaep.oaepSha1

/-- The `Algorithm` of a parameter element with no content. -/
def paramAlg (e : El) : M String :=
  if !(e.elementOnly && e.children.isEmpty) then refuse s!"{e.lname} must be empty"
  else match e.attr? "Algorithm" with
  | some a => .ok a
  | none => refuse s!"{e.lname} has no Algorithm"

/-- The OAEP parameters: (digest URI, MGF URI, label), each at most once. -/
def oaepParams (m : El) (mgfAllowed : Bool) : M (Option String × Option String × ByteArray) := do
  if !m.elementOnly then refuse "the key transport method has unexpected content"
  let mut dig : Option String := none
  let mut mgf : Option String := none
  let mut label : Option ByteArray := none
  for c in m.children do
    if c.is dsNs "DigestMethod" && dig.isNone then dig := some (← paramAlg c)
    else if mgfAllowed && c.is xenc11Ns "MGF" && mgf.isNone then mgf := some (← paramAlg c)
    else if c.is xencNs "OAEPparams" && label.isNone then
      match c.text? >>= base64Decode? with
      | some b => label := some b
      | none => refuse "xenc:OAEPparams is not base64"
    else refuse s!"the key transport method has an unsupported child {c.lname}"
  pure (dig, mgf, label.getD ByteArray.empty)

def keyAlgOf (m : El) : M KeyAlg := do
  match m.attr? "Algorithm" with
  | none => refuse "xenc:EncryptionMethod has no Algorithm"
  | some u =>
      if u == rsa15 then
        refuse "RSA PKCS #1 v1.5 key transport (rsa-1_5) is refused (Bleichenbacher, CRYPTO 1998)"
      else if u == rsaOaepMgf1p || u == rsaOaep11 then
        -- §5.5.2: the digest defaults to SHA-1; `rsa-oaep-mgf1p` fixes MGF1
        -- with SHA-1, `xmlenc11#rsa-oaep` names it in `xenc11:MGF` (default
        -- `mgf1sha1`).
        let (dig, mgf, label) ← oaepParams m (u == rsaOaep11)
        let d ← match dig with
          | none => pure OaepDigest.sha1
          | some d => match OaepDigest.ofDigestUri? d with
            | some x => pure x
            | none => refuse s!"the RSA-OAEP digest method {d} is not supported"
        let g ← match mgf with
          | none => pure OaepDigest.sha1
          | some g => match OaepDigest.ofMgfUri? g with
            | some x => pure x
            | none => refuse s!"the RSA-OAEP mask generation function {g} is not supported"
        pure (.oaep d g label)
      else if u == kwAes128 || u == kwAes256 then
        if !(m.elementOnly && m.children.isEmpty) then refuse "the key wrap method must have no parameters"
        else pure (.kw (if u == kwAes128 then 16 else 32))
      else if u == kwAes192 then refuse "AES-192 key wrap is not supported"
      else refuse s!"the key encryption algorithm {u} is not supported"

/-! ## Choosing the caller's key -/

def pick {α : Type} (what : String) (name? : Option String) (ks : List α) (kid : α → Option String) : M α :=
  match name? with
  | some n =>
      match ks.filter (fun k => kid k == some n) with
      | [k] => .ok k
      | [] => refuse s!"no {what} key named {n} is configured"
      | _ => refuse s!"more than one {what} key is named {n}"
  | none =>
      match ks with
      | [k] => .ok k
      | [] => refuse s!"no {what} key is configured"
      | _ => refuse s!"more than one {what} key is configured and the document names none"

def keyNameOf (k : El) : M String :=
  match k.text? with
  | some t => if (trimWs t).isEmpty then refuse "ds:KeyName is empty" else .ok (trimWs t)
  | none => refuse "ds:KeyName must hold text only"

/-! ## Key agreement (§5.4.1, §5.6) -/

/-- The X25519 SubjectPublicKeyInfo prefix (RFC 8410 §4). -/
def x25519SpkiPrefix : ByteArray :=
  ⟨#[0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x6e, 0x03, 0x21, 0x00]⟩

/-- The originator's public key: the curve and the raw key (P-256 `x || y`,
X25519 u-coordinate). -/
def originatorKey (o : El) : M (Curve × ByteArray) := do
  if !o.elementOnly then refuse "xenc:OriginatorKeyInfo has unexpected content"
  let cands := o.children.foldl (fun acc c =>
    if c.is dsNs "KeyValue" then acc ++ c.children else acc ++ [c]) []
  match cands with
  | [k] =>
      if k.is dsig11Ns "ECKeyValue" then
        if !k.elementOnly then refuse "dsig11:ECKeyValue has unexpected content"
        match k.children with
        | [nc, pk] =>
            if !(nc.is dsig11Ns "NamedCurve" && nc.attr? "URI" == some p256Oid) then
              refuse "the originator key is not on P-256"
            if !pk.is dsig11Ns "PublicKey" then refuse "dsig11:ECKeyValue has no dsig11:PublicKey"
            match pk.text? >>= base64Decode? with
            | some b =>
                if b.size == 65 && b.get! 0 == 4 then pure (.p256, b.extract 1 65)
                else refuse "the P-256 originator key is not an uncompressed point"
            | none => refuse "dsig11:PublicKey is not base64"
        | _ => refuse "dsig11:ECKeyValue must be NamedCurve and PublicKey"
      else if k.is dsig11Ns "DEREncodedKeyValue" then
        match k.text? >>= base64Decode? with
        | some b =>
            if b.size == 44 && b.extract 0 12 == x25519SpkiPrefix then pure (.x25519, b.extract 12 44)
            else refuse "the DER-encoded originator key is not an X25519 key"
        | none => refuse "dsig11:DEREncodedKeyValue is not base64"
      else refuse s!"the originator key form {k.lname} is not supported"
  | _ => refuse "xenc:OriginatorKeyInfo must hold one public key"

/-- The ConcatKDF parameters (§5.4.1). -/
def concatKdfParams (kdm : El) : M ConcatKdf.XmlEncParams := do
  if kdm.attr? "Algorithm" != some concatKdfAlg then refuse "the key derivation method must be ConcatKDF"
  if !kdm.elementOnly then refuse "xenc11:KeyDerivationMethod has unexpected content"
  match kdm.children with
  | [p] =>
      if !p.is xenc11Ns "ConcatKDFParams" then refuse "xenc11:KeyDerivationMethod must hold ConcatKDFParams"
      if !p.elementOnly then refuse "xenc11:ConcatKDFParams has unexpected content"
      match p.children with
      | [dm] =>
          if !dm.is dsNs "DigestMethod" then refuse "xenc11:ConcatKDFParams must hold ds:DigestMethod"
          if (← paramAlg dm) != sha256Digest then refuse "ConcatKDF is supported with SHA-256 only"
          let attr (n : String) : M (Option ByteArray) :=
            match p.attr? n with
            | none => .ok none
            | some v =>
                -- An empty value is read as the empty bit string, as an absent
                -- attribute is: the W3C interop case AGRMNT.1 (Oracle) writes
                -- AlgorithmID="" and PartyVInfo="".
                if (trimWs v).isEmpty then .ok none
                else match hexBytes? (trimWs v) with
                  | some b => .ok (some b)
                  | none => refuse s!"ConcatKDFParams {n} is not hexBinary"
          let params : ConcatKdf.XmlEncParams :=
            { algorithmId := ← attr "AlgorithmID", partyUInfo := ← attr "PartyUInfo",
              partyVInfo := ← attr "PartyVInfo", suppPubInfo := ← attr "SuppPubInfo",
              suppPrivInfo := ← attr "SuppPrivInfo" }
          if (ConcatKdf.xmlEncOtherInfo? params).isNone then
            refuse ("ConcatKDFParams are malformed or not a whole number of octets " ++
              "(https://github.com/danbri/factoidal/issues/1097)")
          pure params
      | _ => refuse "xenc11:ConcatKDFParams must hold one ds:DigestMethod"
  | _ => refuse "xenc11:KeyDerivationMethod must hold one ConcatKDFParams"

/-! ## PBKDF2 (§5.4.2) -/

/-- The `xenc11:PBKDF2-params` of §5.4.2: the specified salt, the iteration
count, the key length in octets and the pseudorandom function (HMAC over
`prf`). -/
structure Pbkdf2Params where
  salt : ByteArray
  iterations : Nat
  keyLength : Nat
  prf : WebHacl.HashAlg

/-- The `xenc11:PRF` algorithms accepted: HMAC-SHA-1 (XML Signature 1.1
§6.3) and HMAC-SHA-256/384/512 (RFC 9231 §2.2). HMAC-SHA-224 and others are
refused (no HACL* HMAC for them here). -/
def prfOf? (u : String) : Option WebHacl.HashAlg :=
  if u == hmacSha1Prf then some .sha1
  else if u == hmacSha256Prf then some .sha256
  else if u == hmacSha384Prf then some .sha384
  else if u == hmacSha512Prf then some .sha512
  else none

/-- Decimal digits to a number, at most 12 digits (a larger value is refused
by the caller's bounds anyway). -/
def digitsLoop : List Char → Nat → Option Nat
  | [], n => some n
  | c :: cs, n => if c.isDigit then digitsLoop cs (n * 10 + (c.toNat - 48)) else none

/-- An `xsd:positiveInteger` (XML Schema 1.1 Part 2 §3.4.25): an optional `+`,
digits, value at least 1; whitespace collapsed. -/
def positiveInteger? (s : String) : Option Nat :=
  let t := trimWs s
  let cs := match t.toList with
    | '+' :: rest => rest
    | l => l
  if cs.isEmpty || cs.length > 12 then none
  else match digitsLoop cs 0 with
    | some n => if n ≥ 1 then some n else none
    | none => none

/-- The PBKDF2 parameters of a `xenc11:KeyDerivationMethod` (§5.4.2). The
children are the schema's sequence `Salt`, `IterationCount`, `KeyLength`,
`PRF`, each once and in that order. `Salt` must be `Specified` (`OtherSource`
is refused: no algorithm for it is defined). -/
def pbkdf2Params (opts : Opts) (kdm : El) : M Pbkdf2Params := do
  if kdm.attr? "Algorithm" != some pbkdf2Alg then refuse "the key derivation method must be pbkdf2"
  if !kdm.elementOnly then refuse "xenc11:KeyDerivationMethod has unexpected content"
  match kdm.children with
  | [p] =>
      if !p.is xenc11Ns "PBKDF2-params" then refuse "xenc11:KeyDerivationMethod must hold PBKDF2-params"
      if !p.elementOnly then refuse "xenc11:PBKDF2-params has unexpected content"
      match p.children with
      | [saltEl, itEl, lenEl, prfEl] =>
          if !saltEl.is xenc11Ns "Salt" then refuse "xenc11:PBKDF2-params must start with xenc11:Salt"
          if !itEl.is xenc11Ns "IterationCount" then refuse "xenc11:PBKDF2-params has no xenc11:IterationCount"
          if !lenEl.is xenc11Ns "KeyLength" then refuse "xenc11:PBKDF2-params has no xenc11:KeyLength"
          if !prfEl.is xenc11Ns "PRF" then refuse "xenc11:PBKDF2-params has no xenc11:PRF"
          if !saltEl.elementOnly then refuse "xenc11:Salt has unexpected content"
          let salt ← match saltEl.children with
            | [sp] =>
                if sp.is xenc11Ns "OtherSource" then
                  refuse "PBKDF2 xenc11:OtherSource salt is not supported: no algorithm for it is defined"
                if !sp.is xenc11Ns "Specified" then refuse "xenc11:Salt must hold xenc11:Specified"
                match sp.text? >>= base64Decode? with
                | some b => pure b
                | none => refuse "PBKDF2 xenc11:Specified salt is not base64"
            | _ => refuse "xenc11:Salt must hold one xenc11:Specified"
          let iterations ← match itEl.text? >>= positiveInteger? with
            | some n => pure n
            | none => refuse "PBKDF2 xenc11:IterationCount is not a positive integer"
          if iterations > opts.maxPbkdf2Iterations then
            refuse s!"PBKDF2 xenc11:IterationCount {iterations} is above the limit {opts.maxPbkdf2Iterations}"
          let keyLength ← match lenEl.text? >>= positiveInteger? with
            | some n => pure n
            | none => refuse "PBKDF2 xenc11:KeyLength is not a positive integer"
          if !prfEl.kids.all wsOnly then refuse "xenc11:PRF parameters are not supported"
          let prfUri := (prfEl.attr? "Algorithm").getD ""
          let prf ← match prfOf? prfUri with
            | some a => pure a
            | none => refuse s!"the PBKDF2 PRF {prfUri} is not supported"
          pure { salt, iterations, keyLength, prf }
      | _ => refuse "xenc11:PBKDF2-params must hold Salt, IterationCount, KeyLength and PRF, in that order"
  | _ => refuse "xenc11:KeyDerivationMethod must hold one PBKDF2-params"

/-- A key derivation method of §5.4: Concat KDF (§5.4.1) or PBKDF2 (§5.4.2). -/
inductive Kdf where
  | concat (p : ConcatKdf.XmlEncParams)
  | pbkdf2 (p : Pbkdf2Params)

/-- The key derivation method named by `Algorithm`. -/
def kdfOf (opts : Opts) (kdm : El) : M Kdf :=
  let alg := (kdm.attr? "Algorithm").getD ""
  if alg == concatKdfAlg then Kdf.concat <$> concatKdfParams kdm
  else if alg == pbkdf2Alg then Kdf.pbkdf2 <$> pbkdf2Params opts kdm
  else refuse s!"the key derivation method {alg} is not supported (ConcatKDF or pbkdf2)"

/-- `keyLen` octets from the shared secret `z` (§5.4). `none` is a failure
after the structure check. -/
def Kdf.derive? (prims : Prims) (z : ByteArray) (keyLen : Nat) : Kdf → Option ByteArray
  | .concat p => ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash z keyLen p
  | .pbkdf2 p =>
      let k := prims.pbkdf2 p.prf z p.salt p.iterations p.keyLength
      if k.size == keyLen then some k else none

/-! ### Theorems relating §5.4.2 to RFC 8018, WebCrypto and §5.4.1

Says: the PBKDF2 of `nativePrims` is the pure-Lean RFC 8018 PBKDF2 of
`WebCrypto.pbkdf2` (the function WebCrypto's `deriveBits` with `PBKDF2` is
specified by here), given HACL*'s functional correctness as the hypotheses
`HashAgrees` and `HmacAgrees`; the Concat KDF path of XML Encryption 1.1
§5.4.1 is the one it was before §5.4.2 was added; a PBKDF2 key is used only
when it has the length the key is used for.
Does not say: that a document's PBKDF2 parameters are strong (the reader
bounds only the iteration count); anything about constant-time behaviour. -/

/-- XML Encryption 1.1 §5.4.2 PBKDF2 on the native primitives is RFC 8018
§5.2 PBKDF2 over the specification hash and HMAC. -/
theorem xmlenc11_pbkdf2_native_eq_rfc8018 (hh : WebHacl.HashAgrees) (hm : WebHacl.HmacAgrees)
    (a : WebHacl.HashAlg) (pw salt : ByteArray) (it len : Nat) :
    nativePrims.pbkdf2 a pw salt it len = WebCrypto.pbkdf2 a.pure pw salt it len :=
  WebHacl.pbkdf2_hacl_eq hh hm a pw salt it len

/-- Adding §5.4.2 leaves the §5.4.1 Concat KDF method as it was: a
`KeyDerivationMethod` with the ConcatKDF algorithm is read by
`concatKdfParams`. -/
theorem xmlenc11_kdfOf_concatKdf (opts : Opts) (kdm : El)
    (h : kdm.attr? "Algorithm" = some concatKdfAlg) :
    kdfOf opts kdm = Kdf.concat <$> concatKdfParams kdm := by
  simp [kdfOf, h]

/-- The Concat KDF derivation is `ConcatKdf.xmlEncDerive?` over SHA-256. -/
theorem xmlenc11_derive_concat (prims : Prims) (z : ByteArray) (n : Nat) (p : ConcatKdf.XmlEncParams) :
    (Kdf.concat p).derive? prims z n = ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash z n p := rfl

/-- A PBKDF2 key is given only with the length it is used for. -/
theorem xmlenc11_derive_pbkdf2_size (prims : Prims) (z : ByteArray) (n : Nat) (p : Pbkdf2Params)
    (k : ByteArray) (h : (Kdf.pbkdf2 p).derive? prims z n = some k) : k.size = n := by
  simp only [Kdf.derive?] at h
  split at h
  · rename_i e
    cases h
    simpa using e
  · cases h

/-- The PBKDF2 key of §5.4.2 is the one `WebCrypto` `deriveBits` (PBKDF2,
`8 * KeyLength` bits) gives for the same password, salt, iterations and hash,
on the native primitives, given HACL*'s functional correctness. -/
theorem xmlenc11_derive_pbkdf2_eq_webcrypto (hh : WebHacl.HashAgrees) (hm : WebHacl.HmacAgrees)
    (z : ByteArray) (p : Pbkdf2Params) :
    (Kdf.pbkdf2 p).derive? nativePrims z p.keyLength =
      (let k := WebCrypto.pbkdf2 p.prf.pure z p.salt p.iterations p.keyLength
       if k.size == p.keyLength then some k else none) := by
  simp only [Kdf.derive?, xmlenc11_pbkdf2_native_eq_rfc8018 hh hm]

/-- The key derivation method of `kdm` for a key of `keyLen` octets: a
PBKDF2 `KeyLength` must be `keyLen` (§5.4.2). -/
def kdfSized (opts : Opts) (kdm : El) (keyLen : Nat) : M Kdf := do
  let kdf ← kdfOf opts kdm
  match kdf with
  | .pbkdf2 p =>
      if p.keyLength != keyLen then
        refuse s!"PBKDF2 xenc11:KeyLength {p.keyLength} is not the {keyLen} octets the key is used for"
      pure kdf
  | .concat _ => pure kdf

/-! ## Derived keys (§5.4.3) -/

/-- `keyLen` octets derived from the master key `master` (§5.4.3): the
shared secret `Z` of Concat KDF, or the password of PBKDF2. `none` is a
failure after the structure check. -/
def deriveFromMaster (prims : Prims) (kdf : Kdf) (master : ByteArray) (keyLen : Nat) : Option ByteArray :=
  match kdf.derive? prims master keyLen with
  | some k => if k.size == keyLen then some k else none
  | none => none

/-- A key of `keyLen` octets from an `xenc11:DerivedKey` (§5.4.3). Children,
each at most once: `xenc11:KeyDerivationMethod` (required here),
`xenc:ReferenceList` and `xenc11:DerivedKeyName` (labels, not read), and
`xenc11:MasterKeyName`, which names the caller's symmetric master key. -/
def derivedKey (prims : Prims) (keys : Keys) (dk : El) (keyLen : Nat) (opts : Opts := {}) : M ByteArray := do
  if !dk.elementOnly then refuse "xenc11:DerivedKey has unexpected content"
  let mut kdm : Option El := none
  let mut master : Option El := none
  let mut refs := false
  let mut dname := false
  for c in dk.children do
    if c.is xenc11Ns "KeyDerivationMethod" && kdm.isNone then kdm := some c
    else if c.is xencNs "ReferenceList" && !refs then refs := true
    else if c.is xenc11Ns "DerivedKeyName" && !dname then dname := true
    else if c.is xenc11Ns "MasterKeyName" && master.isNone then master := some c
    else refuse s!"xenc11:DerivedKey has an unsupported or repeated child {c.lname}"
  let kdf ← match kdm with
    | some k => kdfSized opts k keyLen
    | none => refuse "xenc11:DerivedKey has no xenc11:KeyDerivationMethod"
  let name? ← match master with
    | some m => some <$> keyNameOf m
    | none => pure none
  let mk ← pick "symmetric master" name? keys.sym (·.kid)
  match deriveFromMaster prims kdf mk.k keyLen with
  | some k => pure k
  | none => .error .decryptFailed

/-! ### Theorems relating §5.4.3 to §5.4.1 and §5.4.2

Says: a `DerivedKey` uses the same Concat KDF (§5.4.1) and PBKDF2 (§5.4.2)
functions as key agreement, with the master key in the place of the shared
secret `Z`; a derived key is given only with the length it is used for; the
PBKDF2 derived key is RFC 8018 PBKDF2 as WebCrypto specifies it, given
HACL*'s functional correctness (`HashAgrees`, `HmacAgrees`).
Does not say: that a master key is secret or strong; that a key named by
`MasterKeyName` is the one the sender used. -/

/-- A derived key has the length it is used for. -/
theorem xmlenc11_deriveFromMaster_size (prims : Prims) (kdf : Kdf) (m : ByteArray) (n : Nat)
    (k : ByteArray) (h : deriveFromMaster prims kdf m n = some k) : k.size = n := by
  unfold deriveFromMaster at h
  split at h
  · split at h
    · rename_i e
      cases h
      simpa using e
    · cases h
  · cases h

/-- §5.4.3 with Concat KDF is §5.4.1 Concat KDF over SHA-256 with the master
key as `Z`, kept when it has the length asked for. -/
theorem xmlenc11_derivedKey_concat (prims : Prims) (p : ConcatKdf.XmlEncParams) (m : ByteArray) (n : Nat) :
    deriveFromMaster prims (.concat p) m n =
      (match ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash m n p with
       | some k => if k.size == n then some k else none
       | none => none) := rfl

/-- §5.4.3 with PBKDF2, on the native primitives, is RFC 8018 PBKDF2 (the
function of WebCrypto `deriveBits`) with the master key as the password. -/
theorem xmlenc11_derivedKey_pbkdf2_eq_rfc8018 (hh : WebHacl.HashAgrees) (hm : WebHacl.HmacAgrees)
    (p : Pbkdf2Params) (m : ByteArray) :
    deriveFromMaster nativePrims (.pbkdf2 p) m p.keyLength =
      (let k := WebCrypto.pbkdf2 p.prf.pure m p.salt p.iterations p.keyLength
       if k.size == p.keyLength then some k else none) := by
  simp only [deriveFromMaster, Kdf.derive?, xmlenc11_pbkdf2_native_eq_rfc8018 hh hm]
  split <;> simp_all

/-! ## Finite-field Diffie-Hellman (§5.6.1, §5.6.3) -/

/-- The 1024-bit Diffie-Hellman refusal. It names the opt-in of each
surface. -/
def dh1024Refusal : String :=
  "a Diffie-Hellman prime of fewer than 2048 bits is refused by default (NIST SP 800-131A Rev. 2 disallows it for key agreement). To accept it: the member dangerouslyAndRegrettablyAcceptDh1024: true of the xmlDecrypt options, or Opts.dh1024 := some (Risk.dangerouslyAccept .dh1024Agreement) in Lean. https://github.com/danbri/factoidal/issues/1227"

/-- The index of the first non-zero octet at or after `i`; a tail call per
octet. -/
def firstNonZero (b : ByteArray) : (fuel i : Nat) → Nat
  | 0, i => i
  | f + 1, i => if h : i < b.size then (if b[i] == 0 then firstNonZero b f (i + 1) else i) else i

/-- The octets of a number without leading zero octets (the `ds:CryptoBinary`
form, XML Signature 1.1 §4.0.1). -/
def stripZeros (b : ByteArray) : ByteArray := b.extract (firstNonZero b b.size 0) b.size

/-- `b`, as a number, right-aligned in `k` octets; `none` when it does not
fit. -/
def rightAlign (b : ByteArray) (k : Nat) : Option ByteArray :=
  let s := stripZeros b
  if s.size > k then none else some (⟨Array.replicate (k - s.size) 0⟩ ++ s)

/-- An originator's `xenc:DHKeyValue` (§5.6.1): the optional domain
parameters `(P, Q, Generator)` and the public value `Public`, each without
leading zero octets. `seed` and `pgenCounter` are accepted and not read. -/
structure DhPublic where
  domain : Option (ByteArray × ByteArray × ByteArray)
  y : ByteArray

/-- The originator key of `xmlenc11#dh-es`: one `xenc:DHKeyValue`, directly
or in `ds:KeyValue`. The children are the schema's sequence
`(P, Q, Generator)?, Public, (seed, pgenCounter)?`. -/
def dhOriginatorKey (o : El) : M DhPublic := do
  if !o.elementOnly then refuse "xenc:OriginatorKeyInfo has unexpected content"
  let cands := o.children.foldl (fun acc c =>
    if c.is dsNs "KeyValue" then acc ++ c.children else acc ++ [c]) []
  let k ← match cands with
    | [k] => pure k
    | _ => refuse "xenc:OriginatorKeyInfo must hold one public key"
  if !k.is xencNs "DHKeyValue" then
    refuse s!"dh-es needs an xenc:DHKeyValue originator key, not {k.lname}"
  if !k.elementOnly then refuse "xenc:DHKeyValue has unexpected content"
  let bin (e : El) : M ByteArray :=
    match e.text? >>= base64Decode? with
    | some b => pure (stripZeros b)
    | none => refuse s!"xenc:{e.lname} is not base64"
  let (domain, rest) ← match k.children with
    | p :: q :: g :: rest =>
        if p.is xencNs "P" then
          if !(q.is xencNs "Q" && g.is xencNs "Generator") then
            refuse "xenc:DHKeyValue: xenc:P must be followed by xenc:Q and xenc:Generator"
          pure (some (← bin p, ← bin q, ← bin g), rest)
        else pure (none, k.children)
    | cs => pure (none, cs)
  match rest with
  | [y] =>
      if !y.is xencNs "Public" then refuse "xenc:DHKeyValue has no xenc:Public"
      pure { domain, y := ← bin y }
  | [y, sd, pc] =>
      if !y.is xencNs "Public" then refuse "xenc:DHKeyValue has no xenc:Public"
      if !(sd.is xencNs "seed" && pc.is xencNs "pgenCounter") then
        refuse "xenc:DHKeyValue: xenc:Public may be followed only by xenc:seed and xenc:pgenCounter"
      pure { domain, y := ← bin y }
  | _ => refuse "xenc:DHKeyValue must be (P, Q, Generator)?, Public, (seed, pgenCounter)?"

/-- The prime size check: 128 to 512 octets (1024 to 4096 bits) in steps of
8 octets (the limb of `Dh.modExp`); fewer than 256 octets only with the
`dh1024` token. -/
def dhPrimeCheck (opts : Opts) (k : Nat) : M Unit :=
  if k % 8 != 0 || k < 128 || k > 512 then
    refuse s!"a Diffie-Hellman prime of {k * 8} bits is not supported (1024 to 4096 bits, a multiple of 64)"
  else if k < 256 && opts.dh1024.isNone then refuse dh1024Refusal
  else pure ()

/-- `y^x mod p` as `|p|` octets, kept only when it has that size and is not
0 or 1 (NIST SP 800-56A Rev. 3 §5.7.1.1: an output of 1 is an error). -/
def dhZ? (prims : Prims) (p x y : ByteArray) : Option ByteArray :=
  match prims.dhModExp p x y with
  | some z => if z.size == p.size && 1 < Dh.natOfBytes z then some z else none
  | none => none

/-- The shared secret `Z` of `xmlenc11#dh-es` (§5.6.3; RFC 2631 §2.1.1) for
the recipient key `key` and the originator's public value. Before the
private value is used: the prime size (`dhPrimeCheck`); the originator's
domain parameters, when given, must be the key's; the public value must be
in `[2, p - 2]` and in the subgroup of order `q` (`y^q mod p = 1`; RFC 2631
§2.1.5, NIST SP 800-56A Rev. 3 §5.6.2.3.1). Each of these is a refusal with
a message: none depends on the private value. -/
def dhSharedSecret (prims : Prims) (opts : Opts) (key : DhKey) (pub : DhPublic) : M ByteArray := do
  let p := stripZeros key.p
  let q := stripZeros key.q
  let k := p.size
  dhPrimeCheck opts k
  if q.size == 0 then refuse "the Diffie-Hellman key has no subgroup order q"
  match pub.domain with
  | some (pp, qq, gg) =>
      if pp != p || qq != q || gg != stripZeros key.g then
        refuse "the originator's Diffie-Hellman domain parameters are not the recipient key's"
  | none => pure ()
  let yN := Dh.natOfBytes pub.y
  if yN < 2 || yN + 2 > Dh.natOfBytes p then
    refuse "the originator's Diffie-Hellman public value is not in [2, p - 2]"
  let y ← match rightAlign pub.y k with
    | some y => pure y
    | none => refuse "the originator's Diffie-Hellman public value is longer than p"
  match prims.dhModExp p q y with
  | some r =>
      if Dh.natOfBytes r != 1 then
        refuse "the originator's Diffie-Hellman public value is not in the subgroup of order q"
  | none => refuse "the Diffie-Hellman subgroup check was refused"
  match dhZ? prims p key.x y with
  | some z => pure z
  | none => .error .decryptFailed

/-! ### Theorems relating §5.6.3 to RFC 2631 and §5.4

Says: on the native primitives, the shared secret of `dh-es` is `y^x mod p`
as `|p|` octets, given HACL*'s functional correctness (`ModExpAgrees`); it
has the size of `p`; a prime of fewer than 2048 bits is refused unless the
caller holds the `dh1024Agreement` token; the key derivation after it is
the same `Kdf.derive?` as for ECDH-ES (Concat KDF of §5.4.1 or PBKDF2 of
§5.4.2).
Does not say: that a group is strong; anything about constant-time
behaviour of the Lean code around HACL*. -/

/-- The `dh-es` shared secret has the size of `p` (RFC 2631 §2.1.2: "the
same length as p"). -/
theorem xmlenc11_dhZ_size (prims : Prims) (p x y z : ByteArray) (h : dhZ? prims p x y = some z) :
    z.size = p.size := by
  unfold dhZ? at h
  split at h
  · split at h
    · rename_i e
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at e
      exact e.1
    · cases h
  · cases h

/-- On the native primitives, the `dh-es` shared secret is RFC 2631 `ZZ =
y^x mod p` as `|p|` octets, given HACL*'s functional correctness. -/
theorem xmlenc11_dhZ_eq_rfc2631 (hm : Dh.ModExpAgrees) (p x y z : ByteArray)
    (h : dhZ? nativePrims p x y = some z) : z = Dh.modExpSpec p x y := by
  unfold dhZ? at h
  cases e : nativePrims.dhModExp p x y with
  | none => rw [e] at h; cases h
  | some r =>
    rw [e] at h
    simp only at h
    split at h
    · cases h
      exact hm p x y _ e
    · cases h

/-- A prime of 1024 bits is refused without the `dh1024Agreement` token. -/
theorem xmlenc11_dh1024_needs_token (opts : Opts) (h : opts.dh1024 = none) :
    dhPrimeCheck opts 128 = refuse dh1024Refusal := by
  simp [dhPrimeCheck, h]

/-- With the token, a 1024-bit prime passes the size check. -/
theorem xmlenc11_dh1024_with_token (opts : Opts) (t : Risk.Accepted .dh1024Agreement)
    (h : opts.dh1024 = some t) : dhPrimeCheck opts 128 = pure () := by
  simp [dhPrimeCheck, h]

/-- Primes of 2048 to 4096 bits pass the size check with no token. -/
theorem xmlenc11_dh_2048_no_token (opts : Opts) (k : Nat) (h1 : 256 ≤ k) (h2 : k ≤ 512) (h3 : k % 8 = 0) :
    dhPrimeCheck opts k = pure () := by
  have a : ¬ k < 128 := by omega
  have b : ¬ k > 512 := by omega
  have c : ¬ k < 256 := by omega
  simp [dhPrimeCheck, h3, a, b, c]

/-- The key from a key agreement's shared secret (§5.4): the same function
for ECDH-ES, X25519 and `dh-es`. -/
def agreeDerive (prims : Prims) (kdf : Kdf) (z? : Option ByteArray) (keyLen : Nat) : M ByteArray :=
  match z? >>= fun z => kdf.derive? prims z keyLen with
  | some k => pure k
  | none => .error .decryptFailed

/-- `dh-es` with Concat KDF is §5.4.1 Concat KDF over SHA-256 with the DH
shared secret as `Z`, as for ECDH-ES. -/
theorem xmlenc11_dhes_concat (prims : Prims) (p : ConcatKdf.XmlEncParams) (z : ByteArray) (n : Nat) :
    agreeDerive prims (.concat p) (some z) n =
      (match ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash z n p with
       | some k => pure k
       | none => .error .decryptFailed) := rfl

/-- A key of `keyLen` octets from an `xenc:AgreementMethod`. -/
def agreeKey (prims : Prims) (keys : Keys) (a : El) (keyLen : Nat) (opts : Opts := {}) : M ByteArray := do
  let alg := (a.attr? "Algorithm").getD ""
  if alg != ecdhEs && alg != x25519Agreement && alg != dhEs then
    refuse s!"the key agreement algorithm {alg} is not supported"
  if !a.elementOnly then refuse "xenc:AgreementMethod has unexpected content"
  let mut kdm : Option El := none
  let mut orig : Option El := none
  let mut recip : Option El := none
  for c in a.children do
    if c.is xencNs "KA-Nonce" then refuse "xenc:KA-Nonce is not supported"
    else if c.is xenc11Ns "KeyDerivationMethod" && kdm.isNone then kdm := some c
    else if c.is xencNs "OriginatorKeyInfo" && orig.isNone then orig := some c
    else if c.is xencNs "RecipientKeyInfo" && recip.isNone then recip := some c
    else refuse s!"xenc:AgreementMethod has an unsupported child {c.lname}"
  let kdf ← match kdm with
    | some k => kdfSized opts k keyLen
    | none => refuse "xenc:AgreementMethod has no key derivation method"
  let o ← match orig with
    | some o => pure o
    | none => refuse "xenc:AgreementMethod has no originator key"
  let name? ← match recip with
    | none => pure none
    | some r => do
        if !r.elementOnly then refuse "xenc:RecipientKeyInfo has unexpected content"
        match r.children.filter (·.is dsNs "KeyName") with
        | [] => pure none
        | [k] => pure (some (← keyNameOf k))
        | _ => refuse "xenc:RecipientKeyInfo has more than one ds:KeyName"
  if alg == dhEs then
    let pub ← dhOriginatorKey o
    let key ← pick "Diffie-Hellman" name? keys.dh (·.kid)
    let z ← dhSharedSecret prims opts key pub
    agreeDerive prims kdf (some z) keyLen
  else
    let (curve, pub) ← originatorKey o
    if alg == x25519Agreement && curve != .x25519 then
      refuse "xmldsig-more#x25519 needs an X25519 originator key"
    let key ← pick (if curve == .p256 then "P-256" else "X25519") name?
      (keys.ec.filter (·.curve == curve)) (·.kid)
    let z? := match curve with
      | .p256 => prims.p256Ecdh pub key.d
      | .x25519 => prims.x25519 key.d pub
    agreeDerive prims kdf z? keyLen

/-! ## Content keys -/

/-- What `ds:KeyInfo` of an `EncryptedKey` says about the key encryption key. -/
inductive KekRef where
  | name (n : String)
  | agreement (a : El)
  | derived (d : El)
  | unnamed

def kekRefOf (ki : Option El) : M KekRef := do
  match ki with
  | none => pure .unnamed
  | some k =>
      if !k.elementOnly then refuse "ds:KeyInfo has unexpected content"
      let mut out : KekRef := .unnamed
      let mut seen := false
      for c in k.children do
        if c.is dsNs "X509Data" || c.is dsNs "KeyValue" then pure ()
        else if c.is dsNs "KeyName" || c.is xencNs "AgreementMethod" || c.is xenc11Ns "DerivedKey" then
          if seen then refuse "ds:KeyInfo of xenc:EncryptedKey names more than one key"
          seen := true
          if c.is dsNs "KeyName" then
            let nm ← keyNameOf c
            out := .name nm
          else if c.is xencNs "AgreementMethod" then out := .agreement c
          else out := .derived c
        else refuse s!"ds:KeyInfo of xenc:EncryptedKey holds {c.lname}, which is not supported"
      pure out

/-- The content key in an `EncryptedKey`. -/
def unwrapKey (cipher : Cipher) (prims : Prims) (keys : Keys) (ek : El) (keyLen : Nat) (opts : Opts := {}) :
    M ByteArray := do
  let p ← encParts ek fun c => c.is xencNs "ReferenceList" || c.is xencNs "CarriedKeyName"
  let alg ← keyAlgOf p.method
  let kr ← kekRefOf p.keyInfo
  match alg with
  | .oaep dig mgf label =>
      let name? ← match kr with
        | .name n => pure (some n)
        | .unnamed => pure none
        | .agreement _ => refuse "RSA-OAEP key transport with a key agreement is not supported"
        | .derived _ => refuse "RSA-OAEP key transport with a derived key is not supported"
      let k ← pick "RSA" name? keys.rsa (·.kid)
      match RsaOaep.oaepDecryptChecked (prims.oaepProvider dig) (prims.oaepProvider mgf)
          prims.rsaPrivate k.n k.d p.cipherValue label with
      | some cek => if cek.size == keyLen then pure cek else .error .decryptFailed
      | none => .error .decryptFailed
  | .kw len =>
      let kek ← match kr with
        | .name n => do
            let s ← pick "symmetric" (some n) keys.sym (·.kid)
            pure s.k
        | .unnamed => do
            let s ← pick "symmetric" none (keys.sym.filter (·.k.size == len)) (·.kid)
            pure s.k
        | .agreement a => agreeKey prims keys a len opts
        | .derived dk => derivedKey prims keys dk len opts
      if kek.size != len then refuse "the key encryption key does not have the size of the key wrap algorithm"
      let cek ← ccall cipher { op := .kwUnwrap, key := kek, data := p.cipherValue }
      if cek.size == keyLen then pure cek else .error .decryptFailed

/-! ## Finding an `EncryptedKey` by `Id` -/

mutual

/-- The `EncryptedKey` elements whose `Id` is `id` below a node, prepended
to `acc`. -/
def findKeysNode (id : String) (sc : Scope) (acc : List El) : Node → List El
  | n@(.element _ attrs kids) =>
      let acc := match elOf? sc n with
        | some e => if isEncKey e && e.attr? "Id" == some id then e :: acc else acc
        | none => acc
      findKeysNodes id (extendScope sc (nsDecls attrs)) acc kids
  | _ => acc

/-- `findKeysNode` over siblings; a tail call per sibling. -/
def findKeysNodes (id : String) (sc : Scope) (acc : List El) : List Node → List El
  | [] => acc
  | n :: ns => findKeysNodes id sc (findKeysNode id sc acc n) ns

end

/-! ## Decryption -/

/-- What decryption needs besides the element. -/
structure Ctx where
  cipher : Cipher
  prims : Prims
  keys : Keys
  opts : Opts
  /-- The document element, for `ds:RetrievalMethod`. -/
  root : Node

/-- The content key of an `EncryptedData`. `fallback`: the `EncryptedKey`
to use when `ds:KeyInfo` is absent. -/
def contentKey (ctx : Ctx) (ki : Option El) (fallback : Option El) (keyLen : Nat) : M ByteArray := do
  match ki with
  | none =>
      match fallback with
      | some ek => unwrapKey ctx.cipher ctx.prims ctx.keys ek keyLen ctx.opts
      | none => refuse "xenc:EncryptedData has no ds:KeyInfo and no key"
  | some k =>
      if !k.elementOnly then refuse "ds:KeyInfo has unexpected content"
      match k.children with
      | [c] =>
          if isEncKey c then unwrapKey ctx.cipher ctx.prims ctx.keys c keyLen ctx.opts
          else if c.is xencNs "AgreementMethod" then agreeKey ctx.prims ctx.keys c keyLen ctx.opts
          else if c.is xenc11Ns "DerivedKey" then derivedKey ctx.prims ctx.keys c keyLen ctx.opts
          else if c.is dsNs "KeyName" then do
            let nm ← keyNameOf c
            let s ← pick "symmetric" (some nm) ctx.keys.sym (·.kid)
            if s.k.size == keyLen then pure s.k
            else refuse "the named content key does not have the size of the data algorithm"
          else if c.is dsNs "RetrievalMethod" then do
            if c.attr? "Type" != some typeEncryptedKey then
              refuse "ds:RetrievalMethod must have the Type xenc:EncryptedKey"
            if !(c.elementOnly && c.children.isEmpty) then
              refuse "ds:RetrievalMethod transforms are not supported"
            let uri := (c.attr? "URI").getD ""
            if !uri.startsWith "#" || uri.length < 2 then
              refuse "ds:RetrievalMethod must refer to an element of this document (#id)"
            match findKeysNode (uri.drop 1).toString rootScope [] ctx.root with
            | [ek] => unwrapKey ctx.cipher ctx.prims ctx.keys ek keyLen ctx.opts
            | [] => refuse s!"no xenc:EncryptedKey has the Id {(uri.drop 1).toString}"
            | _ => refuse s!"more than one xenc:EncryptedKey has the Id {(uri.drop 1).toString}"
          else refuse s!"ds:KeyInfo of xenc:EncryptedData holds {c.lname}, which is not supported"
      | _ => refuse "ds:KeyInfo of xenc:EncryptedData must hold one key"

/-- ISO 10126 / XML Encryption §5.2 padding removed: the last octet is the
count. -/
def unpad (b : ByteArray) : Option ByteArray :=
  if b.size == 0 then none
  else
    let n := (b.get! (b.size - 1)).toNat
    if n == 0 || n > 16 || n > b.size then none else some (b.extract 0 (b.size - n))

/-- The plaintext octets of `cv` under `cek`. -/
def decryptContent (cipher : Cipher) (alg : DataAlg) (cek cv : ByteArray) : M ByteArray :=
  match alg with
  | .gcm _ =>
      if cv.size < 28 then .error .decryptFailed
      else ccall cipher { op := .gcmDecrypt, key := cek, iv := cv.extract 0 12, data := cv.extract 12 cv.size }
  | .cbc _ =>
      if cv.size < 32 || cv.size % 16 != 0 then .error .decryptFailed
      else
        match ccall cipher { op := .cbcEncrypt, key := cek, iv := cv.extract (cv.size - 16) cv.size,
                             data := ByteArray.empty } with
        | .error f => .error f
        | .ok padBlock =>
            if padBlock.size != 16 then .error .decryptFailed
            else
              match ccall cipher { op := .cbcDecrypt, key := cek, iv := cv.extract 0 16,
                                   data := cv.extract 16 cv.size ++ padBlock } with
              | .error f => .error f
              | .ok p => match unpad p with
                | some q => .ok q
                | none => .error .decryptFailed

/-- `xmlns` attributes for the bindings of `sc` (the `xml` prefix left out). -/
def scopeDecls (sc : Scope) : String :=
  sc.foldl (fun acc (p, u) =>
    if p == "xml" then acc
    else if p == "" then acc ++ " xmlns=\"" ++ escAttr u ++ "\""
    else acc ++ " xmlns:" ++ p ++ "=\"" ++ escAttr u ++ "\"") ""

/-- The plaintext parsed in the context of the bindings `sc` (§4.4 step
3.4): the nodes, or the decryption failure. `depth`: the nesting of the
parent element. -/
def parseFragment (opts : Opts) (sc : Scope) (depth : Nat) (pt : ByteArray) : M (List Node) :=
  match String.fromUTF8? pt with
  | none => .error .decryptFailed
  | some text =>
      if !nestingWithin opts.maxDepth text.toList depth then .error .decryptFailed
      else
        match parseXML ("<w" ++ scopeDecls sc ++ ">" ++ text ++ "</w>") with
        | .error _ => .error .decryptFailed
        | .ok d =>
            match d.root with
            | .element _ _ kids =>
                if d.prolog.isEmpty && d.epilog.isEmpty && d.doctype.isNone
                    && countNodesAcc isEncData sc kids 0 == 0
                then .ok kids else .error .decryptFailed
            | _ => .error .decryptFailed

/-- The plaintext octets of an `EncryptedData` read as `p` (§4.4 steps 1
to 3): the algorithm, the content key, the decryption. -/
def partsOctets (ctx : Ctx) (fallback : Option El) (p : EncParts) : M ByteArray := do
  let alg ← dataAlgOf ctx.opts p.method
  let cek ← contentKey ctx p.keyInfo fallback alg.keyLen
  decryptContent ctx.cipher alg cek p.cipherValue

/-- The nodes that replace one `EncryptedData` whose parent has bindings
`e.parent` and nesting `depth`. -/
def decryptData (ctx : Ctx) (fallback : Option El) (e : El) (depth : Nat) : M (List Node) := do
  let p ← encParts e fun _ => false
  let isElement ← match e.attr? "Type" with
    | some t =>
        if t == typeElement then pure true
        else if t == typeContent then pure false
        else refuse s!"the EncryptedData Type {t} is not supported"
    | none => refuse ("xenc:EncryptedData has no Type (Element or Content): its plaintext is octets, " ++
        "which the octets form of decryption gives")
  let pt ← partsOctets ctx fallback p
  let nodes ← parseFragment ctx.opts e.parent depth pt
  if isElement then
    match nodes with
    | [n@(.element ..)] => pure [n]
    | _ => .error .decryptFailed
  else pure nodes

mutual

/-- Decrypt below one node: the nodes that replace it, and the count of
`EncryptedData` decrypted so far. `depth`: the nesting of its parent. -/
def walkNode (ctx : Ctx) (sc : Scope) (depth : Nat) (count : Nat) : Node → M (List Node × Nat)
  | n@(.element t attrs kids) =>
      match elOf? sc n with
      | none => .error (.refused "an element or attribute prefix is not bound")
      | some e =>
          if isEncData e then
            if count + 1 > ctx.opts.maxEncrypted then
              .error (.refused s!"more than {ctx.opts.maxEncrypted} xenc:EncryptedData elements")
            else
              match decryptData ctx none e depth with
              | .ok ns => .ok (ns, count + 1)
              | .error f => .error f
          else
            match walkNodes ctx (extendScope sc (nsDecls attrs)) (depth + 1) count kids [] with
            | .ok (kids', c) => .ok ([.element t attrs kids'], c)
            | .error f => .error f
  | n => .ok ([n], count)

/-- `walkNode` over siblings, the output reversed in `acc`; a tail call per
sibling. -/
def walkNodes (ctx : Ctx) (sc : Scope) (depth : Nat) (count : Nat) :
    List Node → List Node → M (List Node × Nat)
  | [], acc => .ok (acc.reverse, count)
  | n :: ns, acc =>
      match walkNode ctx sc depth count n with
      | .ok (out, c) => walkNodes ctx sc depth c ns (out.reverseAux acc)
      | .error f => .error f

end

/-- Decrypt every `EncryptedData` of a document (§4.4). -/
def decrypt (cipher : Cipher) (prims : Prims) (keys : Keys) (opts : Opts) (d : Document) : M Document :=
  if d.doctype.isSome then refuse "a document type declaration is not allowed"
  else
    let ctx : Ctx := { cipher, prims, keys, opts, root := d.root }
    match walkNode ctx rootScope 0 0 d.root with
    | .ok ([r@(.element ..)], _) => .ok { d with root := r }
    | .ok _ => .error .decryptFailed
    | .error f => .error f

/-- The plaintext octets of a document whose element is an `EncryptedData`,
with any or no `Type` (§4.4 step 3: the octets go to the application). -/
def decryptOctets (cipher : Cipher) (prims : Prims) (keys : Keys) (opts : Opts) (d : Document) :
    M ByteArray :=
  if d.doctype.isSome then refuse "a document type declaration is not allowed"
  else match elOf? rootScope d.root with
    | none => refuse "an element or attribute prefix is not bound"
    | some e =>
        if !isEncData e then refuse "the document element must be xenc:EncryptedData for its octets"
        else do
          let p ← encParts e fun _ => false
          partsOctets { cipher, prims, keys, opts, root := d.root } none p

/-- An element of SAML's `EncryptedElementType` (SAML Core §2.2.4):
`xenc:EncryptedData`, then `xenc:EncryptedKey` elements. The one decrypted
element; the `EncryptedKey` sibling is used when it is the only one and the
`EncryptedData` has no `ds:KeyInfo`. `root`: the document element;
`depth`: the nesting of `w`. -/
def decryptWrapped (cipher : Cipher) (prims : Prims) (keys : Keys) (opts : Opts) (root : Node)
    (w : El) (depth : Nat) : M Node := do
  if !w.elementOnly then refuse s!"{w.lname} has unexpected content"
  match w.children with
  | [] => refuse s!"{w.lname} holds no xenc:EncryptedData"
  | ed :: eks =>
      if !isEncData ed then refuse s!"{w.lname} must begin with xenc:EncryptedData"
      if !eks.all isEncKey then refuse s!"{w.lname} holds other than xenc:EncryptedKey after the data"
      let fallback := match eks with
        | [k] => some k
        | _ => none
      let ctx : Ctx := { cipher, prims, keys, opts, root }
      match ← decryptData ctx fallback ed depth with
      | [n@(.element ..)] => pure n
      | _ => .error .decryptFailed

/-- The element with an `xmlns` attribute for each binding of `sc` it does
not declare itself (the `xml` prefix left out): a decrypted element made a
document element keeps the bindings it was parsed with. -/
def withScope (sc : Scope) : Node → Node
  | .element t attrs kids =>
      let own := attrs.map (·.name)
      let extra := sc.filterMap fun (p, u) =>
        let n := if p == "" then "xmlns" else "xmlns:" ++ p
        if p == "xml" || own.contains n then none else some ({ name := n, value := u } : Attribute)
      .element t (attrs ++ extra) kids
  | n => n

/-! ## Encryption -/

/-- The recipient of the content key. -/
inductive Recipient where
  /-- RSA-OAEP: `sha256 = false` is `rsa-oaep-mgf1p` (SHA-1); `true` is
  `xmlenc11#rsa-oaep` with SHA-256 and `mgf1sha256`. -/
  | rsa (kid : Option String) (n e : ByteArray) (sha256 : Bool)
  /-- ECDH-ES (P-256) or xmldsig-more#x25519, ConcatKDF with SHA-256, then
  AES Key Wrap with a key of `kwLen` octets. `pub`: P-256 `x || y`, or the
  X25519 u-coordinate. -/
  | agree (kid : Option String) (curve : Curve) (pub : ByteArray) (kwLen : Nat)
  /-- AES Key Wrap under a symmetric key named `kid`. -/
  | kek (kid : Option String) (k : ByteArray)
  /-- AES Key Wrap (key of `kwLen` octets) under a key derived from the
  symmetric master key `master` (§5.4.3), named by `kid` in
  `xenc11:MasterKeyName`. -/
  | derived (kid : Option String) (master : ByteArray) (kwLen : Nat)

/-- The key derivation method the writer puts in an `xenc:AgreementMethod`
or an `xenc11:DerivedKey` (§5.4). -/
inductive WriteKdf where
  /-- Concat KDF over SHA-256 (§5.4.1); `AlgorithmID` is the key wrap URI. -/
  | concat
  /-- PBKDF2 (§5.4.2): HMAC over `prf`, `iterations` rounds, and a
  `xenc11:Specified` salt of `saltLen` random octets. -/
  | pbkdf2 (prf : WebHacl.HashAlg) (iterations : Nat) (saltLen : Nat := 16)

/-- How many random octets the method takes (the PBKDF2 salt). -/
def WriteKdf.randLen : WriteKdf → Nat
  | .concat => 0
  | .pbkdf2 _ _ s => s

structure EncryptSpec where
  /-- AES-GCM content key length: 16 or 32. -/
  keyLen : Nat := 16
  recipient : Recipient
  /-- `Type` Content (the element's children) instead of Element. -/
  content : Bool := false
  /-- The key derivation method of an `agree` or `derived` recipient. -/
  kdf : WriteKdf := .concat

def mkAttrs (as : List (String × String)) : List Attribute := as.map fun (n, v) => { name := n, value := v }

def mkEl (t : String) (as : List (String × String)) (kids : List Node) : Node := .element t (mkAttrs as) kids

def cipherDataNode (cv : ByteArray) : Node :=
  mkEl "xenc:CipherData" [] [mkEl "xenc:CipherValue" [] [.text (base64 cv)]]

def keyNameNodes (kid : Option String) : List Node :=
  match kid with
  | some n => [mkEl "ds:KeyName" [] [.text n]]
  | none => []

/-- How many random octets an encryption takes after the content key and
the IV. -/
def Recipient.randLen : Recipient → Nat
  | .rsa _ _ _ sha256 => if sha256 then 32 else 20
  | .agree .. => 32
  | .kek .. => 0
  | .derived .. => 0

/-- Random octets after the content key and the IV: the recipient's, then
the PBKDF2 salt when the recipient derives a key. -/
def EncryptSpec.restLen (spec : EncryptSpec) : Nat :=
  match spec.recipient with
  | .agree .. | .derived .. => spec.recipient.randLen + spec.kdf.randLen
  | _ => spec.recipient.randLen

def kwUri (len : Nat) : String := if len == 16 then kwAes128 else kwAes256

/-- `00 || utf8(s)` as hexBinary: an octet string with no padding bits. -/
def paddedHex (s : String) : String := "00" ++ hexOf s.toUTF8

/-- The `xenc11:PRF` URI of an HMAC hash (the inverse of `prfOf?`). -/
def prfUri : WebHacl.HashAlg → String
  | .sha1 => hmacSha1Prf
  | .sha256 => hmacSha256Prf
  | .sha384 => hmacSha384Prf
  | .sha512 => hmacSha512Prf

/-- The method the reader gets back from what the writer writes, for a key
of `kwLen` octets and the salt `salt`. -/
def WriteKdf.toKdf (kwLen : Nat) (salt : ByteArray) : WriteKdf → Kdf
  | .concat => .concat { algorithmId := hexBytes? (paddedHex (kwUri kwLen)) }
  | .pbkdf2 prf it _ => .pbkdf2 { salt, iterations := it, keyLength := kwLen, prf }

/-- The writer's limits: PBKDF2 needs 1 to `maxIt` iterations (the reader's
default limit is 1,000,000) and a salt of 8 to 64 octets (RFC 8018 §4.1
asks for at least eight). -/
def WriteKdf.check (maxIt : Nat := 1000000) : WriteKdf → M Unit
  | .concat => pure ()
  | .pbkdf2 _ it s => do
      if it < 1 || it > maxIt then refuse s!"PBKDF2 iterations must be 1 to {maxIt}"
      if s < 8 || s > 64 then refuse "the PBKDF2 salt must be 8 to 64 octets"

/-- The `xenc11:KeyDerivationMethod` element for a key of `kwLen` octets. -/
def kdfNode (kwLen : Nat) (salt : ByteArray) : WriteKdf → Node
  | .concat =>
      mkEl "xenc11:KeyDerivationMethod" [("xmlns:xenc11", xenc11Ns), ("Algorithm", concatKdfAlg)]
        [mkEl "xenc11:ConcatKDFParams"
          -- PartyUInfo and PartyVInfo absent (empty): Apache Santuario 4.0.4
          -- refuses the one-octet value "00" ("ConcatKDF parameter is to short").
          [("AlgorithmID", paddedHex (kwUri kwLen))]
          [mkEl "ds:DigestMethod" [("Algorithm", sha256Digest)] []]]
  | .pbkdf2 prf it _ =>
      mkEl "xenc11:KeyDerivationMethod" [("xmlns:xenc11", xenc11Ns), ("Algorithm", pbkdf2Alg)]
        [mkEl "xenc11:PBKDF2-params" []
          [mkEl "xenc11:Salt" [] [mkEl "xenc11:Specified" [] [.text (base64 salt)]],
           mkEl "xenc11:IterationCount" [] [.text (toString it)],
           mkEl "xenc11:KeyLength" [] [.text (toString kwLen)],
           mkEl "xenc11:PRF" [("Algorithm", prfUri prf)] []]]

/-! ### Theorems relating the writer's §5.4 methods to the reader's

Says: the PRF URI that the writer writes is read back as the same hash; the
Concat KDF key that the writer uses is the §5.4.1 key with `AlgorithmID` the
key wrap URI (as before PBKDF2 was added to the writer); the PBKDF2 key that
the writer uses is RFC 8018 PBKDF2 as WebCrypto `deriveBits` specifies it,
on the native primitives, given HACL*'s functional correctness.
Does not say: that the reader parses every document the writer writes (the
round-trip tests check that); that the chosen iteration count is strong. -/

/-- `prfOf?` reads back every PRF URI the writer writes. -/
theorem xmlenc11_prfOf_prfUri (a : WebHacl.HashAlg) : prfOf? (prfUri a) = some a := by
  cases a <;> decide

/-- The writer's Concat KDF is §5.4.1 over SHA-256 with `AlgorithmID` the
key wrap URI. -/
theorem xmlenc11_write_concat (prims : Prims) (z salt : ByteArray) (n : Nat) :
    (WriteKdf.concat.toKdf n salt).derive? prims z n =
      ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash z n { algorithmId := hexBytes? (paddedHex (kwUri n)) } :=
  rfl

/-- The writer's PBKDF2 key on the native primitives is RFC 8018 PBKDF2 (the
function of WebCrypto `deriveBits`) over the same secret, salt, iterations
and hash. -/
theorem xmlenc11_write_pbkdf2_eq_rfc8018 (hh : WebHacl.HashAgrees) (hm : WebHacl.HmacAgrees)
    (prf : WebHacl.HashAlg) (it s n : Nat) (z salt : ByteArray) :
    ((WriteKdf.pbkdf2 prf it s).toKdf n salt).derive? nativePrims z n =
      (let k := WebCrypto.pbkdf2 prf.pure z salt it n
       if k.size == n then some k else none) :=
  xmlenc11_derive_pbkdf2_eq_webcrypto hh hm z { salt, iterations := it, keyLength := n, prf }

/-- A `DerivedKey` key encryption key that the writer uses is the one the
reader's §5.4.3 derivation gives from the same master key, so it has the
length of the key wrap key. -/
theorem xmlenc11_write_derived_size (prims : Prims) (w : WriteKdf) (salt m k : ByteArray) (n : Nat)
    (h : deriveFromMaster prims (w.toKdf n salt) m n = some k) : k.size = n :=
  xmlenc11_deriveFromMaster_size prims _ m n k h

/-- The `xenc:EncryptedKey` holding `cek` for the recipient. `rand`: the
recipient's random octets, then the PBKDF2 salt. -/
def encryptedKeyNode (cipher : Cipher) (prims : Prims) (r : Recipient) (cek rand : ByteArray)
    (kdf : WriteKdf := .concat) : M Node := do
  match r with
  | .rsa kid n e sha256 =>
      let digest := prims.oaepProvider (if sha256 then .sha256 else .sha1)
      let ct ← match RsaOaep.oaepEncryptChecked digest digest prims.rsaPublic n e cek ByteArray.empty rand with
        | some c => pure c
        | none => refuse "RSA-OAEP encryption was refused (the key must be 2048, 3072 or 4096 bits)"
      let method :=
        if sha256 then
          mkEl "xenc:EncryptionMethod" [("Algorithm", rsaOaep11)]
            [mkEl "ds:DigestMethod" [("Algorithm", sha256Digest)] [],
             mkEl "xenc11:MGF" [("xmlns:xenc11", xenc11Ns), ("Algorithm", mgf1Sha256)] []]
        else mkEl "xenc:EncryptionMethod" [("Algorithm", rsaOaepMgf1p)] []
      pure (mkEl "xenc:EncryptedKey" [] ([method] ++
        (if kid.isSome then [mkEl "ds:KeyInfo" [] (keyNameNodes kid)] else []) ++ [cipherDataNode ct]))
  | .kek kid k =>
      let wrapped ← ccallEnc cipher { op := .kwWrap, key := k, data := cek }
      pure (mkEl "xenc:EncryptedKey" []
        ([mkEl "xenc:EncryptionMethod" [("Algorithm", kwUri k.size)] []] ++
         (if kid.isSome then [mkEl "ds:KeyInfo" [] (keyNameNodes kid)] else []) ++ [cipherDataNode wrapped]))
  | .derived kid master kwLen =>
      if kwLen != 16 && kwLen != 32 then refuse "the key wrap key must be 16 or 32 octets"
      kdf.check
      let salt := rand.extract 0 kdf.randLen
      let kek ← (deriveFromMaster prims (kdf.toKdf kwLen salt) master kwLen).elim
        (refuse "the key derivation was refused") pure
      let wrapped ← ccallEnc cipher { op := .kwWrap, key := kek, data := cek }
      let names := match kid with
        | some n => [mkEl "xenc11:MasterKeyName" [] [.text n]]
        | none => []
      pure (mkEl "xenc:EncryptedKey" []
        [mkEl "xenc:EncryptionMethod" [("Algorithm", kwUri kwLen)] [],
         mkEl "ds:KeyInfo" []
           [mkEl "xenc11:DerivedKey" [("xmlns:xenc11", xenc11Ns)] ([kdfNode kwLen salt kdf] ++ names)],
         cipherDataNode wrapped])
  | .agree kid curve pub kwLen =>
      if kwLen != 16 && kwLen != 32 then refuse "the key wrap key must be 16 or 32 octets"
      kdf.check
      let eph := rand.extract 0 32
      let salt := rand.extract 32 (32 + kdf.randLen)
      let (ephPub?, z?) := match curve with
        | .p256 => (prims.p256Public eph, prims.p256Ecdh pub eph)
        | .x25519 => (prims.x25519Public eph, prims.x25519 eph pub)
      let ephPub ← ephPub?.elim (refuse "the ephemeral key was refused") pure
      let z ← z?.elim (refuse "the recipient's public key was refused") pure
      let kek ← ((kdf.toKdf kwLen salt).derive? prims z kwLen).elim
        (refuse "the key derivation was refused") pure
      let wrapped ← ccallEnc cipher { op := .kwWrap, key := kek, data := cek }
      let origKey := match curve with
        | .p256 =>
            mkEl "ds:KeyValue" [] [mkEl "dsig11:ECKeyValue" [("xmlns:dsig11", dsig11Ns)]
              [mkEl "dsig11:NamedCurve" [("URI", p256Oid)] [],
               mkEl "dsig11:PublicKey" [] [.text (base64 (ByteArray.mk #[4] ++ ephPub))]]]
        | .x25519 =>
            mkEl "dsig11:DEREncodedKeyValue" [("xmlns:dsig11", dsig11Ns)]
              [.text (base64 (x25519SpkiPrefix ++ ephPub))]
      let agreement := mkEl "xenc:AgreementMethod"
        [("Algorithm", if curve == .p256 then ecdhEs else x25519Agreement)]
        [kdfNode kwLen salt kdf,
         mkEl "xenc:OriginatorKeyInfo" [] [origKey],
         mkEl "xenc:RecipientKeyInfo" [] (keyNameNodes kid)]
      pure (mkEl "xenc:EncryptedKey" []
        [mkEl "xenc:EncryptionMethod" [("Algorithm", kwUri kwLen)] [],
         mkEl "ds:KeyInfo" [] [agreement], cipherDataNode wrapped])

/-- An `xenc:EncryptedData` (AES-GCM) holding `plaintext`, `Type`
Element or Content. `rand`: the content key, the 12-octet IV, then
`Recipient.randLen` octets. -/
def encryptOctets (cipher : Cipher) (prims : Prims) (spec : EncryptSpec) (rand plaintext : ByteArray) :
    M Node := do
  if spec.keyLen != 16 && spec.keyLen != 32 then refuse "the content key must be 16 or 32 octets"
  if rand.size < spec.keyLen + 12 + spec.restLen then
    refuse s!"encryption needs {spec.keyLen + 12 + spec.restLen} random octets"
  let cek := rand.extract 0 spec.keyLen
  let iv := rand.extract spec.keyLen (spec.keyLen + 12)
  let rest := rand.extract (spec.keyLen + 12) (spec.keyLen + 12 + spec.restLen)
  let ek ← encryptedKeyNode cipher prims spec.recipient cek rest spec.kdf
  let ct ← ccallEnc cipher { op := .gcmEncrypt, key := cek, iv, data := plaintext }
  pure (mkEl "xenc:EncryptedData"
    [("xmlns:xenc", xencNs), ("Type", if spec.content then typeContent else typeElement)]
    [mkEl "xenc:EncryptionMethod" [("Algorithm", (DataAlg.gcm spec.keyLen).uri)] [],
     mkEl "ds:KeyInfo" [("xmlns:ds", dsNs)] [ek],
     cipherDataNode (iv ++ ct)])

/-- Encrypt an element: the `EncryptedData` that replaces it (Element), or
the element with the `EncryptedData` as its only child (Content). -/
def encryptNode (cipher : Cipher) (prims : Prims) (spec : EncryptSpec) (rand : ByteArray) (n : Node) :
    M Node :=
  match n with
  | .element t attrs kids =>
      if spec.content then
        match encryptOctets cipher prims spec rand (serNodes "" kids).toUTF8 with
        | .ok ed => .ok (.element t attrs [ed])
        | .error f => .error f
      else encryptOctets cipher prims spec rand (serNode "" n).toUTF8
  | _ => refuse "only an element can be encrypted"

/-- Encrypt the document element. -/
def encryptDocument (cipher : Cipher) (prims : Prims) (spec : EncryptSpec) (rand : ByteArray) (d : Document) :
    M Document :=
  if d.doctype.isSome then refuse "a document type declaration is not allowed"
  else match encryptNode cipher prims spec rand d.root with
    | .ok r => .ok { d with root := r }
    | .error f => .error f

end L4Factoidal.XML.Enc
