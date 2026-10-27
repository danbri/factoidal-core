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
    `Type` is refused). Children: `xenc:EncryptionMethod` (required here),
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
    (direct key agreement), or one `ds:KeyName` that names a caller's
    symmetric key. `decryptWrapped` (SAML `EncryptedElementType`) also
    takes the one `EncryptedKey` sibling when `KeyInfo` is absent.
  * Key transport (§5.5): `xmlenc#rsa-oaep-mgf1p` (SHA-1 digest, MGF1 with
    SHA-1, optional `xenc:OAEPparams`), `xmlenc11#rsa-oaep` with the digest
    and the mask generation function the same hash: SHA-1 with
    `mgf1sha1` (the defaults of §5.5.2) or SHA-256 with `mgf1sha256`.
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
    `ds:DigestMethod` SHA-256; no `KA-Nonce`. The recipient key is named by
    `ds:KeyName` in `xenc:RecipientKeyInfo`, or is the caller's only key on
    that curve.

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
one `EncryptedKey` (RSA-OAEP, ECDH-ES with Concat KDF and AES Key Wrap, or
AES Key Wrap under a named key). The content key, the IV, the OAEP seed and
the ephemeral private key are octets the caller gives (`rand`); nothing
here reads a clock or a random source.

## Loops

Each walk over the tree recurses once per level of element nesting, which
the caller bounds (the plaintext nesting is checked here); each walk over
siblings, octets or characters is a tail call with an accumulator.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.DSig
import L4Factoidal.XML.Parser
import L4Factoidal.Crypto.CipherCall
import L4Factoidal.Crypto.RsaOaep
import L4Factoidal.Crypto.P256Native
import L4Factoidal.Crypto.X25519
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
def x25519Agreement : String := "http://www.w3.org/2021/04/xmldsig-more#x25519"
def concatKdfAlg : String := xenc11Ns ++ "ConcatKDF"
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

/-- The public-key primitives: HACL* natively (`nativePrims`), any
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

/-- The caller's keys. -/
structure Keys where
  rsa : List RsaKey := []
  ec : List EcKey := []
  sym : List SymKey := []

def Keys.isEmpty (k : Keys) : Bool := k.rsa.isEmpty && k.ec.isEmpty && k.sym.isEmpty

structure Opts where
  /-- Accept `aes128-cbc` and `aes256-cbc` data encryption. -/
  allowCbc : Bool := false
  /-- The deepest element nesting of a decrypted document. -/
  maxDepth : Nat := 32
  /-- The most `EncryptedData` elements decrypted in one document. -/
  maxEncrypted : Nat := 16

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

/-- The key encryption algorithm of an `EncryptedKey`. -/
inductive KeyAlg where
  | oaep (sha256 : Bool) (label : ByteArray)
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
      else if u == rsaOaepMgf1p then
        let (dig, _, label) ← oaepParams m false
        match dig with
        | none => pure (.oaep false label)
        | some d =>
            if d == sha1Digest then pure (.oaep false label)
            else refuse "rsa-oaep-mgf1p is supported with the SHA-1 digest only (MGF1 there is SHA-1)"
      else if u == rsaOaep11 then
        let (dig, mgf, label) ← oaepParams m true
        let d := dig.getD sha1Digest
        let g := mgf.getD mgf1Sha1
        if d == sha1Digest && g == mgf1Sha1 then pure (.oaep false label)
        else if d == sha256Digest && g == mgf1Sha256 then pure (.oaep true label)
        else refuse "xmlenc11#rsa-oaep is supported with SHA-1 and mgf1sha1, or SHA-256 and mgf1sha256"
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

/-- A key of `keyLen` octets from an `xenc:AgreementMethod`. -/
def agreeKey (prims : Prims) (keys : Keys) (a : El) (keyLen : Nat) : M ByteArray := do
  let alg := (a.attr? "Algorithm").getD ""
  if alg != ecdhEs && alg != x25519Agreement then
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
  let params ← match kdm with
    | some k => concatKdfParams k
    | none => refuse "xenc:AgreementMethod has no key derivation method"
  let (curve, pub) ← match orig with
    | some o => originatorKey o
    | none => refuse "xenc:AgreementMethod has no originator key"
  if alg == x25519Agreement && curve != .x25519 then
    refuse "xmldsig-more#x25519 needs an X25519 originator key"
  let name? ← match recip with
    | none => pure none
    | some r => do
        if !r.elementOnly then refuse "xenc:RecipientKeyInfo has unexpected content"
        match r.children.filter (·.is dsNs "KeyName") with
        | [] => pure none
        | [k] => pure (some (← keyNameOf k))
        | _ => refuse "xenc:RecipientKeyInfo has more than one ds:KeyName"
  let key ← pick (if curve == .p256 then "P-256" else "X25519") name?
    (keys.ec.filter (·.curve == curve)) (·.kid)
  let z? := match curve with
    | .p256 => prims.p256Ecdh pub key.d
    | .x25519 => prims.x25519 key.d pub
  match z? >>= fun z => ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash z keyLen params with
  | some k => pure k
  | none => .error .decryptFailed

/-! ## Content keys -/

/-- What `ds:KeyInfo` of an `EncryptedKey` says about the key encryption key. -/
inductive KekRef where
  | name (n : String)
  | agreement (a : El)
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
        else if c.is dsNs "KeyName" || c.is xencNs "AgreementMethod" then
          if seen then refuse "ds:KeyInfo of xenc:EncryptedKey names more than one key"
          seen := true
          if c.is dsNs "KeyName" then
            let nm ← keyNameOf c
            out := .name nm
          else out := .agreement c
        else refuse s!"ds:KeyInfo of xenc:EncryptedKey holds {c.lname}, which is not supported"
      pure out

/-- The content key in an `EncryptedKey`. -/
def unwrapKey (cipher : Cipher) (prims : Prims) (keys : Keys) (ek : El) (keyLen : Nat) : M ByteArray := do
  let p ← encParts ek fun c => c.is xencNs "ReferenceList" || c.is xencNs "CarriedKeyName"
  let alg ← keyAlgOf p.method
  let kr ← kekRefOf p.keyInfo
  match alg with
  | .oaep sha256 label =>
      let name? ← match kr with
        | .name n => pure (some n)
        | .unnamed => pure none
        | .agreement _ => refuse "RSA-OAEP key transport with a key agreement is not supported"
      let k ← pick "RSA" name? keys.rsa (·.kid)
      match RsaOaep.oaepDecrypt (KeyAlg.oaepHash sha256) prims.rsaPrivate k.n k.d p.cipherValue label with
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
        | .agreement a => agreeKey prims keys a len
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
      | some ek => unwrapKey ctx.cipher ctx.prims ctx.keys ek keyLen
      | none => refuse "xenc:EncryptedData has no ds:KeyInfo and no key"
  | some k =>
      if !k.elementOnly then refuse "ds:KeyInfo has unexpected content"
      match k.children with
      | [c] =>
          if isEncKey c then unwrapKey ctx.cipher ctx.prims ctx.keys c keyLen
          else if c.is xencNs "AgreementMethod" then agreeKey ctx.prims ctx.keys c keyLen
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
            | [ek] => unwrapKey ctx.cipher ctx.prims ctx.keys ek keyLen
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

/-- The nodes that replace one `EncryptedData` whose parent has bindings
`e.parent` and nesting `depth`. -/
def decryptData (ctx : Ctx) (fallback : Option El) (e : El) (depth : Nat) : M (List Node) := do
  let p ← encParts e fun _ => false
  let isElement ← match e.attr? "Type" with
    | some t =>
        if t == typeElement then pure true
        else if t == typeContent then pure false
        else refuse s!"the EncryptedData Type {t} is not supported"
    | none => refuse "xenc:EncryptedData has no Type (Element or Content)"
  let alg ← dataAlgOf ctx.opts p.method
  let cek ← contentKey ctx p.keyInfo fallback alg.keyLen
  let pt ← decryptContent ctx.cipher alg cek p.cipherValue
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

structure EncryptSpec where
  /-- AES-GCM content key length: 16 or 32. -/
  keyLen : Nat := 16
  recipient : Recipient
  /-- `Type` Content (the element's children) instead of Element. -/
  content : Bool := false

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

def kwUri (len : Nat) : String := if len == 16 then kwAes128 else kwAes256

/-- `00 || utf8(s)` as hexBinary: an octet string with no padding bits. -/
def paddedHex (s : String) : String := "00" ++ hexOf s.toUTF8

/-- The `xenc:EncryptedKey` holding `cek` for the recipient. -/
def encryptedKeyNode (cipher : Cipher) (prims : Prims) (r : Recipient) (cek rand : ByteArray) : M Node := do
  match r with
  | .rsa kid n e sha256 =>
      let ct ← match RsaOaep.oaepEncrypt (KeyAlg.oaepHash sha256) prims.rsaPublic n e cek ByteArray.empty rand with
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
  | .agree kid curve pub kwLen =>
      if kwLen != 16 && kwLen != 32 then refuse "the key wrap key must be 16 or 32 octets"
      let eph := rand
      let (ephPub?, z?) := match curve with
        | .p256 => (prims.p256Public eph, prims.p256Ecdh pub eph)
        | .x25519 => (prims.x25519Public eph, prims.x25519 eph pub)
      let ephPub ← ephPub?.elim (refuse "the ephemeral key was refused") pure
      let z ← z?.elim (refuse "the recipient's public key was refused") pure
      let params : ConcatKdf.XmlEncParams :=
        { algorithmId := hexBytes? (paddedHex (kwUri kwLen)) }
      let kek ← (ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash z kwLen params).elim
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
        [mkEl "xenc11:KeyDerivationMethod" [("xmlns:xenc11", xenc11Ns), ("Algorithm", concatKdfAlg)]
          [mkEl "xenc11:ConcatKDFParams"
            -- PartyUInfo and PartyVInfo absent (empty): Apache Santuario 4.0.4
            -- refuses the one-octet value "00" ("ConcatKDF parameter is to short").
            [("AlgorithmID", paddedHex (kwUri kwLen))]
            [mkEl "ds:DigestMethod" [("Algorithm", sha256Digest)] []]],
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
  if rand.size < spec.keyLen + 12 + spec.recipient.randLen then
    refuse s!"encryption needs {spec.keyLen + 12 + spec.recipient.randLen} random octets"
  let cek := rand.extract 0 spec.keyLen
  let iv := rand.extract spec.keyLen (spec.keyLen + 12)
  let rest := rand.extract (spec.keyLen + 12) (spec.keyLen + 12 + spec.recipient.randLen)
  let ek ← encryptedKeyNode cipher prims spec.recipient cek rest
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
