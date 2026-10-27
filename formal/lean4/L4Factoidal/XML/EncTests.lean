/-
L4Factoidal.XML.EncTests — build-time checks of the XML Encryption 1.1
profile (`L4Factoidal.XML.Enc`, https://github.com/danbri/factoidal/issues/1084)
over a STUB cipher and STUB public-key primitives.

The stubs are defined here only and are not cryptography: the "AES-GCM" is
an XOR with a SHA-256 keystream and a SHA-256 tag, the "key wrap" an XOR
with an 8-octet SHA-256 check, the "RSA" the identity, the "ECDH" an XOR of
SHA-256 values (commutative, so both parties derive the same secret). They
let the structure, the allowlist, the key choice, the request flow and the
one decryption error be checked in the interpreter, where an `@[extern]`
cannot run. The real primitives are checked in `lake exe l4xmlenc-probe`
(HACL* RSA-OAEP and AES-GCM against Apache Santuario fixtures) and in
`tests/xmlenc/wasm.mjs` (WebCrypto answering the requests).
-/
import L4Factoidal.XML.Enc
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.XML.EncTests

open L4Factoidal.XML
open L4Factoidal.XML.Enc
open L4Factoidal.Crypto
open L4Factoidal.Crypto.CipherCall
open L4Factoidal.XML.Canonical (canonDocument)

/-! ## Stubs -/

def xorB (a b : ByteArray) : ByteArray := ⟨((a.data.toList.zip b.data.toList).map fun (x, y) => x ^^^ y).toArray⟩

def ksLoop (key iv : ByteArray) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | f + 1, i, acc => ksLoop key iv f (i + 1) (acc ++ sha256 (key ++ iv ++ ByteArray.mk #[i.toUInt8]))

/-- `n` keystream octets. -/
def ks (key iv : ByteArray) (n : Nat) : ByteArray := (ksLoop key iv (n / 32 + 1) 0 ByteArray.empty).extract 0 n

def tag (key iv aad ct : ByteArray) : ByteArray := (sha256 (key ++ iv ++ aad ++ ct)).extract 0 16

def kwIv : ByteArray := "kw".toUTF8

def stubCipher : Cipher where
  call r :=
    if !r.wellFormed then .error .refused
    else match r.op with
      | .gcmEncrypt =>
          let ct := xorB r.data (ks r.key r.iv r.data.size)
          .ok (ct ++ tag r.key r.iv r.aad ct)
      | .gcmDecrypt =>
          let ct := r.data.extract 0 (r.data.size - 16)
          if r.data.extract (r.data.size - 16) r.data.size == tag r.key r.iv r.aad ct then
            .ok (xorB ct (ks r.key r.iv ct.size))
          else .error .refused
      | .kwWrap => .ok (xorB r.data (ks r.key kwIv r.data.size) ++ (sha256 (r.key ++ r.data)).extract 0 8)
      | .kwUnwrap =>
          let w := r.data.extract 0 (r.data.size - 8)
          let d := xorB w (ks r.key kwIv w.size)
          if r.data.extract (r.data.size - 8) r.data.size == (sha256 (r.key ++ d)).extract 0 8 then .ok d
          else .error .refused
      | _ => .error .refused

def stubPrims : Prims where
  rsaPrivate n _ c := if c.size == n.size then some c else none
  rsaPublic n _ m := if m.size == n.size then some m else none
  p256Public sk := some (sha256 sk ++ sha256 sk)
  p256Ecdh xy sk := if xy.size == 64 then some (xorB (xy.extract 0 32) (sha256 sk)) else none
  x25519Public sk := some (sha256 sk)
  x25519 sk pub := if pub.size == 32 then some (xorB pub (sha256 sk)) else none

def bytes (n : Nat) (seed : Nat) : ByteArray := ⟨((List.range n).map fun i => (i * 7 + seed).toUInt8).toArray⟩

def rsaN : ByteArray := bytes 128 1
def ecD : ByteArray := bytes 32 2
def xD : ByteArray := bytes 32 3
def kek16 : ByteArray := bytes 16 4
def rand : ByteArray := bytes 96 5

def keys : Keys :=
  { rsa := [{ kid := some "rsa-1", n := rsaN, d := bytes 128 9 }]
    ec := [{ kid := some "ec-1", curve := .p256, d := ecD }, { curve := .x25519, d := xD }]
    sym := [{ kid := some "kek128", k := kek16 }] }

def ecPub : ByteArray := (stubPrims.p256Public ecD).getD ByteArray.empty
def xPub : ByteArray := (stubPrims.x25519Public xD).getD ByteArray.empty

/-! ## The sample document and round trips -/

def sampleText : String :=
  "<r:order xmlns:r=\"urn:example:order\" xmlns:p=\"urn:example:pay\" id=\"o1\">" ++
  "<r:item n=\"2\">tea &amp; cake</r:item>" ++
  "<p:card r:kind=\"debit\"><p:number>4019</p:number><!-- c --><p:holder>Zoë</p:holder></p:card>" ++
  "<r:note>&lt;not markup&gt;</r:note></r:order>"

def sample : Document := match parseXML sampleText with
  | .ok d => d
  | .error _ => default

#guard (canonDocument sample).length > 100

/-- Encrypt `p:card` (or its content) with `spec`. -/
def encryptCard (spec : EncryptSpec) (cipher : Cipher := stubCipher) : M Document :=
  match sample.root with
  | .element t attrs kids =>
      let step (n : Node) : M Node := match n with
        | .element "p:card" .. => encryptNode cipher stubPrims spec rand n
        | _ => .ok n
      match kids.mapM step with
      | .ok kids' => .ok { sample with root := .element t attrs kids' }
      | .error f => .error f
  | _ => refuse "no root"

/-- Serialize, parse again, decrypt. -/
def reopen (d : Document) (cipher : Cipher := stubCipher) (ks : Keys := keys) (opts : Opts := {}) : M Document :=
  match parseXML (serializeDocument d) with
  | .ok d' => decrypt cipher stubPrims ks opts d'
  | .error _ => refuse "the encrypted document does not parse"

def roundTrips (e : M Document) (ks : Keys := keys) : Bool :=
  match e with
  | .ok d => match reopen d (ks := ks) with
    | .ok d' => canonDocument d' == canonDocument sample
    | .error _ => false
  | .error _ => false

def rsaSpec (sha256 : Bool) (keyLen := 16) (content := false) : EncryptSpec :=
  { keyLen, content, recipient := .rsa (some "rsa-1") rsaN ByteArray.empty sha256 }

-- RSA-OAEP (mgf1p and 1.1 with SHA-256), AES-128 and AES-256-GCM, Element and Content.
#guard roundTrips (encryptCard (rsaSpec false))
#guard roundTrips (encryptCard (rsaSpec true 32))
#guard roundTrips (encryptCard (rsaSpec false 16 true))
-- The document element itself.
#guard roundTrips (encryptDocument stubCipher stubPrims (rsaSpec true) rand sample)
-- AES Key Wrap under a named key; ECDH-ES P-256 and X25519 with ConcatKDF.
#guard roundTrips (encryptCard { recipient := .kek (some "kek128") kek16 })
#guard roundTrips (encryptCard { keyLen := 32, recipient := .agree (some "ec-1") .p256 ecPub 16 })
#guard roundTrips (encryptCard { recipient := .agree none .x25519 xPub 32 })
-- The plaintext is UTF-8 and keeps its comment.
#guard match encryptCard (rsaSpec false) with
  | .ok d => match reopen d with
    | .ok d' => ((canonDocument d').splitOn "<!-- c -->").length == 2 && ((canonDocument d').splitOn "Zoë").length == 2
    | .error _ => false
  | .error _ => false
-- The encrypted form shows neither.
#guard match encryptCard (rsaSpec false) with
  | .ok d => ((serializeDocument d).splitOn "4019").length == 1 && ((serializeDocument d).splitOn "debit").length == 1
  | .error _ => false

/-! ## Failures: one message after the structure check -/

def failsWith (e : M Document) (p : Failure → Bool) : Bool :=
  match e with
  | .error f => p f
  | .ok _ => false

def isDecryptFailed : Failure → Bool
  | .decryptFailed => true
  | _ => false

def refusedHas (frag : String) : Failure → Bool
  | .refused m => (m.splitOn frag).length ≥ 2
  | _ => false

/-- The serialized encryption with the first character of the last
`CipherValue` (the content) changed. -/
def tamperLast (d : Document) : String :=
  let parts := (serializeDocument d).splitOn "<xenc:CipherValue>"
  match parts.getLast? with
  | some last =>
      let c := last.front
      let last' := String.singleton (if c == 'A' then 'B' else 'A') ++ (last.drop 1).toString
      "<xenc:CipherValue>".intercalate (parts.dropLast ++ [last'])
  | none => ""

def decryptText (s : String) (ks : Keys := keys) (opts : Opts := {}) (cipher : Cipher := stubCipher) : M Document :=
  match parseXML s with
  | .ok d => decrypt cipher stubPrims ks opts d
  | .error _ => refuse "does not parse"

-- An altered ciphertext fails the tag: the one decryption error.
#guard match encryptCard (rsaSpec false) with
  | .ok d => failsWith (decryptText (tamperLast d)) isDecryptFailed
  | .error _ => false
-- A wrong key encryption key: the same error and the same message.
#guard match encryptCard { recipient := .kek (some "kek128") kek16 } with
  | .ok d => failsWith (reopen d (ks := { keys with sym := [{ kid := some "kek128", k := bytes 16 77 }] }))
      fun f => isDecryptFailed f && f.message == decryptionError
  | .error _ => false
-- A wrong P-256 key.
#guard match encryptCard { recipient := .agree (some "ec-1") .p256 ecPub 16 } with
  | .ok d => failsWith (reopen d (ks := { keys with ec := [{ kid := some "ec-1", curve := .p256, d := bytes 32 50 }] }))
      isDecryptFailed
  | .error _ => false
-- A plaintext that holds an EncryptedData is not decrypted again.
#guard match encryptCard (rsaSpec false 16 true) with
  | .ok d => failsWith (encryptDocument stubCipher stubPrims (rsaSpec false) rand d >>= fun d2 => reopen d2)
      isDecryptFailed
  | .error _ => false
-- A plaintext nested deeper than the bound.
#guard match encryptCard (rsaSpec false) with
  | .ok d => failsWith (reopen d (opts := { maxDepth := 2 })) isDecryptFailed
  | .error _ => false

/-! ## The allowlist -/

def edDoc (method keyInfo cipherData : String) (typ : String := typeElement) : String :=
  "<r xmlns:xenc=\"" ++ xencNs ++ "\" xmlns:ds=\"" ++ L4Factoidal.XML.DSig.dsNs ++ "\">" ++
  "<xenc:EncryptedData Type=\"" ++ typ ++ "\"><xenc:EncryptionMethod Algorithm=\"" ++ method ++ "\"/>" ++
  keyInfo ++ cipherData ++ "</xenc:EncryptedData></r>"

def cvData : String := "<xenc:CipherData><xenc:CipherValue>AAAA</xenc:CipherValue></xenc:CipherData>"

def ekWith (method : String) (inner : String := "") : String :=
  "<ds:KeyInfo><xenc:EncryptedKey><xenc:EncryptionMethod Algorithm=\"" ++ method ++ "\">" ++ inner ++
  "</xenc:EncryptionMethod>" ++ cvData ++ "</xenc:EncryptedKey></ds:KeyInfo>"

def ekRsa : String := ekWith rsaOaepMgf1p

-- RSA PKCS #1 v1.5 key transport is refused before any key is used.
#guard failsWith (decryptText (edDoc aes128Gcm (ekWith rsa15) cvData)) (refusedHas "rsa-1_5")
-- CipherReference is refused: no retrieval.
#guard failsWith (decryptText (edDoc aes128Gcm ekRsa
  "<xenc:CipherData><xenc:CipherReference URI=\"http://example.org/x\"/></xenc:CipherData>"))
  (refusedHas "CipherReference")
-- CBC is refused unless the caller allows it.
#guard failsWith (decryptText (edDoc aes128Cbc ekRsa cvData)) (refusedHas "allowCbc")
#guard failsWith (decryptText (edDoc aes256Cbc ekRsa cvData)) (refusedHas "allowCbc")
-- AES-192, unknown algorithms, mixed OAEP hashes.
#guard failsWith (decryptText (edDoc aes192Gcm ekRsa cvData)) (refusedHas "AES-192")
#guard failsWith (decryptText (edDoc "urn:example:cipher" ekRsa cvData)) (refusedHas "not supported")
#guard failsWith (decryptText (edDoc aes128Gcm (ekWith rsaOaepMgf1p
  ("<ds:DigestMethod Algorithm=\"" ++ sha256Digest ++ "\"/>")) cvData)) (refusedHas "SHA-1 digest only")
#guard failsWith (decryptText (edDoc aes128Gcm (ekWith rsaOaep11
  ("<ds:DigestMethod Algorithm=\"" ++ sha256Digest ++ "\"/>")) cvData)) (refusedHas "mgf1sha256")
#guard failsWith (decryptText (edDoc aes128Gcm (ekWith "http://www.w3.org/2001/04/xmlenc#kw-tripledes") cvData))
  (refusedHas "not supported")
-- No Type, another Type.
#guard failsWith (decryptText ((edDoc aes128Gcm ekRsa cvData).replace (" Type=\"" ++ typeElement ++ "\"") ""))
  (refusedHas "no Type")
#guard failsWith (decryptText (edDoc aes128Gcm ekRsa cvData "urn:example:type")) (refusedHas "Type")
-- A document type declaration.
#guard failsWith (decryptText ("<!DOCTYPE r>" ++ edDoc aes128Gcm ekRsa cvData)) (refusedHas "document type")
-- RetrievalMethod: same document only, and the Id must exist.
#guard failsWith (decryptText (edDoc aes128Gcm
  ("<ds:KeyInfo><ds:RetrievalMethod Type=\"" ++ typeEncryptedKey ++ "\" URI=\"http://example.org/k\"/></ds:KeyInfo>")
  cvData)) (refusedHas "this document")
#guard failsWith (decryptText (edDoc aes128Gcm
  ("<ds:KeyInfo><ds:RetrievalMethod Type=\"" ++ typeEncryptedKey ++ "\" URI=\"#k9\"/></ds:KeyInfo>") cvData))
  (refusedHas "no xenc:EncryptedKey has the Id k9")
-- A key name the caller does not have; no key at all.
#guard failsWith (decryptText (edDoc aes128Gcm "<ds:KeyInfo><ds:KeyName>other</ds:KeyName></ds:KeyInfo>" cvData))
  (refusedHas "no symmetric key named other")
#guard failsWith (decryptText (edDoc aes128Gcm ekRsa cvData) (ks := {})) (refusedHas "no RSA key")
#guard failsWith (decryptText (edDoc aes128Gcm "" cvData)) (refusedHas "no ds:KeyInfo")
-- An unsupported KeyInfo form.
#guard failsWith (decryptText (edDoc aes128Gcm "<ds:KeyInfo><ds:X509Data/></ds:KeyInfo>" cvData))
  (refusedHas "X509Data")
-- The bound on EncryptedData elements.
#guard failsWith (decryptText (edDoc aes128Gcm ekRsa cvData) (opts := { maxEncrypted := 0 }))
  (refusedHas "more than 0")
-- A KA-Nonce is refused.
#guard failsWith (decryptText (edDoc aes128Gcm
  ("<ds:KeyInfo><xenc:EncryptedKey><xenc:EncryptionMethod Algorithm=\"" ++ kwAes128 ++ "\"/><ds:KeyInfo>" ++
   "<xenc:AgreementMethod Algorithm=\"" ++ ecdhEs ++ "\"><xenc:KA-Nonce>AA==</xenc:KA-Nonce></xenc:AgreementMethod>" ++
   "</ds:KeyInfo>" ++ cvData ++ "</xenc:EncryptedKey></ds:KeyInfo>") cvData)) (refusedHas "KA-Nonce")

/-! ## Requests to the host -/

def needOp (e : M Document) : Option Op :=
  match e with
  | .error (.need r) => some r.op
  | _ => none

-- With no answers, the first request comes back unchanged.
#guard match encryptCard (rsaSpec false) with
  | .ok d => needOp (reopen d (cipher := replayCipher [])) == some .gcmDecrypt
  | .error _ => false
#guard match encryptCard { recipient := .kek (some "kek128") kek16 } with
  | .ok d => needOp (reopen d (cipher := replayCipher [])) == some .kwUnwrap
  | .error _ => false
-- CBC, allowed: the first request is the padding block (an encryption of
-- nothing under the last ciphertext block).
#guard match decryptText (edDoc aes128Cbc
    "<ds:KeyInfo><ds:KeyName>kek128</ds:KeyName></ds:KeyInfo>"
    "<xenc:CipherData><xenc:CipherValue>AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=</xenc:CipherValue></xenc:CipherData>")
    (opts := { allowCbc := true }) (cipher := replayCipher []) with
  | .error (.need r) => r.op == .cbcEncrypt && r.iv.size == 16 && r.data.size == 0
  | _ => false
-- Encryption asks too.
#guard match encryptCard { recipient := .kek (some "kek128") kek16 } (cipher := replayCipher []) with
  | .error (.need r) => r.op == .kwWrap
  | _ => false

/-- The host loop: run, answer the one request with `answer`, run again.
`fuel` bounds the rounds (`maxRequests` on the wasm surface). -/
def drive (run : Cipher → M Document) (answer : Cipher) : (fuel : Nat) → List (Req × Ans) → M Document × Nat
  | 0, acc => (refuse "too many requests", acc.length)
  | f + 1, acc =>
      match run (replayCipher acc) with
      | .error (.need r) =>
          let a : Ans := match answer.call r with
            | .ok b => .ok b
            | .error _ => .refused
          drive run answer f (acc ++ [(r, a)])
      | out => (out, acc.length)

-- Two requests (unwrap, then GCM) and the same document as a direct run.
#guard match encryptCard { recipient := .kek (some "kek128") kek16 } with
  | .ok d =>
      match drive (fun c => reopen d (cipher := c)) stubCipher maxRequests [] with
      | (.ok d', n) => n == 2 && canonDocument d' == canonDocument sample
      | _ => false
  | .error _ => false
-- Encryption through the loop, then decryption through the loop.
#guard match drive (fun c => encryptCard { recipient := .agree none .x25519 xPub 32 } (cipher := c)) stubCipher 8 [] with
  | (.ok d, 2) =>
      match drive (fun c => reopen d (cipher := c)) stubCipher 8 [] with
      | (.ok d', 2) => canonDocument d' == canonDocument sample
      | _ => false
  | _ => false
-- A refused answer is the one decryption error, never a need.
#guard match encryptCard (rsaSpec false) with
  | .ok d =>
      match drive (fun c => reopen d (cipher := c)) { call := fun _ => .error .refused } 4 [] with
      | (.error .decryptFailed, 1) => true
      | _ => false
  | .error _ => false

/-! ## Octet helpers -/

#guard base64 "".toUTF8 == ""
#guard base64 "f".toUTF8 == "Zg=="
#guard base64 "fo".toUTF8 == "Zm8="
#guard base64 "foobar".toUTF8 == "Zm9vYmFy"
#guard base64 (bytes 200 3) == base64 ((base64Decode? (base64 (bytes 200 3))).getD ByteArray.empty)
#guard hexBytes? "00Ff10" == some ⟨#[0, 255, 16]⟩
#guard hexBytes? "0" == none
#guard hexOf ⟨#[0, 255, 16]⟩ == "00ff10"
#guard unpad ⟨#[1, 2, 3, 9, 9, 3]⟩ == some ⟨#[1, 2, 3]⟩
#guard unpad ⟨#[1, 2, 0]⟩ == none
#guard nestingWithin 2 "<a><b/></a>".toList 0
#guard !nestingWithin 2 "<a><b><c/></b></a>".toList 0

end L4Factoidal.XML.EncTests
