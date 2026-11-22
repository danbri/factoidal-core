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
  oaepDigest d m := some (d.fn m)
  rsaPrivate n _ c := if c.size == n.size then some c else none
  rsaPublic n _ m := if m.size == n.size then some m else none
  p256Public sk := some (sha256 sk ++ sha256 sk)
  p256Ecdh xy sk := if xy.size == 64 then some (xorB (xy.extract 0 32) (sha256 sk)) else none
  x25519Public sk := some (sha256 sk)
  x25519 sk pub := if pub.size == 32 then some (xorB pub (sha256 sk)) else none
  pbkdf2 a := WebCrypto.pbkdf2 a.pure

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
-- RSA-OAEP digests and MGF1 hashes (§5.5.2). A digest or MGF this profile
-- does not know is refused by name; a known one passes the allowlist, and the
-- stub RSA operation then refuses the 3-octet ciphertext: the one error.
def digestEl (u : String) : String := "<ds:DigestMethod Algorithm=\"" ++ u ++ "\"/>"
def mgfEl (u : String) : String :=
  "<xenc11:MGF xmlns:xenc11=\"" ++ xenc11Ns ++ "\" Algorithm=\"" ++ u ++ "\"/>"
#guard failsWith (decryptText (edDoc aes128Gcm (ekWith rsaOaep11 (digestEl "urn:example:md5")) cvData))
  (refusedHas "digest method urn:example:md5")
#guard failsWith (decryptText (edDoc aes128Gcm (ekWith rsaOaep11 (mgfEl "urn:example:mgf")) cvData))
  (refusedHas "mask generation function urn:example:mgf")
-- `rsa-oaep-mgf1p` fixes MGF1 with SHA-1, so it has no `xenc11:MGF` child.
#guard failsWith (decryptText (edDoc aes128Gcm (ekWith rsaOaepMgf1p (mgfEl mgf1Sha1)) cvData))
  (refusedHas "unsupported child")
#guard OaepDigest.all.all fun d =>
  failsWith (decryptText (edDoc aes128Gcm (ekWith rsaOaepMgf1p (digestEl d.digestUri)) cvData)) isDecryptFailed
#guard OaepDigest.all.all fun d => OaepDigest.all.all fun g =>
  failsWith (decryptText (edDoc aes128Gcm (ekWith rsaOaep11 (digestEl d.digestUri ++ mgfEl g.mgfUri)) cvData))
    isDecryptFailed
#guard OaepDigest.all.all fun d =>
  OaepDigest.ofDigestUri? d.digestUri == some d && OaepDigest.ofMgfUri? d.mgfUri == some d
#guard OaepDigest.all.all fun d => (d.fn ByteArray.empty).size == d.len

-- EME-OAEP with a label hash that differs from the MGF1 hash (W3C WRAP.3:
-- SHA-384 with MGF1-SHA-1; WRAP.4: SHA-512 with MGF1-SHA-1 and a label),
-- through the identity as the RSA operation: the round trip holds, and
-- decoding with MGF1 over the label hash instead fails.
def oaepN : ByteArray := bytes 512 11
def oaepMsg : ByteArray := "a 32-octet content encryption k.".toUTF8
def oaepLabel : ByteArray := "dummy123".toUTF8
def oaepRound (enc dec : L4Factoidal.Crypto.RsaOaep.OaepHash) (seedLen : Nat) : Option ByteArray :=
  (L4Factoidal.Crypto.RsaOaep.oaepEncrypt enc stubPrims.rsaPublic oaepN ByteArray.empty oaepMsg oaepLabel
      (bytes seedLen 12)).bind
    fun c => L4Factoidal.Crypto.RsaOaep.oaepDecrypt dec stubPrims.rsaPrivate oaepN ByteArray.empty c oaepLabel
#guard oaepRound (oaepHashOf .sha384 .sha1) (oaepHashOf .sha384 .sha1) 48 == some oaepMsg
#guard oaepRound (oaepHashOf .sha512 .sha1) (oaepHashOf .sha512 .sha1) 64 == some oaepMsg
#guard (oaepRound (oaepHashOf .sha512 .sha1) (oaepHashOf .sha512 .sha512) 64).isNone
#guard (oaepRound (oaepHashOf .sha384 .sha1) (oaepHashOf .sha256 .sha1) 48).isNone

-- Exercise the XML caller with a valid OAEP ciphertext. For SHA-1 the
-- second decoding mask hashes the 20-byte seed plus four counter bytes.
def checkedDigestFailure (bad : ByteArray → Bool) (answer : Option ByteArray) : Bool :=
  match encryptCard (rsaSpec false) with
  | .error _ => false
  | .ok doc =>
      let p := { stubPrims with oaepDigest := fun d m => if bad m then answer else some (d.fn m) }
      failsWith (decrypt stubCipher p keys {} doc) isDecryptFailed

#guard checkedDigestFailure (fun m => m.size == 0) none
#guard checkedDigestFailure (fun m => m.size == 24 && m.data.toList.getLast? == some 1) none
#guard checkedDigestFailure (fun m => m.size == 24 && m.data.toList.getLast? == some 1) (some (bytes 1 7))
#guard (RsaOaep.mgf1Checked { size := 0, run := fun _ => some ByteArray.empty } [] 4).isNone
#guard (RsaOaep.mgf1Checked { size := 20, run := fun _ => some ByteArray.empty } [] 21).isNone
#guard WebHacl.HashAlg.ofName? "SHA-224" == none

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

/-! ## PBKDF2 key derivation (§5.4.2) -/

/-- A `KeyDerivationMethod` element from its text, or none. -/
def kdmOf (s : String) : Option DSig.El :=
  match parseXML s with
  | .ok d => DSig.elOf? Canonical.rootScope d.root
  | .error _ => none

def kdmText (it len prf : String) (salt : String := "AAECAwQFBgc=") : String :=
  "<k:KeyDerivationMethod xmlns:k=\"" ++ xenc11Ns ++ "\" Algorithm=\"" ++ pbkdf2Alg ++ "\"><k:PBKDF2-params>" ++
  "<k:Salt><k:Specified>" ++ salt ++ "</k:Specified></k:Salt><k:IterationCount>" ++ it ++
  "</k:IterationCount><k:KeyLength>" ++ len ++ "</k:KeyLength><k:PRF Algorithm=\"" ++ prf ++
  "\"/></k:PBKDF2-params></k:KeyDerivationMethod>"

def pbOk (s : String) (p : Pbkdf2Params → Bool) : Bool :=
  match kdmOf s with
  | some e => match pbkdf2Params {} e with
    | .ok q => p q
    | .error _ => false
  | none => false

def pbRefused (s : String) (frag : String) : Bool :=
  match kdmOf s with
  | some e => match kdfOf {} e with
    | .error (.refused m) => (m.splitOn frag).length ≥ 2
    | _ => false
  | none => false

#guard positiveInteger? "2000" == some 2000
#guard positiveInteger? " +07 " == some 7
#guard positiveInteger? "0" == none
#guard positiveInteger? "-1" == none
#guard positiveInteger? "1e3" == none
#guard positiveInteger? "1234567890123" == none
#guard prfOf? hmacSha256Prf == some .sha256
#guard prfOf? "http://www.w3.org/2001/04/xmldsig-more#hmac-sha224" == none
#guard pbOk (kdmText "2000" "32" hmacSha256Prf) fun p =>
  p.iterations == 2000 && p.keyLength == 32 && p.prf == .sha256 && p.salt.size == 8
#guard pbOk (kdmText "1" "16" hmacSha1Prf) (·.prf == .sha1)
#guard pbRefused (kdmText "0" "32" hmacSha256Prf) "IterationCount"
#guard pbRefused (kdmText "1000001" "32" hmacSha256Prf) "above the limit"
#guard pbRefused (kdmText "10" "32" "urn:x") "PRF"
#guard pbRefused (kdmText "10" "32" hmacSha256Prf "!!") "not base64"
#guard pbRefused ((kdmText "10" "32" hmacSha256Prf).replace "pbkdf2\"" "hkdf\"") "not supported"
-- RFC 6070 test 2 (PBKDF2-HMAC-SHA1, 2 iterations) through a stub's derivation.
#guard match kdmOf (kdmText "2" "20" hmacSha1Prf (base64 "salt".toUTF8)) with
  | some e => match kdfOf {} e with
    | .ok k => (k.derive? stubPrims "password".toUTF8 20).map hexOf ==
        some "ea6c014dc72d6f8ccd1ed92ace1d41f0d8de8957"
    | .error _ => false
  | none => false
-- A derived key of another length than the one it is used for is not given.
#guard match kdmOf (kdmText "2" "20" hmacSha1Prf) with
  | some e => match kdfOf {} e with
    | .ok k => (k.derive? stubPrims "password".toUTF8 16).isNone
    | .error _ => false
  | none => false

/-! ## Derived keys (§5.4.3) and octets (§4.4 step 3) -/

def master32 : ByteArray := bytes 32 21

def dkText (kdm : String) (extra : String := "<k:MasterKeyName>m1</k:MasterKeyName>") : String :=
  "<k:DerivedKey xmlns:k=\"" ++ xenc11Ns ++ "\">" ++ kdm ++ extra ++ "</k:DerivedKey>"

def concatKdm : String :=
  "<k:KeyDerivationMethod Algorithm=\"" ++ concatKdfAlg ++ "\"><k:ConcatKDFParams AlgorithmID=\"0001\" " ++
  "PartyUInfo=\"0002\" PartyVInfo=\"0003\"><ds:DigestMethod xmlns:ds=\"" ++ L4Factoidal.XML.DSig.dsNs ++
  "\" Algorithm=\"" ++ sha256Digest ++ "\"/></k:ConcatKDFParams></k:KeyDerivationMethod>"

def dkKeys : Keys := { sym := [{ kid := some "m1", k := master32 }, { kid := some "kek128", k := kek16 }] }

def dkRun (s : String) (n : Nat) (ks : Keys := dkKeys) : M ByteArray :=
  match kdmOf s with
  | some e => derivedKey stubPrims ks e n
  | none => refuse "does not parse"

def mRefused (r : M ByteArray) (frag : String) : Bool :=
  match r with
  | .error (.refused m) => (m.splitOn frag).length ≥ 2
  | _ => false

def concatParams : ConcatKdf.XmlEncParams :=
  { algorithmId := some ⟨#[0, 1]⟩, partyUInfo := some ⟨#[0, 2]⟩, partyVInfo := some ⟨#[0, 3]⟩ }

-- A Concat KDF DerivedKey is §5.4.1 over the named master key.
#guard match dkRun (dkText concatKdm) 32 with
  | .ok k => some k == ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash master32 32 concatParams && k.size == 32
  | .error _ => false
-- A PBKDF2 DerivedKey is RFC 8018 PBKDF2 over the master key as the password.
#guard match dkRun (dkText (kdmText "3" "16" hmacSha256Prf)) 16 with
  | .ok k => k == WebCrypto.pbkdf2 WebHacl.HashAlg.sha256.pure master32
      ((base64Decode? "AAECAwQFBgc=").getD ByteArray.empty) 3 16
  | .error _ => false
#guard mRefused (dkRun (dkText (kdmText "3" "32" hmacSha256Prf)) 16) "KeyLength"
#guard mRefused (dkRun (dkText "") 32) "no xenc11:KeyDerivationMethod"
#guard mRefused (dkRun (dkText concatKdm "<k:MasterKeyName>nope</k:MasterKeyName>") 32) "no symmetric master key named nope"
#guard mRefused (dkRun (dkText concatKdm "") 32) "more than one symmetric master key"
#guard mRefused (dkRun (dkText concatKdm "<k:Other/>") 32) "unsupported or repeated child Other"
#guard mRefused (dkRun (dkText (concatKdm ++ concatKdm)) 32) "repeated child"
-- With one symmetric key, MasterKeyName may be left out.
#guard (dkRun (dkText concatKdm "") 32 (ks := { sym := [{ k := master32 }] })).toOption.isSome

/-- An `EncryptedData` with the stub AES-GCM of `pt` under `key`, IV `iv`. -/
def gcmDoc (keyInfo : String) (key iv pt : ByteArray) (typ : String := "") : String :=
  let ct := (stubCipher.call { op := .gcmEncrypt, key, iv, data := pt }).toOption.getD ByteArray.empty
  "<xenc:EncryptedData xmlns:xenc=\"" ++ xencNs ++ "\" xmlns:ds=\"" ++ L4Factoidal.XML.DSig.dsNs ++ "\"" ++
  (if typ.isEmpty then "" else " Type=\"" ++ typ ++ "\"") ++ "><xenc:EncryptionMethod Algorithm=\"" ++
  aes128Gcm ++ "\"/>" ++ keyInfo ++ "<xenc:CipherData><xenc:CipherValue>" ++ base64 (iv ++ ct) ++
  "</xenc:CipherValue></xenc:CipherData></xenc:EncryptedData>"

def octetsOf (s : String) (ks : Keys := dkKeys) : M ByteArray :=
  match parseXML s with
  | .ok d => decryptOctets stubCipher stubPrims ks {} d
  | .error _ => refuse "does not parse"

def octPt : ByteArray := ⟨#[0xd9, 0x31, 0x32, 0x25, 0, 1, 2, 255]⟩
def namedKi : String := "<ds:KeyInfo><ds:KeyName>kek128</ds:KeyName></ds:KeyInfo>"

-- No Type: the octets, not a document.
#guard (octetsOf (gcmDoc namedKi kek16 (bytes 12 6) octPt)).toOption == some octPt
#guard failsWith (decryptText (gcmDoc namedKi kek16 (bytes 12 6) octPt) (ks := dkKeys)) (refusedHas "no Type")
-- The octets of an Element EncryptedData are the text that `decrypt` parses.
#guard (octetsOf (gcmDoc namedKi kek16 (bytes 12 6) "<a/>".toUTF8 typeElement)).toOption == some "<a/>".toUTF8
-- A content key from a DerivedKey (here, 16 octets by Concat KDF).
#guard match ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash master32 16 concatParams with
  | some cek => (octetsOf (gcmDoc ("<ds:KeyInfo>" ++ dkText concatKdm ++ "</ds:KeyInfo>") cek (bytes 12 7) octPt)).toOption
      == some octPt
  | none => false
-- A wrong master key: the one decryption error.
#guard match ConcatKdf.xmlEncDerive? ConcatKdf.sha256Hash master32 16 concatParams with
  | some cek =>
      match octetsOf (gcmDoc ("<ds:KeyInfo>" ++ dkText concatKdm ++ "</ds:KeyInfo>") cek (bytes 12 7) octPt)
          (ks := { sym := [{ kid := some "m1", k := bytes 32 99 }] }) with
      | .error .decryptFailed => true
      | _ => false
  | none => false
-- The octets form needs an EncryptedData document element.
#guard mRefused (octetsOf "<r/>") "must be xenc:EncryptedData"

end L4Factoidal.XML.EncTests
