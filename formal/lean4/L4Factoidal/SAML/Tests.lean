/-
L4Factoidal.SAML.Tests — `#guard`s for SAML 2.0 assertion validation and
the XML Signature profile under it
(https://github.com/danbri/factoidal/issues/926).

The assertions are `L4Factoidal.SAML.Fixtures`, made by the JDK's XML
Signature API (`tests/saml/MakeFixtures.java`), so the exclusive canonical
forms and the digests are checked against an implementation that is not
this one.

The RSA public operation here is `refPublicOp`: `s^e mod n` over Lean's
`Nat`, a test reference only (an extern cannot run in the interpreter).
The padding check is the production one, `JOSE.Pkcs1.rs256Verify`. The
executable edge uses HACL*'s public operation through the same function
(`Authz.hacl`).
-/
import L4Factoidal.Authz.Tests
import L4Factoidal.SAML.Fixtures
import L4Factoidal.XML.EncTests

namespace L4Factoidal.SAML.Tests

open L4Factoidal.SAML
open L4Factoidal.SAML.Fixtures

/-! ## A reference RSA public operation (tests only) -/

def natOfBytes (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

def bytesOfNat (k : Nat) (v : Nat) : ByteArray :=
  ⟨((List.range k).reverse.map fun i => UInt8.ofNat (v / 256 ^ i % 256)).toArray⟩

def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1
  let mut x := b % m
  let mut y := e
  for _ in [0:4096] do
    if y == 0 then break
    if y % 2 == 1 then r := r * x % m
    x := x * x % m
    y := y / 2
  return r

def refPublicOp (n e s : ByteArray) : Option ByteArray :=
  let nn := natOfBytes n
  let ss := natOfBytes s
  if n.size < 256 || s.size != n.size || ss ≥ nn then none
  else some (bytesOfNat n.size (powMod ss (natOfBytes e) nn))

def rsa : L4Factoidal.XML.DSig.RsaVerify :=
  fun n e sig msg => L4Factoidal.JOSE.Pkcs1.rs256Verify refPublicOp n e sig msg

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toNat - 87

def hexBytes (s : String) : ByteArray :=
  let rec go : List Char → List UInt8 → List UInt8
    | a :: b :: rest, acc => go rest (UInt8.ofNat (hexVal a * 16 + hexVal b) :: acc)
    | _, acc => acc.reverse
  ⟨(go s.toList []).toArray⟩

def idp : Idp := { entityId := "https://idp.example", n := hexBytes idpN, e := hexBytes idpE }

def policy (now : Nat := 1761313610) : Policy :=
  { idps := [idp], audience := "https://as.example", now }

def ok? (t : String) (p : Policy := policy) : Option Claims :=
  match validate rsa p t with
  | .ok c => some c
  | .error _ => none

/-- Refused, with a reason that contains `frag`. -/
def refusedWith (t frag : String) (p : Policy := policy) : Bool :=
  match validate rsa p t with
  | .ok _ => false
  | .error w => (w.splitOn frag).length ≥ 2

/-! ## The JDK's assertions -/

-- The reference RSA operation agrees with the fixture key.
#guard (hexBytes idpN).size == 256

-- A valid assertion: NameID is the subject, the bearer Recipient the client.
#guard ok? valid == some { issuer := "https://idp.example", nameId := "https://id.example/end-user",
                           recipient := "https://app.example/SAML" }
-- With an InclusiveNamespaces PrefixList on the reference transform.
#guard (ok? inclusive).map (·.nameId) == some "https://id.example/end-user"

-- Altered after signing: the digest no longer matches.
#guard refusedWith altered "digest"
-- Unsigned.
#guard refusedWith unsigned "exactly one ds:Signature"
-- Signed by another key, which its KeyInfo carries: the configured key is used.
#guard refusedWith attackerKey "signature value does not verify"
-- A comment in NameID is refused although the identity provider signed it.
#guard refusedWith comment "comments"
-- Signature wrapping: the signed assertion inside an unsigned one.
#guard refusedWith wrapChild "not a child of the document element"
-- Signature wrapping: the outer assertion takes the ID and the signature,
-- the signed assertion is moved into ds:Object.
#guard refusedWith wrapObject "ID"

-- Times, with 60 seconds of skew.
#guard (ok? valid (policy (1761313600 - 59))).isSome
#guard refusedWith valid "not valid yet" (policy (1761313600 - 61))
#guard (ok? valid (policy (1761313900 + 59))).isSome
#guard refusedWith valid "expired" (policy (1761313900 + 60))
-- Audience: this server must be named.
#guard refusedWith valid "audience" { policy with audience := "https://other-as.example" }
-- Trust: an issuer that is not configured, or a different key for it.
#guard refusedWith valid "not a trusted identity provider" { policy with idps := [] }
#guard refusedWith valid "signature value does not verify"
  { policy with idps := [{ idp with n := hexBytes ((idpN.dropEnd 2).toString ++ "01") }] }

-- Not base64url, not XML, too large.
#guard refusedWith "PHNhbWw+" "base64url"
#guard refusedWith "PHNhbWw-" "well-formed"
#guard refusedWith (String.ofList (List.replicate (maxTokenChars + 1) 'A')) "too large"

/-! ## Assertions written here (structure checks; no valid signature) -/

def b64 (s : String) : String := L4Factoidal.JOSE.Base64Url.encode s.toUTF8

-- A document type declaration is refused before any key is chosen.
#guard refusedWith (b64 ("<!DOCTYPE a [<!ENTITY x \"y\">]><saml:Assertion xmlns:saml=\"" ++ samlNs ++
  "\" ID=\"_1\" Version=\"2.0\"><saml:Issuer>https://idp.example</saml:Issuer></saml:Assertion>"))
  "document type declaration"
-- Nesting deeper than `maxDepth` is refused before parsing.
#guard refusedWith (b64 (String.join (List.replicate 40 "<a>") ++ String.join (List.replicate 40 "</a>"))) "nests"
#guard nestingOk "<a><b/><c></c><!-- x --><?p?></a>".toList 0

-- An encrypted assertion is refused, naming the issue, when no decryption
-- key is configured (`validate` takes none; `validateWith` below).
#guard refusedWith (b64 ("<saml:EncryptedAssertion xmlns:saml=\"" ++ samlNs ++ "\"/>")) encryptionIssue
-- A declared encoding other than UTF-8.
#guard refusedWith (b64 "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?><a/>") "encoding"
-- Not SAML 2.0.
#guard refusedWith (b64 ("<saml:Assertion xmlns:saml=\"" ++ samlNs ++ "\" ID=\"_1\" Version=\"1.1\"/>"))
  "SAML 2.0"

/-! ## Through the authorization server -/

open L4Factoidal.Authz in
def ctxSaml (idps : List Idp) : Ctx :=
  { C := { L4Factoidal.Authz.Tests.stub with verifiers := { L4Factoidal.Authz.Tests.stub.verifiers with rs256 := rsa } }
    issuer := "https://as.example", now := 1761313610, samlIdps := idps }

open L4Factoidal.Authz in
#guard validateSubject (ctxSaml [idp]) tokenTypeSaml2 valid
  == .valid "https://id.example/end-user" "https://app.example/SAML"
open L4Factoidal.Authz in
#guard (match validateSubject (ctxSaml []) tokenTypeSaml2 valid with
  | .refused w => (w.splitOn "trusts no SAML identity provider").length == 2
  | _ => false)
open L4Factoidal.Authz in
#guard (match validateSubject (ctxSaml [idp]) tokenTypeSaml2 altered with
  | .refused _ => true
  | _ => false)

/-! ## Encrypted assertions (https://github.com/danbri/factoidal/issues/1073)

The JDK's signed assertions, encrypted here with the stub cipher and stub
primitives of `XML/EncTests.lean` (not cryptography). Real AES-GCM and
RSA-OAEP over Apache Santuario's encryption: `lake exe l4xmlenc-probe`. -/

open L4Factoidal.XML.EncTests (stubCipher stubPrims rsaN rand)
open L4Factoidal.XML
open L4Factoidal.XML.DSig (elOf? El)
open L4Factoidal.XML.Canonical (rootScope)

def encKeys : L4Factoidal.XML.Enc.Keys := { rsa := L4Factoidal.XML.EncTests.keys.rsa }

def encPolicy : Policy := { policy with decryptKeys := encKeys }

def rsaSpec (sha256 : Bool := false) : L4Factoidal.XML.Enc.EncryptSpec :=
  { recipient := .rsa (some "rsa-1") rsaN ByteArray.empty sha256 }

/-- The assertion of token `t` in a `saml:EncryptedAssertion`, as a token. -/
def encryptedToken (t : String) (spec : L4Factoidal.XML.Enc.EncryptSpec := rsaSpec) : String :=
  match decodeToken t with
  | .ok d =>
      match L4Factoidal.XML.Enc.encryptNode stubCipher stubPrims spec rand d.root with
      | .ok ed =>
          b64 (L4Factoidal.XML.Enc.serNode ""
            (.element "saml:EncryptedAssertion" [{ name := "xmlns:saml", value := samlNs }] [ed]))
      | .error _ => ""
  | .error _ => ""

def okEnc? (t : String) (p : Policy := encPolicy)
    (cipher : L4Factoidal.Crypto.CipherCall.Cipher := stubCipher) : Option Claims :=
  match validateWith cipher stubPrims rsa p t with
  | .ok c => some c
  | .error _ => none

def refusedEnc (t frag : String) (p : Policy := encPolicy) : Bool :=
  match validateWith stubCipher stubPrims rsa p t with
  | .error (.refused w) => (w.splitOn frag).length ≥ 2
  | _ => false

-- Decrypted, then the same checks: the claims of the plain assertion.
#guard (okEnc? (encryptedToken valid)).isSome
#guard okEnc? (encryptedToken valid) == ok? valid
#guard okEnc? (encryptedToken valid (rsaSpec true)) == ok? valid
#guard okEnc? (encryptedToken inclusive) == ok? inclusive
-- A plain assertion through validateWith, keys or not.
#guard okEnc? valid == ok? valid
#guard okEnc? valid policy == ok? valid
-- No decryption key: refused, naming the issue, by both functions.
#guard refusedWith (encryptedToken valid) encryptionIssue
#guard refusedEnc (encryptedToken valid) encryptionIssue policy
-- The decrypted assertion must be signed, and signed by the trusted key.
#guard refusedEnc (encryptedToken unsigned) "exactly one ds:Signature"
#guard refusedEnc (encryptedToken altered) "digest"
#guard refusedEnc (encryptedToken attackerKey) "signature value does not verify"
#guard refusedEnc (encryptedToken wrapChild) "not a child of the document element"
-- A wrong RSA key: the one decryption error.
#guard refusedEnc (encryptedToken valid) L4Factoidal.XML.Enc.decryptionError
  { encPolicy with decryptKeys := { rsa := [{ kid := some "rsa-1", n := L4Factoidal.XML.EncTests.bytes 129 3, d := rsaN }] } }
-- With no answer yet, the AES request comes back unchanged.
#guard (match validateWith (L4Factoidal.Crypto.CipherCall.replayCipher []) stubPrims rsa encPolicy (encryptedToken valid) with
  | .error (.need r) => r.op == .gcmDecrypt
  | _ => false)
-- Expiry still applies to a decrypted assertion.
#guard refusedEnc (encryptedToken valid) "expired" { encPolicy with now := 1761313900 + 60 }

/-! ### saml:EncryptedID -/

/-- The assertion of `valid` with its `saml:NameID` in a `saml:EncryptedID`. -/
def withEncryptedId : Option El :=
  match decodeToken valid with
  | .error _ => none
  | .ok d =>
      let encId (n : Node) : Node :=
        match n with
        | .element "saml:NameID" .. =>
            match L4Factoidal.XML.Enc.encryptNode stubCipher stubPrims rsaSpec rand n with
            | .ok ed => .element "saml:EncryptedID" [] [ed]
            | .error _ => n
        | _ => n
      let inA (n : Node) : Node :=
        match n with
        | .element "saml:Subject" as ks => .element "saml:Subject" as (ks.map encId)
        | _ => n
      match d.root with
      | .element t as ks => elOf? rootScope (.element t as (ks.map inA))
      | _ => none

-- Refused without decryption, read after.
#guard match withEncryptedId with
  | some a =>
      (match claimsOf policy a "https://idp.example" with
        | .error w => (w.splitOn encryptionIssue).length == 2
        | .ok _ => false) &&
      (match decryptSubjectIds stubCipher stubPrims encKeys a with
        | .ok a' => (match claimsOf policy a' "https://idp.example" with
            | .ok c => c.nameId == "https://id.example/end-user"
            | .error _ => false)
        | .error _ => false)
  | none => false

/-! ### Expected failure: the authorization server has no decryption keys

XFAIL, https://github.com/danbri/factoidal/issues/1073: `Authz.validateSubject`
calls `SAML.validate`, which takes no decryption key, so `authz-serve`
refuses an encrypted SAML subject token. When the server is given
decryption keys and a cipher (`validateWith`), this guard fails and becomes
a positive check. -/

open L4Factoidal.Authz in
#guard (match validateSubject (ctxSaml [idp]) tokenTypeSaml2 (encryptedToken valid) with
  | .refused w => (w.splitOn encryptionIssue).length == 2
  | _ => false)

/-! ### Expected failure: saml:EncryptedAttribute

XFAIL, https://github.com/danbri/factoidal/issues/1073: an
`EncryptedAttribute` is refused, never skipped. When attributes are read and
decrypted, this guard fails and becomes a positive check. -/

#guard match decodeToken (b64 ("<saml:Assertion xmlns:saml=\"" ++ samlNs ++ "\" ID=\"_x\" Version=\"2.0\">" ++
    "<saml:AttributeStatement><saml:EncryptedAttribute/></saml:AttributeStatement></saml:Assertion>")) with
  | .ok d => match elOf? rootScope d.root with
    | some a => match claimsOf policy a "https://idp.example" with
      | .error w => (w.splitOn encryptionIssue).length == 2
      | .ok _ => false
    | none => false
  | .error _ => false

end L4Factoidal.SAML.Tests
