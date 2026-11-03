/-
L4Factoidal.XML.DSig11Sign — signature generation (XML Signature Syntax and
Processing Version 1.1, W3C Recommendation 11 April 2013, §3.1) over the
core validation of `L4Factoidal.XML.DSig11`
(https://github.com/danbri/factoidal/issues/1165, track B, item 4).

## Processing model (§3.1)

  * §3.1.1 Reference generation: for each reference of the `SignSpec`, the
    data object is dereferenced and transformed exactly as core validation
    does it (`DSig11.referenceOctets`, the same function), and its digest
    goes into `ds:DigestValue`.
  * §3.1.2 Signature generation: `ds:SignedInfo` (methods and references)
    is canonicalized in its place in the document (`DSig11.signedInfoOctets`,
    the same function) and the `Signer` signs those octets; the value goes
    into `ds:SignatureValue`.

The digests and the canonical `ds:SignedInfo` depend on where the
signature is: an inclusive method takes the namespaces of the ancestors.
So each step places the signature text in the document and parses the
result, and the octets always come from the document that is returned.

Placement: `enveloped` (the last child of the document element; the
references normally carry the enveloped-signature transform) or
`enveloping` (the signature is the document, and the content is in a
`ds:Object` with an `Id`).

## The signer (custodian)

A `Signer` is the custodian of one key (`docs/web/hub/webdav-lws-design.md`,
"One custodian per privileged resource"): it signs octets on request and
never gives the key out. This module sees its algorithm, its public key
(for `ds:KeyInfo` and the check) and its answers. The private-key forms are
made only in `XML/DSig11Native.lean` (`rsaSigner`, `p256Signer`) and by
`hmacSigner` here, whose key stays in its closure. The random octets of a
signature (the ECDSA nonce) are an argument of each `sign` call, never part
of the signer, so two signatures never share a nonce through the signer.

## Self-check

Before a signed document is returned, it is checked by core validation
(`DSig11.validateText`) with the signer's public key and `ds:KeyInfo` not
read; for HMAC, the references are checked and the custodian recomputes the
MAC. `dsig11_sign_validates` states that every returned document with a
public-key signer passes core validation, for every backend. The guarantee
comes from that run-time check, so it holds also when a reference would
cover the signature itself (that document is refused, not returned).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.DSig11
import L4Factoidal.XML.Enc

namespace L4Factoidal.XML.DSig11

open L4Factoidal.XML.C14n

/-! ## Algorithm identifiers (the inverses of the parsers) -/

def DigestAlg.uri : DigestAlg → String
  | .sha1 => "http://www.w3.org/2000/09/xmldsig#sha1"
  | .sha224 => "http://www.w3.org/2001/04/xmldsig-more#sha224"
  | .sha256 => "http://www.w3.org/2001/04/xmlenc#sha256"
  | .sha384 => "http://www.w3.org/2001/04/xmldsig-more#sha384"
  | .sha512 => "http://www.w3.org/2001/04/xmlenc#sha512"

def DigestAlg.suffix : DigestAlg → String
  | .sha1 => "sha1" | .sha224 => "sha224" | .sha256 => "sha256" | .sha384 => "sha384"
  | .sha512 => "sha512"

/-- The identifier of a signature method; `none` for DSA, which this tree
does not have (https://github.com/danbri/factoidal/issues/1224). -/
def SigAlg.uri? : SigAlg → Option String
  | .hmac .sha1 => some "http://www.w3.org/2000/09/xmldsig#hmac-sha1"
  | .hmac h => some s!"{dsMoreNs}hmac-{h.suffix}"
  | .rsa .sha1 => some "http://www.w3.org/2000/09/xmldsig#rsa-sha1"
  | .rsa h => some s!"{dsMoreNs}rsa-{h.suffix}"
  | .ecdsa h => some s!"{dsMoreNs}ecdsa-{h.suffix}"
  | .dsa _ => none

def _root_.L4Factoidal.XML.C14n.Method.uri (m : Method) : String :=
  let base := match m.version with
    | .c14n10 => "http://www.w3.org/TR/2001/REC-xml-c14n-20010315"
    | .c14n11 => "http://www.w3.org/2006/12/xml-c14n11"
    | .exc10 => "http://www.w3.org/2001/10/xml-exc-c14n#"
  if m.comments then
    if m.version == .exc10 then base ++ "WithComments" else base ++ "#WithComments"
  else base

def Curve.oid : Curve → String
  | .p256 => "urn:oid:1.2.840.10045.3.1.7"
  | .p384 => "urn:oid:1.3.132.0.34"
  | .p521 => "urn:oid:1.3.132.0.35"

theorem DigestAlg.ofUri_uri (h : DigestAlg) : DigestAlg.ofUri? h.uri = some h := by
  cases h <;> rfl

theorem SigAlg.ofUri_uri (a : SigAlg) (u : String) (hu : a.uri? = some u) :
    SigAlg.ofUri? u = some a := by
  rcases a with h | h | h | h <;> cases h <;> simp [SigAlg.uri?] at hu <;> subst hu <;> rfl

theorem Method.ofUri_uri_version (m : Method) :
    (Method.ofUri? m.uri).map (fun x => (x.version, x.comments)) = some (m.version, m.comments) := by
  rcases m with ⟨v, c, _⟩
  cases v <;> cases c <;> rfl

/-! ## The signer and the request -/

/-- The custodian of one signing key. `sign msg rand` answers the
signature value of `msg` (`rand`: fresh random octets, used as the ECDSA
nonce and ignored by HMAC and RSA), or `none` when it refuses. -/
structure Signer where
  alg : SigAlg
  /-- The public key; `none` for HMAC. -/
  publicKey : Option PublicKey
  sign : ByteArray → ByteArray → Option ByteArray

/-- An HMAC signer (§6.3). The key stays in the closure. -/
def hmacSigner (h : DigestAlg) (key : ByteArray) : Signer where
  alg := .hmac h
  publicKey := none
  sign := fun m _ => some (Crypto.hmacWith h.digest h.block key m)

/-- A transform of a reference (§6.6). -/
inductive TransformSpec where
  | enveloped
  | c14n (m : Method)
  | base64

structure RefSpec where
  /-- `""` (the document), `#id`, `#xpointer(/)` or `#xpointer(id('id'))`. -/
  uri : String
  transforms : List TransformSpec := []
  digest : DigestAlg := .sha256

inductive Placement where
  /-- The signature is the last child of the document element. -/
  | enveloped
  /-- The signature is the document; `content` (XML text) goes in a
      `ds:Object` with the ID `objectId`. -/
  | enveloping (objectId : String) (content : String)

structure SignSpec where
  c14n : Method := { version := .exc10 }
  refs : List RefSpec
  placement : Placement := .enveloped
  /-- Write the public key as `ds:KeyValue` in `ds:KeyInfo`. -/
  keyValue : Bool := true

/-! ## Text of the signature element -/

def esc (s : String) : String := L4Factoidal.XML.Canonical.escAttr s
def b64 (b : ByteArray) : String := L4Factoidal.XML.Enc.base64 b

/-- An `Algorithm`-carrying element of a method, with the PrefixList of
Exclusive canonicalization when there is one. -/
def methodEl (tag : String) (m : Method) : String :=
  let ps := if m.version == .exc10 && !m.inclusivePrefixes.isEmpty then
      s!"<ec:InclusiveNamespaces xmlns:ec=\"{excNs}\" PrefixList=\"{esc (" ".intercalate m.inclusivePrefixes)}\"/>"
    else ""
  s!"<ds:{tag} Algorithm=\"{esc m.uri}\">{ps}</ds:{tag}>"

def transformEl : TransformSpec → String
  | .enveloped => s!"<ds:Transform Algorithm=\"{envelopedAlg}\"/>"
  | .c14n m => methodEl "Transform" m
  | .base64 => s!"<ds:Transform Algorithm=\"{base64Alg}\"/>"

def referenceEl (r : RefSpec) (digest : ByteArray) : String :=
  let ts := if r.transforms.isEmpty then ""
    else "<ds:Transforms>" ++ String.join (r.transforms.map transformEl) ++ "</ds:Transforms>"
  s!"<ds:Reference URI=\"{esc r.uri}\">{ts}<ds:DigestMethod Algorithm=\"{r.digest.uri}\"/>" ++
    s!"<ds:DigestValue>{b64 digest}</ds:DigestValue></ds:Reference>"

def signedInfoEl (spec : SignSpec) (sigUri : String) (digests : List ByteArray) : String :=
  "<ds:SignedInfo>" ++ methodEl "CanonicalizationMethod" spec.c14n ++
    s!"<ds:SignatureMethod Algorithm=\"{sigUri}\"/>" ++
    String.join ((spec.refs.zip digests).map fun (r, d) => referenceEl r d) ++ "</ds:SignedInfo>"

/-- `ds:KeyInfo` with `ds:KeyValue` (§4.5.2): `ds:RSAKeyValue`, or
`dsig11:ECKeyValue` with a named curve and an uncompressed point. -/
def keyInfoEl : Option PublicKey → String
  | none => ""
  | some (.rsa n e) =>
      s!"<ds:KeyInfo><ds:KeyValue><ds:RSAKeyValue><ds:Modulus>{b64 n}</ds:Modulus>" ++
        s!"<ds:Exponent>{b64 e}</ds:Exponent></ds:RSAKeyValue></ds:KeyValue></ds:KeyInfo>"
  | some (.ec c xy) =>
      s!"<ds:KeyInfo><ds:KeyValue><dsig11:ECKeyValue xmlns:dsig11=\"{ds11Ns}\">" ++
        s!"<dsig11:NamedCurve URI=\"{c.oid}\"/><dsig11:PublicKey>{b64 (ByteArray.mk #[4] ++ xy)}" ++
        "</dsig11:PublicKey></dsig11:ECKeyValue></ds:KeyValue></ds:KeyInfo>"

def signatureEl (spec : SignSpec) (si : String) (value : ByteArray) (key : Option PublicKey) : String :=
  let obj := match spec.placement with
    | .enveloped => ""
    | .enveloping id content => s!"<ds:Object Id=\"{esc id}\">{content}</ds:Object>"
  s!"<ds:Signature xmlns:ds=\"{dsNs}\">{si}<ds:SignatureValue>{b64 value}</ds:SignatureValue>" ++
    keyInfoEl (if spec.keyValue then key else none) ++ obj ++ "</ds:Signature>"

/-! ## Placement -/

/-- Split off trailing white space. -/
def splitTrailingWs (s : String) : String × String :=
  let cs := s.toList
  let k := (cs.reverse.takeWhile isXmlWs).length
  (String.ofList (cs.take (cs.length - k)), String.ofList (cs.drop (cs.length - k)))

/-- The children of the document node: node 0's children. -/
def docChildren (cd : C14nDoc) : List Nat := (cd.doc.get 0).children.toList

/-- Put `sig` as the last child of the document element of `src`. Refused
when a comment or processing instruction follows the document element (the
end tag is then not the end of the text). -/
def insertEnveloped (src sig : String) : Except String String := do
  let cd ← C14nDoc.ofString? src
  let kids := docChildren cd
  let some root := kids.find? (fun i => kindOf cd.doc i == .element)
    | throw "the document has no document element"
  let after := kids.dropWhile (· != root) |>.drop 1
  if !after.isEmpty then throw "a comment or processing instruction follows the document element; put the signature by hand"
  let (core, ws) := splitTrailingWs src
  let qn := qnameText (cd.doc.get root).name
  if core.endsWith "/>" then
    return (core.dropEnd 2).toString ++ ">" ++ sig ++ "</" ++ qn ++ ">" ++ ws
  let parts := core.splitOn "</"
  if parts.length < 2 then throw "the end tag of the document element was not found"
  return "</".intercalate parts.dropLast ++ sig ++ "</" ++ parts.getLast! ++ ws

def place (spec : SignSpec) (src sig : String) : Except String String :=
  match spec.placement with
  | .enveloped => insertEnveloped src sig
  | .enveloping .. => .ok sig

/-- The one `ds:Signature` of a document, parsed. -/
def theSignature (out : String) : Except String (C14nDoc × Signature) := do
  let cd ← C14nDoc.ofString? out
  match signatures cd with
  | [s] => return (cd, ← parseSignature cd.doc s)
  | [] => throw "the document has no ds:Signature"
  | _ => throw "the document already has a ds:Signature; signing another is not supported"

/-! ## Generation (§3.1) -/

/-- The digests of the references, in the document with the signature
`sigText` in place. -/
def digestsIn (spec : SignSpec) (src sigText : String) : Except String (List ByteArray) := do
  let d0 ← place spec src sigText
  let (cd, s) ← theSignature d0
  s.si.refs.mapM fun r => do
    let o ← referenceOctets {} cd s.node r
    return r.digest.digest o

/-- The self-check of a signed document. -/
def selfCheck (be : Backend) (sg : Signer) (out : String) : Except String Unit :=
  match sg.publicKey with
  | some pk =>
      match validateText be { key := some pk, keyFromKeyInfo := false } out with
      | .ok _ => .ok ()
      | .error e => .error s!"the signed document does not validate: {e}"
  | none => do
      let (cd, s) ← theSignature out
      let _ ← checkRefsAcc (referenceOctets {} cd s.node) s.si.refs []
      let siC ← signedInfoOctets cd s
      if sg.sign siC.toUTF8 ByteArray.empty == some s.value then pure ()
      else throw "the signed document does not validate: the MAC does not match"

/-- The signed document before its self-check: §3.1.1, then §3.1.2. -/
def signUnchecked (sg : Signer) (spec : SignSpec) (rand : ByteArray) (src : String) :
    Except String String := do
  let some sigUri := sg.alg.uri? | throw "DSA is not supported (https://github.com/danbri/factoidal/issues/1224)"
  if spec.refs.isEmpty then throw "a signature needs at least one reference (§4.4)"
  let zeros := spec.refs.map fun _ => ByteArray.empty
  -- §3.1.1: digests, with the signature in place
  let digests ← digestsIn spec src (signatureEl spec (signedInfoEl spec sigUri zeros) .empty sg.publicKey)
  let si := signedInfoEl spec sigUri digests
  -- §3.1.2: the canonical SignedInfo, in place
  let d1 ← place spec src (signatureEl spec si .empty sg.publicKey)
  let (cd1, s1) ← theSignature d1
  let siC ← signedInfoOctets cd1 s1
  let some value := sg.sign siC.toUTF8 rand | throw "the signer refused"
  place spec src (signatureEl spec si value sg.publicKey)

/-- Sign `src` (for `enveloping`, `src` is ignored) by `spec` with the
custodian `sg`; `rand` is fresh random octets for the signer. The result
has passed `selfCheck`. -/
def sign (be : Backend) (sg : Signer) (spec : SignSpec) (rand : ByteArray) (src : String) :
    Except String String :=
  match signUnchecked sg spec rand src with
  | .error e => .error e
  | .ok out =>
      match selfCheck be sg out with
      | .ok () => .ok out
      | .error e => .error e

/-! ## Theorems -/

/-- §3.1 and §3.2, XML Signature 1.1 (2013): a document that `sign`
returns for a public-key signer passes core validation with that public key
(and `ds:KeyInfo` not read), for every backend. -/
theorem dsig11_sign_validates {be : Backend} {sg : Signer} {spec : SignSpec} {rand : ByteArray}
    {src out : String} {pk : PublicKey} (hk : sg.publicKey = some pk)
    (h : sign be sg spec rand src = .ok out) :
    ∃ v, validateText be { key := some pk, keyFromKeyInfo := false } out = .ok v := by
  unfold sign at h
  cases hu : signUnchecked sg spec rand src with
  | error e => rw [hu] at h; cases h
  | ok o =>
      rw [hu] at h
      dsimp only at h
      cases hs : selfCheck be sg o with
      | error e => rw [hs] at h; cases h
      | ok u =>
          rw [hs] at h
          cases h
          unfold selfCheck at hs
          rw [hk] at hs
          dsimp only at hs
          cases hv : validateText be { key := some pk, keyFromKeyInfo := false } out with
          | ok v => exact ⟨v, rfl⟩
          | error e => rw [hv] at hs; cases hs

/-- An HMAC signer's value is the HMAC of §6.3 with its key, which is
what `DSig11.checkMac` compares with no `HMACOutputLength`. -/
theorem ctDiffFrom_self (a : ByteArray) : ∀ n i, Crypto.ctDiffFrom a a n i 0 = 0
  | 0, _ => rfl
  | n + 1, i => by
      have hx : ∀ x : UInt8, ((0 : UInt8) ||| (x ^^^ x)) = 0 := by
        intro x; simp
      simp only [Crypto.ctDiffFrom, hx]
      exact ctDiffFrom_self a n (i + 1)

theorem ctEqBytes_self (a : ByteArray) : Crypto.ctEqBytes a a = true := by
  simp [Crypto.ctEqBytes, ctDiffFrom_self]

theorem dsig11_hmacSigner_checks (h : DigestAlg) (key msg rand : ByteArray) :
    ∃ v, (hmacSigner h key).sign msg rand = some v ∧ checkMac h key none msg v = .ok true := by
  refine ⟨_, rfl, ?_⟩
  simp [checkMac, ctEqBytes_self]

/-! ## Checks -/

#guard (SigAlg.rsa .sha256).uri? == some "http://www.w3.org/2001/04/xmldsig-more#rsa-sha256"
#guard (SigAlg.hmac .sha1).uri? == some "http://www.w3.org/2000/09/xmldsig#hmac-sha1"
#guard Method.uri { version := .exc10, comments := true } == "http://www.w3.org/2001/10/xml-exc-c14n#WithComments"
#guard splitTrailingWs "<a/>\n " == ("<a/>", "\n ")
#guard insertEnveloped "<a x=\"1\"/>\n" "<s/>" == .ok "<a x=\"1\"><s/></a>\n"
#guard insertEnveloped "<p:a xmlns:p=\"u\"><b/></p:a >" "<s/>" == .ok "<p:a xmlns:p=\"u\"><b/><s/></p:a >"
#guard (insertEnveloped "<a/><!--c-->" "<s/>").isOk == false

-- An enveloped HMAC-SHA256 signature made here validates with the key,
-- and not with another key.
def hmacSpec : SignSpec :=
  { refs := [{ uri := "", transforms := [.enveloped, .c14n { version := .exc10 }] }] }
def hmacOut : Except String String :=
  sign macOnly (hmacSigner .sha256 "secret".toUTF8) hmacSpec .empty
    "<doc xmlns=\"urn:x\"><a>one &amp; two</a><!--c--></doc>"
#guard (hmacOut.bind fun o => validateText macOnly { hmacKey := some "secret".toUTF8 } o).isOk
#guard !(hmacOut.bind fun o => validateText macOnly { hmacKey := some "other".toUTF8 } o).isOk
-- Enveloping, with an `#id` reference and inclusive canonicalization.
#guard ((sign macOnly (hmacSigner .sha512 "k".toUTF8)
    { c14n := { version := .c14n11 }, refs := [{ uri := "#obj", digest := .sha384 }],
      placement := .enveloping "obj" "<x:v xmlns:x=\"urn:v\">1</x:v>" } .empty "").bind
    fun o => validateText macOnly { hmacKey := some "k".toUTF8 } o).isOk
-- A reference to the whole document without the enveloped-signature
-- transform covers the signature value, so the self-check refuses it.
#guard !(sign macOnly (hmacSigner .sha256 "k".toUTF8) { refs := [{ uri := "" }] } .empty "<d/>").isOk

end L4Factoidal.XML.DSig11
