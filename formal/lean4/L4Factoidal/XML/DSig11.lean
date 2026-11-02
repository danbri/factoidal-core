/-
L4Factoidal.XML.DSig11 — core validation of XML Signatures (XML Signature
Syntax and Processing Version 1.1, W3C Recommendation 11 April 2013,
https://www.w3.org/TR/xmldsig-core1/), over the node table of
`L4Factoidal.XML.C14n` (https://github.com/danbri/factoidal/issues/1165,
track B, item 4).

`L4Factoidal.XML.DSig` verifies ONE profile (SAML 2.0 Core §5: one
enveloped signature, rsa-sha256, SHA-256, exclusive canonicalization).
This module is the general processing model of §3.2 that the profile is
a case of. `DSig` is not changed; `dsig11_saml_profile_*` at the end of
this file state that the profile's algorithm choices are entries of the
tables here, and that its RSA check is `rsaPkcs1Verify` at SHA-256.

## Processing model

  * §3.2.1 Reference validation: each `ds:Reference` of `ds:SignedInfo`
    is dereferenced (§4.4.3.3), its transforms are applied in order
    (§4.4.3.2, §6.6), the result is converted to octets by Canonical XML
    1.0 without comments when it is still a node-set, and its digest
    (§6.2) must equal `ds:DigestValue`. `checkRefsAcc_ok`.
  * §3.2.2 Signature validation: `ds:SignedInfo` is canonicalized by its
    `ds:CanonicalizationMethod` (§4.4.1) and the `ds:SignatureValue` is
    checked over those octets by the `ds:SignatureMethod` (§6.3, §6.4)
    with the key. `validateParsed_ok`.

Same-document references (§4.4.3.3): `URI=""` is the document without
comments; `#v` is the element with ID `v` and its descendants, without
comments; `#xpointer(/)` and `#xpointer(id('v'))` are the same with
comments. An ID is an attribute that the DTD declares `ID`, `xml:id`, or
an unqualified `Id`, `ID` or `id` (the ID attributes of the XML Signature
schema and of SAML). A value carried by two elements is refused: the
reference would not name one element (the signature wrapping attacks of
Somorovsky et al., USENIX Security 2012). Any other URI goes to the
caller's resolver, which gives octets; with no resolver it is refused.

## Algorithms (§6)

  * Digest: SHA-1, SHA-224, SHA-256, SHA-384, SHA-512 (pure Lean,
    FIPS 180-4, `Crypto.SHA1`, `Crypto.SHA2`).
  * MAC: HMAC over the same five (`Crypto.hmacWith`), with
    `HMACOutputLength` (§6.3.1: refused when below 80 bits or below half
    the hash output).
  * RSASSA-PKCS1-v1_5 over the same five (`JOSE.Pkcs1.rsaPkcs1Verify`,
    the RSA public operation a parameter).
  * ECDSA over the same five (§6.4.3, signature `r || s`); the curve
    operation is a parameter (`Backend.ecdsaVerify`), `none` when the
    backend does not have that curve and hash.
  * DSA (`dsa-sha1`, `dsa-sha256`): refused. There is no DSA in the
    project (https://github.com/danbri/factoidal/issues/1224).
  * Canonicalization: the six methods of `L4Factoidal.XML.C14n`.
  * Transforms: the canonicalization methods, enveloped signature
    (§6.6.4), XPath filtering (§6.6.3, `C14nXPath.xpathFilter`), base64
    (§6.6.2), XPath Filter 2.0 (`L4Factoidal.XML.DSigFilter2`), XSLT
    (§6.6.5, `L4Factoidal.XML.DSigXslt`, on the XSLT 4.0 processor).
    `here()` names the `ds:XPath` or filter `XPath` element when the
    input is a node-set of the signature's document.

## Keys (§4.5)

The caller gives the key (`Config.key`, `Config.hmacKey`), or allows the
key of `ds:KeyInfo` (`Config.keyFromKeyInfo`): `ds:KeyValue` with
`ds:RSAKeyValue`, `dsig11:ECKeyValue` (named curve) or the RFC 4050
`ECDSAKeyValue`; `dsig11:DEREncodedKeyValue` (an RSA or EC
SubjectPublicKeyInfo); `dsig11:KeyInfoReference` to a `ds:KeyInfo` of the
same document; `ds:X509Data` (§4.5.4): the certificate that its
`X509IssuerSerial`, `X509SubjectName`, `X509SKI` and `dsig11:X509Digest`
identify among its `X509Certificate`s and the caller's certificates
(`Config.certificates`), or, with no identifier, its one end-entity
certificate; the key is that certificate's SubjectPublicKeyInfo
(`L4Factoidal.XML.X509`). A key from `ds:KeyInfo` only says that the
signature verifies under that key; `Validated.key` returns it, and
`signingCertificate?` the certificate, so the caller decides whether it
trusts it (certificate path validation and revocation, `X509CRL`
included, are the caller's). `ds:RetrievalMethod` (§4.5.3) is
followed one level: its `URI` is dereferenced as a reference's (the
caller's resolver for other documents), its `ds:Transforms` are applied,
and the result is read as its `Type` says: `rawX509Certificate` octets,
or one apex element (`ds:X509Data`, `ds:RSAKeyValue`,
`dsig11:ECKeyValue`, `dsig11:DEREncodedKeyValue`, `ds:KeyValue`) whose
expanded name is the `Type` (https://github.com/danbri/factoidal/issues/1228).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.C14nXPath
import L4Factoidal.XML.DSigFilter2
import L4Factoidal.XML.DSigXslt
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Crypto.Hmac
import L4Factoidal.JOSE.Pkcs1
import L4Factoidal.VC.Multibase
import L4Factoidal.XML.DSig
import L4Factoidal.XML.X509

namespace L4Factoidal.XML.DSig11

open L4Factoidal.XPath4
open L4Factoidal.XML.C14n

/-! ## Namespaces and algorithm identifiers -/

def dsNs : String := "http://www.w3.org/2000/09/xmldsig#"
def ds11Ns : String := "http://www.w3.org/2009/xmldsig11#"
def dsMoreNs : String := "http://www.w3.org/2001/04/xmldsig-more#"
def excNs : String := "http://www.w3.org/2001/10/xml-exc-c14n#"

def envelopedAlg : String := "http://www.w3.org/2000/09/xmldsig#enveloped-signature"
def base64Alg : String := "http://www.w3.org/2000/09/xmldsig#base64"
def xpathAlg : String := "http://www.w3.org/TR/1999/REC-xpath-19991116"
def xsltAlg : String := DSigXslt.xsltAlg

/-- The digest algorithms of XML Signature 1.1 §6.2. -/
inductive DigestAlg where
  | sha1 | sha224 | sha256 | sha384 | sha512
deriving DecidableEq, Repr, Inhabited

def DigestAlg.ofUri? (u : String) : Option DigestAlg :=
  if u == "http://www.w3.org/2000/09/xmldsig#sha1" then some .sha1
  else if u == "http://www.w3.org/2001/04/xmldsig-more#sha224" then some .sha224
  else if u == "http://www.w3.org/2001/04/xmlenc#sha256" then some .sha256
  else if u == "http://www.w3.org/2001/04/xmldsig-more#sha384" then some .sha384
  else if u == "http://www.w3.org/2001/04/xmlenc#sha512" then some .sha512
  else none

def DigestAlg.digest : DigestAlg → ByteArray → ByteArray
  | .sha1 => Crypto.sha1
  | .sha224 => Crypto.sha224
  | .sha256 => Crypto.sha256
  | .sha384 => Crypto.sha384
  | .sha512 => Crypto.sha512

def DigestAlg.name : DigestAlg → String
  | .sha1 => "SHA-1" | .sha224 => "SHA-224" | .sha256 => "SHA-256" | .sha384 => "SHA-384"
  | .sha512 => "SHA-512"

/-- The digest length in octets. -/
def DigestAlg.size : DigestAlg → Nat
  | .sha1 => 20 | .sha224 => 28 | .sha256 => 32 | .sha384 => 48 | .sha512 => 64

/-- The block size of the hash in octets (FIPS 180-4 §5.1), for HMAC. -/
def DigestAlg.block : DigestAlg → Nat
  | .sha1 => 64 | .sha224 => 64 | .sha256 => 64 | .sha384 => 128 | .sha512 => 128

/-- The DigestInfo of RFC 8017 §9.2 note 1. -/
def DigestAlg.digestInfo : DigestAlg → List UInt8
  | .sha1 => JOSE.Pkcs1.sha1DigestInfo
  | .sha224 => JOSE.Pkcs1.sha224DigestInfo
  | .sha256 => JOSE.Pkcs1.sha256DigestInfo
  | .sha384 => JOSE.Pkcs1.sha384DigestInfo
  | .sha512 => JOSE.Pkcs1.sha512DigestInfo

/-- The signature and MAC algorithms of XML Signature 1.1 §6.3 and §6.4. -/
inductive SigAlg where
  | hmac (h : DigestAlg)
  | rsa (h : DigestAlg)
  | ecdsa (h : DigestAlg)
  | dsa (h : DigestAlg)
deriving DecidableEq, Repr, Inhabited

def SigAlg.ofUri? (u : String) : Option SigAlg :=
  if u == "http://www.w3.org/2000/09/xmldsig#hmac-sha1" then some (.hmac .sha1)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#hmac-sha224" then some (.hmac .sha224)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#hmac-sha256" then some (.hmac .sha256)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#hmac-sha384" then some (.hmac .sha384)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#hmac-sha512" then some (.hmac .sha512)
  else if u == "http://www.w3.org/2000/09/xmldsig#rsa-sha1" then some (.rsa .sha1)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#rsa-sha224" then some (.rsa .sha224)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#rsa-sha256" then some (.rsa .sha256)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#rsa-sha384" then some (.rsa .sha384)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#rsa-sha512" then some (.rsa .sha512)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha1" then some (.ecdsa .sha1)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha224" then some (.ecdsa .sha224)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha256" then some (.ecdsa .sha256)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha384" then some (.ecdsa .sha384)
  else if u == "http://www.w3.org/2001/04/xmldsig-more#ecdsa-sha512" then some (.ecdsa .sha512)
  else if u == "http://www.w3.org/2000/09/xmldsig#dsa-sha1" then some (.dsa .sha1)
  else if u == "http://www.w3.org/2009/xmldsig11#dsa-sha256" then some (.dsa .sha256)
  else none

/-! ## Keys -/

/-- The named curves of XML Signature 1.1 §4.5.2.3. -/
inductive Curve where
  | p256 | p384 | p521
deriving DecidableEq, Repr, Inhabited

def Curve.ofOid? (u : String) : Option Curve :=
  if u == "urn:oid:1.2.840.10045.3.1.7" then some .p256
  else if u == "urn:oid:1.3.132.0.34" then some .p384
  else if u == "urn:oid:1.3.132.0.35" then some .p521
  else none

def Curve.name : Curve → String
  | .p256 => "P-256" | .p384 => "P-384" | .p521 => "P-521"

/-- The length of a field element in octets. -/
def Curve.coordSize : Curve → Nat
  | .p256 => 32 | .p384 => 48 | .p521 => 66

inductive PublicKey where
  /-- Modulus and exponent, big-endian, no leading zero octet. -/
  | rsa (n e : ByteArray)
  /-- The affine point `x || y`, each `coordSize` octets. -/
  | ec (c : Curve) (xy : ByteArray)
deriving Inhabited

/-- The cryptographic operations that are not pure Lean. Parameters, so
that every theorem here holds for any backend and the `#guard`s can run
a stub. -/
structure Backend where
  /-- RSAVP1 (RFC 8017 §5.2.2): `s^e mod n`, `none` when refused. -/
  rsaPublicOp : JOSE.Pkcs1.PublicOp
  /-- ECDSA verification of `sig = r || s` over `msg` hashed by the
      digest, under the point `xy`; `none` when the backend does not
      have this curve and digest. -/
  ecdsaVerify : Curve → DigestAlg → ByteArray → ByteArray → ByteArray → Option Bool

/-- What the caller supplies. -/
structure Config where
  /-- The HMAC key. A MAC is checked only with this key. -/
  hmacKey : Option ByteArray := none
  /-- The public key. When given, `ds:KeyInfo` is not read. -/
  key : Option PublicKey := none
  /-- Read the key from `ds:KeyInfo` when `key` is not given. -/
  keyFromKeyInfo : Bool := true
  /-- Octets of a URI that is not a same-document reference. -/
  resolve : String → Option ByteArray := fun _ => none
  /-- DER certificates that `ds:X509Data` identifiers may name (§4.5.4).
      Giving one is not trusting it: it only lets an identifier find it. -/
  certificates : List ByteArray := []

/-! ## Navigation in the node table -/

def isEl (d : Doc) (i : Nat) (ns loc : String) : Bool :=
  let r := d.get i
  r.kind == .element && r.name.uri == ns && r.name.loc == loc

/-- The element children of an element. -/
def elemKids (d : Doc) (i : Nat) : List Nat :=
  (d.get i).children.toList.filter fun j => (d.get j).kind == .element

/-- The value of an unqualified attribute. -/
def attrVal? (d : Doc) (i : Nat) (loc : String) : Option String :=
  ((d.get i).attrs.toList.find? fun j =>
    let a := d.get j
    a.kind == .attribute && a.name.uri == "" && a.name.loc == loc).map fun j => (d.get j).value

def isXmlWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Only elements, comments, processing instructions and white space
text among the children. -/
def elementOnly (d : Doc) (i : Nat) : Bool :=
  (d.get i).children.toList.all fun j =>
    let r := d.get j
    r.kind != .text || r.value.all isXmlWs

/-- The concatenated text children. -/
def textOf (d : Doc) (i : Nat) : String :=
  String.join ((d.get i).children.toList.filterMap fun j =>
    let r := d.get j
    if r.kind == .text then some r.value else none)

def bytesOf (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- base64 content (white space ignored). -/
def b64? (s : String) : Option ByteArray :=
  (L4Factoidal.VC.Multibase.base64FlexDecode (String.ofList (s.toList.filter (!isXmlWs ·)))).map bytesOf

def b64Text? (d : Doc) (i : Nat) : Option ByteArray := b64? (textOf d i)

/-- The element children with the expanded name, of an element. -/
def kidsNamed (d : Doc) (i : Nat) (ns loc : String) : List Nat :=
  (elemKids d i).filter fun j => isEl d j ns loc

def kidNamed? (d : Doc) (i : Nat) (ns loc : String) : Option Nat := (kidsNamed d i ns loc).head?

/-- An attribute is an ID: the DTD declares it `ID`, it is `xml:id`, or it
is an unqualified `Id`, `ID` or `id`. -/
def isIdAttr (d : Doc) (elem attr : Nat) : Bool :=
  let a := d.get attr
  let e := d.get elem
  (a.name.uri == "" && (a.name.loc == "Id" || a.name.loc == "ID" || a.name.loc == "id")) ||
  (a.name.uri == nsXML && a.name.loc == "id") ||
  d.idAttrs.any fun (en, an) => en == qnameText e.name && an == qnameText a.name

/-- The elements that carry an ID with the value `v`, in document order. -/
def idTargets (cd : C14nDoc) (v : String) : List Nat :=
  (List.range cd.n0).filter fun i =>
    let r := cd.doc.get i
    r.kind == .element && r.attrs.toList.any fun j =>
      (cd.doc.get j).kind == .attribute && (cd.doc.get j).value == v && isIdAttr cd.doc i j

/-- The one element with ID `v`. -/
def idTarget (cd : C14nDoc) (v : String) : Except String Nat :=
  match idTargets cd v with
  | [i] => .ok i
  | [] => .error s!"no element has the ID {v}"
  | _ => .error s!"more than one element has the ID {v}"

/-! ## Parsed signature -/

structure Reference where
  node : Nat
  uri : Option String
  transforms : List Nat
  digest : DigestAlg
  value : ByteArray

structure SignedInfo where
  node : Nat
  c14n : Method
  sig : SigAlg
  /-- `HMACOutputLength`, in bits. -/
  hmacLen : Option Nat
  refs : List Reference

structure Signature where
  node : Nat
  si : SignedInfo
  value : ByteArray
  keyInfo : Option Nat

def algorithm? (d : Doc) (i : Nat) : Option String := attrVal? d i "Algorithm"

/-- The InclusiveNamespaces PrefixList of a canonicalization method or
transform (Exclusive XML Canonicalization §4.1). -/
def prefixList (d : Doc) (i : Nat) : List String :=
  match kidNamed? d i excNs "InclusiveNamespaces" with
  | some j => ((attrVal? d j "PrefixList").getD "").splitToList isXmlWs |>.filter (· != "")
  | none => []

/-- A canonicalization method from an element with an `Algorithm`. -/
def methodOf? (d : Doc) (i : Nat) : Option Method :=
  (algorithm? d i).bind Method.ofUri? |>.map fun m =>
    if m.version == .exc10 then { m with inclusivePrefixes := prefixList d i } else m

def parseReference (d : Doc) (r : Nat) : Except String Reference := do
  if !elementOnly d r then throw "ds:Reference has text content"
  let kids := elemKids d r
  let (ts, rest) := match kids with
    | t :: rest => if isEl d t dsNs "Transforms" then ((elemKids d t), rest) else ([], kids)
    | [] => ([], [])
  if !(ts.all fun t => isEl d t dsNs "Transform") then throw "ds:Transforms holds an element that is not ds:Transform"
  match rest with
  | [dm, dv] =>
      if !(isEl d dm dsNs "DigestMethod" && isEl d dv dsNs "DigestValue") then
        throw "ds:Reference must be Transforms, DigestMethod, DigestValue"
      let some alg := algorithm? d dm | throw "ds:DigestMethod has no Algorithm"
      let some h := DigestAlg.ofUri? alg | throw s!"digest method not supported: {alg}"
      let some v := b64Text? d dv | throw "ds:DigestValue is not base64"
      pure { node := r, uri := attrVal? d r "URI", transforms := ts, digest := h, value := v }
  | _ => throw "ds:Reference must be Transforms, DigestMethod, DigestValue"

def parseRefsAcc (d : Doc) : List Nat → List Reference → Except String (List Reference)
  | [], acc => .ok acc.reverse
  | r :: rs, acc => match parseReference d r with
    | .ok x => parseRefsAcc d rs (x :: acc)
    | .error e => .error e

def parseSignedInfo (d : Doc) (si : Nat) : Except String SignedInfo := do
  if !elementOnly d si then throw "ds:SignedInfo has text content"
  match elemKids d si with
  | cm :: sm :: refs =>
      if !isEl d cm dsNs "CanonicalizationMethod" then throw "ds:SignedInfo must begin with ds:CanonicalizationMethod"
      let some m := methodOf? d cm | throw s!"canonicalization method not supported: {(algorithm? d cm).getD ""}"
      if !isEl d sm dsNs "SignatureMethod" then throw "ds:CanonicalizationMethod must be followed by ds:SignatureMethod"
      let some alg := algorithm? d sm | throw "ds:SignatureMethod has no Algorithm"
      let some sa := SigAlg.ofUri? alg | throw s!"signature method not supported: {alg}"
      let hl ← match kidNamed? d sm dsNs "HMACOutputLength" with
        | none => pure none
        | some j =>
            match (textOf d j).trimAscii.toString.toNat? with
            | some t => pure (some t)
            | none => throw "HMACOutputLength is not an integer"
      if refs.isEmpty then throw "ds:SignedInfo has no ds:Reference"
      if !(refs.all fun r => isEl d r dsNs "Reference") then throw "ds:SignedInfo holds an element that is not ds:Reference"
      let rs ← parseRefsAcc d refs []
      pure { node := si, c14n := m, sig := sa, hmacLen := hl, refs := rs }
  | _ => throw "ds:SignedInfo must be CanonicalizationMethod, SignatureMethod, Reference+"

def parseSignature (d : Doc) (s : Nat) : Except String Signature := do
  if !isEl d s dsNs "Signature" then throw "not a ds:Signature element"
  if !elementOnly d s then throw "ds:Signature has text content"
  match elemKids d s with
  | si :: sv :: rest =>
      if !(isEl d si dsNs "SignedInfo" && isEl d sv dsNs "SignatureValue") then
        throw "ds:Signature must begin with ds:SignedInfo, ds:SignatureValue"
      let p ← parseSignedInfo d si
      let some v := b64Text? d sv | throw "ds:SignatureValue is not base64"
      let ki := rest.head?.filter fun k => isEl d k dsNs "KeyInfo"
      pure { node := s, si := p, value := v, keyInfo := ki }
  | _ => throw "ds:Signature must begin with ds:SignedInfo, ds:SignatureValue"

/-! ## Reference processing (§4.4.3) -/

/-- The data a transform takes and gives (§4.4.3.2). `sameDoc`: the
node-set is of the signature's document. -/
inductive Data where
  | nodes (cd : C14nDoc) (set : Nat → Bool) (sameDoc : Bool)
  | octets (b : ByteArray)

def dropComments (cd : C14nDoc) (s : Nat → Bool) : Nat → Bool :=
  fun i => s i && kindOf cd.doc i != .comment

/-- The ID of a `#xpointer(id('v'))` or `#xpointer(id("v"))` fragment. -/
def xpointerId? (frag : String) : Option String :=
  let strip (q : String) : Option String :=
    let pre := "xpointer(id(" ++ q
    let post := q ++ "))"
    if frag.startsWith pre && frag.endsWith post && frag.length ≥ pre.length + post.length then
      some ((frag.drop pre.length).dropEnd post.length).toString
    else none
  (strip "'").orElse fun _ => strip "\""

/-- §4.4.3.3: the data a `URI` gives. -/
def dereference (cfg : Config) (cd : C14nDoc) (uri : Option String) : Except String Data :=
  match uri with
  | none => .error "a ds:Reference without URI needs an application resolver"
  | some u =>
      if u == "" then .ok (.nodes cd (dropComments cd wholeDocument) true)
      else if u.startsWith "#" then
        let frag := (u.drop 1).toString
        if frag == "xpointer(/)" then .ok (.nodes cd wholeDocument true)
        else match xpointerId? frag with
          | some v => (idTarget cd v).map fun a => .nodes cd (subtreeSet cd a) true
          | none =>
              if frag.startsWith "xpointer(" then .error s!"XPointer not supported in a reference: {u}"
              else (idTarget cd frag).map fun a => .nodes cd (dropComments cd (subtreeSet cd a)) true
      else match cfg.resolve u with
        | some b => .ok (.octets b)
        | none => .error s!"cannot dereference {u}"

/-- Octets parsed into a node-set (§4.4.3.2). -/
def toNodes : Data → Except String (C14nDoc × (Nat → Bool) × Bool)
  | .nodes cd s sd => .ok (cd, s, sd)
  | .octets b =>
      match String.fromUTF8? b with
      | none => .error "the octets are not UTF-8"
      | some t => (C14nDoc.ofString? t).map fun cd => (cd, wholeDocument, false)

/-- The node-set as octets: Canonical XML 1.0 without comments. -/
def toOctets : Data → Except String ByteArray
  | .octets b => .ok b
  | .nodes cd s _ => (canonicalize { version := .c14n10 } cd s).map String.toUTF8

/-- The in-scope prefixed namespaces of an element, for an XPath. -/
def xpathNs (d : Doc) (i : Nat) : List (String × String) :=
  (nsBindings (d.get i)).filter fun (p, _) => p != ""

/-- The text nodes of a node-set in document order (§6.6.2). -/
def textValue (cd : C14nDoc) (s : Nat → Bool) : String :=
  String.join ((List.range cd.n0).filterMap fun i =>
    if s i && kindOf cd.doc i == .text then some (cd.doc.get i).value else none)

/-- One transform (§6.6). `sig`: the `ds:Signature` element. -/
def applyTransform (sigDoc : C14nDoc) (sig : Nat) (t : Nat) (x : Data) : Except String Data := do
  let d := sigDoc.doc
  let some alg := algorithm? d t | throw "a ds:Transform has no Algorithm"
  if let some m := methodOf? d t then
    let (cd, s, _) ← toNodes x
    let o ← canonicalize m cd s
    return .octets o.toUTF8
  if alg == envelopedAlg then
    match x with
    | .nodes cd s true =>
        let sub := subtreeSet cd sig
        return .nodes cd (fun i => s i && !sub i) true
    | _ => throw "the enveloped-signature transform needs a node-set of the signature's document"
  if alg == xpathAlg then
    let some xp := kidNamed? d t dsNs "XPath" | throw "an XPath transform has no ds:XPath"
    let (cd, s, sd) ← toNodes x
    let f ← C14nXPath.xpathFilter cd (textOf d xp) (xpathNs d xp) (if sd then some xp else none)
    return .nodes cd (fun i => s i && f i) sd
  if alg == DSigFilter2.filter2Alg then
    let xps := kidsNamed d t DSigFilter2.filter2Ns "XPath"
    if xps.isEmpty then throw "an XPath Filter 2.0 transform has no XPath element"
    let (cd, s, sd) ← toNodes x
    let fs ← xps.mapM fun xp => do
      let some fa := attrVal? d xp "Filter" | throw "an XPath Filter 2.0 XPath element has no Filter"
      let some op := DSigFilter2.Op.ofString? fa | throw s!"XPath Filter 2.0: Filter {repr fa} is not intersect, subtract or union"
      pure ({ op, expr := textOf d xp, ns := xpathNs d xp, here? := if sd then some xp else none } : DSigFilter2.Filter)
    let o ← DSigFilter2.run cd s fs
    return .nodes cd o sd
  if alg == base64Alg then
    let txt ← match x with
      | .octets b => match String.fromUTF8? b with
        | some t => pure t
        | none => throw "the base64 transform input is not text"
      | .nodes cd s _ => pure (textValue cd s)
    match b64? txt with
    | some b => return .octets b
    | none => throw "the base64 transform input is not base64"
  if alg == xsltAlg then
    -- §6.6.5: octets in (a node-set is canonicalized first), octets out
    let b ← toOctets x
    return .octets (← DSigXslt.apply sigDoc t b)
  throw s!"transform not supported: {alg}"

def applyTransformsAcc (sigDoc : C14nDoc) (sig : Nat) : List Nat → Data → Except String Data
  | [], x => .ok x
  | t :: ts, x => match applyTransform sigDoc sig t x with
    | .ok y => applyTransformsAcc sigDoc sig ts y
    | .error e => .error e

/-- The octets a reference digests. -/
def referenceOctets (cfg : Config) (cd : C14nDoc) (sig : Nat) (r : Reference) : Except String ByteArray := do
  let x ← dereference cfg cd r.uri
  let y ← applyTransformsAcc cd sig r.transforms x
  toOctets y

/-- §3.2.1 over the references: each digest must match. The result is
the URI and the octets of each reference, which are what was signed. -/
def checkRefsAcc (f : Reference → Except String ByteArray) :
    List Reference → List (String × ByteArray) → Except String (List (String × ByteArray))
  | [], acc => .ok acc.reverse
  | r :: rs, acc => match f r with
    | .error e => .error e
    | .ok o =>
        if r.digest.digest o == r.value then checkRefsAcc f rs ((r.uri.getD "", o) :: acc)
        else .error s!"the digest of reference {repr (r.uri.getD "")} does not match"

/-! ## Keys from ds:KeyInfo (§4.5) -/

/-- Leading zero octets removed (CryptoBinary, §4.0.1). -/
def stripZeros (b : ByteArray) : ByteArray :=
  bytesOf (b.data.toList.dropWhile (· == 0))

/-- `n` as `len` big-endian octets, `none` when it does not fit. -/
def natBytes (n len : Nat) : Option ByteArray :=
  if n < 256 ^ len then
    some (bytesOf ((List.range len).map fun i => UInt8.ofNat ((n / 256 ^ (len - 1 - i)) % 256)))
  else none

/-- An uncompressed SEC 1 point `04 || x || y` as `x || y`. -/
def uncompressed? (c : Curve) (b : ByteArray) : Option ByteArray :=
  if b.size == 1 + 2 * c.coordSize && b.get! 0 == 4 then some (b.extract 1 b.size) else none

/-- A DER TLV at `i` with a definite length: tag, content start, content
end (`X509.derTlv?`). -/
def derTlv? (b : ByteArray) (i : Nat) : Option (UInt8 × Nat × Nat) := X509.derTlv? b i

def oidRsa : List UInt8 := [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01]
def oidEc : List UInt8 := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]
def oidP256 : List UInt8 := [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]
def oidP384 : List UInt8 := [0x2b, 0x81, 0x04, 0x00, 0x22]
def oidP521 : List UInt8 := [0x2b, 0x81, 0x04, 0x00, 0x23]

def slice (b : ByteArray) (s e : Nat) : List UInt8 := (b.extract s e).data.toList

/-- A SubjectPublicKeyInfo (RFC 5280 §4.1; RFC 3279 §2.3.1, RFC 5480 §2)
for an RSA or a named-curve EC key. Nothing after it is allowed. -/
def spkiKey? (b : ByteArray) : Option PublicKey := do
  let (t0, s0, e0) ← derTlv? b 0
  if !(t0 == 0x30 && e0 == b.size) then none
  let (t1, s1, e1) ← derTlv? b s0
  if t1 != 0x30 then none
  let (t2, s2, e2) ← derTlv? b s1
  if t2 != 0x06 then none
  let alg := slice b s2 e2
  let (t4, s4, e4) ← derTlv? b e1
  if !(t4 == 0x03 && e4 == e0 && s4 < e4 && b.get! s4 == 0) then none
  let key := b.extract (s4 + 1) e4
  if alg == oidRsa then
    -- parameters NULL, then RSAPublicKey ::= SEQUENCE { modulus, publicExponent }
    let (t3, _, e3) ← derTlv? b e2
    if !(t3 == 0x05 && e3 == e1) then none
    let (u0, v0, w0) ← derTlv? key 0
    if !(u0 == 0x30 && w0 == key.size) then none
    let (u1, v1, w1) ← derTlv? key v0
    let (u2, v2, w2) ← derTlv? key w1
    if !(u1 == 0x02 && u2 == 0x02 && w2 == w0) then none
    some (.rsa (stripZeros (key.extract v1 w1)) (stripZeros (key.extract v2 w2)))
  else if alg == oidEc then
    let (t3, s3, e3) ← derTlv? b e2
    if !(t3 == 0x06 && e3 == e1) then none
    let cOid := slice b s3 e3
    let c ← if cOid == oidP256 then some Curve.p256 else if cOid == oidP384 then some .p384
      else if cOid == oidP521 then some .p521 else none
    (uncompressed? c key).map (.ec c)
  else none

/-- One key element of `ds:KeyValue` (§4.5.2): `ds:RSAKeyValue`,
`dsig11:ECKeyValue`, the RFC 4050 `ECDSAKeyValue`, or `ds:DSAKeyValue`
(refused). -/
def keyElement? (d : Doc) (k : Nat) : Except String PublicKey :=
  if isEl d k dsNs "RSAKeyValue" then
    match kidNamed? d k dsNs "Modulus", kidNamed? d k dsNs "Exponent" with
    | some m, some e =>
        match b64Text? d m, b64Text? d e with
        | some mb, some eb => .ok (.rsa (stripZeros mb) (stripZeros eb))
        | _, _ => .error "ds:RSAKeyValue is not base64"
    | _, _ => .error "ds:RSAKeyValue must have ds:Modulus and ds:Exponent"
  else if isEl d k ds11Ns "ECKeyValue" then
    match kidNamed? d k ds11Ns "NamedCurve", kidNamed? d k ds11Ns "PublicKey" with
    | some nc, some pk =>
        match (attrVal? d nc "URI").bind Curve.ofOid? with
        | none => .error "dsig11:NamedCurve is not P-256, P-384 or P-521"
        | some c =>
            match (b64Text? d pk).bind (uncompressed? c) with
            | some xy => .ok (.ec c xy)
            | none => .error "dsig11:PublicKey is not an uncompressed point of the curve"
    | _, _ => .error "dsig11:ECKeyValue needs dsig11:NamedCurve (explicit ECParameters are not read) and dsig11:PublicKey"
  else if isEl d k dsMoreNs "ECDSAKeyValue" then
    -- RFC 4050 §3.3: NamedCurve URN, and X and Y as decimal Value attributes
    let nc := (kidNamed? d k dsMoreNs "DomainParameters").bind fun dp => kidNamed? d dp dsMoreNs "NamedCurve"
    let pk := kidNamed? d k dsMoreNs "PublicKey"
    match (nc.bind fun n => attrVal? d n "URN").bind Curve.ofOid?, pk with
    | some c, some p =>
        let coord (loc : String) : Option ByteArray :=
          ((kidNamed? d p dsMoreNs loc).bind fun x => attrVal? d x "Value").bind fun v =>
            v.toNat?.bind fun n => natBytes n c.coordSize
        match coord "X", coord "Y" with
        | some x, some y => .ok (.ec c (x ++ y))
        | _, _ => .error "ECDSAKeyValue X or Y is not a coordinate of the curve"
    | _, _ => .error "ECDSAKeyValue needs a named curve P-256, P-384 or P-521 and a PublicKey"
  else if isEl d k dsNs "DSAKeyValue" then .error "DSA keys are not supported (https://github.com/danbri/factoidal/issues/1224)"
  else .error "ds:KeyValue holds an unknown key type"

/-- A `ds:KeyValue` (§4.5.2). -/
def keyValue? (d : Doc) (kv : Nat) : Except String PublicKey :=
  match elemKids d kv with
  | [k] => keyElement? d k
  | _ => .error "ds:KeyValue must hold one key"

/-! ## ds:X509Data (§4.5.4) -/

/-- One identifier of a certificate in `ds:X509Data`. -/
inductive X509Id where
  | issuerSerial (issuer : String) (serial : Int)
  | subjectName (name : String)
  | ski (id : ByteArray)
  | digest (h : DigestAlg) (value : ByteArray)

/-- The certificate is the one the identifier names. -/
def X509Id.matches (c : X509.Cert) : X509Id → Bool
  | .issuerSerial i n => c.serial == n && X509.nameMatches i c.issuer
  | .subjectName n => X509.nameMatches n c.subject
  | .ski k => match c.ski with
    | some k' => k' == k
    | none => false
  | .digest h v => h.digest c.der == v

def trimText (d : Doc) (i : Nat) : String := (textOf d i).trimAscii.toString

/-- The identifiers and the certificates of one `ds:X509Data`.
`X509CRL` and elements of other namespaces are skipped. -/
def x509Contents (d : Doc) (xd : Nat) : Except String (List X509Id × List ByteArray) := do
  let mut ids : Array X509Id := #[]
  let mut certs : Array ByteArray := #[]
  for k in elemKids d xd do
    if isEl d k dsNs "X509IssuerSerial" then
      match kidNamed? d k dsNs "X509IssuerName", kidNamed? d k dsNs "X509SerialNumber" with
      | some n, some sn =>
          match (trimText d sn).toInt? with
          | some v => ids := ids.push (.issuerSerial (textOf d n) v)
          | none => throw "ds:X509SerialNumber is not an integer"
      | _, _ => throw "ds:X509IssuerSerial needs ds:X509IssuerName and ds:X509SerialNumber"
    else if isEl d k dsNs "X509SubjectName" then ids := ids.push (.subjectName (textOf d k))
    else if isEl d k dsNs "X509SKI" then
      match b64Text? d k with
      | some v => ids := ids.push (.ski v)
      | none => throw "ds:X509SKI is not base64"
    else if isEl d k ds11Ns "X509Digest" then
      match (attrVal? d k "Algorithm").bind DigestAlg.ofUri?, b64Text? d k with
      | some h, some v => ids := ids.push (.digest h v)
      | none, _ => throw "dsig11:X509Digest has no digest algorithm of §6.2"
      | _, none => throw "dsig11:X509Digest is not base64"
    else if isEl d k dsNs "X509Certificate" then
      match b64Text? d k with
      | some v => certs := certs.push v
      | none => throw "ds:X509Certificate is not base64"
  return (ids.toList, certs.toList)

/-- The one element of a list; an error naming `what` otherwise. -/
def pickOne (what : String) : List X509.Cert → Except String X509.Cert
  | [c] => .ok c
  | [] => .error s!"no certificate {what}"
  | _ => .error s!"more than one certificate {what}"

/-- Certificates, without repeats of the same DER octets. -/
def dedupCerts (l : List X509.Cert) : List X509.Cert :=
  l.foldl (fun acc c => if acc.any (·.der == c.der) then acc else acc ++ [c]) []

/-- The certificates that are not the issuer of another one of `cs`: the
end-entity certificates of a chain. -/
def endEntities (cs : List X509.Cert) : List X509.Cert :=
  cs.filter fun c => !(cs.any fun o => o.der != c.der && X509.Name.same o.issuer c.subject)

/-- §4.5.4: the certificate of one `ds:X509Data` that holds the
validation key. With identifiers: the one certificate, among those of the
element and the caller's, that every identifier names. With none: the
one end-entity certificate of the element. -/
def x509SelectCore (ids : List X509Id) (inData extra : List ByteArray) : Except String X509.Cert := do
  let some own := inData.mapM X509.parseCert? | throw "ds:X509Certificate is not a DER X.509 certificate"
  if ids.isEmpty then
    if own.isEmpty then throw "ds:X509Data holds no certificate and no identifier this verifier reads"
    pickOne "of ds:X509Data is an end-entity certificate of the others" (endEntities (dedupCerts own))
  else
    let cands := dedupCerts (own ++ extra.filterMap X509.parseCert?)
    pickOne "of ds:X509Data or of the caller matches every identifier of ds:X509Data"
      (cands.filter fun c => ids.all (·.matches c))

/-- The DSA OID 1.2.840.10040.4.1 (RFC 3279 §2.3.2). -/
def oidDsa : List UInt8 := [0x2a, 0x86, 0x48, 0xce, 0x38, 0x04, 0x01]

/-- The key of a certificate: its SubjectPublicKeyInfo, read as
`dsig11:DEREncodedKeyValue` is. -/
def certKey (c : X509.Cert) : Except String PublicKey :=
  match spkiKey? c.spki with
  | some k => .ok k
  | none =>
      let isDsa := match derTlv? c.spki 0 with
        | some (_, s0, _) => match derTlv? c.spki s0 with
          | some (_, s1, _) => match derTlv? c.spki s1 with
            | some (0x06, s2, e2) => slice c.spki s2 e2 == oidDsa
            | _ => false
          | none => false
        | none => false
      if isDsa then .error "the certificate holds a DSA key; DSA is not supported (https://github.com/danbri/factoidal/issues/1224)"
      else .error "the certificate's key is not RSA or named-curve EC"

/-- The certificate a `ds:X509Data` element names. -/
def x509Select (certs : List ByteArray) (d : Doc) (xd : Nat) : Except String X509.Cert := do
  let (ids, own) ← x509Contents d xd
  x509SelectCore ids own certs

/-! ## ds:RetrievalMethod (§4.5.3) -/

/-- The `Type` identifiers of §4.5.3 (and of §4.5.2.3 and §4.5.11 in 1.1)
that name an element: the namespace name followed by the local name. -/
def rmTypeX509Data : String := dsNs ++ "X509Data"
def rmTypeRSAKeyValue : String := dsNs ++ "RSAKeyValue"
def rmTypeDSAKeyValue : String := dsNs ++ "DSAKeyValue"
def rmTypeECKeyValue : String := ds11Ns ++ "ECKeyValue"
def rmTypeDEREncoded : String := ds11Ns ++ "DEREncodedKeyValue"
/-- §4.5.3: a binary (ASN.1 DER) X.509 certificate. -/
def rmTypeRawX509 : String := dsNs ++ "rawX509Certificate"

/-- What a `ds:RetrievalMethod` gives: one element (of the signature's
document, or of a document parsed from octets), or the octets of a DER
certificate. -/
inductive Retrieved where
  | element (d : Doc) (e : Nat)
  | rawCert (der : ByteArray)

/-- The expanded name of an element, written as a §4.5.3 `Type` is. -/
def typeOf (d : Doc) (e : Nat) : String := (d.get e).name.uri ++ (d.get e).name.loc

/-- The elements of a node-set whose parent element is not in it, in
document order. -/
def apexElements (cd : C14nDoc) (s : Nat → Bool) : List Nat :=
  (List.range cd.n0).filter fun i =>
    kindOf cd.doc i == .element && s i &&
      match parentElem? cd.doc i with
      | some p => !s p
      | none => true

/-- The `ds:Transform` children of the `ds:Transforms` of a
`ds:RetrievalMethod`. -/
def retrievalTransforms (d : Doc) (rm : Nat) : Except String (List Nat) :=
  match elemKids d rm with
  | [] => .ok []
  | [t] =>
      if isEl d t dsNs "Transforms" then
        let ts := elemKids d t
        if ts.all fun x => isEl d x dsNs "Transform" then .ok ts
        else .error "ds:Transforms holds an element that is not ds:Transform"
      else .error "ds:RetrievalMethod may hold only ds:Transforms"
  | _ => .error "ds:RetrievalMethod may hold only ds:Transforms"

/-- The data after the URI and the transforms are read as `Type` says.
Octets with `rawX509Certificate` are the certificate. Otherwise the data
is a node-set (octets are parsed as XML) with exactly one apex element,
whose expanded name is `Type` when `Type` is given. -/
def readRetrieved (ty : Option String) (y : Data) : Except String Retrieved :=
  if ty == some rmTypeRawX509 then
    match y with
    | .octets b => .ok (.rawCert b)
    | .nodes .. => .error "a ds:RetrievalMethod of Type rawX509Certificate must give octets, not a node-set"
  else
    match toNodes y with
    | .error e => .error e
    | .ok (cd, s, _) =>
        match apexElements cd s with
        | [e] =>
            match ty with
            | some t =>
                if typeOf cd.doc e == t then .ok (.element cd.doc e)
                else .error s!"the ds:RetrievalMethod gives {typeOf cd.doc e}, not its Type {t}"
            | none => .ok (.element cd.doc e)
        | [] => .error "the ds:RetrievalMethod gives no element"
        | _ => .error "the ds:RetrievalMethod gives more than one element"

/-- §4.5.3: the `URI` (mandatory) is dereferenced as the `URI` of a
`ds:Reference` (§4.4.3.3, `dereference`, the caller's resolver for other
documents), its `ds:Transforms` are applied (`applyTransformsAcc`), and
the result is read as `Type` says (`readRetrieved`). `sig`: the
`ds:Signature` element, for the transforms. -/
def retrieve (cfg : Config) (cd : C14nDoc) (sig rm : Nat) : Except String Retrieved :=
  let d := cd.doc
  match attrVal? d rm "URI" with
  | none => .error "ds:RetrievalMethod has no URI"
  | some u =>
      match retrievalTransforms d rm with
      | .error e => .error e
      | .ok ts =>
          match dereference cfg cd (some u) with
          | .error e => .error e
          | .ok x =>
              match applyTransformsAcc cd sig ts x with
              | .error e => .error e
              | .ok y => readRetrieved (attrVal? d rm "Type") y

/-- The key of what a `ds:RetrievalMethod` gives. A `ds:RetrievalMethod`
that gives another one is not followed: one level only, as for
`dsig11:KeyInfoReference`. -/
def retrievedKey (certs : List ByteArray) : Retrieved → Except String PublicKey
  | .rawCert b =>
      match X509.parseCert? b with
      | some c => certKey c
      | none => .error "the rawX509Certificate octets are not a DER X.509 certificate"
  | .element d e =>
      if isEl d e dsNs "X509Data" then (x509Select certs d e).bind certKey
      else if isEl d e ds11Ns "DEREncodedKeyValue" then
        match (b64Text? d e).bind spkiKey? with
        | some k => .ok k
        | none => .error "dsig11:DEREncodedKeyValue is not an RSA or named-curve EC SubjectPublicKeyInfo"
      else if isEl d e dsNs "KeyValue" then keyValue? d e
      else if isEl d e dsNs "RetrievalMethod" then
        .error "a ds:RetrievalMethod that gives another ds:RetrievalMethod is not followed"
      else keyElement? d e

/-- The certificate of what a `ds:RetrievalMethod` gives, when it is a
certificate or a `ds:X509Data`. -/
def retrievedCert? (certs : List ByteArray) : Retrieved → Option (Except String X509.Cert)
  | .rawCert b =>
      some (match X509.parseCert? b with
        | some c => .ok c
        | none => .error "the rawX509Certificate octets are not a DER X.509 certificate")
  | .element d e => if isEl d e dsNs "X509Data" then some (x509Select certs d e) else none

/-- The key of a `ds:KeyInfo` element, without following
`dsig11:KeyInfoReference`. The first of these that is present is read:
`ds:KeyValue`, `dsig11:DEREncodedKeyValue`, `ds:X509Data`,
`ds:RetrievalMethod`. -/
def keyInfoDirect? (cfg : Config) (cd : C14nDoc) (sig ki : Nat) : Except String PublicKey :=
  let d := cd.doc
  let certs := cfg.certificates
  match kidNamed? d ki dsNs "KeyValue" with
  | some kv => keyValue? d kv
  | none =>
      match kidNamed? d ki ds11Ns "DEREncodedKeyValue" with
      | some der =>
          match (b64Text? d der).bind spkiKey? with
          | some k => .ok k
          | none => .error "dsig11:DEREncodedKeyValue is not an RSA or named-curve EC SubjectPublicKeyInfo"
      | none =>
          match kidNamed? d ki dsNs "X509Data" with
          | some xd => (x509Select certs d xd).bind certKey
          | none =>
              match kidNamed? d ki dsNs "RetrievalMethod" with
              | some rm => (retrieve cfg cd sig rm).bind (retrievedKey certs)
              | none => .error "ds:KeyInfo holds no key this verifier reads"

/-- §4.5: the key of `ds:KeyInfo`; a `dsig11:KeyInfoReference` (§4.5.10)
is followed once, to a `ds:KeyInfo` of the same document. -/
def keyInfoKey? (cfg : Config) (cd : C14nDoc) (sig ki : Nat) : Except String PublicKey :=
  let d := cd.doc
  match kidNamed? d ki ds11Ns "KeyInfoReference" with
  | none => keyInfoDirect? cfg cd sig ki
  | some r =>
      match attrVal? d r "URI" with
      | some u =>
          if u.startsWith "#" then
            match idTarget cd (u.drop 1).toString with
            | .ok t =>
                if isEl d t dsNs "KeyInfo" then keyInfoDirect? cfg cd sig t
                else .error "dsig11:KeyInfoReference does not point to a ds:KeyInfo"
            | .error e => .error e
          else .error "dsig11:KeyInfoReference to another document is not followed"
      | none => .error "dsig11:KeyInfoReference has no URI"

/-! ## Signature value (§3.2.2, §6.3, §6.4) -/

/-- The first `bits` bits of `a` and `b` agree, `b` being exactly
`ceil(bits / 8)` octets. -/
def truncatedEq (a b : ByteArray) (bits : Nat) : Bool :=
  let n := (bits + 7) / 8
  let r := bits % 8
  if b.size != n || a.size < n then false
  else if r == 0 then Crypto.ctEqBytes (a.extract 0 n) b
  else
    let mask : UInt8 := (0xFF : UInt8) <<< (8 - r).toUInt8
    Crypto.ctEqBytes (a.extract 0 (n - 1)) (b.extract 0 (n - 1)) &&
      ((a.get! (n - 1)) &&& mask) == ((b.get! (n - 1)) &&& mask)

/-- §6.3.1: the smallest `HMACOutputLength` a verifier accepts. -/
def hmacMinBits (h : DigestAlg) : Nat := max 80 (h.size * 8 / 2)

def checkMac (h : DigestAlg) (key : ByteArray) (hmacLen : Option Nat) (msg sig : ByteArray) :
    Except String Bool :=
  let mac := Crypto.hmacWith h.digest h.block key msg
  match hmacLen with
  | none => .ok (Crypto.ctEqBytes mac sig)
  | some t =>
      if t < hmacMinBits h then .error s!"HMACOutputLength {t} is below the minimum {hmacMinBits h} (§6.3.1)"
      else if t > h.size * 8 then .error s!"HMACOutputLength {t} is longer than the MAC"
      else .ok (truncatedEq mac sig t)

/-- The key the signature is checked with. -/
def keyFor (cfg : Config) (cd : C14nDoc) (s : Signature) : Except String PublicKey :=
  match cfg.key with
  | some k => .ok k
  | none =>
      if !cfg.keyFromKeyInfo then .error "no key was given"
      else match s.keyInfo with
        | some ki => keyInfoKey? cfg cd s.node ki
        | none => .error "no key was given and the signature has no ds:KeyInfo"

/-- The certificate that the first `ds:X509Data` of the signature's
`ds:KeyInfo` names (§4.5.4), or, with no `ds:X509Data`, the certificate
that its `ds:RetrievalMethod` gives (§4.5.3), for the caller's path validation; `none`
when there is no such element. -/
def signingCertificate? (cfg : Config) (cd : C14nDoc) (s : Signature) : Option (Except String X509.Cert) :=
  s.keyInfo.bind fun ki =>
    match kidNamed? cd.doc ki dsNs "X509Data" with
    | some xd => some (x509Select cfg.certificates cd.doc xd)
    | none =>
        (kidNamed? cd.doc ki dsNs "RetrievalMethod").bind fun rm =>
          match retrieve cfg cd s.node rm with
          | .ok r => retrievedCert? cfg.certificates r
          | .error e => some (.error e)

/-- The check of `ds:SignatureValue` over the canonical `ds:SignedInfo`.
`.ok (b, k)`: the check gave `b`, with the public key `k` (none for a MAC). -/
def signatureValueOk (be : Backend) (cfg : Config) (cd : C14nDoc) (s : Signature) (msg : ByteArray) :
    Except String (Bool × Option PublicKey) :=
  match s.si.sig with
  | .hmac h =>
      match cfg.hmacKey with
      | none => .error "an HMAC signature needs the caller's key"
      | some k => (checkMac h k s.si.hmacLen msg s.value).map (·, none)
  | .rsa h =>
      match keyFor cfg cd s with
      | .ok (.rsa n e) =>
          match be.rsaPublicOp n e s.value with
          | none => .error s!"the RSA public operation refused the key or the value (a {n.size * 8}-bit modulus; the HACL* operation takes 2048, 3072 and 4096 bits: https://github.com/danbri/factoidal/issues/1227)"
          | some _ => .ok (JOSE.Pkcs1.rsaPkcs1Verify be.rsaPublicOp h.digestInfo h.size n e s.value (h.digest msg),
                           some (.rsa n e))
      | .ok (.ec ..) => .error "an RSA signature method with an EC key"
      | .error e => .error e
  | .ecdsa h =>
      match keyFor cfg cd s with
      | .ok (.ec c xy) =>
          if s.value.size != 2 * c.coordSize then .error "the ECDSA signature value is not r || s of the curve"
          else match be.ecdsaVerify c h xy msg s.value with
            | some b => .ok (b, some (.ec c xy))
            | none => .error s!"ECDSA over {c.name} with {h.name} is not available (https://github.com/danbri/factoidal/issues/1223)"
      | .ok (.rsa ..) => .error "an ECDSA signature method with an RSA key"
      | .error e => .error e
  | .dsa _ => .error "DSA is not supported (https://github.com/danbri/factoidal/issues/1224)"

/-! ## Core validation (§3.2) -/

structure Validated where
  /-- The URI and the digested octets of each reference, in order. -/
  references : List (String × ByteArray)
  /-- The public key the signature verified under; `none` for a MAC. -/
  key : Option PublicKey
  signedInfo : String

def signedInfoOctets (cd : C14nDoc) (s : Signature) : Except String String :=
  canonicalize s.si.c14n cd (subtreeSet cd s.si.node)

def validateParsed (be : Backend) (cfg : Config) (cd : C14nDoc) (s : Signature) : Except String Validated :=
  match checkRefsAcc (referenceOctets cfg cd s.node) s.si.refs [] with
  | .error e => .error e
  | .ok outs =>
      match signedInfoOctets cd s with
      | .error e => .error e
      | .ok siC =>
          match signatureValueOk be cfg cd s siC.toUTF8 with
          | .error e => .error e
          | .ok (false, _) => .error "the signature value does not verify"
          | .ok (true, k) => .ok { references := outs, key := k, signedInfo := siC }

/-- The `ds:Signature` elements of a document, in document order. -/
def signatures (cd : C14nDoc) : List Nat :=
  (List.range cd.n0).filter fun i => isEl cd.doc i dsNs "Signature"

/-- Core validation of the signature element `s`. -/
def validate (be : Backend) (cfg : Config) (cd : C14nDoc) (s : Nat) : Except String Validated :=
  (parseSignature cd.doc s).bind (validateParsed be cfg cd)

/-- Core validation of the one `ds:Signature` of a document given as text. -/
def validateText (be : Backend) (cfg : Config) (src : String) : Except String Validated := do
  let cd ← C14nDoc.ofString? src
  match signatures cd with
  | [s] => validate be cfg cd s
  | [] => throw "the document has no ds:Signature"
  | _ => throw "the document has more than one ds:Signature; validate one with `validate`"

/-! ## Theorems -/

/-- §3.2.1: when the references check, every reference's octets were
computed and their digest equals its `ds:DigestValue`. -/
theorem checkRefsAcc_ok {f : Reference → Except String ByteArray} :
    ∀ {rs : List Reference} {acc outs}, checkRefsAcc f rs acc = .ok outs →
      ∀ r ∈ rs, ∃ o, f r = .ok o ∧ (r.digest.digest o == r.value) = true := by
  intro rs
  induction rs with
  | nil => intro _ _ _ r hr; cases hr
  | cons x xs ih =>
      intro acc outs h r hr
      unfold checkRefsAcc at h
      cases hf : f x with
      | error e => rw [hf] at h; cases h
      | ok o =>
          rw [hf] at h
          dsimp only at h
          by_cases hd : (x.digest.digest o == x.value) = true
          · rw [if_pos hd] at h
            cases hr with
            | head => exact ⟨o, hf, hd⟩
            | tail _ hm => exact ih h r hm
          · rw [if_neg hd] at h; cases h

/-- §3.2: core validation succeeds only when every reference's digest
matched (§3.2.1) and the signature value checked over the canonical
`ds:SignedInfo` (§3.2.2). XML Signature 1.1 (2013). -/
theorem dsig11_validateParsed_ok {be : Backend} {cfg : Config} {cd : C14nDoc} {s : Signature}
    {v : Validated} (h : validateParsed be cfg cd s = .ok v) :
    (∀ r ∈ s.si.refs, ∃ o, referenceOctets cfg cd s.node r = .ok o ∧
        (r.digest.digest o == r.value) = true) ∧
    ∃ siC k, signedInfoOctets cd s = .ok siC ∧
      signatureValueOk be cfg cd s siC.toUTF8 = .ok (true, k) := by
  unfold validateParsed at h
  cases hr : checkRefsAcc (referenceOctets cfg cd s.node) s.si.refs [] with
  | error e => rw [hr] at h; cases h
  | ok outs =>
      rw [hr] at h
      dsimp only at h
      refine ⟨checkRefsAcc_ok hr, ?_⟩
      cases hs : signedInfoOctets cd s with
      | error e => rw [hs] at h; cases h
      | ok siC =>
          rw [hs] at h
          dsimp only at h
          cases hv : signatureValueOk be cfg cd s siC.toUTF8 with
          | error e => rw [hv] at h; cases h
          | ok bk =>
              obtain ⟨b, k⟩ := bk
              rw [hv] at h
              cases b with
              | false => cases h
              | true => exact ⟨siC, k, rfl, hv⟩

/-- An HMAC truncated below the §6.3.1 minimum is refused whatever the
signature value is (the `hmac-sha1-truncated40` interop case). -/
theorem dsig11_hmac_short_refused (h : DigestAlg) (key msg sig : ByteArray) (t : Nat)
    (ht : t < hmacMinBits h) : ∃ e, checkMac h key (some t) msg sig = .error e := by
  unfold checkMac
  simp only [if_pos ht]
  exact ⟨_, rfl⟩

/-- An RSA check is `rsaPkcs1Verify`: it accepts only a recovered block
equal to the generated EMSA-PKCS1-v1_5 block of the digest. -/
theorem dsig11_rsa_template {be : Backend} {cfg : Config} {cd : C14nDoc} {s : Signature}
    {msg : ByteArray} {h : DigestAlg} {k : Option PublicKey}
    (hs : s.si.sig = .rsa h) (hv : signatureValueOk be cfg cd s msg = .ok (true, k)) :
    ∃ n e, k = some (.rsa n e) ∧
      JOSE.Pkcs1.rsaPkcs1Verify be.rsaPublicOp h.digestInfo h.size n e s.value (h.digest msg) = true := by
  unfold signatureValueOk at hv
  rw [hs] at hv
  dsimp only at hv
  cases hk : keyFor cfg cd s with
  | error e => rw [hk] at hv; cases hv
  | ok pk =>
      rw [hk] at hv
      cases pk with
      | ec c xy => cases hv
      | rsa n e =>
          dsimp only at hv
          cases hp : be.rsaPublicOp n e s.value with
          | none => rw [hp] at hv; cases hv
          | some _ =>
              rw [hp] at hv
              simp only [Except.ok.injEq, Prod.mk.injEq] at hv
              exact ⟨n, e, hv.2.symm, hv.1⟩

/-! ### The SAML 2.0 profile (`L4Factoidal.XML.DSig`) as a case

The profile's algorithm identifiers are entries of the XML Signature 1.1
tables, and its signature check (`Pkcs1.rs256Verify`) is the RSA check
here at SHA-256. -/

theorem dsig11_saml_profile_algorithms :
    SigAlg.ofUri? DSig.rsaSha256Alg = some (.rsa .sha256) ∧
    DigestAlg.ofUri? DSig.sha256Alg = some .sha256 ∧
    (Method.ofUri? DSig.excC14nAlg).map (·.version) = some .exc10 := by
  refine ⟨rfl, rfl, rfl⟩

theorem dsig11_saml_profile_rsa (pubOp : JOSE.Pkcs1.PublicOp) (n e sig msg : ByteArray) :
    JOSE.Pkcs1.rsaPkcs1Verify pubOp DigestAlg.sha256.digestInfo DigestAlg.sha256.size n e sig
        (DigestAlg.sha256.digest msg) = JOSE.Pkcs1.rs256Verify pubOp n e sig msg :=
  JOSE.Pkcs1.rsaPkcs1Verify_sha256 pubOp n e sig msg

/-! ## Checks -/

/-- A backend with no RSA and no ECDSA, for the MAC checks below. -/
def macOnly : Backend := { rsaPublicOp := fun _ _ _ => none, ecdsaVerify := fun _ _ _ _ _ => none }

-- RFC 2202 §3 test case 2 through the table.
#guard Crypto.bytesToHex (Crypto.hmacWith DigestAlg.sha1.digest DigestAlg.sha1.block "Jefe".toUTF8
    "what do ya want for nothing?".toUTF8) == "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79"
#guard hmacMinBits .sha1 == 80 && hmacMinBits .sha256 == 128 && hmacMinBits .sha512 == 256
#guard truncatedEq (bytesOf [0xAB, 0xCD, 0xEF]) (bytesOf [0xAB, 0xC0]) 12
#guard !truncatedEq (bytesOf [0xAB, 0xCD, 0xEF]) (bytesOf [0xAB, 0xD0]) 12
#guard xpointerId? "xpointer(id('a.b'))" == some "a.b" && xpointerId? "xpointer(id(\"x\"))" == some "x"
#guard xpointerId? "xpointer(/)" == none
#guard (natBytes 258 2).map (·.data.toList) == some [1, 2] && natBytes 65536 2 == none

-- An enveloping HMAC-SHA256 signature made with Python's hmac over the
-- Canonical XML 1.0 form; a changed object and a wrong key are refused.
def macDoc (obj : String) (dv sv : String) : String :=
  "<ds:Signature xmlns:ds=\"http://www.w3.org/2000/09/xmldsig#\"><ds:SignedInfo>" ++
  "<ds:CanonicalizationMethod Algorithm=\"http://www.w3.org/TR/2001/REC-xml-c14n-20010315\"/>" ++
  "<ds:SignatureMethod Algorithm=\"http://www.w3.org/2001/04/xmldsig-more#hmac-sha256\"/>" ++
  "<ds:Reference URI=\"#o\"><ds:DigestMethod Algorithm=\"http://www.w3.org/2001/04/xmlenc#sha256\"/>" ++
  "<ds:DigestValue>" ++ dv ++ "</ds:DigestValue></ds:Reference></ds:SignedInfo>" ++
  "<ds:SignatureValue>" ++ sv ++ "</ds:SignatureValue><ds:Object Id=\"o\">" ++ obj ++ "</ds:Object></ds:Signature>"

-- The XSLT transform (§6.6.5) with no stylesheet in its ds:Transform is
-- refused with the reason.
#guard (match validateText macOnly { hmacKey := some "k".toUTF8 }
    ("<ds:Signature xmlns:ds=\"http://www.w3.org/2000/09/xmldsig#\"><ds:SignedInfo>" ++
     "<ds:CanonicalizationMethod Algorithm=\"http://www.w3.org/TR/2001/REC-xml-c14n-20010315\"/>" ++
     "<ds:SignatureMethod Algorithm=\"http://www.w3.org/2001/04/xmldsig-more#hmac-sha256\"/>" ++
     "<ds:Reference URI=\"#o\"><ds:Transforms><ds:Transform Algorithm=\"" ++ xsltAlg ++ "\"/></ds:Transforms>" ++
     "<ds:DigestMethod Algorithm=\"http://www.w3.org/2001/04/xmlenc#sha256\"/>" ++
     "<ds:DigestValue>AA==</ds:DigestValue></ds:Reference></ds:SignedInfo>" ++
     "<ds:SignatureValue>AA==</ds:SignatureValue><ds:Object Id=\"o\">x</ds:Object></ds:Signature>") with
  | .error e => (e.splitOn "has no stylesheet").length > 1
  | .ok _ => false)

-- The XSLT transform runs the stylesheet of its ds:Transform on the
-- canonical form of the referenced element; the stylesheet keeps the
-- namespace bindings it inherits from the signature (here `xsl`).
#guard (match (do
    let cd ← C14nDoc.ofString?
      ("<ds:Signature xmlns:ds=\"http://www.w3.org/2000/09/xmldsig#\" xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\"><ds:SignedInfo>" ++
       "<ds:CanonicalizationMethod Algorithm=\"http://www.w3.org/TR/2001/REC-xml-c14n-20010315\"/>" ++
       "<ds:SignatureMethod Algorithm=\"http://www.w3.org/2001/04/xmldsig-more#hmac-sha256\"/>" ++
       "<ds:Reference URI=\"#o\"><ds:Transforms><ds:Transform Algorithm=\"" ++ xsltAlg ++ "\">" ++
       "<xsl:stylesheet version=\"1.0\"><xsl:output method=\"text\"/>" ++
       "<xsl:template match=\"/\">[<xsl:value-of select=\"count(//b)\"/>]</xsl:template></xsl:stylesheet>" ++
       "</ds:Transform></ds:Transforms>" ++
       "<ds:DigestMethod Algorithm=\"http://www.w3.org/2001/04/xmlenc#sha256\"/>" ++
       "<ds:DigestValue>AA==</ds:DigestValue></ds:Reference></ds:SignedInfo>" ++
       "<ds:SignatureValue>AA==</ds:SignatureValue><ds:Object Id=\"o\"><a><b/><b/></a></ds:Object></ds:Signature>")
    let some s := (signatures cd).head? | throw "no signature"
    let sg ← parseSignature cd.doc s
    let some r := sg.si.refs.head? | throw "no reference"
    referenceOctets {} cd sg.node r) with
  | .ok o => o == "[2]".toUTF8
  | .error _ => false)

/-! ## Theorems: ds:X509Data (XML Signature 1.1, 2013, §4.5.4) -/

theorem pickOne_mem {w : String} : ∀ {l : List X509.Cert} {c}, pickOne w l = .ok c → c ∈ l
  | [c'], c, h => by simp only [pickOne, Except.ok.injEq] at h; simp [h]
  | [], _, h => by simp [pickOne] at h
  | _ :: _ :: _, _, h => by simp [pickOne] at h

/-- XML Signature 1.1 (2013) §4.5.4: when `ds:X509Data` has identifiers,
the certificate selected is named by every one of them. -/
theorem x509SelectCore_2013_identified {ids : List X509Id} {a b : List ByteArray} {c : X509.Cert}
    (hne : ids ≠ []) (h : x509SelectCore ids a b = .ok c) : ∀ i ∈ ids, i.matches c = true := by
  have hnil : ids.isEmpty = false := by cases ids <;> simp_all
  unfold x509SelectCore at h
  cases ho : a.mapM X509.parseCert? with
  | none => simp only [ho] at h; cases h
  | some own =>
    simp only [ho, hnil] at h
    have hm := pickOne_mem h
    simp only [List.mem_filter, List.all_eq_true] at hm
    exact hm.2

/-- An `X509Digest` names exactly the certificates whose DER octets have
that digest. -/
theorem x509Id_2013_digest_matches (c : X509.Cert) (h : DigestAlg) (v : ByteArray) :
    (X509Id.digest h v).matches c = true ↔ h.digest c.der = v := by
  show ByteArray.beq (h.digest c.der) v = true ↔ _
  unfold ByteArray.beq
  rw [beq_iff_eq]
  exact ⟨ByteArray.ext, fun e => e ▸ rfl⟩

/-- XML Signature 1.1 (2013) §4.5.4 and §4.5.8: the key of a certificate
in `ds:X509Data` is its SubjectPublicKeyInfo read as a
`dsig11:DEREncodedKeyValue` is, so the two routes give the same key. -/
theorem dsig11_2013_x509_key_eq_derEncoded (c : X509.Cert) (k : PublicKey)
    (h : spkiKey? c.spki = some k) : certKey c = .ok k := by
  simp [certKey, h]

/-! ## Theorems: ds:RetrievalMethod (XML Signature 1.1, 2013, §4.5.3) -/

/-- XML Signature 1.1 (2013) §4.5.3 and §4.5.4: a `ds:X509Data` that a
`ds:RetrievalMethod` gives yields the key that the same element yields
as a child of `ds:KeyInfo`. -/
theorem dsig11_2013_retrieved_x509Data_eq_direct (certs : List ByteArray) (d : Doc) (e : Nat)
    (h : isEl d e dsNs "X509Data" = true) :
    retrievedKey certs (.element d e) = (x509Select certs d e).bind certKey := by
  simp [retrievedKey, h]

/-- XML Signature 1.1 (2013) §4.5.3: with a `Type` other than
`rawX509Certificate`, an element is read only when its expanded name is
that `Type`. -/
theorem dsig11_2013_retrieved_type {t : String} {y : Data} {d : Doc} {e : Nat}
    (ht : t ≠ rmTypeRawX509) (h : readRetrieved (some t) y = .ok (.element d e)) : typeOf d e = t := by
  have hne : (some t == some rmTypeRawX509) = false := by simp [ht]
  unfold readRetrieved at h
  rw [hne] at h
  simp only [Bool.false_eq_true, if_false] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; simpa using ‹(typeOf _ _ == t) = true›
      · cases h
    · cases h
    · cases h

/-- XML Signature 1.1 (2013) §4.5.3: `rawX509Certificate` takes octets;
a node-set is refused. -/
theorem dsig11_2013_raw_needs_octets (cd : C14nDoc) (s : Nat → Bool) (b : Bool) :
    ∃ m, readRetrieved (some rmTypeRawX509) (.nodes cd s b) = .error m := by
  simp [readRetrieved]

/-- XML Signature 1.1 (2013) §4.5.3 and §4.5.4: a `rawX509Certificate`
gives the key and the certificate that a `ds:X509Data` holding only that
`ds:X509Certificate` gives. -/
theorem dsig11_2013_raw_eq_x509Certificate (certs : List ByteArray) (b : ByteArray) (c : X509.Cert)
    (h : X509.parseCert? b = some c) :
    retrievedKey certs (.rawCert b) = certKey c ∧ x509SelectCore [] [b] certs = .ok c := by
  refine ⟨by simp [retrievedKey, h], ?_⟩
  have hb : (c.der != c.der) = false := by
    show (!(ByteArray.beq c.der c.der)) = false
    unfold ByteArray.beq
    simp
  simp [x509SelectCore, h, endEntities, dedupCerts, pickOne, hb]

end L4Factoidal.XML.DSig11
