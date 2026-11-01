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
    (§6.6.2). XSLT and XPath Filter 2.0 are refused
    (https://github.com/danbri/factoidal/issues/1225).

## Keys (§4.5)

The caller gives the key (`Config.key`, `Config.hmacKey`), or allows the
key of `ds:KeyInfo` (`Config.keyFromKeyInfo`): `ds:KeyValue` with
`ds:RSAKeyValue`, `dsig11:ECKeyValue` (named curve) or the RFC 4050
`ECDSAKeyValue`; `dsig11:DEREncodedKeyValue` (an RSA or EC
SubjectPublicKeyInfo); `dsig11:KeyInfoReference` to a `ds:KeyInfo` of the
same document. A key from `ds:KeyInfo` only says that the signature
verifies under that key; `Validated.key` returns it so the caller decides
whether it trusts it. `ds:X509Data` is not read
(https://github.com/danbri/factoidal/issues/1226).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.C14nXPath
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Crypto.Hmac
import L4Factoidal.JOSE.Pkcs1
import L4Factoidal.VC.Multibase
import L4Factoidal.XML.DSig

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
    let f ← C14nXPath.xpathFilter cd (textOf d xp) (xpathNs d xp)
    return .nodes cd (fun i => s i && f i) sd
  if alg == base64Alg then
    let txt ← match x with
      | .octets b => match String.fromUTF8? b with
        | some t => pure t
        | none => throw "the base64 transform input is not text"
      | .nodes cd s _ => pure (textValue cd s)
    match b64? txt with
    | some b => return .octets b
    | none => throw "the base64 transform input is not base64"
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

/-- A DER TLV at `i` with a definite length: tag, content start, content end. -/
def derTlv? (b : ByteArray) (i : Nat) : Option (UInt8 × Nat × Nat) :=
  if i + 2 > b.size then none else
  let tag := b.get! i
  let l0 := (b.get! (i + 1)).toNat
  if l0 < 128 then
    if i + 2 + l0 ≤ b.size then some (tag, i + 2, i + 2 + l0) else none
  else if l0 == 0x81 && i + 3 ≤ b.size then
    let l := (b.get! (i + 2)).toNat
    if i + 3 + l ≤ b.size then some (tag, i + 3, i + 3 + l) else none
  else if l0 == 0x82 && i + 4 ≤ b.size then
    let l := (b.get! (i + 2)).toNat * 256 + (b.get! (i + 3)).toNat
    if i + 4 + l ≤ b.size then some (tag, i + 4, i + 4 + l) else none
  else none

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

/-- A `ds:KeyValue` (§4.5.2). -/
def keyValue? (d : Doc) (kv : Nat) : Except String PublicKey :=
  match elemKids d kv with
  | [k] =>
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
  | _ => .error "ds:KeyValue must hold one key"

/-- The key of a `ds:KeyInfo` element, without following
`dsig11:KeyInfoReference`. -/
def keyInfoDirect? (d : Doc) (ki : Nat) : Except String PublicKey :=
  match kidNamed? d ki dsNs "KeyValue" with
  | some kv => keyValue? d kv
  | none =>
      match kidNamed? d ki ds11Ns "DEREncodedKeyValue" with
      | some der =>
          match (b64Text? d der).bind spkiKey? with
          | some k => .ok k
          | none => .error "dsig11:DEREncodedKeyValue is not an RSA or named-curve EC SubjectPublicKeyInfo"
      | none =>
          if (kidNamed? d ki dsNs "X509Data").isSome then
            .error "ds:X509Data is not read (https://github.com/danbri/factoidal/issues/1226)"
          else .error "ds:KeyInfo holds no key this verifier reads"

/-- §4.5: the key of `ds:KeyInfo`; a `dsig11:KeyInfoReference` (§4.5.10)
is followed once, to a `ds:KeyInfo` of the same document. -/
def keyInfoKey? (cd : C14nDoc) (ki : Nat) : Except String PublicKey :=
  let d := cd.doc
  match kidNamed? d ki ds11Ns "KeyInfoReference" with
  | none => keyInfoDirect? d ki
  | some r =>
      match attrVal? d r "URI" with
      | some u =>
          if u.startsWith "#" then
            match idTarget cd (u.drop 1).toString with
            | .ok t =>
                if isEl d t dsNs "KeyInfo" then keyInfoDirect? d t
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
        | some ki => keyInfoKey? cd ki
        | none => .error "no key was given and the signature has no ds:KeyInfo"

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

end L4Factoidal.XML.DSig11
