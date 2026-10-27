/-
L4Factoidal.XML.DSig — verification of ONE enveloped XML Signature over the
document element, in the profile SAML 2.0 Core §5 uses
(https://github.com/danbri/factoidal/issues/926).

Specs: XML Signature Syntax and Processing Version 1.1, W3C Recommendation
11 April 2013, https://www.w3.org/TR/xmldsig-core1/ (sections cited below);
Exclusive XML Canonicalization 1.0 (`L4Factoidal.XML.ExcC14n`); SAML Core
§5.4 ("SAML-specific XML Signature profile"): one enveloped signature, a
Reference whose `URI` is `#` and the `ID` of the signed element, the
enveloped-signature transform and the exclusive canonicalization
transform.

## What is accepted

Nothing outside this profile. Every other form is refused:

  * the document has no document type declaration, no comment and no
    processing instruction anywhere, and every prefix is bound. With no
    DTD there is no entity expansion and no defaulted attribute; with no
    comment the "omits comments" canonical form and the parse tree have
    the same text, so a reader of the tree reads what was digested;
  * exactly one `ds:Signature` element in the whole document, and it is a
    child of the document element (§3.1 enveloped signature);
  * `ds:Signature` = `ds:SignedInfo`, `ds:SignatureValue`, optional
    `ds:KeyInfo` (not read: the key comes from the caller's trust
    configuration), nothing else; no `ds:Object`;
  * `ds:SignedInfo` = `ds:CanonicalizationMethod` exc-c14n (§4.4.3; with an
    optional `ec:InclusiveNamespaces`), `ds:SignatureMethod` rsa-sha256
    (RFC 6931 §2.3.2, no `HMACOutputLength`), exactly ONE `ds:Reference`;
  * the Reference `URI` is `#` and the value of the document element's
    `ID` attribute, and no other element carries that `ID` value;
    `ds:Transforms` = enveloped-signature then exc-c14n; `ds:DigestMethod`
    SHA-256; `ds:DigestValue`.

Between the elements of the signature only whitespace text is allowed.

The walks below recurse once per level of element nesting; a caller bounds
the nesting before it parses (`SAML.decodeToken`: at most `maxDepth`).

## What is checked

  1. Digest (§3.2.1): SHA-256 of the exclusive canonical form of the
     document element with the `ds:Signature` element removed equals the
     DigestValue.
  2. Signature (§3.2.2): the RSA PKCS #1 v1.5 SHA-256 verifier, applied
     to the exclusive canonical form of `ds:SignedInfo` with the caller's
     key, returns true. The verifier is a parameter: the executable edge
     passes `JOSE.Pkcs1.rs256Verify` over HACL*'s RSA public operation,
     which compares the whole padded block (`Pkcs1.rs256Verify_iff_template`)
     and refuses moduli below 2048 bits.

Because the only reference is the document element itself, the element a
caller reads after `verifyEnveloped` returns `ok` is the signed element:
there is no ID lookup that a second element could answer (the signature
wrapping attacks of Somorovsky et al., USENIX Security 2012).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.ExcC14n
import L4Factoidal.Crypto.SHA2
import L4Factoidal.VC.Multibase

namespace L4Factoidal.XML.DSig

open L4Factoidal.XML
open L4Factoidal.XML.Canonical (Scope nsDecls extendScope splitQName lookup rootScope)

def dsNs : String := "http://www.w3.org/2000/09/xmldsig#"
def excC14nAlg : String := "http://www.w3.org/2001/10/xml-exc-c14n#"
def envelopedAlg : String := "http://www.w3.org/2000/09/xmldsig#enveloped-signature"
def rsaSha256Alg : String := "http://www.w3.org/2001/04/xmldsig-more#rsa-sha256"
def sha256Alg : String := "http://www.w3.org/2001/04/xmlenc#sha256"

/-- RSA PKCS #1 v1.5 with SHA-256: modulus, exponent, signature, message. -/
abbrev RsaVerify := ByteArray → ByteArray → ByteArray → ByteArray → Bool

/-! ## Elements with expanded names -/

/-- An element of the tree with its expanded name. `parent`: the bindings
in force on its parent; `scope`: those in force on it. -/
structure El where
  ns : String
  lname : String
  attrs : List Attribute
  kids : List Node
  parent : Scope
  scope : Scope
  node : Node

/-- The expanded name of a QName; `none` when its prefix is unbound. -/
def expand (sc : Scope) (q : String) : Option (String × String) :=
  let (p, l) := splitQName q
  if p == "" then some ((lookup sc "").getD "", l) else (lookup sc p).map (·, l)

def elOf? (parent : Scope) : Node → Option El
  | n@(.element t attrs kids) =>
      let sc := extendScope parent (nsDecls attrs)
      (expand sc t).map fun (ns, l) => { ns, lname := l, attrs, kids, parent, scope := sc, node := n }
  | _ => none

def El.is (e : El) (ns l : String) : Bool := e.ns == ns && e.lname == l

/-- An unprefixed attribute's value. -/
def El.attr? (e : El) (n : String) : Option String := (e.attrs.find? (·.name == n)).map (·.value)

def El.children (e : El) : List El := e.kids.filterMap (elOf? e.scope)

def isXmlWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def wsOnly (n : Node) : Bool :=
  match n with
  | .text s => s.all isXmlWs
  | .element .. => true
  | _ => false

/-- Element content only: every other child is whitespace text. -/
def El.elementOnly (e : El) : Bool := e.kids.all wsOnly

/-- The character content of an element with no element child. -/
def El.text? (e : El) : Option String :=
  e.kids.foldl (fun acc n => acc.bind fun s =>
    match n with
    | .text t => some (s ++ t)
    | .cdata t => some (s ++ t)
    | _ => none) (some "")

/-- XML whitespace removed from both ends. -/
def trimWs (s : String) : String :=
  String.ofList ((s.toList.dropWhile isXmlWs).reverse.dropWhile isXmlWs).reverse

/-! ## Whole-document conditions -/

mutual

/-- No comment, no processing instruction, every element and attribute
prefix bound, below a node whose parent has bindings `sc`. -/
def plainNode (sc : Scope) : Node → Bool
  | .text _ => true
  | .cdata _ => true
  | .comment _ => false
  | .pi _ _ => false
  | .element t attrs kids =>
      let own := extendScope sc (nsDecls attrs)
      if (expand own t).isSome
          && attrs.all (fun a =>
            Canonical.isNsDeclName a.name || (splitQName a.name).1 == "" || (expand own a.name).isSome)
      then plainNodes own kids else false

/-- `plainNode` of every sibling; a tail call per sibling. -/
def plainNodes (sc : Scope) : List Node → Bool
  | [] => true
  | n :: ns => if plainNode sc n then plainNodes sc ns else false

end

mutual

/-- How many elements below a node (itself included) satisfy `p`, plus
`acc`. -/
def countNode (p : El → Bool) (sc : Scope) (acc : Nat) : Node → Nat
  | n@(.element _ attrs kids) =>
      let here := match elOf? sc n with
        | some e => if p e then 1 else 0
        | none => 0
      countNodesAcc p (extendScope sc (nsDecls attrs)) kids (acc + here)
  | _ => acc

/-- `countNode` over siblings, accumulated; a tail call per sibling. -/
def countNodesAcc (p : El → Bool) (sc : Scope) : List Node → Nat → Nat
  | [], acc => acc
  | n :: ns, acc => countNodesAcc p sc ns (countNode p sc acc n)

end

/-! ## The signature's parts -/

/-- The InclusiveNamespaces PrefixList of a CanonicalizationMethod or a
Transform: no child, or exactly one `ec:InclusiveNamespaces`. -/
def prefixList (m : El) : Except String (List String) :=
  if !m.elementOnly then .error "a canonicalization method has content other than InclusiveNamespaces"
  else match m.children with
  | [] => .ok []
  | [i] =>
      if i.is excC14nAlg "InclusiveNamespaces" && i.kids.isEmpty then
        .ok (((i.attr? "PrefixList").getD "").splitToList isXmlWs |>.filter (· != ""))
      else .error "a canonicalization method has an unexpected child"
  | _ => .error "a canonicalization method has more than one child"

def algorithmIs (e : El) (alg : String) : Bool := e.attr? "Algorithm" == some alg

/-- What verification reads from the signature. -/
structure Parts where
  signedInfo : El
  siPrefixes : List String
  refUri : String
  refPrefixes : List String
  digest : ByteArray
  sigValue : ByteArray

def base64Value (e : El) : Option ByteArray :=
  e.text?.bind fun t =>
    (L4Factoidal.VC.Multibase.base64FlexDecode (String.ofList (t.toList.filter (!isXmlWs ·)))).map
      fun bs => ⟨bs.toArray⟩

def parseReference (r : El) : Except String (String × List String × ByteArray) := do
  if !r.elementOnly then throw "ds:Reference has unexpected content"
  let uri ← (r.attr? "URI").elim (.error "ds:Reference has no URI") .ok
  match r.children with
  | [ts, dm, dv] =>
      if !(ts.is dsNs "Transforms" && dm.is dsNs "DigestMethod" && dv.is dsNs "DigestValue") then
        throw "ds:Reference must be Transforms, DigestMethod, DigestValue"
      if !ts.elementOnly then throw "ds:Transforms has unexpected content"
      let pl ← match ts.children with
        | [t1, t2] =>
            if !(t1.is dsNs "Transform" && algorithmIs t1 envelopedAlg && t1.kids.isEmpty) then
              .error "the first transform must be enveloped-signature"
            else if !(t2.is dsNs "Transform" && algorithmIs t2 excC14nAlg) then
              .error "the second transform must be exclusive canonicalization"
            else prefixList t2
        | _ => .error "the transforms must be enveloped-signature, then exclusive canonicalization"
      if !(algorithmIs dm sha256Alg && dm.kids.all wsOnly && dm.children.isEmpty) then
        throw "the digest method must be SHA-256"
      let d ← (base64Value dv).elim (.error "ds:DigestValue is not base64") .ok
      if d.size != 32 then throw "ds:DigestValue is not a SHA-256 digest"
      pure (uri, pl, d)
  | _ => throw "ds:Reference must be Transforms, DigestMethod, DigestValue"

def parseSignature (s : El) : Except String Parts := do
  if !s.elementOnly then throw "ds:Signature has unexpected content"
  let (si, sv) ← match s.children with
    | [si, sv] => pure (si, sv)
    | [si, sv, ki] =>
        if ki.is dsNs "KeyInfo" then pure (si, sv) else .error "ds:Signature has an unexpected child"
    | _ => .error "ds:Signature must be SignedInfo, SignatureValue and an optional KeyInfo"
  if !(si.is dsNs "SignedInfo" && sv.is dsNs "SignatureValue") then
    throw "ds:Signature must be SignedInfo, SignatureValue and an optional KeyInfo"
  if !si.elementOnly then throw "ds:SignedInfo has unexpected content"
  match si.children with
  | [cm, sm, r] =>
      if !(cm.is dsNs "CanonicalizationMethod" && algorithmIs cm excC14nAlg) then
        throw "the canonicalization method must be exclusive canonicalization without comments"
      let sip ← prefixList cm
      if !(sm.is dsNs "SignatureMethod" && algorithmIs sm rsaSha256Alg && sm.kids.all wsOnly
            && sm.children.isEmpty) then
        throw "the signature method must be rsa-sha256"
      if !r.is dsNs "Reference" then throw "ds:SignedInfo must hold exactly one ds:Reference"
      let (uri, rp, d) ← parseReference r
      let v ← (base64Value sv).elim (.error "ds:SignatureValue is not base64") .ok
      pure { signedInfo := si, siPrefixes := sip, refUri := uri, refPrefixes := rp,
             digest := d, sigValue := v }
  | _ => throw "ds:SignedInfo must be CanonicalizationMethod, SignatureMethod, one Reference"

/-! ## Verification -/

def isSignature (e : El) : Bool := e.is dsNs "Signature"

/-- The document element with its `ds:Signature` children removed: the
result of the enveloped-signature transform (§6.6.4) on it. -/
def withoutSignature (root : El) : Node :=
  .element (match root.node with | .element t _ _ => t | _ => "")
    root.attrs (root.kids.filter fun n => !((elOf? root.scope n).map isSignature).getD false)

/-- The two canonical forms a verification hashes: the document element
after the transforms, and `ds:SignedInfo`. -/
def canonForms (root : El) (p : Parts) : Option (String × String) := do
  let r ← ExcC14n.canonSubtree p.refPrefixes rootScope (withoutSignature root)
  let s ← ExcC14n.canonSubtree p.siPrefixes p.signedInfo.parent p.signedInfo.node
  pure (r, s)

/-- The cryptographic checks, given the two canonical forms. -/
def cryptoOk (rsa : RsaVerify) (n e : ByteArray) (p : Parts) (refC siC : String) : Bool :=
  L4Factoidal.Crypto.sha256 refC.toUTF8 == p.digest && rsa n e p.sigValue siC.toUTF8

/-- The structural checks: the document, the one signature, its parts.
`idAttr`: the name of the document element's identifier attribute (`ID`
in SAML). -/
def signedParts (d : Document) (idAttr : String) : Except String (El × Parts) := do
  if d.doctype.isSome then throw "a document type declaration is not allowed"
  if !(plainNodes rootScope (d.prolog ++ [d.root] ++ d.epilog)) then
    throw "comments, processing instructions and unbound prefixes are not allowed"
  let root ← (elOf? rootScope d.root).elim (.error "no document element") .ok
  let id ← (root.attr? idAttr).elim (.error s!"the document element has no {idAttr}") .ok
  if id.isEmpty then throw s!"the document element has an empty {idAttr}"
  if countNode (fun e => e.attr? idAttr == some id) rootScope 0 d.root != 1 then
    throw s!"another element has the {idAttr} {id}"
  if countNode isSignature rootScope 0 d.root != 1 then
    throw "the document must hold exactly one ds:Signature"
  let sig ← (root.children.find? isSignature).elim
    (.error "the ds:Signature is not a child of the document element") .ok
  let p ← parseSignature sig
  if p.refUri != "#" ++ id then throw "the signature does not reference the document element"
  pure (root, p)

/-- Verify the enveloped signature of `d` under the RSA key `(n, e)`. -/
def verifyEnveloped (rsa : RsaVerify) (n e : ByteArray) (d : Document)
    (idAttr : String := "ID") : Except String Unit :=
  match signedParts d idAttr with
  | .error w => .error w
  | .ok (root, p) =>
      match canonForms root p with
      | none => .error "the signed content cannot be canonicalized"
      | some (refC, siC) =>
          if !(L4Factoidal.Crypto.sha256 refC.toUTF8 == p.digest) then
            .error "the digest of the signed element does not match"
          else if !cryptoOk rsa n e p refC siC then .error "the signature value does not verify"
          else .ok ()

/-- `ok` only when the verifier accepted the signature value over the
canonical `ds:SignedInfo` and the digest matched. -/
theorem verifyEnveloped_ok {rsa : RsaVerify} {n e : ByteArray} {d : Document} {idAttr : String}
    (h : verifyEnveloped rsa n e d idAttr = .ok ()) :
    ∃ root p refC siC, signedParts d idAttr = .ok (root, p) ∧ canonForms root p = some (refC, siC) ∧
      (L4Factoidal.Crypto.sha256 refC.toUTF8 == p.digest) = true ∧
      rsa n e p.sigValue siC.toUTF8 = true := by
  unfold verifyEnveloped at h
  cases hs : signedParts d idAttr with
  | error w => rw [hs] at h; cases h
  | ok rp =>
    obtain ⟨root, p⟩ := rp
    rw [hs] at h
    dsimp only at h
    cases hc : canonForms root p with
    | none => rw [hc] at h; cases h
    | some fs =>
      obtain ⟨refC, siC⟩ := fs
      rw [hc] at h
      dsimp only at h
      by_cases hd : (!(L4Factoidal.Crypto.sha256 refC.toUTF8 == p.digest)) = true
      · rw [if_pos hd] at h; cases h
      · rw [if_neg hd] at h
        by_cases hk : (!cryptoOk rsa n e p refC siC) = true
        · rw [if_pos hk] at h; cases h
        · refine ⟨root, p, refC, siC, rfl, hc, ?_, ?_⟩
          · cases hab : (L4Factoidal.Crypto.sha256 refC.toUTF8 == p.digest)
            · rw [hab] at hd; exact absurd rfl hd
            · rfl
          · unfold cryptoOk at hk
            cases hr : rsa n e p.sigValue siC.toUTF8
            · rw [hr, Bool.and_false] at hk; exact absurd rfl hk
            · rfl

end L4Factoidal.XML.DSig
