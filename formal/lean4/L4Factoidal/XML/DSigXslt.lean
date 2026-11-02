/-
L4Factoidal.XML.DSigXslt — the XSLT transform of XML Signature
(XML Signature Syntax and Processing Version 1.1, W3C Recommendation
11 April 2013, §6.6.5; the same text is in the Second Edition of 1.0,
2008), algorithm `http://www.w3.org/TR/1999/REC-xslt-19991116`.

§6.6.5, in short:

* the input is an octet stream; a node-set input is first converted to
  octets (§4.4.3.2: Canonical XML 1.0 without comments, `DSig11.toOctets`);
* the stylesheet is the content of `ds:Transform`: one `xsl:stylesheet`
  or `xsl:transform` element, the child of `ds:Transform`;
* the output is the octet stream that the transformation writes; the
  specification recommends a canonicalization after it, which is the
  next transform of the reference, not part of this one.

Reuse:

* the stylesheet element is written out as text by Canonical XML 1.0
  (`XML.C14n.canonicalize`) over its subtree. Canonical XML writes every
  namespace that is in scope at the apex, so the stylesheet keeps the
  bindings that it inherits from the signature document;
* the stylesheet runs on the XSLT 4.0 processor (`XSLT4.compileStylesheet`,
  `XSLT4.transform`). A stylesheet with `version="1.0"` runs in its
  backwards-compatible mode (XSLT 4.0 §3.9);
* the principal result is serialized with the stylesheet's own output
  definition (`xsl:output`), by `XSLT4.serializeResult`, as an XSLT 1.0
  processor writes it (XSLT 1.0 §16).

Tracking: https://github.com/danbri/factoidal/issues/1225 (the XSLT
transform), https://github.com/danbri/factoidal/issues/1165 (track B, item 4).
-/
import L4Factoidal.XML.C14n
import L4Factoidal.XSLT4.Transform

namespace L4Factoidal.XML.DSigXslt

open L4Factoidal.XPath4
open L4Factoidal.XSLT4
open L4Factoidal.XML.C14n

/-- The algorithm URI of the XSLT transform (§6.6.5). -/
def xsltAlg : String := "http://www.w3.org/TR/1999/REC-xslt-19991116"

/-- The namespace of XSLT stylesheets (XSLT 1.0 §2.1). -/
def xslNs : String := "http://www.w3.org/1999/XSL/Transform"

/-- The base URIs that the transform gives to the stylesheet and to the
source document. The stylesheet is in the signature, so it has no URI of
its own; a relative URI in it (for `xsl:import`) is refused by the
processor, because no resource is supplied. -/
def styleUri : String := "urn:factoidal:xmldsig:xslt:stylesheet"
def sourceUri : String := "urn:factoidal:xmldsig:xslt:source"

/-- Run a stylesheet text on a source text; the serialized principal
result, written with the stylesheet's output definition. -/
def runText (style src : String) : Except String String :=
  let r : M String := do
    let S ← compileStylesheet styleUri [(styleUri, style)]
    let d ← match Doc.ofString src sourceUri with
      | .ok d => pure d
      | .error e => throw { code := "FODC0002", msg := s!"the transform input is not well-formed XML: {e}" }
    let env : Env := { docs := #[d], docUris := [(sourceUri, 0)] }
    let tr ← transform S { globalCtx := some (.node (NodeRef.mk' 0 0)), env }
    let props ← S.outputProps tr.principalFormat.1 tr.principalFormat.2
    -- the result tree is a document node (XSLT 1.0 §2.1)
    let wrap : M Seq := do pure [← materialize env (2 ^ 45) (.doc (Out.ofSeq tr.raw) "")]
    let v ← match tr.raw with
      | [.node n] => if (env.nrec n).kind == .document then pure tr.raw else wrap
      | _ => wrap
    serializeResult S env props v
  match r with
  | .ok t => .ok t
  | .error e => .error s!"the XSLT transform failed: {e.code} {e.msg}"

/-- The element children of node `i`. -/
def elementKids (d : Doc) (i : Nat) : List Nat :=
  (d.get i).children.toList.filter fun c => (d.get c).kind == .element

/-- The stylesheet of the `ds:Transform` element `t`, as text: its one
element child, which must be `xsl:stylesheet` or `xsl:transform`,
written by Canonical XML 1.0 (without comments). -/
def stylesheetText (sigDoc : C14nDoc) (t : Nat) : Except String String := do
  let d := sigDoc.doc
  match elementKids d t with
  | [el] =>
      let q := (d.get el).name
      if q.uri == xslNs && (q.loc == "stylesheet" || q.loc == "transform") then
        canonicalize { version := .c14n10 } sigDoc (subtreeSet sigDoc el)
      else throw s!"the XSLT transform's child is not xsl:stylesheet or xsl:transform: {q.loc}"
  | [] => throw "the XSLT transform has no stylesheet"
  | _ => throw "the XSLT transform has more than one element child"

/-- §6.6.5: the transform over the input octets. -/
def apply (sigDoc : C14nDoc) (t : Nat) (input : ByteArray) : Except String ByteArray := do
  let style ← stylesheetText sigDoc t
  let some src := String.fromUTF8? input | throw "the XSLT transform input is not UTF-8"
  let out ← runText style src
  pure out.toUTF8

/-! ## Theorems (XML Signature 1.1 §6.6.5; XSLT 1.0, 1999) -/

/-- The XSLT transform of XML Signature 1.1 gives octets that are the
UTF-8 encoding of the serialized result of the stylesheet named in the
`ds:Transform`, run on the input: the output is the transformation's
octet stream (§6.6.5), with nothing added. -/
theorem dsig11_xslt_1999_output (sigDoc : C14nDoc) (t : Nat) (input out : ByteArray)
    (h : apply sigDoc t input = .ok out) :
    ∃ style src res, stylesheetText sigDoc t = .ok style ∧ String.fromUTF8? input = some src ∧
      runText style src = .ok res ∧ out = res.toUTF8 := by
  unfold apply at h
  cases hs : stylesheetText sigDoc t with
  | error e => rw [hs] at h; cases h
  | ok style =>
    rw [hs] at h
    cases hu : String.fromUTF8? input with
    | none => simp only [hu] at h; cases h
    | some src =>
      simp only [hu] at h
      cases hr : runText style src with
      | error e => simp [hr, bind, Except.bind] at h
      | ok res =>
        simp [hr, bind, Except.bind, pure, Except.pure] at h
        refine ⟨style, src, res, rfl, rfl, hr, ?_⟩
        first | exact h.symm | (cases h; rfl) | simp_all

/-- A `ds:Transform` whose content is not one stylesheet element is
refused: the transform never runs a stylesheet that the signature does
not name. -/
theorem dsig11_xslt_1999_no_stylesheet (sigDoc : C14nDoc) (t : Nat) (input : ByteArray)
    (h : elementKids sigDoc.doc t = []) :
    apply sigDoc t input = .error "the XSLT transform has no stylesheet" := by
  simp [apply, stylesheetText, h]
  rfl

#print axioms dsig11_xslt_1999_output
#print axioms dsig11_xslt_1999_no_stylesheet

/-! ## Tests -/

-- Merlin Hughes's XSLT reference of `merlin-xmldsig-twenty-three`
-- (2001): the stylesheet and the canonical form of `#notaries`. The
-- expected text is the result of libxslt on the same input.
private def merlinStyle : String :=
  "<xsl:stylesheet xmlns=\"http://www.w3.org/TR/xhtml1/strict\" xmlns:foo=\"http://example.org/foo\" " ++
  "xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" exclude-result-prefixes=\"foo\" version=\"1.0\">" ++
  "<xsl:output encoding=\"UTF-8\" indent=\"no\" method=\"xml\"></xsl:output>" ++
  "<xsl:template match=\"/\"><html><head><title>Notaries</title></head><body><table>" ++
  "<xsl:for-each select=\"Notaries/Notary\"><tr><th><xsl:value-of select=\"@name\"></xsl:value-of></th></tr></xsl:for-each>" ++
  "</table></body></html></xsl:template></xsl:stylesheet>"

private def merlinSource : String :=
  "<Notaries xmlns:foo=\"http://example.org/foo\" Id=\"notaries\">\n" ++
  "    <Notary name=\"Great, A. T.\"></Notary>\n    <Notary name=\"Hun, A. T.\"></Notary>\n  </Notaries>"

#guard match runText merlinStyle merlinSource with
  | .ok t => (t.splitOn "<html xmlns=\"http://www.w3.org/TR/xhtml1/strict\"><head><title>Notaries</title></head><body><table><tr><th>Great, A. T.</th></tr><tr><th>Hun, A. T.</th></tr></table></body></html>").length == 2
  | .error _ => false

-- a source that is not XML is refused with the reason
#guard match runText merlinStyle "<a>" with
  | .error e => (e.splitOn "not well-formed").length > 1
  | .ok _ => false

end L4Factoidal.XML.DSigXslt
