/- Regression checks for selectable DTD and XInclude processing. -/
import L4Factoidal.XPath4.XmlParse
import L4Factoidal.XPath4.Eval

namespace L4Factoidal.XPath4

open L4Factoidal.XML

private def dtdSource : String :=
  "<!DOCTYPE r [<!ELEMENT r EMPTY><!ATTLIST r ident ID #IMPLIED refs IDREFS #IMPLIED mode NMTOKENS ' a  b '>]><r ident='a' refs='a'/>"

private def parsedDtd := parseDocument {} { baseUri := "", dtdValidation := true }
  (Atomic.ofStr dtdSource)

-- Defaults and token normalization come from the real XML parser.
#guard match parsedDtd with
  | .ok d => match d.root with
    | .element _ attrs _ => attrs.any (fun a => a.name == "mode" && a.value == "a b")
    | _ => false
  | .error _ => false

-- The runtime parse-xml path retains DTD ID and IDREF declarations.
#guard match parseXmlFn { call := fun _ _ => pure [] } {}
    [[.atom (Atomic.ofStr dtdSource)]] with
  | .ok [.node n] => match n.rt with
    | some d => d.idAttrs.contains ("r", "ident") && d.idrefAttrs.contains ("r", "refs")
    | none => false
  | _ => false

#guard match parseXmlFn { call := fun _ _ => pure [] }
    { features := { dtdInfoset := false } } [[.atom (Atomic.ofStr dtdSource)]] with
  | .ok [.node n] => match n.rt with
    | some d => d.idAttrs.isEmpty && d.idrefAttrs.isEmpty
    | none => false
  | _ => false

-- DTD validity rejects dangling references; nonvalidating parsing accepts them.
private def dangling : String :=
  "<!DOCTYPE r [<!ELEMENT r EMPTY><!ATTLIST r refs IDREF #IMPLIED>]><r refs='missing'/>"
#guard match parseDocument {} { baseUri := "", dtdValidation := true } (Atomic.ofStr dangling) with
  | .error e => e.code == "FODC0007"
  | _ => false
#guard (parseDocument {} { baseUri := "" } (Atomic.ofStr dangling)).isOk

-- Parser notes retain reference provenance for EMPTY content validation.
private def emptyEntity : String :=
  "<!DOCTYPE r [<!ELEMENT r EMPTY><!ENTITY empty ''>]><r>&empty;</r>"
#guard match parseDocument {} { baseUri := "", dtdValidation := true } (Atomic.ofStr emptyEntity) with
  | .error e => e.code == "FODC0007"
  | _ => false

#guard match parseOpts { features := { dtdValidation := false } }
    [.map [(Atomic.ofStr "dtd-validation", sBool true)]] with
  | .error e => e.code == "FODC0007"
  | _ => false

private def xiNodes : List Node := [.element "r"
  [{ name := "xmlns:xi", value := "http://www.w3.org/2001/XInclude" }]
  [.element "xi:include" [{ name := "href", value := "part.xml" }] []]]
private def xiEnv : Env :=
  { features := { xinclude := true }, resources := [("http://example.test/part.xml", "<part>value</part>")] }
private def xiOptions : ParseOpts := { baseUri := "http://example.test/main.xml", xinclude := true, trustExternal := true }

#guard match configuredIncludes xiEnv xiOptions xiOptions.baseUri xiNodes with
  | .ok [.element _ _ [.element "part" attrs [.text "value"]]] =>
    attrs.any (fun a => a.name == "xmlns" && a.value == "") &&
    attrs.any (fun a => a.name == "xml:base" && a.value == "http://example.test/part.xml") &&
    attrs.any (fun a => a.name == "xml:lang" && a.value == "")
  | _ => false

#guard match configuredIncludes xiEnv { xiOptions with xinclude := false } xiOptions.baseUri xiNodes with
  | .ok result => decide (result = xiNodes)
  | _ => false

#guard match configuredIncludes {} xiOptions xiOptions.baseUri xiNodes with
  | .error e => e.code == "FODC0013"
  | _ => false

#guard match configuredIncludes xiEnv { xiOptions with trustExternal := false } xiOptions.baseUri xiNodes with
  | .error e => e.code == "FODC0016"
  | _ => false

#guard match parseOpts {} [.map [(Atomic.ofStr "xinclude", sBool true)]] with
  | .error e => e.code == "FODC0013"
  | _ => false

-- Text inclusion keeps markup literal.
#guard match configuredIncludes { resources := [("part.txt", "<literal>")] }
    xiOptions "" [.element "include"
      [{ name := "xmlns", value := "http://www.w3.org/2001/XInclude" },
       { name := "href", value := "part.txt" }, { name := "parse", value := "text" }] []] with
  | .ok [.text "<literal>"] => true
  | _ => false

-- Missing resources select fallback, whose inherited namespace is retained.
#guard match configuredIncludes {} xiOptions "http://example.test/main.xml"
    [.element "xi:include"
      [{ name := "xmlns:xi", value := "http://www.w3.org/2001/XInclude" },
       { name := "href", value := "absent.xml" }]
      [.element "xi:fallback" [{ name := "xmlns:p", value := "urn:fallback" }]
        [.element "p:result" [] []]]] with
  | .ok [.element "p:result" attrs []] =>
    attrs.any (fun a => a.name == "xmlns:p" && a.value == "urn:fallback")
  | _ => false

-- A resource cannot include itself indefinitely.
#guard match configuredIncludes
    { resources := [("http://example.test/part.xml",
        "<xi:include xmlns:xi='http://www.w3.org/2001/XInclude' href='part.xml'/>")] }
    xiOptions xiOptions.baseUri xiNodes with
  | .error e => e.code == "FODC0013"
  | _ => false

private def resultCode (r : M Seq) : String :=
  match r with
  | .ok items => showSeq items
  | .error e => e.code

private def dtdEvalEnv : Env :=
  { vars := [({ uri := "", loc := "source" }, sStr dtdSource)] }

#guard resultCode (evalString "name(id('a',parse-xml($source)))" dtdEvalEnv) == "r"
#guard resultCode (evalString "name(idref('a',parse-xml($source)))" dtdEvalEnv) == "refs"
#guard resultCode (evalString "name(element-with-id('a',parse-xml($source)))" dtdEvalEnv) == "r"
#guard resultCode (evalString "count(id('a',parse-xml($source)))"
  (dtdEvalEnv.restrictFeatures { dtdInfoset := false })) == "0"
#guard resultCode (evalString "count(idref('a',parse-xml($source)))"
  (dtdEvalEnv.restrictFeatures { dtdInfoset := false })) == "0"

-- Disabling namespace axes is a static error, including in an unused branch.
#guard resultCode (evalString "if (false()) then namespace::* else 1"
  (({} : Env).restrictFeatures { namespaceAxis := false })) == "XPST0010"

private def xiEvalEnv : Env :=
  { xiEnv with baseUri := xiOptions.baseUri,
    vars := [({ uri := "", loc := "source" },
      sStr "<r xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='part.xml'/></r>")] }
#guard resultCode (evalString
  "string(parse-xml($source,map{'xinclude':true(),'trust-external':true()})/r/part)"
  xiEvalEnv) == "value"
#guard resultCode (evalString
  "parse-xml($source,map{'xinclude':true(),'trust-external':true()})"
  { xiEvalEnv with features := { xinclude := false } }) == "FODC0013"

-- Registered fn:doc documents are reparsed from their resources when an
-- explicit option changes document construction.
private def registeredDtdEnv : Env :=
  { dtdEvalEnv with docs := #[Doc.ofNodes [.element "stale" [] []]],
    docUris := [("doc.xml", 0)], resources := [("doc.xml", dtdSource)] }
#guard resultCode (evalString "name(doc('doc.xml',map{'dtd-validation':true()})/*)"
  registeredDtdEnv) == "r"
#guard resultCode (evalString "name(doc('doc.xml')/*)" registeredDtdEnv) == "stale"

end L4Factoidal.XPath4
