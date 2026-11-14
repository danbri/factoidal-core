/-
L4Factoidal.DOM.XPath.Xslt — `XSLTProcessor` (HTML §4.12.1.4 names the interface; the
transform is XSLT 1.0) over the tree's own XSLT 1.0 processor, `L4Factoidal.XSLT`.

The stylesheet and the source are DOM trees. Each is given to the processor as the
`XML.Document` of its projection (`DOM/XPath/Project.lean`, the projection that DOM
XPath uses): the same tree, with the namespace declarations that give each node the
DOM's namespace and the prefix declarations of the DOM in scope. The processor answers
the serialised result tree and the stylesheet's output method; the page's script layer
gives that text to the HTML or the XML parser of the engine for the method, and makes
the Document or the DocumentFragment. Nothing of XSLT is decided outside `XSLT.transform`.

For the output method `html` the text is made fit for the HTML parser (`expandEmptyTags`).

Not done here (open): parameters (`setParameter`) do not reach the stylesheet; the
functions `key`, `format-number` and `unparsed-entity-uri` are not in the processor;
`xsl:import` and `xsl:include` load nothing.
-/
import L4Factoidal.DOM.XPath.Project
import L4Factoidal.XSLT.Transform

namespace L4Factoidal.DOM.XsltDom

open L4Factoidal.DOM

/-- An element node of the projection. -/
def isElementNode : XML.Node → Bool
  | .element _ _ _ => true
  | _ => false

/-- The XML document of the tree under DOM node `node` (a Document, or an element as the
document element), or `none` when it has no element at the top. -/
def documentOf (d : Dom) (node : NodeId) : Option XML.Document :=
  let doc := XPathDom.projDoc d node
  match doc.dropWhile (fun n => !isElementNode n) with
  | r :: rest =>
    some { decl := none, doctype := none,
           prolog := doc.takeWhile (fun n => !isElementNode n), root := r, epilog := rest }
  | [] => none

/-- The void elements of HTML: the empty elements that the HTML syntax writes with no end
tag (HTML §13.1.2). -/
def htmlVoidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source",
   "track", "wbr"]

/-- The serialised result for the HTML parser: each empty element that is not a void
element of HTML is written with an end tag. The XSLT 1.0 processor serialises as XML
(`<div/>`), and the HTML parser reads `<div/>` as a start tag that nothing closes.

This is the scan of the lab's `WebXslt.expandEmptyTags` (which a page's
`<?xml-stylesheet?>` uses), here for `XSLTProcessor`; the two are one function to be
(listed as open in the design record). States: 0 text, 1 in a tag name, 2 in a tag,
3 in a comment or a processing instruction. -/
def expandEmptyTags (text : String) : String := Id.run do
  let mut out : Array Char := #[]
  let mut tag : Array Char := #[]
  let mut state := 0
  let mut quote : Option Char := none
  for c in text.toList do
    if state == 3 then
      out := out.push c
      if c == '>' && (out.size < 3 || (out[out.size-2]! == '-' && out[out.size-3]! == '-') || out[out.size-2]! == '?') then state := 0
    else if state == 0 then
      out := out.push c
      if c == '<' then
        tag := #[]
        state := 1
    else if let some q := quote then
      out := out.push c
      if c == q then quote := none
    else if c == '"' || c == '\'' then
      out := out.push c
      quote := some c
    else if state == 1 && (c == '!' || c == '?') && tag.isEmpty then
      out := out.push c
      state := 3
    else if c == '>' then
      let name := String.ofList tag.toList
      if out.back? == some '/' && !htmlVoidTags.contains name.toLower then
        out := out.pop ++ (">" ++ "</" ++ name ++ ">").toList.toArray
      else out := out.push c
      state := 0
    else
      out := out.push c
      if state == 1 then
        if c.isWhitespace || c == '/' then state := 2 else tag := tag.push c
  return String.ofList out.toList

/-- `node_query` op 127: transform the tree under `source` with the stylesheet under
`style`. The answer is `1`, the output method (`xml`, `html` or `text`), U+0001 and the
serialised result; or `0` and the reason the processor refused. -/
def transformAnswer (d : Dom) (style source : NodeId) : String :=
  match documentOf d style, documentOf d source with
  | some st, some src =>
    (match XSLT.transform st src with
     | .produced text =>
       let method := (XSLT.readStylesheetWith [] 8 0 st.root).outputMethod
       "1" ++ method ++ "\x01" ++ (if method == "html" then expandEmptyTags text else text)
     | .refused reason => "0" ++ reason)
  | _, _ => "0the stylesheet or the source has no document element"

end L4Factoidal.DOM.XsltDom
