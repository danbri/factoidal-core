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

/-- `node_query` op 127: transform the tree under `source` with the stylesheet under
`style`. The answer is `1`, the output method (`xml`, `html` or `text`), U+0001 and the
serialised result; or `0` and the reason the processor refused. -/
def transformAnswer (d : Dom) (style source : NodeId) : String :=
  match documentOf d style, documentOf d source with
  | some st, some src =>
    (match XSLT.transform st src with
     | .produced text =>
       "1" ++ (XSLT.readStylesheetWith [] 8 0 st.root).outputMethod ++ "\x01" ++ text
     | .refused reason => "0" ++ reason)
  | _, _ => "0the stylesheet or the source has no document element"

end L4Factoidal.DOM.XsltDom
