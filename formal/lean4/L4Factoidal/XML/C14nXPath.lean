/-
L4Factoidal.XML.C14nXPath — a document subset (XPath 1.0 node-set) for
`L4Factoidal.XML.C14n`, selected by an XPath expression evaluated with
each node of the document as the context node.

This is the XPath Filtering transform of XML Signature (XML-Signature
Syntax and Processing Version 1.1, W3C Recommendation 11 April 2013,
§6.6.3, `http://www.w3.org/TR/1999/REC-xpath-19991116`): "the
expression is evaluated once for each node of the input node-set and
the result is converted to a boolean"; the node is kept when it is
true. The input node-set here is the whole document, namespace nodes
included (`C14nDoc.ofDoc`). The document subset expressions of the
Canonical XML examples (§3.7 of 1.0, §3.7 and §3.8 of 1.1) have the
form `(//. | //@* | //namespace::*)[P]`, which selects the same nodes
as the filter `P` (XPath 1.0 §2.4: a predicate filters the node-set
with each node as the context node; `P` here uses neither `position()`
nor `last()`). `subsetPredicate?` takes `P` out of such an expression.

The expression is evaluated by the XPath 4.0 engine
(`L4Factoidal.XPath4.Eval`); its namespace nodes are the records that
`C14nDoc.ofDoc` adds, which the ancestor, parent and self axes reach
through their parent links.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.C14n
import L4Factoidal.XPath4.Eval

namespace L4Factoidal.XML.C14nXPath

open L4Factoidal.XPath4
open L4Factoidal.XML.C14n

/-- The node-set of the nodes for which `expr` is true, with `ns` the
namespace declarations in scope for the expression. -/
def xpathFilter (cd : C14nDoc) (expr : String) (ns : List (String × String)) :
    Except String (Nat → Bool) := do
  let e ← (parseXPath expr ns).mapError (fun er => er.code ++ " " ++ er.msg)
  let mut keep : Array Bool := #[]
  for i in [0:cd.doc.nodes.size] do
    let env : Env := { docs := #[cd.doc], ctx := some [.node (NodeRef.mk' 0 i)],
                       pos := 1, size := 1, ns }
    let v ← (eval 100000 env e >>= ebv).mapError (fun er => er.code ++ " " ++ er.msg)
    keep := keep.push v
  pure fun i => keep.getD i false

/-- `P` of a document subset expression `(//. | //@* | //namespace::*)[P]`. -/
def subsetPredicate? (s : String) : Option String :=
  let t := s.trimAscii.toString
  let head := "(//. | //@* | //namespace::*)"
  if !t.startsWith head then none
  else
    let rest := (t.drop head.length).trimAscii.toString
    if rest.startsWith "[" && rest.endsWith "]" then
      some ((rest.drop 1).dropEnd 1).toString
    else none

-- A filter that keeps one element and its namespace and attribute nodes.
#guard (match C14nDoc.ofString? "<r xmlns:p=\"u\"><p:a x=\"1\"/><b/></r>" with
  | .ok cd => match xpathFilter cd "ancestor-or-self::p:a" [("p", "u")] with
    | .ok s => match canonicalize { version := .c14n10 } cd s with
      | .ok o => o
      | .error e => e
    | .error e => e
  | .error e => e) == "<p:a xmlns:p=\"u\" x=\"1\"></p:a>"
#guard subsetPredicate? "(//. | //@* | //namespace::*)\n[\n  self::a\n]" == some "\n  self::a\n"

end L4Factoidal.XML.C14nXPath
