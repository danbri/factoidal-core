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
import Std.Data.HashMap

namespace L4Factoidal.XML.C14nXPath

open L4Factoidal.XPath4
open L4Factoidal.XML.C14n

/-- The engine's index of node `i`. The engine gives an element's
namespace nodes indexes of their own (`nsNodeIdx`, read by `Doc.get`);
a namespace node that `C14nDoc.ofDoc` added is evaluated as the engine's
namespace node of the same parent and prefix, so that node identity (the
`|` operator, `count` of a union) agrees with the `namespace` axis. -/
def engineIdx (cd : C14nDoc) (i : Nat) : Nat :=
  if i < cd.n0 then i else
  let r := cd.doc.get i
  match r.parent with
  | some p =>
      match (nsNodesOf (cd.doc.get p)).findIdx? (·.1 == r.name.loc) with
      | some k => nsNodeIdx p k
      | none => i
  | none => i

/-- The function `here()` of XML Signature §6.6.3.1 and XPath Filter 2.0
§3.3: the element that bears the expression (`here?`, a node of `cd`).
With `none` the expression is not in the document it is evaluated
against, and the call is an error, as both specifications say. -/
def hereHost (cd : C14nDoc) (here? : Option Nat) : QN → Nat → Option HostFn := fun q k =>
  if q.uri == nsFN && q.loc == "here" && k == 0 then
    some fun _ _ => match here? with
      | some h => pure [.node (NodeRef.mk' 0 (engineIdx cd h))]
      | none => err "XPDY0002" "here(): the expression is not in the document it is evaluated against"
  else none

/-- The node-set of the nodes for which `expr` is true, with `ns` the
namespace declarations in scope for the expression and `here?` the
element that bears it (`hereHost`). -/
def xpathFilter (cd : C14nDoc) (expr : String) (ns : List (String × String))
    (here? : Option Nat := none) : Except String (Nat → Bool) := do
  let e ← (parseXPath expr ns).mapError (fun er => er.code ++ " " ++ er.msg)
  let mut keep : Array Bool := #[]
  for i in [0:cd.doc.nodes.size] do
    let env : Env := { docs := #[cd.doc], ctx := some [.node (NodeRef.mk' 0 (engineIdx cd i))],
                       pos := 1, size := 1, ns, host := hereHost cd here? }
    let v ← (eval 100000 env e >>= ebv).mapError (fun er => er.code ++ " " ++ er.msg)
    keep := keep.push v
  pure fun i => keep.getD i false

/-- The node of `cd` that the engine's index `j` names (the inverse of
`engineIdx`); `none` for a namespace node that `C14nDoc.ofDoc` did not
add (the engine's `xml` namespace node). -/
def cdIndexMap (cd : C14nDoc) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for j in [cd.n0:cd.doc.nodes.size] do
    m := m.insert (engineIdx cd j) j
  m

/-- The node-set that `expr` gives when it is evaluated once, with the
root node as the context node, context position and size 1 (XPath
Filter 2.0 §3.3). A result that is not a sequence of nodes of `cd` is an
error. -/
def xpathSelect (cd : C14nDoc) (expr : String) (ns : List (String × String))
    (here? : Option Nat := none) : Except String (Nat → Bool) := do
  let e ← (parseXPath expr ns).mapError (fun er => er.code ++ " " ++ er.msg)
  let env : Env := { docs := #[cd.doc], ctx := some [.node (NodeRef.mk' 0 0)],
                     pos := 1, size := 1, ns, host := hereHost cd here? }
  let v ← (eval 100000 env e).mapError (fun er => er.code ++ " " ++ er.msg)
  let m := cdIndexMap cd
  let mut keep : Array Bool := Array.replicate cd.doc.nodes.size false
  for it in v do
    match it with
    | .node r =>
        if r.doc != 0 || r.rt.isSome then throw "an XPath Filter 2.0 expression gave a node of another document"
        let j? := if r.idx < cd.n0 then some r.idx else m.get? r.idx
        if let some j := j? then keep := keep.set! j true
    | _ => throw "an XPath Filter 2.0 expression must give a node-set"
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
