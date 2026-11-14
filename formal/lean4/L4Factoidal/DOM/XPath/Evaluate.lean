/-
L4Factoidal.DOM.XPath.Evaluate — `document.evaluate` (DOM §8 "XPath"; the interfaces of
DOM Level 3 XPath) over the tree's XPath 1.0 evaluator.

The evaluator is `L4Factoidal.XPath.Full` (parser `XPath/Expr.lean`, data model
`XPath/Data.lean`, evaluation `XPath/Eval.lean`); `DOM/XPath/Project.lean` gives it the
DOM tree. This module holds what DOM XPath adds to XPath 1.0:

* the namespace prefixes of an expression (`prefixesOf`), which the page's
  XPathNSResolver resolves before evaluation;
* the name test of HTML documents (`htmlNameTest`): in an HTML document an unprefixed
  name test selects HTML elements, compared in ASCII lower case, and does not select
  an element of another or of no namespace; an unprefixed attribute name test on an
  HTML element is compared in ASCII lower case. This is the rule that Chrome, Firefox
  and Safari implement and that WPT `domxpath/text-html-elements.html` and
  `text-html-attributes.html` test; the DOM standard names the interfaces only;
* the conversion of the value to the requested XPathResult type (`answerOf`), and the
  errors (`evaluate`).

The page's script layer (`tools/wasmvm/quickjs/prelude.js`, section `xmlweb`) declares
the interfaces, calls the resolver and makes the result object. It decides nothing about
the expression or the nodes.

Wire format (`node_query` ops 121 and 122, `Hosts.DomOps`). Fields are separated by
U+0001, the parts of a field by U+0002. An answer that begins with `!` is an error: the
name of the exception follows.
-/
import L4Factoidal.DOM.XPath.Project

namespace L4Factoidal.DOM.XPathDom

open L4Factoidal.DOM

/-- The separator of the fields of a request and of an answer. -/
def sep : String := "\x01"

/-- The separator of the parts of one field. -/
def sep2 : String := "\x02"

/-- The answer for an error: `!` and the name of the exception the page throws. -/
def errAnswer (name : String) : String := "!" ++ name

/-! ## The prefixes of an expression -/

/-- The prefixes of the names in a token list, in the order written: a name token with a
colon (`p:local`), and a name before `:` (the test `p:*`). An axis name is followed by
`::`, which is another token, and a string literal is not a name token. -/
def prefixesGo (acc : List String) : List XPath.Full.Tok → List String
  | [] => acc.reverse
  | t :: rest =>
    match t, rest with
    | .name n, .op ":" :: _ => prefixesGo (n :: acc) rest
    | .name n, _ =>
      let p := XPath.Full.prefixOf n
      prefixesGo (if p == "" then acc else p :: acc) rest
    | _, _ => prefixesGo acc rest

/-- The namespace prefixes that expression `expr` uses, or `none` when `expr` is not an
XPath 1.0 expression. -/
def prefixesOf (expr : String) : Option (List String) :=
  match XPath.Full.parseExpr expr, XPath.Full.tokenize expr.toList with
  | some _, some ts => some (prefixesGo [] ts)
  | _, _ => none

/-- Op 121: the prefixes of `expr` separated by U+0001, or the SyntaxError answer. -/
def prefixesAnswer (expr : String) : String :=
  match prefixesOf expr with
  | some ps => sep.intercalate ps
  | none => errAnswer "SyntaxError"

/-! ## The name test of HTML documents -/

/-- The element that an attribute item belongs to is an HTML element. -/
def ownerIsHtml (d : XPath.Full.Doc) (it : XPath.Full.Item) : Bool :=
  match XPath.Full.parentOf d it with
  | some p => (XPath.Full.expandedName d p).1 == htmlNS
  | none => false

/-- The node test of a step when the context node's document is an HTML document. Only a
name test (`QName`) differs from XPath 1.0 §2.3 (`XPath.Full.matchesTest`):

* an HTML element matches when its local name and the test's local part are equal in
  ASCII lower case, and the test has no prefix or its prefix is bound to the HTML
  namespace;
* any other element matches as in XPath 1.0, but never a test with no prefix;
* an attribute of an HTML element matches a test with no prefix when the attribute has
  no namespace and its local name is the test in ASCII lower case;
* every other case is XPath 1.0. -/
def htmlNameTest (d : XPath.Full.Doc) (nsctx : List (String × String)) (ax : XPath.Full.Ax)
    (t : XPath.Full.NodeTest) (it : XPath.Full.Item) : Bool :=
  match t with
  | .name q =>
    if it.kind != XPath.Full.principalKind ax then false
    else if it.kind == XPath.Full.Kind.element then
      let nm := XPath.Full.expandedName d it
      let test := XPath.Full.expandTestName nsctx q
      let unprefixed := XPath.Full.prefixOf q == ""
      if nm.1 == htmlNS then
        Dom.asciiLower nm.2 == Dom.asciiLower test.2 && (unprefixed || test.1 == nm.1)
      else !unprefixed && nm == test
    else if it.kind == XPath.Full.Kind.attribute then
      let nm := XPath.Full.expandedName d it
      if XPath.Full.prefixOf q == "" && ownerIsHtml d it then
        nm.1 == "" && nm.2 == Dom.asciiLower q
      else nm == XPath.Full.expandTestName nsctx q
    else XPath.Full.matchesTest d nsctx ax t it
  | _ => XPath.Full.matchesTest d nsctx ax t it

/-! ## The answer -/

/-- A result node on the wire: the number of a node of the arena, or `a`, the element's
number, U+0002, the attribute's namespace (empty for none), U+0002, its local name. -/
def refWire (d : Dom) : Ref → String
  | .node id => toString id
  | .attr el idx =>
    match (d.get el).attrs[idx]? with
    | some a => "a" ++ toString el ++ sep2 ++ a.ns.getD "" ++ sep2 ++ a.lname
    | none => "a" ++ toString el ++ sep2 ++ sep2

/-- The nodes of a node-set on the wire, in document order, after the result type `k`. -/
def nodesAnswer (d : Dom) (root : NodeId) (k : Nat) (ns : List XPath.Full.Item) : String :=
  sep.intercalate (toString k ::
    (XPath.Full.normalize ns).filterMap fun it => (refOfItem d root it).map (refWire d))

/-- The value as the XPathResult type `want` asks (DOM Level 3 XPath §1.2, the constants
of `XPathResult`): 0 any type (a node-set gives an unordered iterator, type 4), 1 number,
2 string, 3 boolean (the conversions of XPath 1.0 §4), 4 to 9 the node-set types, which a
value that is not a node-set does not have (TypeError). The answer is the result type,
U+0001, and the value: a number as XPath writes it, a string, `1` or `0`, or the nodes. -/
def answerOf (d : Dom) (root : NodeId) (want : Nat) (v : XPath.Full.Value) : String :=
  if want == 0 then
    (match v with
     | .nodes ns => nodesAnswer d root 4 ns
     | .num n => "1" ++ sep ++ n.toXString
     | .bool b => "3" ++ sep ++ (if b then "1" else "0")
     | other => "2" ++ sep ++ other.toStr)
  else if want == 1 then "1" ++ sep ++ v.toNum.toXString
  else if want == 2 then "2" ++ sep ++ v.toStr
  else if want == 3 then "3" ++ sep ++ (if v.toBool then "1" else "0")
  else if want ≤ 9 then
    (match v with
     | .nodes ns => nodesAnswer d root want ns
     | _ => errAnswer "TypeError")
  else errAnswer "NotSupportedError"

/-- Evaluate expression `expr` with context node `ctx`, the namespace bindings of the
page's resolver and the requested result type.

Errors: SyntaxError when `expr` is not an XPath 1.0 expression or uses a function or a
variable the evaluator does not have; NotSupportedError when the context node is a
DocumentType or a DocumentFragment (they are not nodes of the XPath data model);
TypeError when a node-set type is asked of a value that is not a node-set.

The evaluation is `XPath.Full.evalExpr`, on the projection of the tree of the context
node. The checked entry `XPath.Full.eval` is not used: it refuses a document that is
not namespace well-formed, and a DOM tree need not be one (the HTML parser makes
elements whose local names hold a colon); the DOM, not the projection, is the authority
on a node's namespace. -/
def evaluate (d : Dom) (ctx : Ref) (expr : String) (bindings : List (String × String))
    (want : Nat) : String :=
  match XPath.Full.parseExpr expr with
  | none => errAnswer "SyntaxError"
  | some e =>
    let n := match ctx with | .node id => id | .attr el _ => el
    let t := (d.get n).type
    if n ≥ d.size || t == .doctype || t == .fragment then errAnswer "NotSupportedError" else
    let root := d.root n
    let doc := projDoc d root
    match itemOfRef d root doc ctx with
    | none => errAnswer "NotSupportedError"
    | some item =>
      let html := (d.get (if t == .document then n else (d.get n).doc)).htmlDoc
      let c : XPath.Full.Ctx :=
        { doc := doc, item := item, nsctx := bindings,
          nameTest? := if html then some htmlNameTest else none }
      match XPath.Full.evalExpr c e with
      | none => errAnswer "SyntaxError"
      | some v => answerOf d root want v

/-- One binding of the resolver on the wire: prefix, U+0002, namespace. -/
def bindingOf (s : String) : Option (String × String) :=
  match s.splitOn sep2 with
  | [p, u] => some (p, u)
  | _ => none

/-- The context node of a request: node `id`, or, when `spec` is `a`, a namespace (empty
for none), U+0002 and a local name, that attribute of element `id`. -/
def ctxOf (d : Dom) (id : NodeId) (spec : String) : Option Ref :=
  if spec == "" then some (Ref.node id)
  else
    match (String.ofList (spec.toList.drop 1)).splitOn sep2 with
    | [ns, lname] =>
      (d.attrIndexNS id (if ns == "" then none else some ns) lname).map (Ref.attr id)
    | _ => none

/-- Op 122: `q` is the result type, the context (`ctxOf`), the number of bindings, the
bindings (`bindingOf`) and the expression, separated by U+0001. The expression is last,
so it may itself hold U+0001 (in a string literal). The answer is `answerOf`'s or an
error. -/
def answer (d : Dom) (id : NodeId) (q : String) : String :=
  match q.splitOn sep with
  | want :: spec :: count :: rest =>
    let k := count.toNat?.getD 0
    let expr := sep.intercalate (rest.drop k)
    (match ctxOf d id spec with
     | some r => evaluate d r expr ((rest.take k).filterMap bindingOf) (want.toNat?.getD 0)
     | none => errAnswer "NotSupportedError")
  | _ => errAnswer "SyntaxError"

end L4Factoidal.DOM.XPathDom
