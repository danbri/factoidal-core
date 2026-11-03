/-
L4Factoidal.XML.XPointerXPath — the xpointer() scheme of XPointer, by
the XPath 4.0 engine (`L4Factoidal.XPath4.Eval`).

XPointer xpointer() Scheme, W3C Working Draft 19 December 2002,
https://www.w3.org/TR/2002/WD-xptr-xpointer-20021219/ . Its scheme data
is an XPath 1.0 `Expr` (§4) evaluated with the document node as the
context node, context position and size 1 (§4.1), and the namespace
bindings of the xmlns() parts to its left (Framework §3.3). Only the
location paths, node tests, predicates and functions of XPath 1.0 that
the XPath 4.0 engine reads are evaluated; the XPointer additions to
XPath 1.0 (points, ranges, `range-to`, `here()`, `origin()`,
`start-point()`) are not, and a part that uses them identifies no
subresource. A result that is not a sequence of nodes, an empty result
and an evaluation error each make the part fail (Framework §3.3).

`id()` is XPath's: the DTD's ID-typed attributes and `xml:id`
(`Doc.ofDocument`).

A node of the engine's table is turned back into a parse-tree node by
`toNode`; the bindings that its ancestors declare are kept apart in the
`Hit`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.XPointer
import L4Factoidal.XPath4.Eval

namespace L4Factoidal.XML.XPointerXPath

open L4Factoidal.XML
open L4Factoidal.XML.XPointer
open L4Factoidal.XPath4

/-- A name as written (`prefix:local` or `local`). -/
def written (q : QN) : String := if q.pfx == "" then q.loc else q.pfx ++ ":" ++ q.loc

/-- The bindings of a scope, the newest of each prefix only, without
`xml`. -/
def effective (sc : List (String × String)) : List (String × String) :=
  (sc.foldl (fun (acc : List (String × String)) (p, u) =>
    if p == "xml" || (acc.lookup p).isSome then acc else (p, u) :: acc) []).reverse

/-- The namespace declarations an element makes: the bindings of its
scope that differ from its parent's scope. -/
def ownDecls (parent own : List (String × String)) : List Attribute :=
  let par := effective parent
  (effective own).filterMap (fun (p, u) =>
    let before := (par.lookup p).getD ""
    if before == u then none
    else some { name := if p == "" then "xmlns" else "xmlns:" ++ p, value := u })

/-- The scope of a record's parent element (empty for the document node). -/
def parentScope (d : Doc) (r : NRec) : List (String × String) :=
  match r.parent with
  | some p => (d.get p).inscope
  | none => []

/-- The parse-tree node of record `i` of the engine's table. Recursion is
on the depth (`fuel`), as in `Doc.ofNodes`. -/
def toNode (d : Doc) : Nat → Nat → List Node
  | 0, _ => []
  | f + 1, i =>
    let r := d.get i
    match r.kind with
    | .text => [.text r.value]
    | .comment => [.comment r.value]
    | .pi => [.pi r.name.loc r.value]
    | .element =>
      let decls := ownDecls (parentScope d r) r.inscope
      let attrs := r.attrs.toList.map (fun j =>
        let a := d.get j
        ({ name := written a.name, value := a.value } : Attribute))
      [.element (written r.name) (decls ++ attrs) (r.children.toList.flatMap (toNode d f))]
    | .document => r.children.toList.flatMap (toNode d f)
    | .attribute | .namespace => []

/-- The hit of record `i`. A document node gives its children. -/
def hitOf (d : Doc) (i : Nat) : List Hit :=
  let r := d.get i
  match r.kind with
  | .attribute => [.attr { name := written r.name, value := r.value }]
  | .namespace => [.nsNode r.name.loc r.value]
  | .document => (toNode d 100000 i).map (fun n => .node n [])
  | _ => (toNode d 100000 i).map (fun n => .node n (parentScope d r))

/-- The xpointer() scheme (`XPointer.Schemes.xpointer`). -/
def xpointerScheme : SchemeHook := fun doc ns data =>
  let d := Doc.ofDocument doc
  match parseXPath data ns with
  | .error _ => none
  | .ok e =>
    let env : Env := { docs := #[d], ctx := some [.node (NodeRef.mk' 0 0)], pos := 1, size := 1, ns }
    match eval 100000 env e with
    | .error _ => none
    | .ok seq =>
      let idxs := seq.filterMap (fun it => match it with
        | .node r => if r.doc == 0 then some r.idx else none
        | _ => none)
      if idxs.isEmpty || idxs.length != seq.length then none
      else some (idxs.flatMap (hitOf d))

/-- The four schemes of XPointer: the Framework's shorthand, element(),
xmlns(), and xpointer(). -/
def schemes : Schemes := { xpointer := some xpointerScheme }

/-- Resolve a pointer with every scheme. -/
def resolveAll (d : Document) (s : String) : Outcome := resolve schemes d s

end L4Factoidal.XML.XPointerXPath
