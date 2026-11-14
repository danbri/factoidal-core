/-
L4Factoidal.DOM.Named — named access on the Window object (HTML §7.3.3).

Specification: HTML Living Standard, §7.3.3 "Named access on the Window object": the
supported property names of a Window, the named objects of a Window with a name, and the
value of a named property.

A page script that reads a name with no binding (`container.appendChild(x)` with an element
`<div id=container>`), or a property that the global object and its prototype chain do not
have (`window.container`), gets the value this module decides. The decision is a function of
the document tree only. It is asked for on a miss: a page that never reads such a name does
no work here.

The function answers for the document's tree (shadow trees are not document trees, and are
not walked). A nested browsing context is named by its container's `name` content attribute
when it was created; a later `window.name = …` inside the frame is not followed (open).
-/
import L4Factoidal.DOM.Arena

namespace L4Factoidal.DOM.Named
open L4Factoidal.DOM

/-- The value of the content attribute `nm` (no namespace) of a node. -/
def attrOf (x : Node) (nm : String) : Option String :=
  (x.attrs.find? fun a => a.ns.isNone && a.lname == nm).map (·.value)

/-- A navigable container whose content navigable has the target name `name` (HTML §7.3.3,
first bullet of "named objects"): an `iframe` or `frame` with that `name` attribute. -/
def namesFrame (x : Node) (name : String) : Bool :=
  (Dom.isHtmlElement x "iframe" || Dom.isHtmlElement x "frame") && attrOf x "name" == some name

/-- An element that is a named object for `name` (second and third bullets): an `embed`,
`form`, `img` or `object` whose `name` attribute is `name`, or an HTML element whose `id` is
`name`. -/
def namesElement (x : Node) (name : String) : Bool :=
  x.type == .element && x.ns == some htmlNS &&
    (attrOf x "id" == some name ||
      ((x.lname == "embed" || x.lname == "form" || x.lname == "img" || x.lname == "object") &&
        attrOf x "name" == some name))

/-- The named objects of the Window of document `doc` with the name `name`, in tree order:
navigable containers and elements. The empty string names nothing (the attributes must be
non-empty). -/
def namedObjects (d : Dom) (doc : NodeId) (name : String) : Array NodeId :=
  if name.isEmpty then #[]
  else (d.treeOrder doc false).filter fun k => namesFrame (d.get k) name || namesElement (d.get k) name

/-- The value of a named property (HTML §7.3.3, "determine the value of a named property"). -/
inductive Value where
  /-- Not a supported property name. -/
  | absent
  /-- The WindowProxy of the content navigable of this container (step 2). -/
  | frame (container : NodeId)
  /-- The one element (step 3). -/
  | element (el : NodeId)
  /-- An HTMLCollection of these elements, in tree order (step 4). -/
  | collection (els : Array NodeId)
  deriving Repr, BEq, Inhabited

/-- The value of the named property `name` of the Window of document `doc`. -/
def value (d : Dom) (doc : NodeId) (name : String) : Value :=
  let objs := namedObjects d doc name
  match objs.find? fun k => namesFrame (d.get k) name with
  | some c => .frame c
  | none =>
    if objs.size == 0 then .absent
    else if objs.size == 1 then .element (objs.getD 0 0)
    else .collection objs

/-- The answer for the page objects: "" (absent), "w" and the container, "e" and the element,
or "c" and the elements, numbers separated by spaces. -/
def Value.wire : Value → String
  | .absent => ""
  | .frame c => "w" ++ toString c
  | .element e => "e" ++ toString e
  | .collection els => "c" ++ " ".intercalate (els.toList.map toString)

/-- `node_query` op 33: the wire form of `value`. -/
def answer (d : Dom) (doc : NodeId) (name : String) : String := (value d doc name).wire

/-! ## What is proved -/

/-- Refusal (kind: a policy decision refuses what it must). Says: the empty string names no
object, in any document. Does not say: anything about names that are not empty. -/
theorem namedObjects_empty (d : Dom) (doc : NodeId) : namedObjects d doc "" = #[] := by
  simp [namedObjects]

/-- Soundness (kind: every answer is justified). Says: each node among the named objects is
in the tree order of the document asked about and is named `name` by one of the three
bullets of §7.3.3 (`namesFrame` or `namesElement`). Does not say: that `treeOrder` is the
tree order of the DOM standard (that is `Arena`'s), nor completeness (which holds by the
definition: the answer is the filter of the whole tree order). -/
theorem namedObjects_sound (d : Dom) (doc : NodeId) (name : String) (k : NodeId)
    (h : k ∈ namedObjects d doc name) :
    k ∈ d.treeOrder doc false ∧ (namesFrame (d.get k) name || namesElement (d.get k) name) = true := by
  unfold namedObjects at h
  split at h
  · simp at h
  · exact Array.mem_filter.mp h

/-- Refusal. Says: the empty string is never a supported property name: its value is
`absent`. Does not say: anything about other names. -/
theorem value_empty (d : Dom) (doc : NodeId) : value d doc "" = .absent := by
  simp [value, namedObjects]

/-- Says: an absent value has the empty wire form, so the page objects read "" as "not a
supported property name". Does not say: that other values have non-empty wire forms (they
do, by the leading letter; see the `#guard`s). -/
theorem wire_absent : Value.absent.wire = "" := rfl

/-! ## Tests -/

private def el (lname : String) (attrs : List (String × String)) (parent : NodeId) : Node :=
  { type := .element, ns := some htmlNS, lname, parent := some parent,
    attrs := (attrs.map fun (k, v) => ({ lname := k, value := v } : Attr)).toArray }

/-- A document 0 with children 1 `div#a`, 2 `form[name=f]`, 3 `img[name=a]`, 4 `p#b`,
5 `span#b`, 6 `iframe[name=fr]#x`, 7 `div[name=g]`, 8 an SVG `g#s`. -/
private def sample : Dom :=
  { nodes := #[
      { type := .document, kids := #[1, 2, 3, 4, 5, 6, 7, 8] },
      el "div" [("id", "a")] 0, el "form" [("name", "f")] 0, el "img" [("name", "a")] 0,
      el "p" [("id", "b")] 0, el "span" [("id", "b")] 0, el "iframe" [("name", "fr"), ("id", "x")] 0,
      el "div" [("name", "g")] 0,
      { type := .element, ns := some svgNS, lname := "g", parent := some 0,
        attrs := #[{ lname := "id", value := "s" }] }] }

#guard answer sample 0 "f" == "e2"
#guard answer sample 0 "a" == "c1 3"
#guard answer sample 0 "b" == "c4 5"
#guard answer sample 0 "fr" == "w6"
#guard answer sample 0 "x" == "e6"
-- `name` counts only on embed, form, img and object; `id` only on HTML elements
#guard answer sample 0 "g" == ""
#guard answer sample 0 "s" == ""
#guard answer sample 0 "" == ""
#guard answer sample 0 "nothing" == ""

end L4Factoidal.DOM.Named
