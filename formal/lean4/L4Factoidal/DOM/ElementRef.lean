/-
L4Factoidal.DOM.ElementRef — IDL attributes that reflect a content attribute as an element or
a list of elements (HTML §2.6.1 "Reflecting content attributes in IDL attributes", the rules
for `Element?` and `FrozenArray<Element>?`).

Specification: HTML Living Standard §2.6.1: "get the attr-associated element" and "get the
attr-associated elements"; DOM §4.2.4 (ID lookup in tree order), §4.8 (shadow-including
ancestors).

Used by the ARIA element attributes of ARIAMixin (`ariaActiveDescendantElement`,
`ariaLabelledByElements`, …), `popoverTargetElement` and `commandForElement`. The page keeps
the explicitly set elements (they are JavaScript object references); which element the getter
answers is decided here, from the tree.

The decision is a privacy boundary: an element inside a shadow tree is answered only to an
element inside that tree (or deeper), so a reference can not hand a script a node of a
shadow tree it could not reach.
-/
import L4Factoidal.DOM.Shadow

namespace L4Factoidal.DOM.ElementRef
open L4Factoidal.DOM

/-- The value of content attribute `name` (no namespace) of `el`. -/
def attr (d : Dom) (el : NodeId) (name : String) : Option String :=
  ((d.get el).attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)

/-- `c` is a descendant of a shadow-including ancestor of `el` (step 1.1 of "get the
attr-associated element"): `c` is not the root of its tree, and that root is a
shadow-including ancestor of `el` other than `el`. -/
def reachable (d : Dom) (el c : NodeId) : Bool :=
  let r := d.root c
  c != r && r != el && d.shadowIncludingAncestor r el

def isWs (c : Char) : Bool := c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '

/-- The first element with ID `id` among the descendants of `el`'s root, in tree order; the
empty string is no ID. -/
def byId (d : Dom) (el : NodeId) (id : String) : Option NodeId :=
  if id.isEmpty then none else d.getElementById (d.root el) id

/-- "Get the attr-associated element": the explicitly set element when it is reachable;
with none set, the first element of `el`'s tree whose ID is the attribute's value. -/
def attrElement (d : Dom) (el : NodeId) (name : String) (explicit : Option NodeId) : Option NodeId :=
  match explicit with
  | some c => if reachable d el c then some c else none
  | none => (attr d el name).bind (byId d el)

/-- "Get the attr-associated elements": the explicitly set elements that are reachable; with
none set, the elements that the attribute's ID tokens name, in the tokens' order. `none`
when there are neither explicit elements nor the attribute (the IDL attribute is null). -/
def attrElements (d : Dom) (el : NodeId) (name : String) (explicit : Option (List NodeId)) :
    Option (List NodeId) :=
  match explicit with
  | some cs => some (cs.filter (reachable d el))
  | none => (attr d el name).map fun v =>
      ((v.splitToList isWs).filter (· != "")).filterMap (byId d el)

/-- Wire form for the page objects: the element's number, or "" for null. -/
def elementWire (r : Option NodeId) : String := match r with | some k => toString k | none => ""

/-- Wire form: "-" for null, else the numbers separated by spaces. -/
def elementsWire (r : Option (List NodeId)) : String :=
  match r with
  | none => "-"
  | some ks => " ".intercalate (ks.map toString)

/-- `node_query` op 184: `q` is the attribute name, U+0000, and the explicitly set element's
number (or nothing). -/
def answerOne (d : Dom) (el : NodeId) (q : String) : String :=
  match q.splitOn "\x00" with
  | [name, e] => elementWire (attrElement d el name (e.toNat?.filter (· < d.size)))
  | _ => ""

/-- `node_query` op 185: `q` is the attribute name, U+0000, and "-" (no explicit elements) or
the explicitly set elements' numbers separated by spaces. -/
def answerMany (d : Dom) (el : NodeId) (q : String) : String :=
  match q.splitOn "\x00" with
  | [name, e] =>
    elementsWire (attrElements d el name
      (if e == "-" then none else some (((e.splitOn " ").filterMap String.toNat?).filter (· < d.size))))
  | _ => "-"

/-! ## What is proved -/

/-- Privacy (kind: a policy decision refuses what it must). Says: an explicitly set element is
answered only when it is reachable: it is a descendant of a shadow-including ancestor of the
referencing element. So an element inside a shadow tree that `el` is not inside is never
answered, whoever set it. Does not say: that `reachable` is the DOM standard's relation
(`shadowIncludingAncestor` is `Shadow`'s walk; on a well-formed arena it is). -/
theorem attrElement_explicit_reachable (d : Dom) (el : NodeId) (name : String) (c r : NodeId)
    (h : attrElement d el name (some c) = some r) : r = c ∧ reachable d el c = true := by
  unfold attrElement at h
  simp only at h
  split at h
  · rename_i hr
    simp only [Option.some.injEq] at h
    exact ⟨h.symm, hr⟩
  · simp at h

/-- Privacy. Says: every element of the answer to an explicit list is reachable, and is one
of the elements that were set (nothing is added). Does not say: anything about order beyond
that the filter keeps it. -/
theorem attrElements_explicit_reachable (d : Dom) (el : NodeId) (name : String) (cs rs : List NodeId)
    (h : attrElements d el name (some cs) = some rs) (r : NodeId) (hr : r ∈ rs) :
    r ∈ cs ∧ reachable d el r = true := by
  unfold attrElements at h
  simp only [Option.some.injEq] at h
  subst h
  exact List.mem_filter.mp hr

/-- Same tree (kind: every answer is justified). Says: an ID reference is answered with an
element found in the tree order of the referencing element's own root: an ID never names an
element of another tree (a shadow tree's inside, or another document). Does not say: that it
is the first such element (that is `Dom.getElementById`'s `find?`). -/
theorem byId_sameTree (d : Dom) (el : NodeId) (id : String) (r : NodeId)
    (h : byId d el id = some r) : r ∈ d.treeOrder (d.root el) false := by
  unfold byId at h
  split at h
  · simp at h
  · unfold Dom.getElementById at h
    exact Array.mem_of_find?_eq_some h

/-- Refusal. Says: with no explicit element and no content attribute, the answer is null. -/
theorem attrElement_absent (d : Dom) (el : NodeId) (name : String) (h : attr d el name = none) :
    attrElement d el name none = none := by
  simp [attrElement, h]

/-! ## Tests -/

private def elN (lname : String) (attrs : List (String × String)) (parent : Option NodeId) (kids : List NodeId)
    (shadow : Option NodeId := none) : Node :=
  { type := .element, ns := some htmlNS, lname, parent, kids := kids.toArray, shadow,
    attrs := (attrs.map fun (k, v) => ({ lname := k, value := v } : Attr)).toArray }

/-- Document 0 > div#host(1) [shadow root 4 > span#in(5), b#a(6)], p#a(2), q(3 for="a" list="in a zz").
A detached div(7) > i#a(8). -/
private def tree : Dom :=
  { nodes := #[
      { type := .document, kids := #[1, 2, 3] },
      elN "div" [("id", "host")] (some 0) [] (some 4),
      elN "p" [("id", "a")] (some 0) [],
      elN "q" [("for", "a"), ("list", "in a  zz")] (some 0) [],
      { type := .fragment, host := some 1, kids := #[5, 6], shadowInit := some {} },
      elN "span" [("id", "in")] (some 4) [],
      elN "b" [("id", "a"), ("for", "a")] (some 4) [],
      elN "div" [] none [8],
      elN "i" [("id", "a")] (some 7) []] }

-- an ID reference stays in its own tree: from the light tree `a` is 2, from the shadow tree 6
#guard attrElement tree 3 "for" none == some 2
#guard attrElement tree 6 "for" none == some 6
-- an ID inside a shadow tree is not found from outside
#guard attrElements tree 3 "list" none == some [2]
#guard attrElement tree 3 "nope" none == none
-- explicit: an element of the document is reachable from inside the shadow tree, not the reverse
#guard attrElement tree 6 "for" (some 2) == some 2
#guard attrElement tree 3 "for" (some 5) == none
#guard attrElement tree 5 "for" (some 6) == some 6
-- an element of a detached tree is not reachable from the document, nor from its own root
#guard attrElement tree 3 "for" (some 8) == none
#guard attrElement tree 7 "for" (some 8) == none
#guard attrElements tree 3 "list" (some [2, 5, 1]) == some [2, 1]
#guard answerOne tree 3 "for\x00" == "2" && answerOne tree 3 "for\x005" == "" && answerMany tree 3 "list\x00-" == "2"
#guard answerMany tree 3 "zz\x00-" == "-" && answerMany tree 3 "zz\x002 5" == "2"

end L4Factoidal.DOM.ElementRef
