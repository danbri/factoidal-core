/-
L4Factoidal.DOM.CustomElements — the decisions of custom elements that are functions of a
name or of the tree (HTML §4.13 "Custom elements").

Specification: HTML Living Standard §4.13.3 "Core concepts" ("valid custom element name"),
DOM §1.4 ("valid element local name"), and §4.13.6 "Custom element reactions" for the order
of the elements a tree change reaches (shadow-including tree order).

The registry, the constructors and the callbacks are JavaScript objects of the page
(prelude.js, section customelements). What is decided here: whether a name may be defined, and
which elements, in which order, an insertion or a removal of a subtree reaches.
-/
import L4Factoidal.DOM.Arena

namespace L4Factoidal.DOM.CustomElements
open L4Factoidal.DOM

/-- The names of SVG and MathML elements that contain a hyphen and so can not be custom
element names (HTML §4.13.3). -/
def reserved : List String :=
  ["annotation-xml", "color-profile", "font-face", "font-face-src", "font-face-uri",
   "font-face-format", "font-face-name", "missing-glyph"]

def isLowerAlpha (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def isUpperAlpha (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- "Valid custom element name" (HTML §4.13.3): a valid element local name whose first code
point is an ASCII lower alpha, with no ASCII upper alpha, with a U+002D (-), and not one of
the reserved names. -/
def validName (name : String) : Bool :=
  Dom.validElementLocalName name &&
  (match name.toList with | c :: _ => isLowerAlpha c | [] => false) &&
  !name.toList.any isUpperAlpha &&
  name.toList.contains '-' &&
  !reserved.contains name

/-- The elements among the shadow-including inclusive descendants of `n`, in
shadow-including tree order (DOM §4.8: a shadow host's shadow root and its descendants come
before the host's children). These are the elements a tree change at `n` reaches. -/
def reachGo (d : Dom) : Nat → List NodeId → Array NodeId → Array NodeId
  | 0, _, out => out
  | _, [], out => out
  | fuel + 1, x :: rest, out =>
    let nd := d.get x
    let out := if nd.type == .element then out.push x else out
    let shadow := match nd.shadow with | some s => [s] | none => []
    reachGo d fuel (shadow ++ nd.kids.toList ++ rest) out

/-- `reachGo` from `n` with fuel for every node of the arena. -/
def reach (d : Dom) (n : NodeId) : Array NodeId := reachGo d (d.size + 1) [n] #[]

/-- The wire form of `reach` for the page objects: node numbers separated by spaces. -/
def reachWire (d : Dom) (n : NodeId) : String := " ".intercalate ((reach d n).toList.map toString)

/-! ## What is proved -/

/-- Refusal (a policy decision refuses what it must). Says: no reserved name is a valid
custom element name. Does not say: which other names are refused. -/
theorem reserved_refused (name : String) (h : reserved.contains name = true) : validName name = false := by
  unfold validName
  rw [h]
  simp

/-- Says: a valid custom element name is a valid element local name, so `createElement`
accepts every name that `define` accepts. Does not say: the converse. -/
theorem validName_local (name : String) (h : validName name = true) :
    Dom.validElementLocalName name = true := by
  simp only [validName, Bool.and_eq_true] at h
  exact h.1.1.1.1

/-- Says: a valid custom element name contains a hyphen (the property that keeps custom
names apart from the names HTML defines now or later). Does not say: where it is. -/
theorem validName_hyphen (name : String) (h : validName name = true) :
    name.toList.contains '-' = true := by
  simp only [validName, Bool.and_eq_true] at h
  exact h.1.2

/-- Says: a valid custom element name has no ASCII upper alpha, so it is its own ASCII
lower-case form and an HTML parser's lower-casing of a tag name does not change it. Does
not say: anything about characters outside ASCII. -/
theorem validName_noUpper (name : String) (h : validName name = true) :
    name.toList.any isUpperAlpha = false := by
  simp only [validName, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.1.2

/-- Says: the walk with no fuel, or with no work, adds nothing. Does not say: that the fuel
of `reach` is enough for every arena (it is one step a node; a well-formed arena has no
node twice in the walk). -/
theorem reachGo_nil (d : Dom) (fuel : Nat) (out : Array NodeId) : reachGo d fuel [] out = out := by
  cases fuel <;> rfl

/-! ## Tests (the names of WPT custom-elements/registries/valid-custom-element-names.html) -/

#guard validName "a-element"
#guard validName "annotation-xml-custom"
#guard validName "a-"
#guard validName "a-é"
#guard validName "a-.b_c:d"
#guard !validName ""
#guard !validName "annotation-xml"
#guard !validName "font-face"
#guard !validName "missing-glyph"
#guard !validName "div"
#guard !validName "-a"
#guard !validName "A-b"
#guard !validName "a-B"
#guard !validName "1-a"
#guard !validName "a- b"
#guard !validName "a-/b"
#guard !validName "a->b"
#guard !validName "a-\x00b"
#guard !validName "_a-b"

private def tree : Dom :=
  { nodes := #[
      { type := .document, kids := #[1] },
      { type := .element, lname := "a", parent := some 0, kids := #[2, 3], shadow := some 4 },
      { type := .text, parent := some 1 },
      { type := .element, lname := "b", parent := some 1 },
      { type := .fragment, host := some 1, kids := #[5], shadowInit := some {} },
      { type := .element, lname := "s", parent := some 4 }] }

-- the shadow tree of 1 (5) comes before its light children (3); text is not an element
#guard reach tree 1 == #[1, 5, 3]
#guard reach tree 0 == #[1, 5, 3]
#guard reachWire tree 3 == "3"

end L4Factoidal.DOM.CustomElements
