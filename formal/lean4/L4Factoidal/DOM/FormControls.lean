/-
L4Factoidal.DOM.FormControls — what a form's script interface reads from the tree: the form
owner of a control, the controls of a form, the options of a `select` and which are selected,
and the labels of a control (HTML §4.10).

Specification: HTML Living Standard §4.10.2 (categories: listed, labelable), §4.10.3 (the
`elements` collection), §4.10.4 (labels), §4.10.7 (the `select` element: list of options,
selectedness, display size), §4.10.18.3 (form owner).

The collections that scripts see (`form.elements`, `select.options`, `select.selectedOptions`,
`control.labels`) are these functions of the tree, asked for when read.

Selectedness: an `option`'s selectedness is its `selected` attribute until a script sets it
(the dirtiness flag); the arena keeps a set value in `Node.checkedness`, as for an `input`'s
checkedness. A `select` without `multiple` and with display size 1 in which no option was
ever set by script shows its first option that is not disabled (the selectedness setting
algorithm's rule), and never has more than one selected option.
-/
import L4Factoidal.DOM.Forms
import L4Factoidal.DOM.Shadow

namespace L4Factoidal.DOM.FormControls
open L4Factoidal.DOM L4Factoidal.DOM.Forms

/-- Listed elements (HTML §4.10.2): the controls of `form.elements` and `fieldset.elements`. -/
def listed (d : Dom) (k : NodeId) : Bool :=
  isHtml d k ["button", "fieldset", "input", "object", "output", "select", "textarea"]

/-- The form owner (HTML §4.10.18.3 "reset the form owner"): for a connected listed element
with a `form` attribute, the first element of its tree with that ID when it is a `form`
(and no owner otherwise); else the nearest ancestor `form`. -/
def formOwner (d : Dom) (k : NodeId) : Option NodeId :=
  match (if listed d k && d.connected k then attr? d k "form" else none) with
  | some id =>
    match (if id.isEmpty then none else d.getElementById (d.root k) id) with
    | some f => if isHtml d f ["form"] then some f else none
    | none => none
  | none => Forms.formOwner d k

/-- The controls of `form.elements` (HTML §4.10.3): the listed elements whose form owner is
the form, except image buttons, in tree order. -/
def formElements (d : Dom) (f : NodeId) : Array NodeId :=
  (d.treeOrder (d.root f) false).filter fun k =>
    listed d k && !(isHtml d k ["input"] && inputType d k == "image") && formOwner d k == some f

/-- The list of options of a `select` (HTML §4.10.7): its `option` descendants, in tree
order (children, the children of `optgroup` children, and options inside other wrappers). -/
def optionList (d : Dom) (sel : NodeId) : Array NodeId :=
  (d.treeOrder sel false).filter fun k => isHtml d k ["option"]

/-- An option's selectedness: the value a script set, else the `selected` attribute. -/
def selectedness (d : Dom) (o : NodeId) : Bool :=
  match (d.get o).checkedness with
  | some v => v
  | none => (attr? d o "selected").isSome

/-- An option is disabled: its own `disabled`, or its parent `optgroup`'s. -/
def optionDisabled (d : Dom) (o : NodeId) : Bool :=
  (attr? d o "disabled").isSome ||
    match (d.get o).parent with
    | some p => isHtml d p ["optgroup"] && (attr? d p "disabled").isSome
    | none => false

/-- A non-negative integer attribute value: ASCII digits only (leading whitespace allowed). -/
def natAttr (s : String) : Option Nat :=
  let t := (s.toList.dropWhile fun c => c == ' ' || c == '\t' || c == '\n' || c == '\x0C' || c == '\r')
  let t := match t with | '+' :: r => r | r => r
  let ds := t.takeWhile fun c => '0' ≤ c && c ≤ '9'
  if ds.isEmpty then none else some (ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)

/-- The display size of a `select` (HTML §4.10.7): its `size` when a positive integer, else
4 with `multiple` and 1 without. -/
def displaySize (d : Dom) (sel : NodeId) : Nat :=
  match (attr? d sel "size").bind natAttr with
  | some n => if n == 0 then (if (attr? d sel "multiple").isSome then 4 else 1) else n
  | none => if (attr? d sel "multiple").isSome then 4 else 1

/-- The selected options of a `select`, in tree order. With `multiple`: every option whose
selectedness is true. Without: the last such option; or, when there is none, the display
size is 1 and no option's selectedness was ever set by a script, the first option that is
not disabled. -/
def selectedOptions (d : Dom) (sel : NodeId) : Array NodeId :=
  let opts := optionList d sel
  let on := opts.filter (selectedness d)
  if (attr? d sel "multiple").isSome then on
  else match on.back? with
    | some o => #[o]
    | none =>
      if displaySize d sel == 1 && opts.all (fun o => (d.get o).checkedness.isNone) then
        match opts.find? (fun o => !optionDisabled d o) with
        | some o => #[o]
        | none => #[]
      else #[]

/-- The labels of a labelable element (HTML §4.10.4): the `label` elements of its tree whose
labeled control it is, in tree order. -/
def labelsOf (d : Dom) (k : NodeId) : Array NodeId :=
  if !labelable d k then #[]
  else (d.treeOrder (d.root k) false).filter fun l => isHtml d l ["label"] && labeledControl d l == some k

def wire (ks : Array NodeId) : String := " ".intercalate (ks.toList.map toString)

/-- `node_query` op 186: "f" the form owner of `k` ("" for none); "e" the elements of form
`k`; "o" the options of select `k`; "s" its selected options; "l" the labels of `k`; "c" the
labeled control of label `k` ("" for none); "x" the selectedness of option `k` ("1" or "0"). -/
def answer (d : Dom) (k : NodeId) (q : String) : String :=
  match q with
  | "f" => match formOwner d k with | some f => toString f | none => ""
  | "e" => wire (formElements d k)
  | "o" => wire (optionList d k)
  | "s" => wire (selectedOptions d k)
  | "l" => wire (labelsOf d k)
  | "c" => match labeledControl d k with | some c => toString c | none => ""
  | "x" => if selectedness d k then "1" else "0"
  | _ => ""

/-! ## What is proved -/

/-- Says: a `select` without `multiple` never has more than one selected option, whatever
the attributes and the script-set selectedness of its options. Does not say: which one. -/
theorem single_select_at_most_one (d : Dom) (sel : NodeId) (h : (attr? d sel "multiple").isSome = false) :
    (selectedOptions d sel).size ≤ 1 := by
  unfold selectedOptions
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  split
  · simp
  · split
    · split <;> simp
    · simp

/-- Says: every control of `form.elements` is a listed element whose form owner is that
form: the collection never holds a control that would submit with another form, or with
none. Does not say: completeness beyond the definition (the filter of the whole tree). -/
theorem formElements_owned (d : Dom) (f k : NodeId) (h : k ∈ formElements d f) :
    listed d k = true ∧ formOwner d k = some f := by
  unfold formElements at h
  have h2 := (Array.mem_filter.mp h).2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h2.1.1, h2.2⟩

/-- Says: each label of a control is a `label` element whose labeled control is that control
(so `label.control` and `control.labels` agree). -/
theorem labelsOf_control (d : Dom) (k l : NodeId) (h : l ∈ labelsOf d k) :
    labeledControl d l = some k := by
  unfold labelsOf at h
  split at h
  · simp at h
  · have h2 := (Array.mem_filter.mp h).2
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact h2.2

/-! ## Tests -/

private def el (lname : String) (attrs : List (String × String)) (parent : Option NodeId) (kids : List NodeId)
    (checked : Option Bool := none) : Node :=
  { type := .element, ns := some htmlNS, lname, parent, kids := kids.toArray, checkedness := checked,
    attrs := (attrs.map fun (k, v) => ({ lname := k, value := v } : Attr)).toArray }

/-- Document 0 > form#f(1)[input(2), select(3)[option(4), optgroup disabled(5)[option selected(6)], option(7)],
input type=image(8), label for=x(9)], input#x form=f(10), input form=nope(11), form#g(12)[input form=f(13)]. -/
private def tree : Dom :=
  { nodes := #[
      { type := .document, kids := #[1, 10, 11, 12] },
      el "form" [("id", "f")] (some 0) [2, 3, 8, 9],
      el "input" [] (some 1) [],
      el "select" [] (some 1) [4, 5, 7],
      el "option" [] (some 3) [],
      el "optgroup" [("disabled", "")] (some 3) [6],
      el "option" [("selected", "")] (some 5) [],
      el "option" [] (some 3) [],
      el "input" [("type", "image")] (some 1) [],
      el "label" [("for", "x")] (some 1) [],
      el "input" [("id", "x"), ("form", "f")] (some 0) [],
      el "input" [("form", "nope")] (some 0) [],
      el "form" [("id", "g")] (some 0) [13],
      el "input" [("form", "f")] (some 12) []] }

#guard formOwner tree 2 == some 1 && formOwner tree 10 == some 1 && formOwner tree 11 == none && formOwner tree 13 == some 1
#guard formElements tree 1 == #[2, 3, 10, 13] && formElements tree 12 == #[]
#guard optionList tree 3 == #[4, 6, 7]
#guard selectedOptions tree 3 == #[6]
-- no option selected: the first that is not disabled
#guard selectedOptions (tree.setNode 6 fun x => { x with attrs := #[] }) 3 == #[4]
-- a script unselected every option: none
#guard selectedOptions (tree.setNode 6 fun x => { x with checkedness := some false }) 3 == #[]
-- two selected without multiple: the last; with multiple: both
#guard selectedOptions (tree.setNode 4 fun x => { x with checkedness := some true }) 3 == #[6]
#guard selectedOptions ((tree.setNode 4 fun x => { x with checkedness := some true }).setNode 3 fun x =>
  { x with attrs := #[{ lname := "multiple", value := "" }] }) 3 == #[4, 6]
#guard labelsOf tree 10 == #[9] && answer tree 9 "c" == "10" && answer tree 2 "f" == "1" && answer tree 1 "e" == "2 3 10 13"
#guard displaySize tree 3 == 1 && natAttr " 12px" == some 12 && natAttr "x" == none

end L4Factoidal.DOM.FormControls
