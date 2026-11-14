/-
L4Factoidal.HTML.FormEntries — "constructing the entry list" of a form for script (HTML
§4.10.21.4), as `new FormData(form, submitter)` needs it (XMLHttpRequest Standard §5.3
"FormData"): the controls that contribute, and what each contributes.

One function for each control (`controlEntries`), so what a control gives is a value that
theorems can speak about; the entry list is those of the form's submittable elements in
tree order. The form owner is `DOM.FormControls.formOwner` (the `form` attribute counts)
and a `select`'s selected options are `DOM.FormControls.selectedOptions` (a selectedness
that a script set counts).

Limits, as elsewhere in the forms code: an `input`'s value is its `value` attribute; no
file is ever selected, so a file control gives one empty file; an image button's
coordinates are 0, 0; form-associated custom elements give nothing.
-/
import L4Factoidal.DOM.FormControls
import L4Factoidal.HTML.FormSubmission

namespace L4Factoidal.HTML.FormEntries
open L4Factoidal.DOM L4Factoidal.DOM.Forms

/-- An entry: a name and a string, or (with `file`) a file control's empty file. -/
structure Entry where
  name : String
  value : String := ""
  file : Bool := false
  deriving Repr, BEq, Inhabited

/-- A submit button (§4.10.18.6.4): a `button` whose type is submit, or an `input` whose
type is submit or image. -/
def isSubmitButton (d : Dom) (k : NodeId) : Bool :=
  (isHtml d k ["button"] && buttonType d k == "submit") ||
    (isHtml d k ["input"] && (inputType d k == "submit" || inputType d k == "image"))

/-- A button of any kind: it contributes only as the submitter. -/
def isButton (d : Dom) (k : NodeId) : Bool :=
  isHtml d k ["button"] || (isHtml d k ["input"] && ["submit", "image", "reset", "button"].contains (inputType d k))

/-- The `dirname` entry of a control (§4.10.18.2): the attribute's value as the name, and
the control's directionality as far as its own `dir` says. -/
def dirnameEntry (d : Dom) (k : NodeId) : List Entry :=
  match attr? d k "dirname" with
  | some n => if n.isEmpty then [] else [{ name := n, value := if Dom.asciiLower ((attr? d k "dir").getD "") == "rtl" then "rtl" else "ltr" }]
  | none => []

/-- What one submittable element gives the entry list (steps 5.1 to 5.13 of "constructing
the entry list"), with `charset` the encoding's name for a hidden `_charset_` control. -/
def controlEntries (d : Dom) (submitter : Option NodeId) (charset : String) (k : NodeId) : List Entry :=
  if FormSubmission.inDatalist d k || disabledControl d k then []
  else if isButton d k && submitter != some k then []
  else
    let isInput := isHtml d k ["input"]
    let t := if isInput then inputType d k else ""
    if isInput && (t == "checkbox" || t == "radio") && !checkedness d k then []
    else
      let name := (attr? d k "name").getD ""
      if isInput && t == "image" then
        let pfx := if name.isEmpty then "" else name ++ "."
        [{ name := pfx ++ "x", value := "0" }, { name := pfx ++ "y", value := "0" }]
      else if name.isEmpty then []
      else if isHtml d k ["select"] then
        ((FormControls.selectedOptions d k).toList.filter fun o => !FormControls.optionDisabled d o).map fun o =>
          { name, value := FormSubmission.optionValue d o }
      else if isInput && (t == "checkbox" || t == "radio") then [{ name, value := (attr? d k "value").getD "on" }]
      else if isInput && t == "file" then [{ name, file := true }]
      else if isInput && t == "hidden" && Dom.asciiLower name == "_charset_" then [{ name, value := charset }]
      else if isHtml d k ["textarea"] then { name, value := (d.textContent k).getD "" } :: dirnameEntry d k
      else if isInput then { name, value := (attr? d k "value").getD "" } :: dirnameEntry d k
      else [{ name, value := (attr? d k "value").getD "" }]

/-- The submittable elements whose form owner is the form, in tree order. -/
def controls (d : Dom) (form : NodeId) : List NodeId :=
  ((d.treeOrder (d.root form) false).filter fun k =>
    isHtml d k ["button", "input", "select", "textarea"] && FormControls.formOwner d k == some form).toList

/-- "Construct the entry list" of a form with a submitter (none: no submitter). -/
def entries (d : Dom) (form : NodeId) (submitter : Option NodeId) (charset : String := "UTF-8") : List Entry :=
  (controls d form).flatMap (controlEntries d submitter charset)

/-- What `new FormData(form, submitter)` checks of its submitter (XHR §5.3 step 1). -/
inductive SubmitterCheck where
  | ok
  /-- Not a submit button: a TypeError. -/
  | notSubmitButton
  /-- Not owned by the form: a "NotFoundError" DOMException. -/
  | notOwned
  deriving Repr, DecidableEq

def checkSubmitter (d : Dom) (form submitter : NodeId) : SubmitterCheck :=
  if !isSubmitButton d submitter then .notSubmitButton
  else if FormControls.formOwner d submitter != some form then .notOwned
  else .ok

/-! ## Wire (node_query 196) -/

/-- A name or a value on the wire: a character below U+0008 is U+0007 and the character 64
above it, so the separators never occur inside one. -/
def esc (s : String) : String :=
  String.ofList (s.toList.flatMap fun c => if c.toNat < 8 then ['\x07', Char.ofNat (c.toNat + 64)] else [c])

/-- node_query 196 on a form: `q` is the submitter's node number, or "" for none. Answers
"T" (the submitter is not a submit button), "N" (it is not owned by the form), or "K" and
the entries separated by U+0002, each its name, U+0001, its value, U+0001, "1" for a file
control's empty file. -/
def answer (d : Dom) (form : NodeId) (q : String) : String :=
  let submitter := if q.isEmpty then none else q.toNat?
  let check := match submitter with
    | some s => checkSubmitter d form s
    | none => .ok
  match check with
  | .notSubmitButton => "T"
  | .notOwned => "N"
  | .ok =>
    "K" ++ "\x02".intercalate ((entries d form submitter).map fun e =>
      esc e.name ++ "\x01" ++ esc e.value ++ "\x01" ++ (if e.file then "1" else "0"))

/-! ## What is proved -/

/-- Says: a disabled control gives the entry list nothing. -/
theorem disabled_gives_nothing (d : Dom) (submitter : Option NodeId) (charset : String) (k : NodeId)
    (h : disabledControl d k = true) : controlEntries d submitter charset k = [] := by
  unfold controlEntries
  rw [h, Bool.or_true]
  rfl

/-- Says: a button that is not the submitter gives nothing (so pressing one button never
sends another's name). -/
theorem other_button_gives_nothing (d : Dom) (submitter : Option NodeId) (charset : String) (k : NodeId)
    (hb : isButton d k = true) (hs : submitter ≠ some k) : controlEntries d submitter charset k = [] := by
  have hc : (isButton d k && submitter != some k) = true := by simp [hb, hs]
  unfold controlEntries
  split
  · rfl
  · first | rfl | rw [if_pos hc]

/-- Says: every entry comes from a submittable element that the form owns. -/
theorem entries_from_owned (d : Dom) (form : NodeId) (submitter : Option NodeId) (charset : String) (e : Entry)
    (h : e ∈ entries d form submitter charset) :
    ∃ k, FormControls.formOwner d k = some form ∧ e ∈ controlEntries d submitter charset k := by
  unfold entries at h
  rcases List.mem_flatMap.mp h with ⟨k, hk, he⟩
  refine ⟨k, ?_, he⟩
  unfold controls at hk
  have := (Array.mem_filter.mp (Array.mem_toList_iff.mp hk)).2
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

/-- Says: with no submitter, no button of any kind is in the entry list's controls'
contributions (`FormData(form)` never names a button). -/
theorem no_submitter_no_button (d : Dom) (charset : String) (k : NodeId) (hb : isButton d k = true) :
    controlEntries d none charset k = [] :=
  other_button_gives_nothing d none charset k hb (by simp)

/-! ## Tests (html/semantics/forms/form-submission-0/constructing-form-data-set.html) -/

private def el (name : String) (parent : Nat) (attrs : List (String × String)) (kids : Array Nat := #[]) : Node :=
  { type := .element, ns := some htmlNS, lname := name, parent := some parent, kids,
    attrs := (attrs.map fun (k, v) => ({ lname := k, value := v } : Attr)).toArray }

private def formDoc : Dom := { nodes := #[
  { type := .document, kids := #[1], htmlDoc := true },
  el "form" 0 [("id", "f")] #[2, 3, 4, 5, 6, 7, 8, 11, 12, 13],
  el "input" 1 [("name", "a"), ("value", "1")],
  el "input" 1 [("name", "b"), ("value", "2"), ("disabled", "")],
  el "input" 1 [("type", "checkbox"), ("name", "c")],
  el "input" 1 [("type", "checkbox"), ("name", "d"), ("checked", "")],
  el "input" 1 [("type", "submit"), ("name", "go"), ("value", "Go")],
  el "button" 1 [("name", "other"), ("value", "x")],
  el "select" 1 [("name", "s")] #[9, 10],
  el "option" 8 [("value", "one")],
  el "option" 8 [("value", "two"), ("selected", "")],
  el "textarea" 1 [("name", "t")],
  el "input" 1 [("type", "file"), ("name", "up")],
  el "input" 1 [("type", "image"), ("name", "img")],
  el "input" 0 [("type", "submit"), ("name", "outside")]] }

#guard (entries formDoc 1 none).map (fun e => (e.name, e.value, e.file)) ==
  [("a", "1", false), ("d", "on", false), ("s", "two", false), ("t", "", false), ("up", "", true)]
#guard (entries formDoc 1 (some 6)).map (·.name) == ["a", "d", "go", "s", "t", "up"]
#guard (entries formDoc 1 (some 13)).map (·.name) == ["a", "d", "s", "t", "up", "img.x", "img.y"]
#guard checkSubmitter formDoc 1 6 == .ok && checkSubmitter formDoc 1 2 == .notSubmitButton && checkSubmitter formDoc 1 14 == .notOwned
#guard answer formDoc 1 "2" == "T" && answer formDoc 1 "14" == "N"
#guard answer formDoc 1 "" == "Ka\x011\x010\x02d\x01on\x010\x02s\x01two\x010\x02t\x01\x010\x02up\x01\x011"
#guard esc "a\x01b" == "a\x07Ab"

end L4Factoidal.HTML.FormEntries
