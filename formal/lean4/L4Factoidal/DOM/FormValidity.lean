/-
L4Factoidal.DOM.FormValidity — the constraint validation of form controls and the typed
value of an `input`, read from the tree (HTML §4.10.21 "Constraints", §4.10.5).

Specification: HTML Living Standard §4.10.21.1 (candidates for constraint validation, barred
elements), §4.10.21.2 (the validity states), §4.10.5.1.5 (valid e-mail address), and the
conversions of `HTML.InputValue`.

The control's current value is the page's (it gives it with each question); everything else
is read from the element's attributes and the tree. The answers are for the page objects'
`validity`, `willValidate`, `checkValidity`, `value`, `valueAsNumber`, `valueAsDate`,
`stepUp` and `stepDown`.
-/
import L4Factoidal.DOM.FormControls
import L4Factoidal.HTML.InputValue
import L4Factoidal.WHATWG.URL.Parser

namespace L4Factoidal.DOM.FormValidity
open L4Factoidal.DOM L4Factoidal.DOM.Forms L4Factoidal.HTML

/-- The attributes of an `input` that its typed value reads. -/
def attrsOf (d : Dom) (k : NodeId) : InputValue.Attrs :=
  { min := attr? d k "min", max := attr? d k "max", step := attr? d k "step", dflt := attr? d k "value" }

/-- The control has a `datalist` ancestor. -/
def inDatalist (d : Dom) (k : NodeId) : Bool := Id.run do
  let mut cur := (d.get k).parent
  for _ in [0:d.size + 1] do
    match cur with
    | none => return false
    | some p => if isHtml d p ["datalist"] then return true else cur := (d.get p).parent
  return false

/-- A candidate for constraint validation (HTML §4.10.21.1): a submittable element that is
not barred. Barred: disabled; `readonly` on an `input` or `textarea`; a `datalist` ancestor;
an `input` of type hidden, reset or button; a `button` of type reset or button. `object`,
`fieldset` and `output` are never candidates. -/
def willValidate (d : Dom) (k : NodeId) : Bool :=
  isHtml d k ["button", "input", "select", "textarea"] &&
  !disabledControl d k &&
  !(isHtml d k ["input", "textarea"] && (attr? d k "readonly").isSome) &&
  !inDatalist d k &&
  !(isHtml d k ["input"] && ["hidden", "reset", "button"].contains (inputType d k)) &&
  !(isHtml d k ["button"] && buttonType d k != "submit")

def isAtext (c : Char) : Bool :=
  c.isAlphanum || ".!#$%&'*+/=?^_`{|}~-".toList.contains c

def isLabelChar (c : Char) : Bool := c.isAlphanum || c == '-'

/-- A valid e-mail address (HTML §4.10.5.1.5): one or more atext characters, "@", and one or
more labels of 1 to 63 letters, digits and hyphens that neither start nor end with a hyphen,
separated by dots. -/
def validEmail (s : String) : Bool :=
  match s.splitOn "@" with
  | [loc, dom] =>
    !loc.isEmpty && loc.toList.all isAtext &&
    (dom.splitOn ".").all fun l =>
      let cs := l.toList
      !cs.isEmpty && cs.length ≤ 63 && cs.all isLabelChar && cs.head? != some '-' && cs.getLast? != some '-'
  | _ => false

/-- The validity states that are functions of the tree and the value: bit 1 valueMissing,
2 typeMismatch, 32 rangeUnderflow, 64 rangeOverflow, 128 stepMismatch. (patternMismatch is
the page's, a JavaScript regular expression; tooLong and tooShort need a user edit;
customError is the page's message.) -/
def validityBits (d : Dom) (k : NodeId) (value : String) : Nat :=
  let b := fun (c : Bool) (bit : Nat) => if c then bit else 0
  let required := (attr? d k "required").isSome
  if isHtml d k ["textarea"] then b (required && value.isEmpty) 1
  else if isHtml d k ["select"] then
    let sel := FormControls.selectedOptions d k
    let placeholder := (attr? d k "multiple").isNone && FormControls.displaySize d k == 1 &&
      match (FormControls.optionList d k)[0]? with
      | some o => (d.get o).parent == some k && sel == #[o] &&
          (match attr? d o "value" with | some v => v.isEmpty | none => (d.textContent o).getD "" == "")
      | none => false
    b (required && (sel.isEmpty || placeholder)) 1
  else if !isHtml d k ["input"] then 0
  else
    let t := inputType d k
    let missing :=
      if t == "checkbox" then required && !checkedness d k
      else if t == "radio" then
        let group := (radioGroup d k).push k
        group.any (fun j => (attr? d j "required").isSome) && !group.any (checkedness d ·)
      else if ["text", "search", "url", "tel", "email", "password", "date", "month", "week", "time",
          "datetime-local", "number"].contains t then required && value.isEmpty
      else false
    let mismatch :=
      if value.isEmpty then false
      else if t == "url" then (L4Factoidal.WHATWG.URL.parseUrl value none).isNone
      else if t == "email" then
        if (attr? d k "multiple").isSome then !((value.splitOn ",").all validEmail) else !validEmail value
      else false
    let numeric := match InputValue.Ty.ofString t, (InputValue.Ty.ofString t).bind (InputValue.toNumber · value) with
      | some ty, some x =>
        let a := attrsOf d k
        b (InputValue.rangeUnderflow ty a x) 32 + b (InputValue.rangeOverflow ty a x) 64 + b (InputValue.stepMismatch ty a x) 128
      | _, _ => 0
    b missing 1 + b mismatch 2 + numeric

/-- `node_query` op 188 on element `k`: `q` is a letter, then U+0000-separated arguments.
"S" value: the sanitized value. "N" value: the value as a number (a JavaScript number
literal), or "" for NaN. "n" number: the value for a number ("v" and the value), or "".
"D" value: the value as milliseconds for `valueAsDate`, or "". "d" milliseconds: the value
for a date ("v" and the value), or "". "+" or "-" value steps: `stepUp` or `stepDown`: "v"
and the new value, "u" unchanged, "e" InvalidStateError. "V" value: the validity bits.
"W": "1" when the element will validate. -/
def answer (d : Dom) (k : NodeId) (q : String) : String :=
  let t := if isHtml d k ["input"] then inputType d k else ""
  let ty := InputValue.Ty.ofString t
  let a := attrsOf d k
  match q.splitOn "\x00" with
  | ["S", v] => InputValue.sanitize t ((attr? d k "multiple").isSome) a v
  | ["N", v] => match ty.bind (InputValue.toNumber · v) with
    | some x => L4Factoidal.JS.numToString x
    | none => ""
  | ["n", x] => match ty.bind (InputValue.ofNumber · (L4Factoidal.JS.strToNumber x)) with
    | some s => "v" ++ s
    | none => ""
  | ["D", v] =>
    match ty with
    | some .date | some .week | some .time => match ty.bind (InputValue.toNumber · v) with
      | some x => L4Factoidal.JS.numToString x
      | none => ""
    | some .month => match InputValue.parseMonth v with
      | some (y, m) => toString (InputValue.daysFromCivil y m 1 * 86400000)
      | none => ""
    | _ => ""
  | ["d", ms] =>
    let x := L4Factoidal.JS.strToNumber ms
    let s := match ty with
      | some .date => InputValue.ofNumber .date ((x / 86400000).floor * 86400000)
      | some .week => InputValue.ofNumber .week x
      | some .time => (InputValue.intOf x).bind fun i => InputValue.ofNumber .time (Float.ofInt (i.fmod 86400000))
      | some .month => (InputValue.intOf x).bind fun i =>
          (InputValue.civilFromDays (i.fdiv 86400000)).bind fun (y, m, _) =>
            InputValue.ofNumber .month (Float.ofInt (((y : Int) - 1970) * 12 + ((m : Int) - 1)))
      | _ => none
    match s with | some s => "v" ++ s | none => ""
  | [dir, v, steps] =>
    if dir != "+" && dir != "-" then "" else
    match ty, steps.toInt? with
    | some ty, some n => match InputValue.stepBy ty a v n (dir == "+") with
      | .invalidState => "e"
      | .unchanged => "u"
      | .value s => "v" ++ s
    | _, _ => "e"
  | ["V", v] => toString (validityBits d k v)
  | ["W"] => if willValidate d k then "1" else "0"
  | _ => ""

/-! ## What is proved -/

/-- Refusal. Says: a disabled control never validates: it is barred from constraint
validation, so it can not block a form's submission. Does not say: what `disabledControl`
decides (that is `Forms`'). -/
theorem disabled_barred (d : Dom) (k : NodeId) (h : disabledControl d k = true) : willValidate d k = false := by
  simp [willValidate, h]

/-- Refusal. Says: only `button`, `input`, `select` and `textarea` elements are candidates
for constraint validation; every other element (an `object`, a `fieldset`, an `output`, a
`div`) answers false. -/
theorem willValidate_submittable (d : Dom) (k : NodeId) (h : willValidate d k = true) :
    isHtml d k ["button", "input", "select", "textarea"] = true := by
  simp only [willValidate, Bool.and_eq_true] at h
  exact h.1.1.1.1.1

/-- Says: an element that is not an `input`, a `select` or a `textarea` has no validity
state set by its value. -/
theorem validityBits_other (d : Dom) (k : NodeId) (v : String)
    (h1 : isHtml d k ["textarea"] = false) (h2 : isHtml d k ["select"] = false) (h3 : isHtml d k ["input"] = false) :
    validityBits d k v = 0 := by
  simp [validityBits, h1, h2, h3]

/-! ## Tests -/

private def el (lname : String) (attrs : List (String × String)) (parent : Option NodeId) (kids : List NodeId) : Node :=
  { type := .element, ns := some htmlNS, lname, parent, kids := kids.toArray,
    attrs := (attrs.map fun (k, v) => ({ lname := k, value := v } : Attr)).toArray }

private def doc (ns : List Node) : Dom := { nodes := (({ type := .document, kids := ((List.range ns.length).map (· + 1)).toArray } : Node) :: ns).toArray }

#guard validEmail "a@b.c" && validEmail "a.b+c@d-e.f" && !validEmail "a@" && !validEmail "@b" && !validEmail "a@b..c" && !validEmail "a@-b.c" && !validEmail "a b@c"
#guard validityBits (doc [el "input" [("required", "")] (some 0) []]) 1 "" == 1
#guard validityBits (doc [el "input" [("required", "")] (some 0) []]) 1 "x" == 0
#guard validityBits (doc [el "input" [("type", "email")] (some 0) []]) 1 "nope" == 2
#guard validityBits (doc [el "input" [("type", "url")] (some 0) []]) 1 "http://a/" == 0
#guard validityBits (doc [el "input" [("type", "url")] (some 0) []]) 1 "a b" == 2
#guard validityBits (doc [el "input" [("type", "number"), ("min", "5"), ("max", "9"), ("step", "2")] (some 0) []]) 1 "4" == 32 + 128
#guard validityBits (doc [el "input" [("type", "number"), ("min", "5"), ("max", "9")] (some 0) []]) 1 "10" == 64
#guard validityBits (doc [el "input" [("type", "checkbox"), ("required", "")] (some 0) []]) 1 "" == 1
#guard validityBits (doc [el "input" [("type", "checkbox"), ("required", ""), ("checked", "")] (some 0) []]) 1 "" == 0
#guard validityBits (doc [el "textarea" [("required", "")] (some 0) []]) 1 "" == 1
#guard willValidate (doc [el "input" [] (some 0) []]) 1 && !willValidate (doc [el "input" [("disabled", "")] (some 0) []]) 1
#guard !willValidate (doc [el "input" [("type", "hidden")] (some 0) []]) 1 && !willValidate (doc [el "input" [("readonly", "")] (some 0) []]) 1
#guard !willValidate (doc [el "button" [("type", "reset")] (some 0) []]) 1 && willValidate (doc [el "button" [] (some 0) []]) 1
#guard !willValidate (doc [el "output" [] (some 0) []]) 1 && !willValidate (doc [el "fieldset" [] (some 0) []]) 1
#guard answer (doc [el "input" [("type", "date")] (some 0) []]) 1 "N\x002019-12-10" == "1575936000000"
#guard answer (doc [el "input" [("type", "date")] (some 0) []]) 1 "n\x001575936000000" == "v2019-12-10"
#guard answer (doc [el "input" [("type", "month")] (some 0) []]) 1 "D\x002019-12" == "1575158400000"
#guard answer (doc [el "input" [("type", "month")] (some 0) []]) 1 "d\x001575158400000" == "v2019-12"
#guard answer (doc [el "input" [("type", "number")] (some 0) []]) 1 "+\x005\x002" == "v7"
#guard answer (doc [el "input" [("type", "text")] (some 0) []]) 1 "+\x005\x002" == "e"
#guard answer (doc [el "input" [("type", "text")] (some 0) []]) 1 "S\x00a\nb" == "ab"
#guard answer (doc [el "input" [("type", "number")] (some 0) []]) 1 "N\x00" == ""
#guard answer (doc [el "input" [] (some 0) []]) 1 "W" == "1" && answer (doc [el "input" [("required", "")] (some 0) []]) 1 "V\x00" == "1"

end L4Factoidal.DOM.FormValidity
