/-
L4Factoidal.DOM.Forms — the state of form controls and the activation behaviour that the
event dispatch algorithm needs (DOM §2.9 "dispatch" steps 5.4–5.13 and 11; HTML §4.10).

- Checkedness (HTML §4.10.5 "checkedness" and "dirty checkedness flag"): `Node.checkedness`
  is `none` while the flag is false (the checkedness is then whether the `checked` content
  attribute is present) and `some v` once script or a click changed it.
- The radio button group (HTML §4.10.5.1.15): radio inputs in the same tree, with the same
  form owner and the same non-empty name. Checking one unchecks the others.
- Which elements have activation behaviour (DOM §2.9 "activation behavior", HTML §4.6.4,
  §4.10.5, §4.10.6, §4.10.4, §4.11.1, §4.11.2) and the activation target of a dispatch.
- Disabled form controls (HTML §4.10.18.5), for `click()`.

The behaviours themselves fire events (`input`, `change`, `submit`, `reset`, `toggle`,
`hashchange`), so the page's script host runs them; the decisions are here.
-/
import L4Factoidal.DOM.Arena

namespace L4Factoidal.DOM.Forms
open L4Factoidal.DOM

def attr? (d : Dom) (k : NodeId) (name : String) : Option String :=
  ((d.get k).attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)

def isHtml (d : Dom) (k : NodeId) (names : List String) : Bool :=
  let x := d.get k
  x.type == .element && x.ns == some htmlNS && names.contains x.lname

/-- The state of an `input`'s `type` attribute: its ASCII lowercase value when it is a
known keyword, else "text" (HTML §4.10.5). -/
def inputTypes : List String :=
  ["hidden", "text", "search", "tel", "url", "email", "password", "date", "month", "week",
   "time", "datetime-local", "number", "range", "color", "checkbox", "radio", "file",
   "submit", "image", "reset", "button"]

def inputType (d : Dom) (k : NodeId) : String :=
  let t := Dom.asciiLower ((attr? d k "type").getD "")
  if inputTypes.contains t then t else "text"

/-- A `button`'s type: "submit" unless the attribute says "reset" or "button". -/
def buttonType (d : Dom) (k : NodeId) : String :=
  let t := Dom.asciiLower ((attr? d k "type").getD "")
  if t == "reset" || t == "button" then t else "submit"

def checkedness (d : Dom) (k : NodeId) : Bool :=
  match (d.get k).checkedness with
  | some v => v
  | none => (attr? d k "checked").isSome

/-- The form owner: the nearest ancestor `form` element (the `form` attribute is not
read). -/
def formOwner (d : Dom) (k : NodeId) : Option NodeId := Id.run do
  let mut cur := (d.get k).parent
  for _ in [0:d.size + 1] do
    match cur with
    | none => return none
    | some p => if isHtml d p ["form"] then return some p else cur := (d.get p).parent
  return none

def isRadio (d : Dom) (k : NodeId) : Bool := isHtml d k ["input"] && inputType d k == "radio"

/-- The other members of `k`'s radio button group. -/
def radioGroup (d : Dom) (k : NodeId) : Array NodeId :=
  match attr? d k "name" with
  | none => #[]
  | some name =>
    if name.isEmpty || !isRadio d k then #[] else
    let owner := formOwner d k
    (d.treeOrder (d.root k)).filter fun j =>
      j != k && isRadio d j && attr? d j "name" == some name && formOwner d j == owner

/-- Set the checkedness (and the dirty flag); checking a radio button unchecks the rest
of its group. -/
def setChecked (d : Dom) (k : NodeId) (v : Bool) : Dom :=
  let d := d.setNode k fun x => { x with checkedness := some v }
  if v && isRadio d k then
    (radioGroup d k).foldl (fun d j => d.setNode j fun x => { x with checkedness := some false }) d
  else d

/-- The checked radio button of `k`'s group other than `k`, if any. -/
def checkedInGroup (d : Dom) (k : NodeId) : Option NodeId :=
  (radioGroup d k).find? (checkedness d ·)

/-- The reset algorithm of a form (HTML §4.10.22): its inputs lose the dirty checkedness
flag, and the options of its selects their dirtiness (the selectedness is again the
`selected` attribute). -/
def resetForm (d : Dom) (form : NodeId) : Dom :=
  (d.treeOrder form false).foldl (fun d j =>
    if (isHtml d j ["input"] && formOwner d j == some form) || isHtml d j ["option"] then
      d.setNode j fun x => { x with checkedness := none }
    else d) d

/-- The summary of its parent details (HTML §4.11.2): the first `summary` child of a
`details` element. -/
def isDetailsSummary (d : Dom) (k : NodeId) : Bool :=
  isHtml d k ["summary"] && match (d.get k).parent with
    | some p => isHtml d p ["details"] && ((d.get p).kids.find? fun c => isHtml d c ["summary"]) == some k
    | none => false

/-- An SVG `a` element that is a hyperlink (SVG 2 §16.2): it has an `href` attribute, in no
namespace or in the XLink namespace. -/
def isSvgLink (d : Dom) (k : NodeId) : Bool :=
  let x := d.get k
  x.type == .element && x.ns == some svgNS && x.lname == "a" &&
    x.attrs.any fun a => a.lname == "href" && (a.ns.isNone || a.ns == some "http://www.w3.org/1999/xlink")

/-- Elements with activation behaviour. -/
def hasActivationBehavior (d : Dom) (k : NodeId) : Bool :=
  (isHtml d k ["a", "area"] && (attr? d k "href").isSome) || isSvgLink d k ||
  isHtml d k ["button", "input", "label"] || isDetailsSummary d k

/-- The activation target of a `click` MouseEvent dispatched to `target` (DOM §2.9
steps 5.4 and 5.9.3): the target when it has activation behaviour, else, when the event
bubbles, its nearest inclusive ancestor that has. -/
def activationTarget (d : Dom) (target : NodeId) (bubbles : Bool) : Option NodeId := Id.run do
  if hasActivationBehavior d target then return some target
  if !bubbles then return none
  let mut cur := (d.get target).parent
  for _ in [0:d.size + 1] do
    match cur with
    | none => return none
    | some p => if hasActivationBehavior d p then return some p else cur := (d.get p).parent
  return none

/-- A form control that is disabled (HTML §4.10.18.5): `button`, `input`, `select`,
`textarea` with a `disabled` attribute or inside a disabled `fieldset` (not in its first
`legend`). -/
def disabledControl (d : Dom) (k : NodeId) : Bool := Id.run do
  if !isHtml d k ["button", "input", "select", "textarea"] then return false
  if (attr? d k "disabled").isSome then return true
  let mut child := k
  let mut cur := (d.get k).parent
  for _ in [0:d.size + 1] do
    match cur with
    | none => return false
    | some p =>
      if isHtml d p ["fieldset"] && (attr? d p "disabled").isSome then
        if ((d.get p).kids.find? fun c => isHtml d c ["legend"]) != some child then return true
      child := p
      cur := (d.get p).parent
  return false

/-- Labelable elements (HTML §4.10.2). -/
def labelable (d : Dom) (k : NodeId) : Bool :=
  isHtml d k ["button", "meter", "output", "progress", "select", "textarea"] ||
  (isHtml d k ["input"] && inputType d k != "hidden")

/-- A label's labeled control (HTML §4.10.4): the element its `for` names, when labelable,
else its first labelable descendant. -/
def labeledControl (d : Dom) (label : NodeId) : Option NodeId :=
  match attr? d label "for" with
  | some id =>
    -- an empty `for` names nothing (an ID is not the empty string)
    match (if id.isEmpty then none else d.getElementById (d.root label) id) with
    | some k => if labelable d k then some k else none
    | none => none
  | none => (d.treeOrder label false).find? (labelable d ·)

/-- Interactive content (HTML §3.2.5.2.7), for a label's activation behaviour. -/
def interactive (d : Dom) (k : NodeId) : Bool :=
  (isHtml d k ["a"] && (attr? d k "href").isSome) ||
  isHtml d k ["button", "details", "embed", "iframe", "label", "select", "textarea"] ||
  (isHtml d k ["input"] && inputType d k != "hidden") ||
  (isHtml d k ["audio", "video"] && (attr? d k "controls").isSome) ||
  (isHtml d k ["img", "object"] && (attr? d k "usemap").isSome)

/-- The control a click on `label` activates, for an event whose target is `target`:
nothing when the target is interactive content inside the label other than the label
itself (HTML §4.10.4). -/
def labelActivates (d : Dom) (label target : NodeId) : Option NodeId := Id.run do
  let mut cur := some target
  for _ in [0:d.size + 1] do
    match cur with
    | none => break
    | some p =>
      if p == label then break
      if interactive d p then return none
      cur := (d.get p).parent
  labeledControl d label

end L4Factoidal.DOM.Forms
