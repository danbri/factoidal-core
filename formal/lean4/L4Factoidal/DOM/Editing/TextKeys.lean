/-
L4Factoidal.DOM.Editing.TextKeys — the keys of the user in a text control.

A key that is not canceled and whose focus is an `input` of a text type or a `textarea`
edits the control's value: its editing command (`keyCommand`: a character inserts it,
Backspace and Delete delete, Enter breaks a line) when the control has that command
(`textCommands`; `textEdit` then decides the value and selection, as for `execCommand`).
A control that is disabled or read-only is not edited (HTML §4.10.18.3 "mutable").

Proved: `textKeyCommandIn_single` (no key breaks a line in an `input`), `textKeyCommand_text` (the command is one a text control has),
`textKeyCommand_printable` (a character key with no Control, Meta or Alt inserts the
character), `textKeyCommand_modified` (no key with Control or Meta inserts text).
Tested: `#guard`s below.
-/
import L4Factoidal.DOM.Editing.Keys
import L4Factoidal.DOM.Editing.TextControl

namespace L4Factoidal.DOM.Editing
open L4Factoidal.DOM

/-- The `input` types whose value is edited as text with a text selection (HTML §4.10.5.2.10:
the selection APIs apply to text, search, tel, url and password; `email` has no selection
there, so its keys are left for later). -/
def textInputTypes : List String := ["text", "search", "url", "tel", "password"]

/-- The `input` types HTML names; any other value of `type` (or none) is the Text state. -/
def inputTypes : List String :=
  ["hidden", "text", "search", "tel", "url", "email", "password", "date", "month", "week", "time",
   "datetime-local", "number", "range", "color", "checkbox", "radio", "file", "submit", "image", "reset", "button"]

/-- The state of an `input`'s `type` attribute value: ASCII lower case, the Text state for
a missing or unknown value. -/
def inputTypeState (v : Option String) : String :=
  match v with
  | none => "text"
  | some t => let t := lower t; if inputTypes.contains t then t else "text"

/-- The element is a text control whose value the user can edit: a `textarea`, or an
`input` in a text state, that is neither disabled nor read-only. -/
def mutableTextControl (d : Dom) (n : NodeId) : Bool :=
  let attr := fun name => d.getAttributeNS? n none name
  let mutable := (attr "disabled").isNone && (attr "readonly").isNone
  match tagOf d n with
  | "textarea" => mutable
  | "input" => mutable && textInputTypes.contains (inputTypeState (attr "type"))
  | _ => false

/-- The command a key runs in a text control: its editing command, when a text control
has it. -/
def textKeyCommand (k : KeyInput) : Option (String × String) :=
  match keyCommand k with
  | some (c, v) => if textCommands.contains c then some (c, v) else none
  | none => none

/-- The command of a key in a text control (`multiline`: a `textarea`): Enter breaks a line
in a `textarea` (`insertLineBreak`, as browsers fire it there) and edits nothing in an
`input` (where it submits the form instead). -/
def textKeyCommandIn (multiline : Bool) (k : KeyInput) : Option (String × String) :=
  match textKeyCommand k with
  | some (c, v) =>
    if c == "insertparagraph" || c == "insertlinebreak" then
      if multiline then some ("insertlinebreak", v) else none
    else some (c, v)
  | none => none

/-! ## Theorems -/

/-- Text commands only. Says: the command of a key in a text control is one of
`textCommands`, so `textEdit` decides it (no formatting command reaches a value). -/
theorem textKeyCommand_text (k : KeyInput) (c v : String) (h : textKeyCommand k = some (c, v)) :
    textCommands.contains c = true := by
  unfold textKeyCommand at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-- Typing. Says: a key that makes one character, with no Control, Meta or Alt held,
inserts exactly that character in a text control. -/
theorem textKeyCommand_printable (key : String) (shift : Bool) (h : key.length = 1) :
    textKeyCommand { key, shift } = some ("inserttext", key) := by
  simp [textKeyCommand, keyCommand_printable key shift h, textCommands]

/-- Shortcuts. Says: a key held with Control or Meta inserts no text in a text control
(Control-B is not a character). -/
theorem textKeyCommand_modified (k : KeyInput) (h : k.ctrl = true ∨ k.cmd = true) (v : String) :
    textKeyCommand k ≠ some ("inserttext", v) := by
  intro hk
  have := keyCommand_modified k h v
  unfold textKeyCommand at hk
  split at hk
  · rename_i c w hc
    split at hk
    · cases hk; exact this hc
    · cases hk
  · cases hk

/-- One line. Says: no key breaks a line in a single-line control. -/
theorem textKeyCommandIn_single (k : KeyInput) (v : String) :
    textKeyCommandIn false k ≠ some ("insertlinebreak", v) ∧ textKeyCommandIn false k ≠ some ("insertparagraph", v) := by
  unfold textKeyCommandIn
  split
  · rename_i c w _
    by_cases h1 : c = "insertparagraph"
    · subst h1; simp
    · by_cases h2 : c = "insertlinebreak"
      · subst h2; simp
      · simp [h1, h2]
  · simp

/-! ## Tests -/

#guard textKeyCommand { key := "a" } == some ("inserttext", "a")
#guard textKeyCommand { key := "Backspace" } == some ("delete", "")
#guard textKeyCommand { key := "Delete" } == some ("forwarddelete", "")
#guard textKeyCommand { key := "Enter" } == some ("insertparagraph", "")
#guard textKeyCommand { key := "b", ctrl := true } == none
#guard textKeyCommand { key := "ArrowLeft" } == none
#guard textKeyCommandIn true { key := "Enter" } == some ("insertlinebreak", "")
#guard textKeyCommandIn false { key := "Enter" } == none
#guard textKeyCommandIn false { key := "x" } == some ("inserttext", "x")
#guard inputTypeState none == "text" && inputTypeState (some "SEARCH") == "search"
#guard inputTypeState (some "bogus") == "text" && inputTypeState (some "checkbox") == "checkbox"

end L4Factoidal.DOM.Editing
