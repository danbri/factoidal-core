/-
L4Factoidal.DOM.Editing.Commands — `execCommand` and the `queryCommand*` methods.

Specification: W3C Editing APIs draft, "Methods to query and execute commands":
`execCommand(command, showUI, value)`, `queryCommandEnabled`, `queryCommandIndeterm`,
`queryCommandState`, `queryCommandSupported`, `queryCommandValue`. A command that is not
supported or not enabled does nothing and `execCommand` answers false; a query of a
command that is not supported, or that has no indeterminacy, state or value, answers
false or the empty string. No method throws.

Proved: `exec_unsupported` (a command that is not supported changes nothing and answers
false), `enabled_needs_range` (a command that is not a miscellaneous command is not
enabled with no active range).
-/
import L4Factoidal.DOM.Editing.Delete

namespace L4Factoidal.DOM.Editing
open L4Factoidal.DOM L4Factoidal.DOM.Range

/-- The commands that are enabled with no active range ("Miscellaneous commands"). -/
def miscCommands : List String := ["defaultparagraphseparator", "selectall", "stylewithcss", "usecss"]

/-- The supported commands. -/
def supportedCommands : List String :=
  ["backcolor", "bold", "createlink", "fontname", "fontsize", "forecolor", "hilitecolor", "italic",
   "removeformat", "strikethrough", "subscript", "superscript", "underline", "unlink"] ++ blockCommands ++
    deleteCommands ++ miscCommands

def isSupported (command : String) : Bool := supportedCommands.contains command

/-- "Enabled": a miscellaneous command, or there is an active range whose start and end
nodes are editable or editing hosts, inside one editing host. -/
def isEnabled (e : Ed) (command : String) : Bool :=
  miscCommands.contains command ||
    (hasActive e &&
      (let r := activeOf e
       (isEditable e r.start.node || isEditingHost e r.start.node) &&
       (isEditable e r.stop.node || isEditingHost e r.stop.node) &&
       (chain e.dom (commonAncestor e.dom r)).any (isEditingHost e)))

/-- Enabled. Says: with no active range, only the miscellaneous commands are enabled.
Does not say: that a command with an active range is enabled (its ends must be editable). -/
theorem enabled_needs_range (e : Ed) (command : String) (h : hasActive e = false)
    (hm : miscCommands.contains command = false) : isEnabled e command = false := by
  simp only [isEnabled, h, hm]
  simp

/-- The `body` of the document, else its document element. -/
def bodyOf (e : Ed) : Option NodeId :=
  let d := e.dom
  match (kidsOf d e.doc).find? (isEl d) with
  | some html => ((kidsOf d html).find? fun c => isHtml d c ["body", "frameset"]).orElse fun _ => some html
  | none => none

/-- The commands with a state. -/
def hasState (command : String) : Bool :=
  command == "stylewithcss" || (inlineActivatedValues command).isSome ||
    command == "insertorderedlist" || command == "insertunorderedlist" || (justifyAlignment command).isSome

def queryState (command : String) : M Bool := do
  if !isSupported command || !hasState command then return false
  if command == "stylewithcss" then return (← rd (·.css))
  if (inlineActivatedValues command).isSome then return (← inlineQueryState command)
  rd fun e => hasActive e && blockState e command

def queryIndeterm (command : String) : M Bool := do
  if !isSupported command then return false
  rd fun e =>
    if !hasActive e then false
    else match command with
    | "subscript" | "superscript" =>
      let vs := formattableValues e command
      (vs.any (· == some command) && vs.any (· != some command)) || vs.any (· == some "mixed")
    | "fontsize" =>
      (formattableValues e command).toList.eraseDups.length ≥ 2
    | _ =>
      if isStandardInlineValueCommand command then standardIndeterm e command
      else match inlineActivatedValues command with
        | some vals => inlineIndeterm e command vals
        | none => blockIndeterm e command

/-- The commands with a value. -/
def hasValue (command : String) : Bool :=
  isStandardInlineValueCommand command || command == "fontsize" || command == "defaultparagraphseparator" ||
    command == "formatblock" || (justifyAlignment command).isSome

def queryValue (command : String) : M String := do
  if !isSupported command || !hasValue command then return ""
  if command == "defaultparagraphseparator" then return (← rd (·.sep))
  if command == "formatblock" || (justifyAlignment command).isSome then
    return (← rd fun e => if hasActive e then blockValue e command else "")
  inlineQueryValue command

/-- The action of a supported, enabled command: false when the value is not usable. -/
def action (command value : String) : M Bool := do
  if let some r := ← inlineAction command value then return r
  match command with
  | "defaultparagraphseparator" =>
    let v := lower value
    if v == "p" || v == "div" then modify (fun e => { e with sep := v }); return true else return false
  | "selectall" =>
    match ← rd bodyOf with
    | some b =>
      let len ← rd fun e => nodeLength e.dom b
      let r : Rng := ⟨⟨b, 0⟩, ⟨b, len⟩⟩
      modify fun e => { e with live := { e.live with ranges := if e.live.ranges.isEmpty then #[some r] else e.live.ranges.set! 0 (some r) } }
    | none => modify fun e => { e with live := { e.live with ranges := if e.live.ranges.isEmpty then #[none] else e.live.ranges.set! 0 none } }
    return true
  | "stylewithcss" => modify (fun e => { e with css := lower value != "false" }); return true
  | "usecss" => modify (fun e => { e with css := lower value == "false" }); return true
  | _ =>
    match ← blockAction command value with
    | some r => return r
    | none =>
      match ← deleteAction command value with
      | some r => return r
      | none => return false

/-- `document.execCommand(command, showUI, value)`: the command name in any case. -/
def execCommand (command value : String) : M Bool := do
  let command := lower command
  if !isSupported command then return false
  if !(← rd fun e => isEnabled e command) then return false
  action command value

/-- Unsupported. Says: `execCommand` of a command that is not supported answers false
and leaves the editing state (arena, ranges, flags, log) as it was. Does not say: what a
supported command does. -/
theorem exec_unsupported (command value : String) (e : Ed) (h : isSupported (lower command) = false) :
    (execCommand command value).run e = (false, e) := by
  simp [execCommand, h, StateT.run, pure, StateT.pure]

def queryEnabled (command : String) : M Bool := do
  let command := lower command
  if !isSupported command then return false
  rd fun e => isEnabled e command

end L4Factoidal.DOM.Editing
