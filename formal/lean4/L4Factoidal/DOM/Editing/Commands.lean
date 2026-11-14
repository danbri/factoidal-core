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

/-- The commands that change formatting: not enabled in a `plaintext-only` editing host
(HTML §6.8.1: only raw text is editable there). -/
def stylingCommands : List String :=
  ["backcolor", "bold", "createlink", "fontname", "fontsize", "forecolor", "hilitecolor", "italic",
   "removeformat", "strikethrough", "subscript", "superscript", "underline", "unlink"] ++ blockCommands

/-- "Enabled": a miscellaneous command, or there is an active range whose start and end
nodes are editable or editing hosts, inside one editing host (and for a formatting
command, not a `plaintext-only` one). -/
def isEnabled (e : Ed) (command : String) : Bool :=
  miscCommands.contains command ||
    (hasActive e &&
      (let r := activeOf e
       (isEditable e r.start.node || isEditingHost e r.start.node) &&
       (isEditable e r.stop.node || isEditingHost e r.stop.node) &&
       (chain e.dom (commonAncestor e.dom r)).any (isEditingHost e)) &&
      !(stylingCommands.contains command && inPlaintextHost e))

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
  let command := lower command
  if !isSupported command || !hasState command then return false
  if command == "stylewithcss" then return (← rd (·.css))
  if (inlineActivatedValues command).isSome then return (← inlineQueryState command)
  rd fun e => hasActive e && blockState e command

def queryIndeterm (command : String) : M Bool := do
  let command := lower command
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
  let command := lower command
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

/-- The elements with no content (HTML §13.1.2 "void elements"). -/
def voidNames : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"]

/-- A boundary point inside a void element is the point just before the element: nothing
can be put in it (browsers edit before it). -/
def leaveVoid (d : Dom) (bp : BP) : BP :=
  if isHtml d bp.node voidNames then
    match parentOf d bp.node with
    | some p => ⟨p, indexOf d bp.node⟩
    | none => bp
  else bp

/-- `document.execCommand(command, showUI, value)`: the command name in any case. -/
def execCommand (command value : String) : M Bool := do
  let command := lower command
  if !isSupported command then return false
  if !(← rd fun e => isEnabled e command) then return false
  if !miscCommands.contains command then
    let e ← get
    let r := activeOf e
    let r' : Rng := ⟨leaveVoid e.dom r.start, leaveVoid e.dom r.stop⟩
    if r' != r then setActive r'
  action command value

/-- Unsupported. Says: `execCommand` of a command that is not supported answers false
and leaves the editing state (arena, ranges, flags, log) as it was. Does not say: what a
supported command does. -/
theorem exec_unsupported (command value : String) (e : Ed) (h : isSupported (lower command) = false) :
    (execCommand command value).run e = (false, e) := by
  simp [execCommand, h, StateT.run, pure, StateT.pure]

/-- The `inputType` of the `input` event of a command (the editing draft's table, as
browsers fill it: Input Events §4.1.3); "" for a command with none. -/
def inputTypeOf (command : String) : String :=
  match command with
  | "backcolor" | "hilitecolor" => "formatBackColor"
  | "bold" => "formatBold"
  | "createlink" => "insertLink"
  | "delete" => "deleteContentBackward"
  | "fontname" => "formatFontName"
  | "forecolor" => "formatFontColor"
  | "forwarddelete" => "deleteContentForward"
  | "indent" => "formatIndent"
  | "inserthorizontalrule" => "insertHorizontalRule"
  | "insertlinebreak" => "insertLineBreak"
  | "insertorderedlist" => "insertOrderedList"
  | "insertparagraph" => "insertParagraph"
  | "inserttext" => "insertText"
  | "insertunorderedlist" => "insertUnorderedList"
  | "italic" => "formatItalic"
  | "justifycenter" => "formatJustifyCenter"
  | "justifyfull" => "formatJustifyFull"
  | "justifyleft" => "formatJustifyLeft"
  | "justifyright" => "formatJustifyRight"
  | "outdent" => "formatOutdent"
  | "removeformat" => "formatRemove"
  | "strikethrough" => "formatStrikeThrough"
  | "subscript" => "formatSubscript"
  | "superscript" => "formatSuperscript"
  | "underline" => "formatUnderline"
  | _ => ""

/-- The `data` of the `input` event of a command: the text, link or font name given, the
colour as its resolved value (a CSS-wide keyword in lowercase), else none. -/
def inputDataOf (command value : String) : Option String :=
  match command with
  | "inserttext" | "createlink" | "fontname" => some value
  | "backcolor" | "hilitecolor" | "forecolor" =>
    let l := lower (trimStr value)
    if ["currentcolor", "inherit", "initial", "reset", "revert", "unset"].contains l then some l
    else match colorCommandValue value with
      | some v => (match parseColor v with
        | some c => some c.text
        | none => some value)
      | none => some value
  | _ => none

/-- "Affected editing host": the innermost editing host that is an inclusive ancestor of
the active range's start node and end node. -/
def affectedHost (e : Ed) : Option NodeId :=
  if !hasActive e then none
  else
    let r := activeOf e
    (chain e.dom r.start.node).toList.reverse.find? fun a => isEditingHost e a && e.dom.isInclusiveAncestor a r.stop.node

/-- `execCommand` with the `input` event it asks for: whether the action was taken, and
for a command that is not a miscellaneous command, the editing host the event is fired
at with its `inputType` and `data`. -/
def execCommandWithEvent (command value : String) : M (Bool × Option (NodeId × String × Option String)) := do
  let c := lower command
  let host ← rd affectedHost
  let ok ← execCommand command value
  if !ok || miscCommands.contains c then return (ok, none)
  -- the host after the action when the one before it is gone from the document
  let host ← match host with
    | some h => if (← rd fun e => detached e.dom h) then rd affectedHost else pure (some h)
    | none => rd affectedHost
  return (ok, host.map fun h => (h, inputTypeOf c, inputDataOf c value))

/-- A boundary point moved down to the end of the inline content before it. -/
def descendBack (e : Ed) (bp : BP) : BP := Id.run do
  let d := e.dom
  let mut cur := bp
  for _ in [0:d.size + 1] do
    if cur.offset == 0 then break
    match (kidsOf d cur.node)[cur.offset - 1]? with
    | some c => if isInlineNode e c && nodeLength d c != 0 && !isHtml d c ["br", "img"] then cur := ⟨c, nodeLength d c⟩ else break
    | none => break
  return cur

/-- A boundary point moved down to the start of the inline content after it. -/
def descendForward (e : Ed) (bp : BP) : BP := Id.run do
  let d := e.dom
  let mut cur := bp
  for _ in [0:d.size + 1] do
    match (kidsOf d cur.node)[cur.offset]? with
    | some c => if isInlineNode e c && nodeLength d c != 0 && !isHtml d c ["br", "img"] then cur := ⟨c, 0⟩ else break
    | none => break
  return cur

/-- The target range of a command's `beforeinput` event: the range the command would
delete first, with its ends in the innermost inline content; none for a command that
deletes nothing, and the selection itself for a command that would change nothing. The
command runs on a copy of the state; nothing is kept. -/
def targetRange (command value : String) : M (Option Rng) := do
  let e ← get
  let (_, e') := (execCommand command value).run { e with target := none, log := #[] }
  -- a command that would change nothing targets the selection as it is
  if e'.log.isEmpty then return if hasActive e then some (activeOf e) else none
  return e'.target.map fun r => ⟨descendBack e r.start, descendForward e r.stop⟩

def queryEnabled (command : String) : M Bool := do
  let command := lower command
  if !isSupported command then return false
  rd fun e => isEnabled e command

end L4Factoidal.DOM.Editing
