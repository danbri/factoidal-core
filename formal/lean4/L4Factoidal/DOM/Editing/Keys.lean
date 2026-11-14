/-
L4Factoidal.DOM.Editing.Keys — what a key does in an editing host.

A key of the user in editable content becomes an editing command (UI Events and the
Input Events specification name the `inputType` of each; the commands are those of the
W3C Editing APIs draft): Backspace is `delete`, Delete is `forwardDelete`, Enter is
`insertParagraph` (with Shift, `insertLineBreak`), a key that makes one character is
`insertText` of it, and Control or Meta with B, I, U is the format command. The arrow keys
Left and Right move the caret by one character.

In a `plaintext-only` editing host Enter is `insertLineBreak` (`keyCommandIn`).

Proved: `keyCommandIn_rich`, `keyCommandIn_plain`, `keyCommand_printable` (a single character with no Control, Meta or Alt inserts
exactly that character), `keyCommand_modified` (with Control or Meta no text is inserted),
`keyCommand_named` (the four editing keys).
-/
import L4Factoidal.DOM.Editing.Commands

namespace L4Factoidal.DOM.Editing
open L4Factoidal.DOM L4Factoidal.DOM.Range

/-- A key of the user: its `key` value (UI Events KeyboardEvent key values) and the
modifiers held. -/
structure KeyInput where
  key : String
  shift : Bool := false
  ctrl : Bool := false
  alt : Bool := false
  cmd : Bool := false
  deriving Repr, Inhabited

/-- The names of the keys that make no character. A `key` value that is not one of them
and is one character long is the character the key makes. -/
def namedKeys : List String :=
  ["Backspace", "Delete", "Enter", "Tab", "Escape", "ArrowLeft", "ArrowRight", "ArrowUp", "ArrowDown", "Home",
   "End", "PageUp", "PageDown", "Insert", "Shift", "Control", "Alt", "Meta", "CapsLock", "Dead", "Unidentified"]

/-- The editing command of a key in an editing host, with its value; `none` for a key
that edits nothing. -/
def keyCommand (k : KeyInput) : Option (String × String) :=
  if k.ctrl || k.cmd then
    if k.alt || k.shift then none
    else match lower k.key with
      | "b" => some ("bold", "")
      | "i" => some ("italic", "")
      | "u" => some ("underline", "")
      | _ => none
  else if k.alt then none
  else match k.key with
    | "Backspace" => some ("delete", "")
    | "Delete" => some ("forwarddelete", "")
    | "Enter" => some (if k.shift then "insertlinebreak" else "insertparagraph", "")
    | key => if key.length == 1 then some ("inserttext", key) else none

/-- Typing. Says: a key that makes one character, with no Control, Meta or Alt held (and
that is not one of the three editing keys' names, which are longer than one character),
inserts exactly that character. Does not say: where it is inserted (the `insertText`
command decides, from the selection). -/
theorem keyCommand_printable (key : String) (shift : Bool) (h : key.length = 1) :
    keyCommand { key, shift } = some ("inserttext", key) := by
  have h1 : key ≠ "Backspace" := by intro e; rw [e] at h; exact absurd h (by decide)
  have h2 : key ≠ "Delete" := by intro e; rw [e] at h; exact absurd h (by decide)
  have h3 : key ≠ "Enter" := by intro e; rw [e] at h; exact absurd h (by decide)
  simp only [keyCommand, Bool.or_self, Bool.false_eq_true, if_false]
  split <;> simp_all

/-- Shortcuts. Says: with Control or Meta held, no key inserts text. Does not say: which
shortcuts exist. -/
theorem keyCommand_modified (k : KeyInput) (h : k.ctrl = true ∨ k.cmd = true) (v : String) :
    keyCommand k ≠ some ("inserttext", v) := by
  have hc : (k.ctrl || k.cmd) = true := by rcases h with h | h <;> simp [h]
  simp only [keyCommand, hc, if_true]
  split
  · simp
  · split <;> simp

/-- The editing keys. Says: Backspace deletes backward, Delete forward, Enter makes a
paragraph and Shift+Enter a line break. -/
theorem keyCommand_named :
    keyCommand { key := "Backspace" } = some ("delete", "") ∧
    keyCommand { key := "Delete" } = some ("forwarddelete", "") ∧
    keyCommand { key := "Enter" } = some ("insertparagraph", "") ∧
    keyCommand { key := "Enter", shift := true } = some ("insertlinebreak", "") := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The editing command of a key where the selection is: as `keyCommand`, but in a
`plaintext-only` editing host Enter makes a line break, not a paragraph (only raw text
is editable there: HTML §6.8.1; browsers fire `insertLineBreak`). -/
def keyCommandIn (e : Ed) (k : KeyInput) : Option (String × String) :=
  match keyCommand k with
  | some (c, v) => some (if c == "insertparagraph" && inPlaintextHost e then "insertlinebreak" else c, v)
  | none => none

/-- Outside plain text. Says: where the selection is not in a `plaintext-only` editing
host, a key does what `keyCommand` says. Does not say: what it does inside one. -/
theorem keyCommandIn_rich (e : Ed) (k : KeyInput) (h : inPlaintextHost e = false) :
    keyCommandIn e k = keyCommand k := by
  unfold keyCommandIn
  cases keyCommand k with
  | none => rfl
  | some cv => simp [h]

/-- Plain text. Says: in a `plaintext-only` editing host no key makes a paragraph.
Does not say: that `execCommand("insertParagraph")` makes none there (the command is
not a key). -/
theorem keyCommandIn_plain (e : Ed) (k : KeyInput) (v : String) (h : inPlaintextHost e = true) :
    keyCommandIn e k ≠ some ("insertparagraph", v) := by
  unfold keyCommandIn
  cases keyCommand k with
  | none => simp
  | some cv =>
    obtain ⟨c, w⟩ := cv
    by_cases hc : c = "insertparagraph"
    · simp [h, hc]
    · simp [h, hc]

/-- A Text node a caret can be in: with data, not a collapsed whitespace node, and (with
`editableOnly`) editable. -/
def isCaretText (e : Ed) (n : NodeId) (editableOnly : Bool := true) : Bool :=
  isText e.dom n && (!editableOnly || isEditable e n) && !(e.dom.get n).data.isEmpty &&
    !isCollapsedWhitespaceNode e n

/-- The caret position one character after `bp`, inside the editing host `host`: in the
same Text node, else in the next Text node (after its first character when no line break
or block boundary lies between). -/
def caretAfter (e : Ed) (host : NodeId) (bp : BP) (editableOnly : Bool := true) : Option BP := Id.run do
  let d := e.dom
  if isText d bp.node && bp.offset < nodeLength d bp.node then
    let c := (splitAtUnits (d.get bp.node).data bp.offset).2.toList.head?
    return some ⟨bp.node, bp.offset + (c.map unitsOf).getD 1⟩
  let mut cur := if isText d bp.node then nextNodeDesc d bp.node
    else match (kidsOf d bp.node)[bp.offset]? with
      | some c => some c
      | none => nextNodeDesc d bp.node
  let mut broke := false
  for _ in [0:d.size + 1] do
    match cur with
    | none => return none
    | some c =>
      if !d.isInclusiveAncestor host c then return none
      if isHtml d c ["br"] || (isEl d c && isBlockNode e c) then broke := true
      if isCaretText e c editableOnly then
        if broke then return some ⟨c, 0⟩
        let ch := (d.get c).data.toList.head?
        return some ⟨c, (ch.map unitsOf).getD 1⟩
      cur := nextNode d c
  return none

/-- The caret position one character before `bp`, inside the editing host `host`. -/
def caretBefore (e : Ed) (host : NodeId) (bp : BP) (editableOnly : Bool := true) : Option BP := Id.run do
  let d := e.dom
  if isText d bp.node && bp.offset > 0 then
    let c := (splitAtUnits (d.get bp.node).data bp.offset).1.toList.getLast?
    return some ⟨bp.node, bp.offset - (c.map unitsOf).getD 1⟩
  let mut cur := if isText d bp.node then prevNode d bp.node
    else if bp.offset ≥ 1 then ((kidsOf d bp.node)[bp.offset - 1]?).map (deepLast d)
    else prevNode d bp.node
  let mut broke := false
  for _ in [0:d.size + 1] do
    match cur with
    | none => return none
    | some c =>
      if !d.isInclusiveAncestor host c || c == host then return none
      if isHtml d c ["br"] || (isEl d c && isBlockNode e c) then broke := true
      if isCaretText e c editableOnly then
        let len := nodeLength d c
        if broke then return some ⟨c, len⟩
        let ch := (d.get c).data.toList.getLast?
        return some ⟨c, len - (ch.map unitsOf).getD 1⟩
      cur := prevNode d c
  return none

/-- The first caret position in `n`: in its first Text node, else before the first node
that is not a container of inline content (`{}<br>`), else in the innermost first element. -/
def firstCaret (e : Ed) (n : NodeId) : BP := Id.run do
  let d := e.dom
  let mut cur := n
  for _ in [0:d.size + 1] do
    match firstChild d cur with
    | some c =>
      if isText d c then return ⟨c, 0⟩
      if !isEl d c || isHtml d c ["br", "img", "hr", "input", "select", "textarea", "button", "table"] ||
          contentEditable d c == "false" then return ⟨cur, 0⟩
      cur := c
    | none => return ⟨cur, 0⟩
  return ⟨cur, 0⟩

/-- The last caret position in `n`: at the end of its last Text node, else after its last node. -/
def lastCaret (e : Ed) (n : NodeId) : BP := Id.run do
  let d := e.dom
  let mut cur := n
  for _ in [0:d.size + 1] do
    match lastChild d cur with
    | some c =>
      if isText d c then return ⟨c, nodeLength d c⟩
      if !isEl d c || isHtml d c ["br", "img", "hr", "input", "select", "textarea", "button", "table"] ||
          contentEditable d c == "false" then
        -- a `br` that ends the block is not a place after which one types
        return if isHtml d c ["br"] then ⟨cur, indexOf d c⟩ else ⟨cur, nodeLength d cur⟩
      cur := c
    | none => return ⟨cur, nodeLength d cur⟩
  return ⟨cur, nodeLength d cur⟩

/-- The active range after ArrowLeft, ArrowRight, Home or End: a selection collapses to
its start or end; a caret moves one character, or to an end of its block; with Shift one
end of the range moves. `none` when the key moves nothing. -/
def caretKey (e : Ed) (k : KeyInput) : Option Rng :=
  if !hasActive e || k.ctrl || k.cmd || k.alt then none
  else
    let r := activeOf e
    match affectedHost e with
    | none => none
    | some host =>
      match k.key with
      | "ArrowRight" =>
        if k.shift then (caretAfter e host r.stop).map fun bp => ⟨r.start, bp⟩
        else if !r.collapsed then some ⟨r.stop, r.stop⟩
        else (caretAfter e host r.stop).map fun bp => ⟨bp, bp⟩
      | "ArrowLeft" =>
        if k.shift then (caretBefore e host r.start).map fun bp => ⟨bp, r.stop⟩
        else if !r.collapsed then some ⟨r.start, r.start⟩
        else (caretBefore e host r.start).map fun bp => ⟨bp, bp⟩
      -- Home and End go to the ends of the block of the caret (lines inside a block are
      -- not told apart: no layout is read here)
      | "Home" =>
        let block := ((chain e.dom r.start.node).toList.reverse.find? fun a => isBlockNode e a || a == host).getD host
        let bp := firstCaret e block
        some (if k.shift then ⟨bp, r.stop⟩ else ⟨bp, bp⟩)
      | "End" =>
        let block := ((chain e.dom r.stop.node).toList.reverse.find? fun a => isBlockNode e a || a == host).getD host
        let bp := lastCaret e block
        some (if k.shift then ⟨r.start, bp⟩ else ⟨bp, bp⟩)
      | _ => none

/-- The character after a caret position in a Text node, if any. -/
def charAfter (d : Dom) (bp : BP) : Option Char :=
  if isText d bp.node then (splitAtUnits (d.get bp.node).data bp.offset).2.toList.head? else none

/-- `Selection.modify`: the focus moved by one `granularity` (Selection API, "modify").
Done: `character`, `word` (to the end of the next word, or the start of the previous
one), `lineboundary` and `paragraphboundary` (the ends of the caret's block; lines inside
a block are not told apart), `documentboundary` (the ends of `limit`). `none` for the
others (`line`, `sentence`, ...) and when there is nowhere to go. -/
def modifyFocus (e : Ed) (limit : NodeId) (editableOnly : Bool) (focus : BP) (forward : Bool)
    (granularity : String) : Option BP :=
  let step := fun (bp : BP) => if forward then caretAfter e limit bp editableOnly else caretBefore e limit bp editableOnly
  match granularity with
  | "character" => step focus
  | "word" => Id.run do
    -- forward: over spaces, then over the word; backward: over spaces, then to the word's start
    let mut cur := focus
    let mut inWord := false
    for _ in [0:4096] do
      match step cur with
      | none => break
      | some nx =>
        -- the character that the step passed over
        let passed := if forward then charAfter e.dom cur else charAfter e.dom nx
        let space := match passed with
          | some c => isWs c || c == Char.ofNat 0xa0
          | none => true
        if inWord && (space || nx.node != cur.node) then break
        if !space then inWord := true
        cur := nx
    return if cur == focus then none else some cur
  | "lineboundary" | "paragraphboundary" =>
    let block := ((chain e.dom focus.node).toList.reverse.find? fun a => isBlockNode e a || a == limit).getD limit
    some (if forward then lastCaret e block else firstCaret e block)
  | "documentboundary" => some (if forward then lastCaret e limit else firstCaret e limit)
  | _ => none

end L4Factoidal.DOM.Editing
