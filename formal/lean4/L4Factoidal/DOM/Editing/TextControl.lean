/-
L4Factoidal.DOM.Editing.TextControl — editing commands in a text control.

`document.execCommand` when the focused element is an `input` (text, search, url, tel,
password) or a `textarea`: the command edits the control's value and selection, not the
document (HTML §4.10.5.2.10 "text control selection"; no draft says what each command does
there, and `editing/other/exec-command-with-text-editor.tentative.html` records what
browsers do). The value is a list of characters and the selection two indexes into it.

`textEdit` is the whole decision: which commands are enabled in a text control, the value
and selection after one, and the `inputType` of the `input` event it fires.

Proved: `textEdit_ok` (the selection stays inside the value), `textEdit_delete_range`
and `textEdit_insert` (the value after deleting a selection and after inserting text),
`textEdit_singleLine` (no line feed enters a single-line control by `insertText`).
-/
import L4Factoidal.DOM.Editing.Style

namespace L4Factoidal.DOM.Editing

/-- The value of a text control and its selection: `start` and `stop` are indexes of
characters, `start ≤ stop ≤ chars.length` (`TextSel.ok`). -/
structure TextSel where
  chars : List Char
  start : Nat
  stop : Nat
  deriving Repr, BEq, DecidableEq

def TextSel.ok (t : TextSel) : Prop := t.start ≤ t.stop ∧ t.stop ≤ t.chars.length

/-- The value with the characters from `a` to `b` replaced by `ins`, the caret after them. -/
def TextSel.replace (t : TextSel) (a b : Nat) (ins : List Char) : TextSel :=
  { chars := t.chars.take a ++ ins ++ t.chars.drop b, start := a + ins.length, stop := a + ins.length }

/-- The commands that edit a text control. The others are not enabled there. -/
def textCommands : List String :=
  ["delete", "forwarddelete", "inserttext", "insertparagraph", "insertlinebreak", "selectall"]

/-- A command in a text control (`multiline`: a `textarea`): `none` when the command is
not enabled there; else the value and selection after it, and the `inputType` of its
`input` event (`none`: no event, the value did not change). -/
def textEdit (multiline : Bool) (command : String) (arg : List Char) (t : TextSel) : Option (TextSel × Option String) :=
  match command with
  | "delete" =>
    if t.start < t.stop then some (t.replace t.start t.stop [], some "deleteContentBackward")
    else if t.start == 0 then some (t, none)
    else some (t.replace (t.start - 1) t.start [], some "deleteContentBackward")
  | "forwarddelete" =>
    if t.start < t.stop then some (t.replace t.start t.stop [], some "deleteContentForward")
    else if t.stop ≥ t.chars.length then some (t, none)
    else some (t.replace t.start (t.start + 1) [], some "deleteContentForward")
  | "inserttext" =>
    let ins := if multiline then arg else arg.filter fun c => c != '\n' && c != '\r'
    some (t.replace t.start t.stop ins, some "insertText")
  | "insertparagraph" =>
    if multiline then some (t.replace t.start t.stop ['\n'], some "insertParagraph") else none
  | "insertlinebreak" =>
    if multiline then some (t.replace t.start t.stop ['\n'], some "insertLineBreak") else none
  | "selectall" => some ({ t with start := 0, stop := t.chars.length }, none)
  | _ => none

theorem TextSel.replace_ok (t : TextSel) (a b : Nat) (ins : List Char) (hab : a ≤ b) (hb : b ≤ t.chars.length) :
    (t.replace a b ins).ok := by
  simp only [TextSel.ok, TextSel.replace, List.length_append, List.length_take, List.length_drop]
  omega

/-- In bounds. Says: a command leaves the selection of a text control inside its value
(start ≤ end ≤ length) when it was inside before. Does not say: that the offsets a page
reads are these indexes (the page counts UTF-16 code units; the glue converts). -/
theorem textEdit_ok (multiline : Bool) (command : String) (arg : List Char) (t : TextSel) (h : t.ok)
    (r : TextSel × Option String) (hr : textEdit multiline command arg t = some r) : r.1.ok := by
  obtain ⟨h1, h2⟩ := h
  unfold textEdit at hr
  repeat' split at hr
  all_goals first
    | (cases hr; exact ⟨h1, h2⟩)
    | (cases hr; exact ⟨Nat.zero_le _, Nat.le_refl _⟩)
    | (cases hr; apply TextSel.replace_ok <;> simp_all <;> omega)
    | cases hr

/-- Deleting a selection. Says: `delete` with a selection that is not collapsed removes
exactly the selected characters and leaves the caret where the selection started. Does
not say: what `delete` removes at a caret (one character before it; a grapheme cluster
is not kept whole). -/
theorem textEdit_delete_range (multiline : Bool) (arg : List Char) (t : TextSel) (h : t.start < t.stop) :
    textEdit multiline "delete" arg t =
      some ({ chars := t.chars.take t.start ++ t.chars.drop t.stop, start := t.start, stop := t.start },
        some "deleteContentBackward") := by
  simp [textEdit, h, TextSel.replace]

/-- Inserting text. Says: `insertText` in a `textarea` replaces the selection by the text
and puts the caret after it. Does not say: anything about a single-line control, where
line feeds are dropped first (`textEdit_singleLine`). -/
theorem textEdit_insert (arg : List Char) (t : TextSel) :
    textEdit true "inserttext" arg t =
      some ({ chars := t.chars.take t.start ++ arg ++ t.chars.drop t.stop, start := t.start + arg.length,
              stop := t.start + arg.length }, some "insertText") := by
  simp [textEdit, TextSel.replace]

/-- Single line. Says: `insertText` in a single-line control never adds a line feed or
carriage return that the value did not have. Does not say: that the value had none. -/
theorem textEdit_singleLine (arg : List Char) (t : TextSel) (r : TextSel × Option String)
    (hr : textEdit false "inserttext" arg t = some r) (c : Char) (hc : c ∈ r.1.chars) (hn : c = '\n' ∨ c = '\r') :
    c ∈ t.chars := by
  simp only [textEdit, Bool.false_eq_true, if_false, Option.some.injEq] at hr
  subst hr
  simp only [TextSel.replace, List.mem_append, List.mem_filter] at hc
  rcases hc with (hc | hc) | hc
  · exact List.mem_of_mem_take hc
  · rcases hn with hn | hn <;> simp [hn] at hc
  · exact List.mem_of_mem_drop hc

#guard textEdit false "delete" [] ⟨"abc".toList, 2, 2⟩ == some (⟨"ac".toList, 1, 1⟩, some "deleteContentBackward")
#guard textEdit false "delete" [] ⟨"abc".toList, 1, 2⟩ == some (⟨"ac".toList, 1, 1⟩, some "deleteContentBackward")
#guard textEdit false "forwarddelete" [] ⟨"abc".toList, 1, 1⟩ == some (⟨"ac".toList, 1, 1⟩, some "deleteContentForward")
#guard textEdit false "selectall" [] ⟨"abc".toList, 1, 2⟩ == some (⟨"abc".toList, 0, 3⟩, none)
#guard textEdit false "inserttext" "**inserted**".toList ⟨"abc".toList, 1, 2⟩ ==
  some (⟨"a**inserted**c".toList, 13, 13⟩, some "insertText")
#guard textEdit true "insertparagraph" [] ⟨"abc".toList, 1, 2⟩ == some (⟨"a\nc".toList, 2, 2⟩, some "insertParagraph")
#guard textEdit false "insertparagraph" [] ⟨"abc".toList, 1, 2⟩ == none
#guard textEdit false "bold" [] ⟨"abc".toList, 1, 2⟩ == none

/-- The index of the character at UTF-16 offset `units` (an offset inside a surrogate
pair is the index after the pair). -/
def indexOfUnits (cs : List Char) (units : Nat) : Nat := Id.run do
  let mut n := 0
  let mut i := 0
  for c in cs do
    if n ≥ units then break
    n := n + (if c.val.toNat ≥ 0x10000 then 2 else 1)
    i := i + 1
  return i

/-- The UTF-16 offset of the character at index `i`. -/
def unitsOfIndex (cs : List Char) (i : Nat) : Nat :=
  (cs.take i).foldl (fun n c => n + (if c.val.toNat ≥ 0x10000 then 2 else 1)) 0

#guard indexOfUnits "a😀b".toList 3 == 2
#guard unitsOfIndex "a😀b".toList 2 == 3

end L4Factoidal.DOM.Editing
