/-
L4Factoidal.HTML.InnerText — the text of `innerText` and `outerText` (HTML §3.2.7 "The
innerText and outerText properties", the "rendered text collection steps" and the
getter's steps 4 to 6).

The page objects walk the element's subtree with its computed styles and give this module
the items in tree order: runs of text with their `white-space` behaviour, line breaks of
`br`, the tab and line feed of table cells and rows, and required line break counts (1
around a block, 2 around a `p`). What is decided here is the text: the white space of each
line collapsed as CSS Text §4.1 says (in the modified way of §3.2.7: collapsible spaces at
the end of a line are removed), then the required line breaks merged and trimmed.
-/
namespace L4Factoidal.HTML.InnerText

/-- How a run of text treats its white space (`white-space`): `collapse` (normal, nowrap),
`preserve` (pre, pre-wrap, break-spaces), `lines` (pre-line: spaces collapse, line feeds
stay). -/
inductive Ws where
  | collapse | preserve | lines
  deriving Repr, DecidableEq, Inhabited

/-- An item of the rendered text collection steps. -/
inductive Item where
  /-- The text of a Text node, with the white-space behaviour of its parent. -/
  | text (ws : Ws) (s : String)
  /-- A `br` element: a line feed. -/
  | br
  /-- The tab after a table cell that is not the last of its row, and the line feed after a
  table row that is not the last: literal text. -/
  | literal (s : String)
  /-- A required line break count. -/
  | breaks (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- White space that collapses: space, tab, line feed, carriage return, form feed. -/
def isCollapsible (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'

/-- The state of the line being written: nothing visible on it yet (`atStart`), and a
collapsible space is waiting to be written before the next visible character (`pending`). -/
structure Line where
  atStart : Bool := true
  pending : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- One character of a collapsing run: white space is remembered, not written; a visible
character is written after the one space that the white space before it collapses to,
unless the line starts there. With `keepLf`, a line feed ends the line (pre-line). -/
def step (keepLf : Bool) (st : Line × List Char) (c : Char) : Line × List Char :=
  let (l, out) := st
  if keepLf && c == '\n' then ({ atStart := true, pending := false }, '\n' :: out)
  else if isCollapsible c then ({ l with pending := !l.atStart }, out)
  else ({ atStart := false, pending := false }, if l.pending then c :: ' ' :: out else c :: out)

/-- The text of the items of one inline run, white space processed, with the line state
after each item; the output is built reversed. -/
def write (st : Line × List Char) : Item → Line × List Char
  | .text .collapse s => s.toList.foldl (step false) st
  | .text .lines s => s.toList.foldl (step true) st
  | .text .preserve s =>
    let (l, out) := st
    if s.isEmpty then st
    else
      let out := if l.pending then ' ' :: out else out
      ({ atStart := s.toList.getLast? == some '\n', pending := false }, s.toList.reverse ++ out)
  -- a line break: the space waiting at the end of the line is dropped
  | .br => ({ atStart := true, pending := false }, '\n' :: st.2)
  | .literal s => ({ atStart := true, pending := false }, s.toList.reverse ++ st.2)
  | .breaks _ => st

/-- A piece of the result: text, or a required line break count. -/
inductive Piece where
  | str (s : String)
  | brk (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Split the items at the required line breaks: each run between them is written as one
line context (`write`), so white space collapses across the Text nodes of a run and a
space waiting at the end of a run is dropped. -/
def pieces (items : List Item) : List Piece :=
  let flush := fun (run : List Item) (acc : List Piece) =>
    if run.isEmpty then acc
    else acc ++ [Piece.str (String.ofList (run.foldl write ({}, [])).2.reverse)]
  let (run, acc) := items.foldl (fun (st : List Item × List Piece) it =>
    match it with
    | .breaks n => ([], flush st.1 st.2 ++ [Piece.brk n])
    | it => (st.1 ++ [it], st.2)) ([], [])
  flush run acc

/-- Steps 4 to 6 of the getter: empty strings removed; runs of required line break counts
at the start and the end removed; each other run replaced by as many line feeds as its
greatest count; the strings concatenated. -/
def join (ps : List Piece) : String :=
  let ps := ps.filter fun p => p != .str ""
  let isBrk := fun (p : Piece) => match p with | .brk _ => true | .str _ => false
  let ps := (ps.dropWhile isBrk).reverse.dropWhile isBrk |>.reverse
  let (out, run) := ps.foldl (fun (st : String × Nat) p =>
    match p with
    | .brk n => (st.1, max st.2 n)
    | .str s => (st.1 ++ String.ofList (List.replicate st.2 '\n') ++ s, 0)) ("", 0)
  out ++ String.ofList (List.replicate run '\n')

/-- The text of `innerText` for the collected items. -/
def render (items : List Item) : String := join (pieces items)

/-- Wire form (`node_query` op 190): the items separated by U+0000; each is a letter and its
data: "c", "p", "l" text (collapse, preserve, lines); "b" a br; "t" literal text; "n" and a
count. -/
def parseItems (q : String) : List Item :=
  (q.splitOn "\x00").filterMap fun s =>
    match s.toList with
    | 'c' :: r => some (.text .collapse (String.ofList r))
    | 'p' :: r => some (.text .preserve (String.ofList r))
    | 'l' :: r => some (.text .lines (String.ofList r))
    | ['b'] => some .br
    | 't' :: r => some (.literal (String.ofList r))
    | 'n' :: r => (String.ofList r).toNat?.map .breaks
    | _ => none

def answer (q : String) : String := render (parseItems q)

/-! ## What is proved -/

/-- Says: no items, no text. -/
theorem render_nil : render [] = "" := by decide

/-- Says: a required line break changes no line's text: `write` leaves the state as it is. -/
theorem write_breaks (st : Line × List Char) (n : Nat) : write st (.breaks n) = st := rfl

/-- Says: white space alone writes nothing in a collapsing run: after any run of collapsible
characters the output is what it was. So an element with only white space between its
tags has no text. Does not say: anything about `preserve` runs, which keep their spaces. -/
theorem step_collapsible_output (l : Line) (out : List Char) (c : Char) (h : isCollapsible c = true) :
    (step false (l, out) c).2 = out := by
  simp [step, h]

/-- Says: joining only required line breaks gives the empty string: line breaks appear only
between pieces of text, never alone and never at the ends. -/
theorem join_breaks_only (ns : List Nat) : join (ns.map Piece.brk) = "" := by
  have hf : (ns.map Piece.brk).filter (fun p => p != Piece.str "") = ns.map Piece.brk := by
    induction ns with
    | nil => rfl
    | cons n t ih => simp [ih]
  have hd : (ns.map Piece.brk).dropWhile (fun p => match p with | .brk _ => true | .str _ => false) = [] := by
    induction ns with
    | nil => rfl
    | cons n t ih => simp [ih]
  simp [join, hf, hd]

/-! ## Tests (WPT html/dom/elements/the-innertext-and-outertext-properties/getter-tests.js) -/

open Item Ws in
#guard render [text collapse "abc"] == "abc"
open Item Ws in
#guard render [text collapse " abc  def "] == "abc def"
open Item Ws in
#guard render [text collapse "abc  ", text collapse "  def"] == "abc def"
open Item Ws in
#guard render [text collapse "abc ", br, text collapse " def"] == "abc\ndef"
open Item Ws in
#guard render [text preserve " abc\n def "] == " abc\n def "
open Item Ws in
#guard render [text lines " abc \n  def "] == "abc\ndef"
open Item Ws in
#guard render [breaks 1, text collapse "abc", breaks 1, breaks 1, text collapse "def", breaks 1] == "abc\ndef"
open Item Ws in
#guard render [breaks 2, text collapse "abc", breaks 2, breaks 1, breaks 2, text collapse "def", breaks 2] == "abc\n\ndef"
open Item Ws in
#guard render [text collapse "abc", breaks 1, text collapse "  ", breaks 1, text collapse "def"] == "abc\ndef"
open Item Ws in
#guard render [text collapse "a", literal "\t", text collapse "b", literal "\n", text collapse "c"] == "a\tb\nc"
open Item Ws in
#guard render [breaks 1, breaks 2] == "" && render [text collapse "   "] == ""
#guard answer "cabc \x00b\x00c def\x00n1\x00pX Y" == "abc\ndef\nX Y"

end L4Factoidal.HTML.InnerText
