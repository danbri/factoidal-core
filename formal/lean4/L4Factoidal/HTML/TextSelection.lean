/-
L4Factoidal.HTML.TextSelection — the selection of a text control (HTML §4.10.20 "APIs for the
text control selections"): `setSelectionRange`, `select`, `setRangeText`.

Specification: HTML Living Standard §4.10.20: "set the selection range" and the steps of
`setRangeText`.

The value and the selection are the page's state; the arithmetic that keeps a selection
inside its text is decided here. Offsets are UTF-16 code units, as the API counts them.
-/
namespace L4Factoidal.HTML.TextSelection

/-- "Set the selection range" with `start` and `end` (`none`: null, which is 0 for the start
and the text's length for the end) on a text of `len` units: the new selection start and
end. The end is at most the length and the start at most the end. -/
def setRange (len : Nat) (start stop : Option Nat) : Nat × Nat :=
  let e := match stop with
    | some e => min e len
    | none => len
  (min (start.getD 0) e, e)

/-- The selection mode of `setRangeText`. -/
inductive Mode where
  | select | start | stop | preserve
  deriving Repr, DecidableEq, Inhabited

def Mode.ofString (s : String) : Mode :=
  if s == "select" then .select else if s == "start" then .start else if s == "end" then .stop else .preserve

/-- The answer of `rangeText`: the range of the old text that is replaced (clamped), and the
selection after. -/
structure Replaced where
  start : Nat
  stop : Nat
  selStart : Nat
  selEnd : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `setRangeText` steps 5 to 13, for a text of `len` units, the range `start`..`stop` given
(with `start ≤ stop`: the caller throws IndexSizeError otherwise), the selection `selS`..`selE`
before, and a replacement of `newLen` units. -/
def rangeText (len start stop selS selE newLen : Nat) (mode : Mode) : Replaced :=
  let start := min start len
  let stop := min stop len
  let newEnd := start + newLen
  match mode with
  | .select => { start, stop, selStart := start, selEnd := newEnd }
  | .start => { start, stop, selStart := start, selEnd := start }
  | .stop => { start, stop, selStart := newEnd, selEnd := newEnd }
  | .preserve =>
    let oldLen := stop - start
    let shift := fun (x : Nat) => x + newLen - oldLen
    let s := if selS > stop then shift selS else if selS > start then start else selS
    let e := if selE > stop then shift selE else if selE > start then newEnd else selE
    { start, stop, selStart := s, selEnd := e }

/-- The length of the text after the replacement. -/
def newLength (len : Nat) (r : Replaced) (newLen : Nat) : Nat := len - (r.stop - r.start) + newLen

/-- Wire form of op 187: `q` is "len start stop selS selE newLen mode"; the answer is
"start stop selStart selEnd". -/
def answer (q : String) : String :=
  match q.splitOn " " with
  | [len, start, stop, selS, selE, newLen, mode] =>
    match len.toNat?, start.toNat?, stop.toNat?, selS.toNat?, selE.toNat?, newLen.toNat? with
    | some len, some start, some stop, some selS, some selE, some newLen =>
      let r := rangeText len start stop selS selE newLen (Mode.ofString mode)
      s!"{r.start} {r.stop} {r.selStart} {r.selEnd}"
    | _, _, _, _, _, _ => ""
  | _ => ""

/-! ## What is proved -/

/-- Bounds. Says: "set the selection range" answers a selection inside the text, with the
start not after the end, whatever numbers a script gives. -/
theorem setRange_bounds (len : Nat) (start stop : Option Nat) :
    (setRange len start stop).1 ≤ (setRange len start stop).2 ∧ (setRange len start stop).2 ≤ len := by
  unfold setRange
  cases stop <;> simp <;> omega

/-- Bounds. Says: the range that `setRangeText` replaces lies inside the old text (given
`start ≤ stop`, which the caller checks). -/
theorem rangeText_range (len start stop selS selE newLen : Nat) (mode : Mode) (h : start ≤ stop) :
    (rangeText len start stop selS selE newLen mode).start ≤ (rangeText len start stop selS selE newLen mode).stop ∧
    (rangeText len start stop selS selE newLen mode).stop ≤ len := by
  unfold rangeText
  cases mode <;> simp <;> omega

/-- Bounds. Says: after `setRangeText` the selection lies inside the new text: both ends are
at most the new length, in every mode, when the selection before was inside the old text
and `start ≤ stop`. So a later read of the selected text never reads outside the value.
Does not say: that the start is not after the end in the "preserve" mode when the old
selection was reversed (the caller's "set the selection range" orders them). -/
theorem rangeText_selection (len start stop selS selE newLen : Nat) (mode : Mode)
    (h : start ≤ stop) (hs : selS ≤ len) (he : selE ≤ len) :
    let r := rangeText len start stop selS selE newLen mode
    r.selStart ≤ newLength len r newLen ∧ r.selEnd ≤ newLength len r newLen := by
  unfold rangeText newLength
  cases mode <;> simp <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

/-! ## Tests (WPT html/semantics/forms/textfieldselection) -/

#guard setRange 10 (some 2) (some 5) == (2, 5)
#guard setRange 10 (some 7) (some 5) == (5, 5)
#guard setRange 10 (some 2) (some 50) == (2, 10)
#guard setRange 10 none none == (0, 10)
-- "foobar".setRangeText("xyz", 1, 3): select / start / end / preserve with the selection 2..4
#guard rangeText 6 1 3 2 4 3 .select == { start := 1, stop := 3, selStart := 1, selEnd := 4 }
#guard rangeText 6 1 3 2 4 3 .start == { start := 1, stop := 3, selStart := 1, selEnd := 1 }
#guard rangeText 6 1 3 2 4 3 .stop == { start := 1, stop := 3, selStart := 4, selEnd := 4 }
#guard rangeText 6 1 3 2 4 3 .preserve == { start := 1, stop := 3, selStart := 1, selEnd := 5 }
-- a range past the end is clamped; the replacement is appended
#guard rangeText 6 9 12 0 6 2 .preserve == { start := 6, stop := 6, selStart := 0, selEnd := 6 }
#guard answer "6 1 3 2 4 3 preserve" == "1 3 1 5" && answer "6 1 3 2 4 3 end" == "1 3 4 4" && answer "x" == ""

end L4Factoidal.HTML.TextSelection
