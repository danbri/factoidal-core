import L4Factoidal.Rendering.Grid.Template

/-!
L4Factoidal.Rendering.Grid.Abspos — the containing block of an absolutely positioned box
whose containing block is a grid container (CSS Grid Layout 2 §9.1).

The grid-placement properties of such a box name lines of the container's grid; an
`auto` line is the container's padding edge (the "augmented grid"). A line that the
implicit grid does not have, given or reached by a span, is `auto` too. Nothing here is
placed: there is no auto-placement for these boxes and they take no part in track sizing.

* `absRaw`: the two lines of one axis, as lines of the explicit grid (`none`: `auto`);
* `absLines`: the same as lines of the implicit grid (`lead` lines before the explicit
  grid's first), or `none` when outside it;
* `absSpan`: the start and end of the containing block in that axis, from the start of
  every track and its size, and the padding edges.

Whole layout units, as the rest of `Rendering/Grid/`.
-/
namespace L4Factoidal.Rendering.Grid

/-- The two lines of an axis (§8.3 and §8.3.1, then §9.1), as lines of the explicit grid
(0 is its first line), `none` for `auto`. Two lines in the wrong order are exchanged; when
they are equal the end line is dropped (so it is `auto`). A span against `auto`, or two
spans, leave both sides `auto`. `names` are the lines of the explicit grid. -/
def absRaw (names : Array (List String)) (start end_ : Line) : Option Int × Option Int :=
  let tracks := names.size - 1
  match resolveSide names tracks false start, resolveSide names tracks true end_ with
  | .line s, .line e => if s < e then (some s, some e) else if e < s then (some e, some s) else (some s, none)
  | .line s, .span n name =>
    (some s, some (match name with | none => s + (n : Int) | some nm => spanEnd names tracks s n nm))
  | .span n name, .line e =>
    (some (match name with | none => e - (n : Int) | some nm => spanStart names e n nm), some e)
  | .line s, .auto => (some s, none)
  | .auto, .line e => (none, some e)
  | _, _ => (none, none)

/-- Line `i` of the explicit grid as a line of an implicit grid of `total` tracks that
has `lead` tracks before the explicit grid; `none` when the implicit grid has no such
line. -/
def inImplicit (lead total : Nat) (i : Int) : Option Nat :=
  if 0 ≤ i + (lead : Int) ∧ i + (lead : Int) ≤ (total : Int) then some (i + (lead : Int)).toNat else none

/-- §9.1: the lines of the containing block in one axis, as lines of the implicit grid;
`none` is the padding edge. -/
def absLines (names : Array (List String)) (lead total : Nat) (start end_ : Line) : Option Nat × Option Nat :=
  let r := absRaw names start end_
  (r.1.bind (inImplicit lead total), r.2.bind (inImplicit lead total))

/-- Where line `i` is when it starts an area: the start of track `i`, or the end of the
last track for the last line. -/
def lineStartAt (starts : Array Int) (sizes : Array Nat) (i : Nat) : Int :=
  if i < starts.size then starts.getD i 0
  else if starts.size = 0 then 0
  else starts.getD (starts.size - 1) 0 + Int.ofNat (sizes.getD (starts.size - 1) 0)

/-- Where line `i` is when it ends an area: the end of track `i - 1` (the gap after it is
not in the area), or the start of the first track for the first line. -/
def lineEndAt (starts : Array Int) (sizes : Array Nat) (i : Nat) : Int :=
  if i = 0 then starts.getD 0 0
  else starts.getD (i - 1) 0 + Int.ofNat (sizes.getD (i - 1) 0)

/-- The start and end of the containing block in one axis: the lines that `absLines`
found, else the padding edges `padStart` and `padEnd`. Positions are from the content
box's start edge, as `starts` are. -/
def absSpan (starts : Array Int) (sizes : Array Nat) (padStart padEnd : Int) (lines : Option Nat × Option Nat) :
    Int × Int :=
  (match lines.1 with | some i => lineStartAt starts sizes i | none => padStart,
   match lines.2 with | some i => lineEndAt starts sizes i | none => padEnd)

/-- Kind: conformance (§9.1). Says: a line `inImplicit` answers is a line of the implicit
grid: at most its number of tracks. -/
theorem inImplicit_le (lead total : Nat) (i : Int) (j : Nat) (h : inImplicit lead total i = some j) :
    j ≤ total := by
  unfold inImplicit at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    omega
  · simp at h

/-- Kind: conformance (§9.1). Says: both lines of a containing block are lines of the
implicit grid, or the padding edge. Does not say: that they are the right lines (the
`#guard`s below test that). -/
theorem absLines_inside (names : Array (List String)) (lead total : Nat) (start end_ : Line) :
    (∀ j, (absLines names lead total start end_).1 = some j → j ≤ total) ∧
    (∀ j, (absLines names lead total start end_).2 = some j → j ≤ total) := by
  constructor
  · intro j h
    simp only [absLines, Option.bind_eq_some_iff] at h
    obtain ⟨i, _, hi⟩ := h
    exact inImplicit_le lead total i j hi
  · intro j h
    simp only [absLines, Option.bind_eq_some_iff] at h
    obtain ⟨i, _, hi⟩ := h
    exact inImplicit_le lead total i j hi

/-- Kind: conformance (§9.1). Says: a box with `auto` on both sides has the padding box
as its containing block in that axis. -/
theorem absSpan_auto (starts : Array Int) (sizes : Array Nat) (padStart padEnd : Int) :
    absSpan starts sizes padStart padEnd (none, none) = (padStart, padEnd) := rfl

/-- Kind: conformance (§8.3.1, §9.1). Says: two numbered lines (no names) give lines in
order: when both are found, the start is before the end. -/
theorem absRaw_ordered (names : Array (List String)) (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) (s e : Int)
    (h : absRaw names (.index a none) (.index b none) = (some s, some e)) : s < e := by
  simp only [absRaw, resolveSide, ha, hb, beq_iff_eq, if_false] at h
  split at h
  · simp only [Prod.mk.injEq, Option.some.injEq] at h; omega
  · split at h
    · simp only [Prod.mk.injEq, Option.some.injEq] at h; omega
    · simp at h

/-! ### Examples (the grid of `abspos/positioned-grid-descendants-*`: two columns of 200
and 300 px, no gaps; units are px here for reading) -/

private def noNames : Array (List String) := #[[], [], []]

#guard absLines noNames 0 2 (.index 1 none) (.index 3 none) == (some 0, some 2)
#guard absLines noNames 0 2 .auto (.index 2 none) == (none, some 1)
#guard absLines noNames 0 2 (.index 2 none) .auto == (some 1, none)
#guard absLines noNames 0 2 .auto .auto == (none, none)
-- equal lines: the end line is dropped
#guard absLines noNames 0 2 (.index 2 none) (.index 2 none) == (some 1, none)
-- reversed lines are exchanged
#guard absLines noNames 0 2 (.index 3 none) (.index 1 none) == (some 0, some 2)
-- a line the grid does not have is `auto`
#guard absLines noNames 0 2 (.index 5 none) .auto == (none, none)
-- a span from a line
#guard absLines noNames 0 2 (.index 1 none) (.span 2 none) == (some 0, some 2)
-- a span against `auto`
#guard absLines noNames 0 2 (.span 2 none) .auto == (none, none)
-- lines of a named area
#guard absLines #[["a-start"], [], ["a-end"]] 0 2 (.ident "a") (.ident "a") == (some 0, some 2)
-- an implicit track before the explicit grid
#guard absLines noNames 1 3 (.index (-4) none) (.index 1 none) == (some 0, some 1)

#guard absSpan #[0, 200] #[200, 300] (-5) 565 (some 0, some 2) == (0, 500)
#guard absSpan #[0, 200] #[200, 300] (-5) 565 (none, some 1) == (-5, 200)
#guard absSpan #[0, 200] #[200, 300] (-5) 565 (some 1, none) == (200, 565)
-- with a gap of 10 the end of an area is the end of its last track, not the gap after it
#guard absSpan #[0, 210] #[200, 300] (-5) 565 (some 0, some 1) == (0, 200)
#guard absSpan #[0, 210] #[200, 300] (-5) 565 (some 1, some 2) == (210, 510)

end L4Factoidal.Rendering.Grid
