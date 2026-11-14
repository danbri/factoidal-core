/-! Scrolling of a scroll container (CSSOM View §4, §6.1, §13; CSS Overflow 3 §2;
CSS Positioned Layout 3 §3.4 for `position: sticky`), on one axis and in whole layout
units. This module has no import from the engine.

A scroll container shows a window (`client` long) on its scrollable overflow (`extent`
long); its scroll position is how far the window is from the start. Everything here is a
function of numbers that a layout already has: **a scroll changes an offset and nothing
that a layout computes**, so the functions take the layout's numbers and never ask for a
new layout.

Proved: a position is always inside the range that can be scrolled (`clamp_within`),
clamping is idempotent and changes no position that is in range; with nothing to scroll
the position is 0; a relative scroll moves in its direction and no further than asked
(`scrollBy_between`); after `intoView` a target that fits in the window is inside it
whenever the range lets it be (`intoView_shows`), and a target already inside is not moved
(`intoView_still`); a sticky box never moves against its direction, stays in its
containing block, and is at its inset from the window's edge whenever that keeps it in
the containing block (`stickyStart_*`). -/
namespace L4Factoidal.Rendering.Scroll

/-- The largest scroll position: what of the overflow is past the window. -/
def range (extent client : Int) : Int := max 0 (extent - client)

/-- A scroll position inside the range. -/
def clamp (extent client position : Int) : Int := max 0 (min (range extent client) position)

theorem range_nonneg (extent client : Int) : 0 ≤ range extent client := by unfold range; omega

/-- Says: a position is never before the start and never past the range. -/
theorem clamp_within (extent client position : Int) :
    0 ≤ clamp extent client position ∧ clamp extent client position ≤ range extent client := by
  unfold clamp range; omega

/-- Says: a position that is in range is left as it is. -/
theorem clamp_in_range (extent client position : Int) (lo : 0 ≤ position) (hi : position ≤ range extent client) :
    clamp extent client position = position := by
  unfold clamp range at *; omega

theorem clamp_idem (extent client position : Int) :
    clamp extent client (clamp extent client position) = clamp extent client position := by
  have h := clamp_within extent client position
  exact clamp_in_range _ _ _ h.1 h.2

/-- Says: a box whose content does not overflow does not scroll. -/
theorem clamp_no_overflow (extent client position : Int) (h : extent ≤ client) : clamp extent client position = 0 := by
  unfold clamp range; omega

/-- Says: a later position is never clamped to before an earlier one. -/
theorem clamp_mono (extent client a b : Int) (h : a ≤ b) : clamp extent client a ≤ clamp extent client b := by
  unfold clamp range; omega

/-- The position after a scroll by `delta` (a wheel step, a key, `scrollBy`). -/
def scrollBy (extent client position delta : Int) : Int := clamp extent client (clamp extent client position + delta)

/-- Says: a scroll forward does not go back and goes no further than asked; a scroll
back likewise. -/
theorem scrollBy_between (extent client position delta : Int) :
    (0 ≤ delta → clamp extent client position ≤ scrollBy extent client position delta ∧
      scrollBy extent client position delta ≤ clamp extent client position + delta) ∧
    (delta ≤ 0 → scrollBy extent client position delta ≤ clamp extent client position ∧
      clamp extent client position + delta ≤ scrollBy extent client position delta) := by
  unfold scrollBy clamp range; omega

/-- Says: a scroll of nothing changes nothing. -/
theorem scrollBy_zero (extent client position : Int) :
    scrollBy extent client position 0 = clamp extent client position := by
  unfold scrollBy
  rw [Int.add_zero, clamp_idem]

/-- Says: the container can scroll further in the direction of `delta`: what the input
path asks before it hands a wheel step to the container around this one. -/
def canScroll (extent client position delta : Int) : Bool := scrollBy extent client position delta != clamp extent client position

theorem canScroll_no_overflow (extent client position delta : Int) (h : extent ≤ client) :
    canScroll extent client position delta = false := by
  unfold canScroll scrollBy
  simp [clamp_no_overflow _ _ _ h]

/-- Where `scrollIntoView` puts a target (CSSOM View §13.1 "scroll an element into view"). -/
inductive Align where
  | start | center | end_ | nearest
  deriving Repr, BEq, DecidableEq

/-- The position that brings the target (from `target`, `size` long, in the coordinates of
the scrollable overflow) into the window, from the position `position`: its start at the
window's start, its centre at the centre, its end at the end, or for `nearest` the least
move that shows it (none when it is inside already; a target longer than the window is
brought to the nearer edge). -/
def intoView (extent client position target size : Int) (align : Align) : Int :=
  let at_ := clamp extent client position
  clamp extent client (match align with
    | .start => target
    | .center => target + size / 2 - client / 2
    | .end_ => target + size - client
    | .nearest =>
      if at_ ≤ target ∧ target + size ≤ at_ + client then at_           -- inside: stay
      else if target < at_ ∧ at_ + client < target + size then at_      -- covers the window: stay
      else if target < at_ then (if size ≤ client then target else target + size - client)
      else (if size ≤ client then target + size - client else target))

/-- Says: `nearest` does not move a target that is inside the window. -/
theorem intoView_still (extent client position target size : Int)
    (h : clamp extent client position ≤ target ∧ target + size ≤ clamp extent client position + client) :
    intoView extent client position target size .nearest = clamp extent client position := by
  unfold intoView
  simp only [h, and_self, ↓reduceIte]
  exact clamp_idem ..

/-- Says: a target that fits in the window and lies inside the scrollable overflow is
inside the window after `intoView`, for every alignment but `center` (whose place the
range may cut on either side). -/
theorem intoView_shows (extent client position target size : Int) (align : Align) (hc : align ≠ .center)
    (fits : size ≤ client) (lo : 0 ≤ target) (hi : target + size ≤ extent) (pos : 0 ≤ size) :
    intoView extent client position target size align ≤ target ∧
      target + size ≤ intoView extent client position target size align + client := by
  cases align with
  | center => exact absurd rfl hc
  | start => unfold intoView clamp range; simp only; omega
  | end_ => unfold intoView clamp range; simp only; omega
  | nearest =>
    unfold intoView
    simp only
    split
    · rename_i h; rw [clamp_idem]; exact h
    · split
      · rename_i h; omega
      · split <;> (unfold clamp range; omega)

/-- `position: sticky` with an inset from the start edge (`top`, `left`): how far the box
moves from where the flow put it. `natural` is its start edge in the flow, `size` its
length, `window` the start of the scroll window (the scroll position, in the same
coordinates), `inset` the inset, and the box stays inside its containing block, which ends
at `blockEnd`. -/
def stickyStart (natural size window inset blockEnd : Int) : Int :=
  max 0 (min (window + inset - natural) (blockEnd - size - natural))

/-- Says: a sticky box never moves towards the start. -/
theorem stickyStart_nonneg (natural size window inset blockEnd : Int) :
    0 ≤ stickyStart natural size window inset blockEnd := by unfold stickyStart; omega

/-- Says: a box that the flow put inside its containing block stays inside it. -/
theorem stickyStart_in_block (natural size window inset blockEnd : Int) (h : natural + size ≤ blockEnd) :
    natural + stickyStart natural size window inset blockEnd + size ≤ blockEnd := by
  unfold stickyStart; omega

/-- Says: while its containing block has room, the box is at its inset from the window's
start or further on: it is not scrolled past. -/
theorem stickyStart_holds (natural size window inset blockEnd : Int)
    (room : window + inset + size ≤ blockEnd) :
    window + inset ≤ natural + stickyStart natural size window inset blockEnd := by
  unfold stickyStart; omega

/-- Says: a box that is past its inset already is where the flow put it. -/
theorem stickyStart_rest (natural size window inset blockEnd : Int) (h : window + inset ≤ natural) :
    stickyStart natural size window inset blockEnd = 0 := by
  unfold stickyStart; omega

/-- The same from the end edge (`bottom`, `right`): how far the box moves back (a number
that is not positive). `windowEnd` is the end of the scroll window and the containing
block starts at `blockStart`. -/
def stickyEnd (natural size windowEnd inset blockStart : Int) : Int :=
  min 0 (max (windowEnd - inset - size - natural) (blockStart - natural))

theorem stickyEnd_nonpos (natural size windowEnd inset blockStart : Int) :
    stickyEnd natural size windowEnd inset blockStart ≤ 0 := by unfold stickyEnd; omega

theorem stickyEnd_in_block (natural size windowEnd inset blockStart : Int) (h : blockStart ≤ natural) :
    blockStart ≤ natural + stickyEnd natural size windowEnd inset blockStart := by
  unfold stickyEnd; omega

#guard range 300 100 == 200
#guard clamp 300 100 250 == 200
#guard clamp 300 100 (-5) == 0
#guard clamp 80 100 30 == 0
#guard scrollBy 300 100 190 40 == 200
#guard scrollBy 300 100 10 (-40) == 0
#guard canScroll 300 100 200 40 == false
#guard canScroll 300 100 200 (-40) == true
#guard intoView 1000 100 0 250 20 .start == 250
#guard intoView 1000 100 0 250 20 .end_ == 170
#guard intoView 1000 100 0 250 20 .center == 210
#guard intoView 1000 100 0 250 20 .nearest == 170
#guard intoView 1000 100 400 250 20 .nearest == 250
#guard intoView 1000 100 200 250 20 .nearest == 200
#guard intoView 1000 100 0 950 20 .start == 900
#guard stickyStart 100 20 0 0 500 == 0
#guard stickyStart 100 20 150 0 500 == 50
#guard stickyStart 100 20 150 10 500 == 60
#guard stickyStart 100 20 600 0 500 == 380
#guard stickyEnd 400 20 300 0 0 == -120

end L4Factoidal.Rendering.Scroll
