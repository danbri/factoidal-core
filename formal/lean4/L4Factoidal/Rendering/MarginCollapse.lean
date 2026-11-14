/-! Collapsing margins (CSS 2.1 §8.3.1), on whole numbers. This module has no import from
the engine.

Two adjoining vertical margins make one: the larger when neither is negative, the more
negative when both are, and their sum when one is negative. The layout stacks boxes with
their margins and takes the `overlap` out between two of them; when no margin is negative
that is the smaller of the two, as it was before negative margins were read
(`overlap_nonneg`).

The layout applies `collapse` two margins at a time, to the margin so far and the next
one. That is exact for two margins and for any number of the same sign; three or more
adjoining margins of mixed signs should take the largest positive and the most negative
of all of them, which the pairwise form does not always give (10, -5, 8: 5 by the rule,
8 pairwise). The layout's own functions are the same text on `Float` (`Layout.collapsePx`,
`Layout.overlapPx`): what is proved here is proved of this form, not of floating point. -/
namespace L4Factoidal.Rendering.MarginCollapse

/-- The margin that the adjoining margins `a` and `b` make. -/
def collapse (a b : Int) : Int :=
  if 0 ≤ a ∧ 0 ≤ b then max a b else if a < 0 ∧ b < 0 then min a b else a + b

/-- How far the second box moves into the first one's margin: what `a + b` loses. -/
def overlap (a b : Int) : Int :=
  if 0 ≤ a ∧ 0 ≤ b then min a b else if a < 0 ∧ b < 0 then max a b else 0

/-- Says: the rule of §8.3.1: the largest positive margin plus the most negative one. -/
theorem collapse_spec (a b : Int) : collapse a b = max (max a 0) (max b 0) + min (min a 0) (min b 0) := by
  unfold collapse
  split
  · omega
  · split <;> omega

/-- Says: stacking the two margins and taking the overlap out leaves the collapsed margin. -/
theorem overlap_spec (a b : Int) : a + b - overlap a b = collapse a b := by
  unfold overlap collapse
  split
  · omega
  · split <;> omega

theorem collapse_comm (a b : Int) : collapse a b = collapse b a := by
  rw [collapse_spec, collapse_spec]
  omega

/-- Says: with no negative margin the larger one stands. -/
theorem collapse_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : collapse a b = max a b := by
  rw [collapse_spec]; omega

/-- Says: with no negative margin the overlap is the smaller one: what the layout took
out before negative margins were read. -/
theorem overlap_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : overlap a b = min a b := by
  unfold overlap; simp [ha, hb]

/-- Says: a margin that adjoins no margin stands as it is. -/
theorem collapse_zero (a : Int) : collapse a 0 = a := by
  rw [collapse_spec]; omega

/-- Says: the collapsed margin is never more than the larger of the two, and never less
than their sum when one is negative or the smaller one otherwise: collapsing never adds
space. -/
theorem collapse_le_max (a b : Int) : collapse a b ≤ max a b := by
  rw [collapse_spec]; omega

/-- Says: a negative margin beside a positive one takes exactly its size off it. -/
theorem collapse_mixed (a b : Int) (ha : 0 ≤ a) (hb : b < 0) : collapse a b = a + b := by
  rw [collapse_spec]; omega

/-- Says: three margins of one sign collapse to the same margin in either grouping. -/
theorem collapse_assoc_nonneg (a b c : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    collapse (collapse a b) c = collapse a (collapse b c) := by
  simp only [collapse_spec]; omega

#guard collapse 10 20 == 20
#guard collapse 10 (-4) == 6
#guard collapse (-10) (-4) == -10
#guard collapse (-10) 4 == -6
#guard overlap 10 20 == 10
#guard overlap 10 (-4) == 0
#guard overlap (-10) (-4) == -4
#guard collapse (collapse 10 (-5)) 8 == 8

end L4Factoidal.Rendering.MarginCollapse
