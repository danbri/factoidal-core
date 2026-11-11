import L4Factoidal.Rendering.SfntFallback

/-! # Where a fallback-placed mark goes across

`SfntFallback.positionMark` (HarfBuzz `position_mark`) places a combining mark on its
base; `SfntProfile.wordWith` uses it also for a mark and a base of two fonts. For the
classes that centre a mark over its base (all but the left, right and double
classes 200, 216, 218, 222, 228, 232, 233 and 234), the mark is never outside the
base's box across, except by the half of the width it has more than the base, and by
one unit of rounding. -/
namespace L4Factoidal.Rendering.SfntFallback

/-- The classes that `positionMark` centres over the base. -/
def centred (cc : Nat) : Bool := !([233,234,200,218,228,216,222,232].contains cc)

/-- The horizontal place of a centred mark: the base's box, less the mark's width,
halved, from the base's left edge, less the mark's own left bearing. -/
theorem positionMark_x (base mark : Extents) (cc : Nat) (gap : Int) (h : centred cc = true) :
    (positionMark base mark cc gap).2.1 = base.xBearing + (base.width - mark.width).tdiv 2 - mark.xBearing := by
  simp [centred] at h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  unfold positionMark
  simp [h1,h2,h3,h4,h5,h6,h7,h8]
  repeat' split
  all_goals rfl

/-- A mark no wider than its base lies inside the base's box across. -/
theorem positionMark_inside (base mark : Extents) (cc : Nat) (gap : Int) (h : centred cc = true) (hb : mark.width ≤ base.width) :
    base.xBearing ≤ (positionMark base mark cc gap).2.1 + mark.xBearing ∧
    (positionMark base mark cc gap).2.1 + mark.xBearing + mark.width ≤ base.xBearing + base.width := by
  rw [positionMark_x base mark cc gap h]
  have e : (base.width - mark.width).tdiv 2 = (base.width - mark.width) / 2 :=
    Int.tdiv_eq_ediv_of_nonneg (by omega)
  rw [e]
  omega

/-- Any mark: its centre is the base's centre, to one unit (the doubled centres
differ by at most 1). So it is outside the base's box across by at most half of the
width it has more than the base, plus one unit. -/
theorem positionMark_centre (base mark : Extents) (cc : Nat) (gap : Int) (h : centred cc = true) :
    let left := (positionMark base mark cc gap).2.1 + mark.xBearing
    2*left + mark.width - (2*base.xBearing + base.width) ≤ 1 ∧
    (2*base.xBearing + base.width) - (2*left + mark.width) ≤ 1 := by
  simp only
  rw [positionMark_x base mark cc gap h]
  have d := Int.mul_tdiv_add_tmod (base.width - mark.width) 2
  have r := Int.tmod_lt_of_pos (base.width - mark.width) (by decide : (0:Int) < 2)
  have r' := Int.lt_tmod_of_pos (base.width - mark.width) (by decide : (0:Int) < 2)
  omega

/-- An above mark (class 230) that must go up to clear its base sits above the base's top
(y up), by the gap: its bottom is the base's top plus the gap. With
`positionMark_inside`, the property of issue 368: the mark is over the base's ink across,
and above it. -/
theorem positionMark_above (base mark : Extents) (gap : Int) (hg : 0 < gap)
    (up : 0 < base.yBearing + gap - mark.yBearing - mark.height) :
    (positionMark base mark 230 gap).2.2 = base.yBearing + gap - mark.yBearing - mark.height ∧
    (positionMark base mark 230 gap).2.2 + mark.yBearing + mark.height = base.yBearing + gap := by
  have e : (positionMark base mark 230 gap).2.2 = base.yBearing + gap - mark.yBearing - mark.height := by
    unfold positionMark
    simp
    split <;> simp_all <;> omega
  exact ⟨e, by rw [e]; omega⟩

end L4Factoidal.Rendering.SfntFallback
