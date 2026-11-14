import L4Factoidal.Rendering.LayoutUnit

/-! Sizes from a preferred aspect ratio (CSS Sizing 4 §5: `aspect-ratio`), on layout units.

A ratio is `num : den`, width to height, both positive. A size in one axis gives the
other through the ratio; the limits `min-width`, `max-width`, `min-height` and
`max-height` are carried to the other axis too (§5.1 "transferred"), and when limits
disagree a limit of the axis itself wins over a transferred one, and a minimum over a
maximum of the same axis. This module has no import from the engine. -/
namespace L4Factoidal.Rendering.Ratio
open LU

/-- The height of a box `w` wide with the ratio `num : den`, rounded down to a unit. -/
def heightFor (num den : Nat) (w : Int) : Int := w * (den : Int) / (num : Int)

/-- The width of a box `h` high with the ratio `num : den`, rounded down to a unit. -/
def widthFor (num den : Nat) (h : Int) : Int := h * (num : Int) / (den : Int)

/-- The used size of a box with `width: auto` and `height: auto`, the ratio `num : den`
and the natural width `natural` (§5.1): the width within the limits carried over from
the height, then within its own (`minW`, `maxW`); the height is that width's by the
ratio, within its own limits (`minH`, `maxH`). `none` is no maximum. -/
def autoSize (num den : Nat) (natural minW : Int) (maxW : Option Int) (minH : Int) (maxH : Option Int) : Int × Int :=
  let w := match maxH with
    | some m => min (widthFor num den m) natural
    | none => natural
  let w := clamp minW maxW (max (widthFor num den minH) w)
  (w, clamp minH maxH (heightFor num den w))

/-- The used size with a width given and `height: auto`. -/
def fromWidth (num den : Nat) (w minW : Int) (maxW : Option Int) (minH : Int) (maxH : Option Int) : Int × Int :=
  let w := clamp minW maxW w
  (w, clamp minH maxH (heightFor num den w))

/-- The used size with a height given and `width: auto`. -/
def fromHeight (num den : Nat) (h minW : Int) (maxW : Option Int) (minH : Int) (maxH : Option Int) : Int × Int :=
  let h := clamp minH maxH h
  (clamp minW maxW (widthFor num den h), h)

/-- Bounds. Says: the width is never below `min-width`, the height never below `min-height`. -/
theorem autoSize_min (num den : Nat) (natural minW : Int) (maxW : Option Int) (minH : Int) (maxH : Option Int) :
    minW ≤ (autoSize num den natural minW maxW minH maxH).1 ∧
    minH ≤ (autoSize num den natural minW maxW minH maxH).2 := by
  unfold autoSize
  exact ⟨le_clamp _ _ _, le_clamp _ _ _⟩

/-- Bounds. Says: the width is no more than `max-width` and the height no more than
`max-height`, unless the minimum of that axis is larger (a minimum wins). -/
theorem autoSize_max (num den : Nat) (natural minW mw minH mh : Int) :
    (autoSize num den natural minW (some mw) minH (some mh)).1 ≤ max minW mw ∧
    (autoSize num den natural minW (some mw) minH (some mh)).2 ≤ max minH mh := by
  unfold autoSize
  exact ⟨clamp_le _ _ _, clamp_le _ _ _⟩

/-- Ratio. Says: when the height that the ratio gives the used width is within the
height's own limits, it is the used height: the box has the ratio (to the unit).
Does not say: that the ratio is kept when a limit of the height binds (then the limit
wins, §5.1). -/
theorem autoSize_ratio (num den : Nat) (natural minW : Int) (maxW : Option Int) (minH : Int) (maxH : Option Int)
    (lo : minH ≤ heightFor num den (autoSize num den natural minW maxW minH maxH).1)
    (hi : ∀ m, maxH = some m → heightFor num den (autoSize num den natural minW maxW minH maxH).1 ≤ m) :
    (autoSize num den natural minW maxW minH maxH).2 =
      heightFor num den (autoSize num den natural minW maxW minH maxH).1 := by
  unfold autoSize at lo hi ⊢
  exact clamp_of_within _ _ _ lo hi

/-- Natural size. Says: with no limit that binds (no maximum, minimums 0, a natural width
that is not negative), the width is the natural width. -/
theorem autoSize_natural (num den : Nat) (natural : Int) (h : 0 ≤ natural) :
    (autoSize num den natural 0 none 0 none).1 = natural := by
  unfold autoSize widthFor clamp
  simp only [Int.zero_mul, Int.zero_ediv]
  omega

/-- Round trip. Says: a height carried to a width and back is not more than it was:
carrying a maximum over to the other axis never lets the box exceed it. -/
theorem heightFor_widthFor_le (num den : Nat) (h : Int) (hn : 0 < num) (hd : 0 < den) :
    heightFor num den (widthFor num den h) ≤ h := by
  unfold heightFor widthFor
  have hd' : (0 : Int) < (den : Int) := by omega
  have hn' : (0 : Int) < (num : Int) := by omega
  have h1 : h * (num : Int) / (den : Int) * (den : Int) ≤ h * (num : Int) := Int.ediv_mul_le _ (by omega)
  calc h * (num : Int) / (den : Int) * (den : Int) / (num : Int) ≤ h * (num : Int) / (num : Int) := Int.ediv_le_ediv hn' h1
    _ = h := Int.mul_ediv_cancel h (by omega)

/-- Bounds. Says: a given width with its limits applied is within them, and so is the height. -/
theorem fromWidth_min (num den : Nat) (w minW : Int) (maxW : Option Int) (minH : Int) (maxH : Option Int) :
    minW ≤ (fromWidth num den w minW maxW minH maxH).1 ∧ minH ≤ (fromWidth num den w minW maxW minH maxH).2 := by
  unfold fromWidth
  exact ⟨le_clamp _ _ _, le_clamp _ _ _⟩

theorem fromHeight_min (num den : Nat) (h minW : Int) (maxW : Option Int) (minH : Int) (maxH : Option Int) :
    minW ≤ (fromHeight num den h minW maxW minH maxH).1 ∧ minH ≤ (fromHeight num den h minW maxW minH maxH).2 := by
  unfold fromHeight
  exact ⟨le_clamp _ _ _, le_clamp _ _ _⟩

-- The cases of WPT css/css-sizing/aspect-ratio/replaced-element-043.html, in px (ratio 2:1,
-- natural width 15): the limit of an axis wins over a transferred one, a minimum over a maximum.
private def px2 (natural minW : Int) (maxW : Option Int) (minH : Int) (maxH : Option Int) : Int × Int :=
  autoSize 2 1 natural minW maxW minH maxH
#guard autoSize 2 1 960 0 none 0 none == (960, 480)
#guard px2 30 0 none 0 none == (30, 15)
#guard px2 30 40 none 0 none == (40, 20)
#guard px2 30 0 none 20 none == (40, 20)
#guard px2 30 0 (some 20) 0 none == (20, 10)
#guard px2 30 0 none 0 (some 10) == (20, 10)
#guard px2 30 40 none 0 (some 10) == (40, 10)
#guard px2 30 0 (some 20) 20 none == (20, 20)
#guard px2 30 0 (some 0) 0 (some 10) == (0, 0)
#guard px2 30 20 none 0 (some 0) == (20, 0)
#guard px2 30 0 (some 60) 30 none == (60, 30)
#guard px2 30 0 (some 100) 50 none == (100, 50)
-- From the test, natural width 15: `min-width: 20px; max-height: 5px` is 20 by 5 and
-- `max-width: 10px; min-height: 10px` is 10 by 10.
#guard autoSize 2 1 15 20 none 0 (some 5) == (20, 5)
#guard autoSize 2 1 15 0 (some 10) 10 none == (10, 10)
#guard autoSize 2 1 15 0 (some 20) 25 none == (20, 25)
#guard autoSize 2 1 15 10 none 0 (some 0) == (10, 0)
#guard fromWidth 2 1 80 0 none 0 none == (80, 40)
#guard fromHeight 2 1 50 0 none 0 none == (100, 50)
#guard fromHeight 16 9 90 0 none 0 none == (160, 90)

end L4Factoidal.Rendering.Ratio
