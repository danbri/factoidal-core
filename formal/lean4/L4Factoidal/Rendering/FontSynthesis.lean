/-
L4Factoidal.Rendering.FontSynthesis — `font-weight` and `font-style` of the layout cascade,
and the bold and oblique faces the engine makes when it holds no such face.

Source: CSS Fonts 4 (https://drafts.csswg.org/css-fonts-4/) §2.2 `font-weight` (the values,
§2.2.1 the relative weights `bolder` and `lighter`), §2.4 `font-style`, §5.3
`font-synthesis-weight` and `font-synthesis-style` (initial value `auto`: "the user agent
may synthesize" a bold or an oblique face when the family has none); HTML §15.3 (the
rendering section: `b`, `strong`, headings and `th` are bold, `i`, `em`, `cite`, `var`,
`dfn` and `address` are italic).

The engine holds one face of its text font (regular, upright). Before this module no page
drew bold or italic text: the two properties had no field in the layout cascade. Here:

* `weight?`: the computed weight (1 to 1000) of a `font-weight` value under a parent's
  weight; `bolder` and `lighter` by the table of §2.2.1.
* `oblique?`: whether a `font-style` value asks for a slanted face.
* `isBold`: a weight of 600 or more is drawn with the bold face (CSS Fonts 4 §5.2 font
  matching: a weight above 500 looks for heavier faces first; browsers synthesize bold
  from 600 up).
* `embolden`: the stroke that makes the bold face, in 1/64 px, for a font size in 1/64
  px: the outline is filled and also stroked with the fill colour, so each stem grows
  by the stroke's width. 1/24 of the size up to 9 px, 1/32 from 36 px, and between the
  two in proportion (the figures of the common open-source rasteriser's "fake bold").
* `shear`: the oblique face: a point moves along the line by a fixed fraction (`slant`,
  1/4: about 14 degrees) of its height above the baseline; the baseline stays.

A page with no bold and no slanted text pays nothing: the regular path is unchanged.

Not here: real bold and italic faces (a family that has them should use them: none is
held), `font-synthesis` (always `auto`), `font-stretch`, oblique angles (any `oblique` is
the one slant), and advances (a synthesized bold glyph keeps the advance of the regular
one, as browsers do).
-/

namespace L4Factoidal.Rendering.FontSynthesis

/-- The weight of `normal`. -/
def normalWeight : Nat := 400
/-- The weight of `bold`. -/
def boldWeight : Nat := 700

/-- CSS Fonts 4 §2.2.1: the weight `bolder` gives under an inherited weight. -/
def bolder (w : Nat) : Nat :=
  if w < 350 then 400 else if w < 550 then 700 else if w < 900 then 900 else w

/-- CSS Fonts 4 §2.2.1: the weight `lighter` gives under an inherited weight. -/
def lighter (w : Nat) : Nat :=
  if w < 100 then w else if w < 550 then 100 else if w < 750 then 400 else 700

/-- A whole number written in decimal digits only (1 to 4 digits). -/
def digits? (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty || cs.length > 4 || !cs.all (fun c => '0' ≤ c && c ≤ '9') then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)

/-- A value as the cascade compares it: no white space around it, lower case. -/
def norm (s : String) : String := s.trimAscii.toString.toLower

/-- The computed weight of a `font-weight` value under the parent's weight `parent`: a
keyword, or a whole number from 1 to 1000; none for any other value (the declaration is
then not this profile's, and the weight stays as it was). -/
def weight? (parent : Nat) (value : String) : Option Nat :=
  let v := norm value
  if v == "normal" then some normalWeight
  else if v == "bold" then some boldWeight
  else if v == "bolder" then some (bolder parent)
  else if v == "lighter" then some (lighter parent)
  else match digits? v with
    | some n => if 1 ≤ n && n ≤ 1000 then some n else none
    | none => none

/-- Whether a `font-style` value asks for a slanted face: `italic`, `oblique` (with or
without an angle); `normal` does not; none for any other value. -/
def oblique? (value : String) : Option Bool :=
  let v := norm value
  if v == "normal" then some false
  else if v == "italic" || v == "oblique" || v.startsWith "oblique " then some true
  else none

/-- A weight drawn with the bold face. -/
def isBold (w : Nat) : Bool := w ≥ 600

/-- HTML §15.3.4 and §15.3.6: the elements whose text is bold by the rendering section. -/
def boldTags : List String := ["b", "strong", "h1", "h2", "h3", "h4", "h5", "h6", "th"]

/-- HTML §15.3.4: the elements whose text is italic by the rendering section. -/
def italicTags : List String := ["i", "em", "cite", "var", "dfn", "address"]

/-- The stroke width of the synthesized bold face in 1/64 px, for a font size in 1/64 px
(the header of this file). -/
def embolden (size : Nat) : Nat :=
  let small := 9 * 64
  let large := 36 * 64
  if size ≤ small then size / 24
  else if size ≥ large then size / 32
  else
    -- between 1/24 and 1/32 in proportion: 768 = lcm(24, 32) * 8 keeps the division exact enough
    let t := size - small
    let span := large - small
    (size * (32 * span - 8 * t)) / (768 * span)

/-- The slant of the synthesized oblique face: a point one unit above the baseline moves
`slantNum / slantDen` units along the line. -/
def slantNum : Int := 1
def slantDen : Int := 4

/-- The oblique face of a point, in whole units scaled by `slantDen` so that the division
is exact: `(x, y)` with `y` growing downwards and the baseline at `baseline` goes to
`(slantDen * x + slantNum * (baseline - y), slantDen * y)`. -/
def shear (baseline : Int) (p : Int × Int) : Int × Int :=
  (slantDen * p.1 + slantNum * (baseline - p.2), slantDen * p.2)

/-! ## Theorems -/

/-- Kind: bounds. Says: `bolder` gives a weight from 1 to 1000 when the inherited weight is
one, and never a lighter weight. Does not say: which face is drawn for it (`isBold`). -/
theorem bolder_bounds (w : Nat) (h : 1 ≤ w ∧ w ≤ 1000) : w ≤ bolder w ∧ bolder w ≤ 1000 := by
  unfold bolder
  repeat' split
  all_goals omega

/-- Kind: bounds. Says: `lighter` gives a weight from 1 to 1000 when the inherited weight
is one, and never a heavier weight. -/
theorem lighter_bounds (w : Nat) (h : 1 ≤ w ∧ w ≤ 1000) : 1 ≤ lighter w ∧ lighter w ≤ w := by
  unfold lighter
  repeat' split
  all_goals omega

/-- Kind: property. Says: text inside `bolder` is drawn bold whenever its parent's weight is
`normal` or heavier (350 and up): `b` inside a paragraph, and `b` inside a heading.
Does not say: anything of the lightest parents (under 350, `bolder` is 400). -/
theorem bolder_isBold (w : Nat) (h : 350 ≤ w) : isBold (bolder w) = true := by
  unfold bolder isBold
  repeat' split
  all_goals simp
  all_goals omega

/-- Kind: property. Says: `lighter` under `bold` (700) is `normal` (400), not bold; and
`bolder` under `normal` is `bold`. The two examples of CSS Fonts 4 §2.2.1. -/
theorem relative_examples : lighter boldWeight = normalWeight ∧ bolder normalWeight = boldWeight ∧
    isBold (lighter boldWeight) = false := by decide

/-- Kind: bounds. Says: a weight that `weight?` reads is from 1 to 1000 when the parent's
is. Does not say: that every CSS weight value is read (`calc()` is not). -/
theorem weight?_bounds (parent : Nat) (value : String) (n : Nat) (hp : 1 ≤ parent ∧ parent ≤ 1000)
    (h : weight? parent value = some n) : 1 ≤ n ∧ n ≤ 1000 := by
  unfold weight? at h
  simp only at h
  split at h
  · cases h; decide
  · split at h
    · cases h; decide
    · split at h
      · cases h
        have := bolder_bounds parent hp
        omega
      · split at h
        · cases h
          have := lighter_bounds parent hp
          omega
        · split at h
          · split at h
            · rename_i hr
              cases h
              simp at hr
              omega
            · cases h
          · cases h

/-- Kind: bounds. Says: the bold stroke is at most 1/24 of the font size (so at 16 px it
is under one pixel, and a stem never grows by more than 1/24 em). Does not say: that the
drawn stroke has that width (the paint is in floating point; this is the number it is
given). -/
theorem embolden_le (size : Nat) : embolden size * 24 ≤ size := by
  unfold embolden
  simp only
  split
  · exact Nat.div_mul_le_self size 24
  · split
    · have := Nat.div_mul_le_self size 32
      omega
    · rename_i h1 h2
      have hs : 9 * 64 < size := by omega
      have hl : size < 36 * 64 := by omega
      -- (size * (32*span - 8*t)) / (768*span) * 24 ≤ size, since 32*span - 8*t ≤ 32*span
      have hnum : size * (32 * (36 * 64 - 9 * 64) - 8 * (size - 9 * 64)) ≤ size * (32 * (36 * 64 - 9 * 64)) :=
        Nat.mul_le_mul_left size (Nat.sub_le _ _)
      have hdiv : size * (32 * (36 * 64 - 9 * 64) - 8 * (size - 9 * 64)) / (768 * (36 * 64 - 9 * 64)) ≤
          size * (32 * (36 * 64 - 9 * 64)) / (768 * (36 * 64 - 9 * 64)) := Nat.div_le_div_right hnum
      have hcancel : size * (32 * (36 * 64 - 9 * 64)) / (768 * (36 * 64 - 9 * 64)) = size / 24 := by
        have e1 : (32 * (36 * 64 - 9 * 64) : Nat) = 55296 := by decide
        have e2 : (768 * (36 * 64 - 9 * 64) : Nat) = 24 * 55296 := by decide
        rw [e1, e2]
        exact Nat.mul_div_mul_right size 24 (by decide)
      calc size * (32 * (36 * 64 - 9 * 64) - 8 * (size - 9 * 64)) / (768 * (36 * 64 - 9 * 64)) * 24
          ≤ size / 24 * 24 := Nat.mul_le_mul_right 24 (Nat.le_trans hdiv (Nat.le_of_eq hcancel))
        _ ≤ size := Nat.div_mul_le_self size 24

/-- Kind: property. Says: the oblique face keeps the baseline: a point on it is not moved
along the line, and no point changes its height (both in units scaled by `slantDen`).
Does not say: anything of the advance of the glyph (it is kept as it was). -/
theorem shear_baseline (baseline x : Int) : shear baseline (x, baseline) = (slantDen * x, slantDen * baseline) := by
  simp [shear]

theorem shear_height (baseline : Int) (p : Int × Int) : (shear baseline p).2 = slantDen * p.2 := rfl

/-- Kind: property. Says: the oblique face leans to the right: a point above the baseline
(`y` smaller) moves further along the line than it would on the baseline, in proportion
to its height. -/
theorem shear_leans (baseline x y : Int) (h : y < baseline) :
    slantDen * x < (shear baseline (x, y)).1 := by
  simp [shear, slantDen, slantNum]
  omega

/-! ## Tests -/

#guard weight? 400 "bold" == some 700 && weight? 400 " Normal " == some 400 && weight? 400 "600" == some 600
#guard weight? 400 "bolder" == some 700 && weight? 700 "bolder" == some 900 && weight? 900 "bolder" == some 900
#guard weight? 100 "bolder" == some 400 && weight? 700 "lighter" == some 400 && weight? 400 "lighter" == some 100
#guard weight? 400 "0" == none && weight? 400 "1001" == none && weight? 400 "1000" == some 1000 && weight? 400 "1" == some 1
#guard weight? 400 "heavy" == none && weight? 400 "" == none && weight? 400 "4e2" == none && weight? 400 "var(--w)" == none
#guard isBold 700 && isBold 600 && !isBold 500 && !isBold 400
#guard oblique? "italic" == some true && oblique? "oblique" == some true && oblique? "oblique 10deg" == some true
#guard oblique? "normal" == some false && oblique? "ITALIC" == some true && oblique? "slanted" == none
-- the stroke of the bold face: 16 px text (1024 units) gets 39/64 px, 9 px 24/64, 36 px 72/64
#guard embolden (16 * 64) == 39 && embolden (9 * 64) == 24 && embolden (36 * 64) == 72 && embolden (72 * 64) == 144
#guard embolden 0 == 0
-- a point 400 units above the baseline moves 100 units along the line (both scaled by 4 here); one below moves back
#guard shear 800 (100, 800) == (400, 3200) && shear 800 (100, 400) == (800, 1600) && shear 800 (100, 1000) == (200, 4000)

end L4Factoidal.Rendering.FontSynthesis
