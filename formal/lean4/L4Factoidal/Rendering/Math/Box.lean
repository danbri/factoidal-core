/-
L4Factoidal.Rendering.Math.Box — the boxes of MathML Core layout as exact integer
arithmetic, with the theorems the layout relies on.

Specification: MathML Core (https://w3c.github.io/mathml-core/), §3.1.3 (`mrow`), §3.3.2
(`mfrac`), §3.3.3 (`msqrt`, `mroot`), §3.4.1 (`msub`, `msup`, `msubsup`), §3.4.2 (`munder`,
`mover`, `munderover`), §3.2.4.3 (stretching), §3.3.6 (`mpadded`), §3.2.5 (`mspace`).

Lengths are layout units, 1/64 of a CSS pixel, as integers: every function here is exact,
so the theorems are statements about the numbers the engine computes, not about an ideal
model beside it. A box has an inline size (`width`) and a line-ascent and line-descent
from its alphabetic baseline. A child is placed by `At`: `dx` from the left edge of its
parent to its own left edge, `dy` from the parent's baseline down to its own baseline.

Nothing here reads a document, a style or a font: the tree walk (`Math.Layout`) gives the
child boxes and the font's parameters, and takes the positions these functions answer.
-/
namespace L4Factoidal.Rendering.Math

/-- A math box: inline size, ascent and descent from the baseline, in layout units. -/
structure MBox where
  width : Int := 0
  ascent : Int := 0
  descent : Int := 0
  deriving Repr, BEq, Inhabited

/-- Where a child sits in its parent: `dx` right of the parent's left edge, `dy` below the
parent's baseline (negative: raised). -/
structure At where
  dx : Int := 0
  dy : Int := 0
  deriving Repr, BEq, Inhabited

/-- The child box `c` placed at `p` lies inside the box `b`: between its left and right
edges, not above its ascent and not below its descent. -/
def Inside (b c : MBox) (p : At) : Prop :=
  0 ≤ p.dx ∧ p.dx + c.width ≤ b.width ∧ c.ascent - p.dy ≤ b.ascent ∧ c.descent + p.dy ≤ b.descent

/-! ### Rows (§3.1.3.2) -/

/-- A child of a row: its box, and the space an operator asks before and after it
(`lspace`, `rspace`; zero for other children). -/
structure RowItem where
  box : MBox
  lspace : Int := 0
  rspace : Int := 0
  deriving Repr, Inhabited

/-- The inline advance of a row child: its spaces and its box. -/
def RowItem.advance (i : RowItem) : Int := i.lspace + i.box.width + i.rspace

/-- The inline size of a row: a loop over the children. -/
def rowWidth (items : List RowItem) : Int := items.foldl (fun w i => w + i.advance) 0
/-- The ascent of a row: the largest ascent of a child, and at least zero. -/
def rowAscent (items : List RowItem) : Int := items.foldl (fun a i => max a i.box.ascent) 0
/-- The descent of a row: the largest descent of a child, and at least zero. -/
def rowDescent (items : List RowItem) : Int := items.foldl (fun a i => max a i.box.descent) 0
/-- The box of a row of children on one baseline. -/
def rowBox (items : List RowItem) : MBox := ⟨rowWidth items, rowAscent items, rowDescent items⟩

/-- The left edge of each child of a row, in order: a loop. -/
def rowOffsets (items : List RowItem) : Array Int :=
  (items.foldl (fun (acc : Int × Array Int) i => (acc.1 + i.advance, acc.2.push (acc.1 + i.lspace))) (0, #[])).2

private theorem foldl_add (f : RowItem → Int) (l : List RowItem) (a : Int) :
    l.foldl (fun w i => w + f i) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih]; omega

private theorem foldl_max_init (f : RowItem → Int) (l : List RowItem) (a : Int) :
    a ≤ l.foldl (fun a i => max a (f i)) a := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl]; exact Int.le_trans (Int.le_max_left a (f x)) (ih _)

private theorem foldl_max_mem (f : RowItem → Int) (l : List RowItem) (a : Int) (i : RowItem) (h : i ∈ l) :
    f i ≤ l.foldl (fun a i => max a (f i)) a := by
  induction l generalizing a with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.foldl]
    cases h with
    | head => exact Int.le_trans (Int.le_max_right a (f i)) (foldl_max_init f xs _)
    | tail _ h => exact ih _ h

/-- Kind: specification conformance (MathML Core §3.1.3.2).
Says: the inline size of a row is the sum of the advances of its children, where the
advance of a child is its box's inline size plus the operator space before and after it.
Does not say: what the spaces are (the operator dictionary and the `lspace` and `rspace`
attributes decide that), nor anything about stretching. -/
theorem rowWidth_eq_sum (items : List RowItem) :
    (rowBox items).width = (items.map RowItem.advance).sum := by
  simp [rowBox, rowWidth, foldl_add]

/-- Kind: specification conformance (MathML Core §3.1.3.2).
Says: the ascent of a row is at least the ascent of each child, and its descent at least
the descent of each child: no child placed on the row's baseline rises above or falls
below the row's box.
Does not say: that the row is no taller than its tallest child needs (`rowAscent_tight`
says that), nor anything about the inline axis. -/
theorem row_child_fits (items : List RowItem) (i : RowItem) (h : i ∈ items) :
    i.box.ascent ≤ (rowBox items).ascent ∧ i.box.descent ≤ (rowBox items).descent :=
  ⟨foldl_max_mem (fun i => i.box.ascent) items 0 i h, foldl_max_mem (fun i => i.box.descent) items 0 i h⟩

private theorem foldl_max_tight (f : RowItem → Int) (l : List RowItem) (a : Int) :
    l.foldl (fun a i => max a (f i)) a = a ∨ ∃ i ∈ l, l.foldl (fun a i => max a (f i)) a = f i := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    rcases ih (max a (f x)) with h | ⟨i, hi, h⟩
    · rcases Int.le_total a (f x) with hle | hle
      · right; exact ⟨x, List.mem_cons_self, by rw [h]; exact Int.max_eq_right hle⟩
      · left; rw [h]; exact Int.max_eq_left hle
    · right; exact ⟨i, List.mem_cons_of_mem _ hi, h⟩

/-- Kind: specification conformance (MathML Core §3.1.3.2).
Says: the ascent of a row is zero or is the ascent of one of its children: the row is no
taller than its tallest child needs. The same holds for the descent (`rowDescent_tight`).
Does not say: which child, nor anything about the inline axis. -/
theorem rowAscent_tight (items : List RowItem) :
    (rowBox items).ascent = 0 ∨ ∃ i ∈ items, (rowBox items).ascent = i.box.ascent :=
  foldl_max_tight (fun i => i.box.ascent) items 0

/-- Kind: specification conformance (MathML Core §3.1.3.2).
Says: the descent of a row is zero or is the descent of one of its children.
Does not say: which child. -/
theorem rowDescent_tight (items : List RowItem) :
    (rowBox items).descent = 0 ∨ ∃ i ∈ items, (rowBox items).descent = i.box.descent :=
  foldl_max_tight (fun i => i.box.descent) items 0

/-! ### Fractions (§3.3.2.1, with a bar) -/

/-- The font's parameters for a fraction, in layout units: the height of the math axis,
the thickness of the bar, the least shift of each part from the baseline and the least
gap between each part and the bar. -/
structure FracParams where
  axis : Int
  rule : Int
  numShift : Int := 0
  denShift : Int := 0
  numGap : Int := 0
  denGap : Int := 0
  deriving Repr, Inhabited

/-- A laid-out fraction: its box, the places of the numerator and denominator, and the
bar (its top edge and bottom edge, measured down from the baseline). -/
structure Frac where
  box : MBox
  num : At
  den : At
  barTop : Int
  barBottom : Int
  deriving Repr, Inhabited

/-- §3.3.2.1 steps for a fraction with a bar: the numerator is raised so that its bottom
clears the bar by the gap, the denominator lowered likewise; both are centred. The bar is
centred on the math axis; half the thickness is rounded down above the axis, the rest is
below it. -/
def fraction (p : FracParams) (num den : MBox) : Frac :=
  let half := p.rule / 2
  let barTop := -(p.axis + half)
  let barBottom := barTop + p.rule
  -- numerator baseline: at least `numShift` up, and its descent above the bar by the gap
  let up := max p.numShift (num.descent + p.numGap - barTop)
  -- denominator baseline: at least `denShift` down, and its ascent below the bar by the gap
  let down := max p.denShift (den.ascent + p.denGap + barBottom)
  let width := max num.width den.width
  -- the box holds both parts: with gaps of zero or more the numerator is the top and the
  -- denominator the bottom
  { box := ⟨width, max (up + num.ascent) (den.ascent - down), max (down + den.descent) (num.descent - up)⟩
    num := ⟨(width - num.width) / 2, -up⟩
    den := ⟨(width - den.width) / 2, down⟩
    barTop, barBottom }

/-- Kind: specification conformance (MathML Core §3.3.2.1).
Says: the numerator and the denominator each lie
inside the fraction's box, on both axes.
Does not say: anything about the padding, border or margin the element's style adds
around this box, nor that the two are centred to the unit (integer halving rounds). -/
theorem fraction_contains (p : FracParams) (num den : MBox) :
    Inside (fraction p num den).box num (fraction p num den).num ∧
    Inside (fraction p num den).box den (fraction p num den).den := by
  simp only [fraction, Inside]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> omega

/-- Kind: specification conformance (MathML Core §3.3.2.1).
Says: with gaps of zero or more, the bottom of the numerator is not below the top of the
bar and the top of the denominator is not above the bottom of the bar: the bar lies
between them, and they do not overlap it. With a bar of thickness zero or more the bar's
top is not below its bottom.
Does not say: that the baseline lies between the two parts (it does not in general: the
bar sits on the math axis, above the baseline, and a thin gap can leave the top of the
denominator above the baseline). -/
theorem fraction_bar_between (p : FracParams) (num den : MBox) (hng : 0 ≤ p.numGap) (hdg : 0 ≤ p.denGap)
    (hr : 0 ≤ p.rule) :
    (fraction p num den).num.dy + num.descent ≤ (fraction p num den).barTop ∧
    (fraction p num den).barTop ≤ (fraction p num den).barBottom ∧
    (fraction p num den).barBottom ≤ (fraction p num den).den.dy - den.ascent := by
  simp only [fraction]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Kind: specification conformance (MathML Core §3.3.2.1).
Says: with a math axis at or above the baseline, a bar of thickness zero or more and a
numerator gap of zero or more, the whole numerator is above the baseline (its bottom edge
is at or above it).
Does not say: the same of the denominator and below (see `fraction_bar_between`). -/
theorem fraction_num_above_baseline (p : FracParams) (num den : MBox) (ha : 0 ≤ p.axis) (hr : 0 ≤ p.rule)
    (hng : 0 ≤ p.numGap) : (fraction p num den).num.dy + num.descent ≤ 0 := by
  simp only [fraction]
  have : 0 ≤ p.rule / 2 := Int.ediv_nonneg hr (by decide)
  omega

/-! ### Scripts (§3.4.1) -/

/-- The font's parameters for subscripts and superscripts, in layout units. -/
structure ScriptParams where
  subShift : Int := 0
  supShift : Int := 0
  /-- The least gap between the bottom of the superscript and the top of the subscript. -/
  gap : Int := 0
  /-- The space after a script. -/
  after : Int := 0
  deriving Repr, Inhabited

/-- A base with an optional subscript and an optional superscript. -/
structure Scripts where
  box : MBox
  base : At
  sub : At
  sup : At
  deriving Repr, Inhabited

/-- §3.4.1: the scripts follow the base on the inline axis; the subscript's baseline is
lowered by at least `subShift` and the superscript's raised by at least `supShift`, and
when both are present they are moved apart until the gap between them is `gap`. `italic`
is the base's italic correction: the superscript starts that far after the subscript. -/
def scripts (p : ScriptParams) (base : MBox) (sub sup : Option MBox) (italic : Int := 0) : Scripts :=
  let subW := match sub with | some b => b.width + p.after | none => 0
  let supW := match sup with | some b => italic + b.width + p.after | none => 0
  let down := match sub with | some _ => p.subShift | none => 0
  let up := match sup with | some _ => p.supShift | none => 0
  -- both present: the gap between the superscript's bottom and the subscript's top
  let (down, up) := match sub, sup with
    | some s, some t =>
      let have_ := (down - s.ascent) - (t.descent - up)
      if have_ < p.gap then (down + (p.gap - have_), up) else (down, up)
    | _, _ => (down, up)
  let subB := sub.getD {}
  let supB := sup.getD {}
  { box := ⟨base.width + max subW supW,
            max base.ascent (max (supB.ascent + up) (subB.ascent - down)),
            max base.descent (max (subB.descent + down) (supB.descent - up))⟩
    base := ⟨0, 0⟩
    sub := ⟨base.width, down⟩
    sup := ⟨base.width + (match sup with | some _ => italic | none => 0), -up⟩ }

/-- Kind: specification conformance (MathML Core §3.4.1).
Says: with inline sizes, italic correction and space after a script of zero or more, the
base, the subscript and the superscript each lie inside the element's box, on both axes.
Does not say: that the scripts do not overlap the base (the shifts come from the font),
nor anything about the element's own padding, border and margin. -/
theorem scripts_contains (p : ScriptParams) (base : MBox) (sub sup : Option MBox) (italic : Int)
    (hb : 0 ≤ base.width) (hi : 0 ≤ italic) (ha : 0 ≤ p.after)
    (hs : ∀ b, sub = some b → 0 ≤ b.width) (ht : ∀ b, sup = some b → 0 ≤ b.width) :
    Inside (scripts p base sub sup italic).box base (scripts p base sub sup italic).base ∧
    (∀ b, sub = some b → Inside (scripts p base sub sup italic).box b (scripts p base sub sup italic).sub) ∧
    (∀ b, sup = some b → Inside (scripts p base sub sup italic).box b (scripts p base sub sup italic).sup) := by
  cases sub with
  | none =>
    cases sup with
    | none => simp [scripts, Inside]; omega
    | some t =>
      have := ht t rfl
      simp [scripts, Inside]; omega
  | some s =>
    have := hs s rfl
    cases sup with
    | none => simp [scripts, Inside]; omega
    | some t =>
      have := ht t rfl
      simp only [scripts, Inside, Option.getD]
      split <;> simp <;> omega

/-- Kind: specification conformance (MathML Core §3.4.1, the sub/superscript gap).
Says: when both scripts are present, the top of the subscript is below the bottom of the
superscript by at least the gap.
Does not say: that either clears the base. -/
theorem scripts_gap (p : ScriptParams) (base s t : MBox) (italic : Int) :
    p.gap ≤ ((scripts p base (some s) (some t) italic).sub.dy - s.ascent) -
            ((scripts p base (some s) (some t) italic).sup.dy + t.descent) := by
  simp only [scripts]
  split <;> simp <;> omega

/-! ### Under and over scripts (§3.4.2) -/

/-- A base with an optional script under it and an optional script over it. -/
structure UnderOver where
  box : MBox
  base : At
  under : At
  over : At
  deriving Repr, Inhabited

/-- §3.4.2: the three boxes are centred on one another; the under script hangs below the
base's descent by `underGap`, the over script sits above its ascent by `overGap`. -/
def underOver (base : MBox) (under over : Option MBox) (underGap overGap : Int := 0) : UnderOver :=
  let u := under.getD {}
  let o := over.getD {}
  let width := max base.width (max u.width o.width)
  let down := match under with | some b => base.descent + underGap + b.ascent | none => 0
  let up := match over with | some b => base.ascent + overGap + b.descent | none => 0
  { box := ⟨width, max base.ascent (max (o.ascent + up) (u.ascent - down)),
            max base.descent (max (u.descent + down) (o.descent - up))⟩
    base := ⟨(width - base.width) / 2, 0⟩
    under := ⟨(width - u.width) / 2, down⟩
    over := ⟨(width - o.width) / 2, -up⟩ }

/-- Kind: specification conformance (MathML Core §3.4.2).
Says: with inline sizes of zero or more, the base, the under script and the over script
each lie inside the element's box, on both axes.
Does not say: that the scripts clear the base when a gap is negative, nor anything about
accents or about operators with movable limits (those are laid out as scripts). -/
theorem underOver_contains (base : MBox) (under over : Option MBox) (underGap overGap : Int)
    (hb : 0 ≤ base.width) (hu : ∀ b, under = some b → 0 ≤ b.width) (ho : ∀ b, over = some b → 0 ≤ b.width) :
    Inside (underOver base under over underGap overGap).box base (underOver base under over underGap overGap).base ∧
    (∀ b, under = some b → Inside (underOver base under over underGap overGap).box b (underOver base under over underGap overGap).under) ∧
    (∀ b, over = some b → Inside (underOver base under over underGap overGap).box b (underOver base under over underGap overGap).over) := by
  cases under with
  | none =>
    cases over with
    | none => simp [underOver, Inside]; omega
    | some o => have := ho o rfl; simp [underOver, Inside]; omega
  | some u =>
    have := hu u rfl
    cases over with
    | none => simp [underOver, Inside]; omega
    | some o => have := ho o rfl; simp [underOver, Inside]; omega

/-! ### Radicals (§3.3.3) -/

/-- The font's parameters for a radical, in layout units: the inline size of the radical
sign, the thickness of the overbar, the gap between the overbar and the content, and the
extra ascender above the overbar. -/
structure RadicalParams where
  signWidth : Int
  rule : Int
  gap : Int
  extra : Int := 0
  deriving Repr, Inhabited

/-- A radical: the sign, then the content under an overbar. Answers the box and the
place of the content. -/
def radical (p : RadicalParams) (content : MBox) : MBox × At :=
  (⟨p.signWidth + content.width, content.ascent + p.gap + p.rule + p.extra, content.descent⟩, ⟨p.signWidth, 0⟩)

/-- Kind: specification conformance (MathML Core §3.3.3).
Says: with a radical sign, content, overbar, gap and extra ascender of size zero or more,
the content lies inside the radical's box, and the box is wider than the content by the
inline size of the sign.
Does not say: that the sign's glyph is stretched to the content (glyph assembly is not
part of this function), nor where an `mroot` index sits. -/
theorem radical_contains (p : RadicalParams) (content : MBox) (hs : 0 ≤ p.signWidth) (hr : 0 ≤ p.rule)
    (hg : 0 ≤ p.gap) (he : 0 ≤ p.extra) :
    Inside (radical p content).1 content (radical p content).2 ∧
    (radical p content).1.width = content.width + p.signWidth := by
  simp only [radical, Inside]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega

/-! ### Stretching (§3.2.4.3) -/

/-- The size a stretchy operator takes along its stretch axis: `base` is its unstretched
size, `target` the size asked for, `variants` the sizes of the font's larger glyphs for
it in increasing order, `assembly` whether the font has a glyph assembly for it (which
can be made any size from its smallest on). The first variant that reaches the target is
taken; else the assembly, at the target; else the largest variant. Never below `base`. -/
def stretchSize (base target : Int) (variants : List Int) (assembly : Bool) : Int :=
  if target ≤ base then base else
  match variants.find? (fun v => target ≤ v) with
  | some v => max base v
  | none => if assembly then target else max base (variants.foldl max base)

/-- Kind: safety (MathML Core §3.2.4.3).
Says: stretching never makes an operator smaller than its unstretched size, whatever the
font's variants are.
Does not say: that the target is reached (`stretchSize_reaches` says when). -/
theorem stretchSize_ge_base (base target : Int) (variants : List Int) (assembly : Bool) :
    base ≤ stretchSize base target variants assembly := by
  unfold stretchSize
  split
  · exact Int.le_refl _
  · split
    · exact Int.le_max_left _ _
    · split
      · omega
      · exact Int.le_max_left _ _

/-- Kind: specification conformance (MathML Core §3.2.4.3).
Says: when the font has a glyph assembly for the operator, the stretched size is at least
the target.
Does not say: that it is exactly the target (a variant larger than the target may be
taken first), nor that the assembly's parts can be laid out without overlap limits. -/
theorem stretchSize_reaches (base target : Int) (variants : List Int) :
    target ≤ stretchSize base target variants true := by
  unfold stretchSize
  split
  · assumption
  · split
    · rename_i v hv
      have := List.find?_some hv
      simp at this
      omega
    · simp

/-! ### Space and padding (§3.2.5, §3.3.6) -/

/-- `mspace`: a box of the given sizes; a negative size is taken as zero. -/
def space (width height depth : Int) : MBox := ⟨max 0 width, max 0 height, max 0 depth⟩

/-- Kind: safety (MathML Core §3.2.5).
Says: the box of an `mspace` has no negative size.
Does not say: how the attribute text is read into a length. -/
theorem space_nonneg (w h d : Int) : 0 ≤ (space w h d).width ∧ 0 ≤ (space w h d).ascent ∧ 0 ≤ (space w h d).descent := by
  simp only [space]; omega

/-- `mpadded`: the content's box with each size replaced when the attribute gives one
(`none`: keep), and the content moved by `lspace` right and `voffset` up. Negative sizes
are taken as zero. -/
def padded (content : MBox) (width height depth : Option Int) (lspace voffset : Int) : MBox × At :=
  (⟨max 0 (width.getD content.width), max 0 (height.getD content.ascent), max 0 (depth.getD content.descent)⟩,
   ⟨lspace, -voffset⟩)

/-- Kind: specification conformance (MathML Core §3.3.6).
Says: an `mpadded` with no attributes has the box of its content when that box has no
negative size, and leaves the content where it is.
Does not say: anything about an `mpadded` with attributes: there the content may lie
outside the box, as the specification allows. -/
theorem padded_none (c : MBox) (hw : 0 ≤ c.width) (ha : 0 ≤ c.ascent) (hd : 0 ≤ c.descent) :
    padded c none none none 0 0 = (c, ⟨0, 0⟩) := by
  simp [padded, Int.max_eq_right hw, Int.max_eq_right ha, Int.max_eq_right hd]

/-! ### Tests: cases of the WPT feature probes (`mathml/support/feature-detection.js`) -/

-- has_mfrac: two fractions of `mspace` 50px/50px and 60px/60px tall and deep differ by 40px.
#guard (fraction ⟨256, 64, 0, 0, 64, 64⟩ ⟨0, 3840, 3840⟩ ⟨0, 3840, 3840⟩).box.ascent +
       (fraction ⟨256, 64, 0, 0, 64, 64⟩ ⟨0, 3840, 3840⟩ ⟨0, 3840, 3840⟩).box.descent -
       ((fraction ⟨256, 64, 0, 0, 64, 64⟩ ⟨0, 3200, 3200⟩ ⟨0, 3200, 3200⟩).box.ascent +
        (fraction ⟨256, 64, 0, 0, 64, 64⟩ ⟨0, 3200, 3200⟩ ⟨0, 3200, 3200⟩).box.descent) == 40 * 64
-- has_munderover: three 20px spaces stack, so the width is 20px, not 60px.
#guard (underOver ⟨1280, 0, 0⟩ (some ⟨1280, 0, 0⟩) (some ⟨1280, 0, 0⟩)).box.width == 1280
-- has_operator_spacing: lspace and rspace of 20px add 40px to the row.
#guard rowWidth [⟨⟨640, 0, 0⟩, 0, 0⟩, ⟨⟨640, 0, 0⟩, 1280, 1280⟩, ⟨⟨640, 0, 0⟩, 0, 0⟩] == 640 * 3 + 2560
#guard rowOffsets [⟨⟨640, 0, 0⟩, 0, 0⟩, ⟨⟨640, 0, 0⟩, 1280, 1280⟩, ⟨⟨640, 0, 0⟩, 0, 0⟩] == #[0, 1920, 3840]
#guard stretchSize 10 50 [20, 40] false == 40 && stretchSize 10 50 [20, 40] true == 50 &&
       stretchSize 10 30 [20, 40] true == 40 && stretchSize 10 5 [20, 40] true == 10

end L4Factoidal.Rendering.Math
