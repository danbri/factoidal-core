/-!
L4Factoidal.Rendering.LogicalAxes — logical and physical coordinates (CSS Writing Modes 4
§6, "Abstract box terminology"), one mapping for every formatting context.

A box's contents are laid out along an inline axis and a block axis. Where those axes lie
on the page is the box's frame: the inline axis is horizontal (`horizontal-tb`) or
vertical (`vertical-rl`, `vertical-lr`); it runs from the right or from the bottom when the
direction is right-to-left (`inlineFlip`); the block axis runs from the right in
`vertical-rl` (`blockFlip`). A layout computes positions in logical coordinates (from the
inline-start and block-start edges of its container) and maps them once to physical ones.

Positions are integers (layout units), so that the mapping and its inverse are exact and
proved inverse to each other.
-/
namespace L4Factoidal.Rendering.Logical

/-- Where the logical axes of a container lie on the page. -/
structure Frame where
  /-- The inline axis is vertical (a vertical writing mode). -/
  vertical : Bool := false
  /-- The inline axis runs from its physical end: right-to-left, or bottom-to-top. -/
  inlineFlip : Bool := false
  /-- The block axis runs from its physical end: from the right (`vertical-rl`). -/
  blockFlip : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The frame of a writing mode and a direction (CSS Writing Modes 4 §2, §3):
`verticalRl` and `verticalLr` select the vertical modes, else `horizontal-tb`. -/
def Frame.of (verticalRl verticalLr rtl : Bool) : Frame :=
  if verticalRl then {vertical := true, inlineFlip := rtl, blockFlip := true}
  else if verticalLr then {vertical := true, inlineFlip := rtl, blockFlip := false}
  else {vertical := false, inlineFlip := rtl, blockFlip := false}

/-- A rectangle in logical coordinates. -/
structure LRect where
  inlineStart : Int
  blockStart : Int
  inlineSize : Int
  blockSize : Int
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A rectangle in physical coordinates. -/
structure PRect where
  x : Int
  y : Int
  width : Int
  height : Int
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The size of the container along the inline axis and along the block axis, from its
physical width and height. -/
def Frame.inlineExtent (f : Frame) (width height : Int) : Int := if f.vertical then height else width
def Frame.blockExtent (f : Frame) (width height : Int) : Int := if f.vertical then width else height

/-- A start along an axis of length `extent`, counted from the other end when `flip`. -/
def flipStart (flip : Bool) (extent start size : Int) : Int := if flip then extent - start - size else start

theorem flipStart_flipStart (flip : Bool) (extent start size : Int) :
    flipStart flip extent (flipStart flip extent start size) size = start := by
  cases flip <;> simp [flipStart] <;> omega

/-- A logical rectangle of a container `width` by `height` as a physical one. -/
def toPhysical (f : Frame) (width height : Int) (r : LRect) : PRect :=
  let i := flipStart f.inlineFlip (f.inlineExtent width height) r.inlineStart r.inlineSize
  let b := flipStart f.blockFlip (f.blockExtent width height) r.blockStart r.blockSize
  if f.vertical then ⟨b, i, r.blockSize, r.inlineSize⟩ else ⟨i, b, r.inlineSize, r.blockSize⟩

/-- A physical rectangle of a container `width` by `height` as a logical one. -/
def toLogical (f : Frame) (width height : Int) (p : PRect) : LRect :=
  let (i, isz, b, bsz) := if f.vertical then (p.y, p.height, p.x, p.width) else (p.x, p.width, p.y, p.height)
  ⟨flipStart f.inlineFlip (f.inlineExtent width height) i isz,
   flipStart f.blockFlip (f.blockExtent width height) b bsz, isz, bsz⟩

/-- Kind: round trip. Says: mapping a logical rectangle to the page and back gives it
again, in every frame. -/
theorem toLogical_toPhysical (f : Frame) (width height : Int) (r : LRect) :
    toLogical f width height (toPhysical f width height r) = r := by
  obtain ⟨v, fi, fb⟩ := f
  obtain ⟨i, b, isz, bsz⟩ := r
  cases v <;> cases fi <;> cases fb <;>
    simp [toLogical, toPhysical, flipStart, Frame.inlineExtent, Frame.blockExtent] <;> omega

/-- Kind: round trip. Says: the converse, a physical rectangle to logical and back. -/
theorem toPhysical_toLogical (f : Frame) (width height : Int) (p : PRect) :
    toPhysical f width height (toLogical f width height p) = p := by
  obtain ⟨v, fi, fb⟩ := f
  obtain ⟨x, y, w, h⟩ := p
  cases v <;> cases fi <;> cases fb <;>
    simp [toLogical, toPhysical, flipStart, Frame.inlineExtent, Frame.blockExtent] <;> omega

/-- Kind: containment. Says: a logical rectangle inside the container (logically) is
inside it physically: the mapping moves nothing out of the container. -/
theorem toPhysical_inside (f : Frame) (width height : Int) (r : LRect)
    (hi : 0 ≤ r.inlineStart ∧ 0 ≤ r.inlineSize ∧ r.inlineStart + r.inlineSize ≤ f.inlineExtent width height)
    (hb : 0 ≤ r.blockStart ∧ 0 ≤ r.blockSize ∧ r.blockStart + r.blockSize ≤ f.blockExtent width height) :
    let p := toPhysical f width height r
    0 ≤ p.x ∧ p.x + p.width ≤ width ∧ 0 ≤ p.y ∧ p.y + p.height ≤ height := by
  obtain ⟨v, fi, fb⟩ := f
  obtain ⟨i, b, isz, bsz⟩ := r
  cases v <;> cases fi <;> cases fb <;>
    simp_all [toPhysical, flipStart, Frame.inlineExtent, Frame.blockExtent] <;> omega

/-- Kind: invariance. Says: the mapping keeps sizes, only exchanging them in a vertical
frame. -/
theorem toPhysical_size (f : Frame) (width height : Int) (r : LRect) :
    let p := toPhysical f width height r
    (if f.vertical then (p.height, p.width) else (p.width, p.height)) = (r.inlineSize, r.blockSize) := by
  obtain ⟨v, fi, fb⟩ := f
  cases v <;> simp [toPhysical]

/-! ### Examples: a 300 by 200 container, an item 20 wide in the inline axis and 40 in the
block axis, 10 from the inline start and 50 from the block start -/

private def r : LRect := ⟨10, 50, 20, 40⟩
#guard toPhysical (Frame.of false false false) 300 200 r == ⟨10, 50, 20, 40⟩
#guard toPhysical (Frame.of false false true) 300 200 r == ⟨270, 50, 20, 40⟩
#guard toPhysical (Frame.of false true false) 300 200 r == ⟨50, 10, 40, 20⟩
#guard toPhysical (Frame.of true false false) 300 200 r == ⟨210, 10, 40, 20⟩
#guard toPhysical (Frame.of false true true) 300 200 r == ⟨50, 170, 40, 20⟩

end L4Factoidal.Rendering.Logical
