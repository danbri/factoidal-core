/-
L4Factoidal.WebCodecs.Orient: a frame's orientation applied to its pixels, for drawing a
`VideoFrame` (WebCodecs §9.4: `rotation` is clockwise, in quarter turns, and is applied before
`flip`, a horizontal mirror). Record: docs/designissues/2026-11-14-webgl-webcodecs.md, section 4.

The visible rectangle, as packed 4-byte pixels `w` wide and `h` high, becomes the oriented image
(`outSize`: the sides change places for a quarter or three-quarter turn). Output pixel `(x, y)`
shows source pixel `source q flip w h x y`. The theorems say that every source pixel read is
inside the rectangle (`source_lt`, `byteSrc_lt`), so the copy never reads past the bytes it was
given, and that a half turn and a flip are each their own inverse (`source_half_involutive`,
`source_flip_involutive`).
-/
namespace L4Factoidal.WebCodecs.Orient

/-- The size of the oriented image of a `w × h` rectangle after `q` quarter turns. -/
def outSize (q w h : Nat) : Nat × Nat := if q % 2 = 1 then (h, w) else (w, h)

/-- The source pixel (column, row) that pixel `(x, y)` of the oriented image shows: mirrored
first when `flip` (the flip is applied last, so it is undone first), then turned back. -/
def source (q : Nat) (flip : Bool) (w h x y : Nat) : Nat × Nat :=
  let x := if flip then (outSize q w h).1 - 1 - x else x
  if q % 4 = 0 then (x, y)
  else if q % 4 = 1 then (y, h - 1 - x)
  else if q % 4 = 2 then (w - 1 - x, h - 1 - y)
  else (w - 1 - y, x)

/-- The source byte that byte `i` of the oriented image copies (4 bytes a pixel). -/
def byteSrc (q : Nat) (flip : Bool) (w h i : Nat) : Nat :=
  let ow := (outSize q w h).1
  let p := i / 4
  let s := source q flip w h (p % ow) (p / ow)
  4 * (s.2 * w + s.1) + i % 4

/-- The oriented image: `none` when `px` is not `w × h` pixels of 4 bytes. -/
def orient (q : Nat) (flip : Bool) (w h : Nat) (px : ByteArray) : Option ByteArray :=
  if px.size ≠ 4 * (w * h) then none
  else some ⟨Array.ofFn (n := 4 * (w * h)) fun i => px.get! (byteSrc q flip w h i.val)⟩

/-- Quarter turns from a frame's `rotation` in degrees (0, 90, 180 or 270). -/
def quarters (degrees : Nat) : Nat := degrees / 90 % 4

/-! ## Theorems -/

/-- Bounds. Says: a pixel of the oriented image shows a pixel inside the source rectangle. -/
theorem source_lt (q : Nat) (flip : Bool) (w h x y : Nat)
    (hx : x < (outSize q w h).1) (hy : y < (outSize q w h).2) :
    (source q flip w h x y).1 < w ∧ (source q flip w h x y).2 < h := by
  have hq : q % 4 = 0 ∧ q % 2 = 0 ∨ q % 4 = 1 ∧ q % 2 = 1 ∨ q % 4 = 2 ∧ q % 2 = 0 ∨ q % 4 = 3 ∧ q % 2 = 1 := by omega
  rcases hq with ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ | ⟨h4, h2⟩ <;>
    simp [outSize, h2] at hx hy <;>
    cases flip <;> simp [source, outSize, h4, h2] <;> omega

/-- The oriented image has as many pixels as the source. -/
theorem outSize_mul (q w h : Nat) : (outSize q w h).1 * (outSize q w h).2 = w * h := by
  unfold outSize; split <;> simp [Nat.mul_comm]

theorem row_lt {r c w h : Nat} (hr : r < h) (hc : c < w) : r * w + c < w * h := by
  have : (r + 1) * w ≤ h * w := Nat.mul_le_mul_right w hr
  rw [Nat.succ_mul] at this
  rw [Nat.mul_comm w h]
  omega

/-- Bounds. Says: every byte the oriented image copies is inside the source's `4 × w × h`
bytes, so `orient` reads only bytes it was given. -/
theorem byteSrc_lt (q : Nat) (flip : Bool) (w h i : Nat) (hi : i < 4 * (w * h)) :
    byteSrc q flip w h i < 4 * (w * h) := by
  simp only [byteSrc]
  have hp : i / 4 < w * h := by omega
  have hw : 0 < (outSize q w h).1 := by
    rcases Nat.eq_zero_or_pos (outSize q w h).1 with h0 | h0
    · have := outSize_mul q w h; rw [h0, Nat.zero_mul] at this; omega
    · exact h0
  have hx : i / 4 % (outSize q w h).1 < (outSize q w h).1 := Nat.mod_lt _ hw
  have hy : i / 4 / (outSize q w h).1 < (outSize q w h).2 := by
    rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm, outSize_mul]; exact hp
  have ⟨h1, h2⟩ := source_lt q flip w h _ _ hx hy
  have := row_lt h2 h1
  have : i % 4 < 4 := Nat.mod_lt _ (by decide)
  omega

/-- Round trip. Says: turning a half turn twice shows every pixel where it was. -/
theorem source_half (w h x y : Nat) : source 2 false w h x y = (w - 1 - x, h - 1 - y) := rfl

theorem source_half_involutive (w h x y : Nat) (hx : x < w) (hy : y < h) :
    source 2 false w h (source 2 false w h x y).1 (source 2 false w h x y).2 = (x, y) := by
  simp only [source_half]
  refine Prod.ext ?_ ?_ <;> simp <;> omega

/-- Round trip. Says: mirroring twice shows every pixel where it was. -/
theorem source_mirror (w h x y : Nat) : source 0 true w h x y = (w - 1 - x, y) := rfl

theorem source_flip_involutive (w h x y : Nat) (hx : x < w) :
    source 0 true w h (source 0 true w h x y).1 (source 0 true w h x y).2 = (x, y) := by
  simp only [source_mirror]
  refine Prod.ext ?_ ?_ <;> simp <;> omega

theorem orient_size (q : Nat) (flip : Bool) (w h : Nat) (px b : ByteArray) (e : orient q flip w h px = some b) :
    b.size = px.size := by
  unfold orient at e
  split at e
  · cases e
  · rename_i hs
    cases e
    simp only [ByteArray.size, Array.size_ofFn, ne_eq, Decidable.not_not] at hs ⊢
    omega

/-! ## Tests: the 4 × 2 image of the WPT orientation tests (y y r r / b b g g), one byte a pixel
read as its name. -/

private def img : ByteArray := ⟨#[1,1,1,1, 1,1,1,1, 2,2,2,2, 2,2,2,2, 3,3,3,3, 3,3,3,3, 4,4,4,4, 4,4,4,4]⟩
private def names (q : Nat) (flip : Bool) : List Nat :=
  ((orient q flip 4 2 img).map fun b => (List.range (b.size / 4)).map fun p => (b.get! (4 * p)).toNat).getD []

-- 0: y y r r / b b g g
#guard names 0 false == [1, 1, 2, 2, 3, 3, 4, 4]
-- 90 clockwise, 2 wide and 4 high: b y / b y / g r / g r
#guard names 1 false == [3, 1, 3, 1, 4, 2, 4, 2]
-- 180: g g b b / r r y y
#guard names 2 false == [4, 4, 3, 3, 2, 2, 1, 1]
-- 270: r g / r g / y b / y b
#guard names 3 false == [2, 4, 2, 4, 1, 3, 1, 3]
-- flipped: r r y y / g g b b
#guard names 0 true == [2, 2, 1, 1, 4, 4, 3, 3]
-- 90 then flipped: y b / y b / r g / r g
#guard names 1 true == [1, 3, 1, 3, 2, 4, 2, 4]
#guard (orient 0 false 4 2 (ByteArray.mk #[0])).isNone
#guard quarters 270 == 3 ∧ quarters 0 == 0 ∧ quarters 90 == 1

end L4Factoidal.WebCodecs.Orient
