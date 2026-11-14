/-
L4Factoidal.WebCodecs.Frame: what a `VideoFrame` is made with (WebCodecs §9.4): the rotation, the
visible rectangle and the display size, for a frame made from bytes (`ofBuffer`) and for a frame
made from another frame (`derive`). Record: docs/designissues/2026-11-14-webgl-webcodecs.md,
section 4.

Rotations are read exactly. The page gives a `double`; `parseRotation` takes its sign, mantissa and
exponent (`decodeDouble`) and computes on integers, so 1e300 and `Number.MAX_VALUE` have the
rotation their exact values have.
-/
import L4Factoidal.WebCodecs.Layout

namespace L4Factoidal.WebCodecs

/-- A finite IEEE 754 binary64 value as `m * 2 ^ e` with `m` an integer; `none` for a NaN or an
infinity. `bits` is the value's 64 bits as a number. -/
def decodeDouble (bits : Nat) : Option (Int × Int) :=
  let frac := bits % 4503599627370496
  let e := (bits / 4503599627370496) % 2048
  let neg := (bits / 9223372036854775808) % 2 == 1
  if e == 2047 then none
  else
    let m : Nat := if e == 0 then frac else frac + 4503599627370496
    let ex : Int := if e == 0 then -1074 else (e : Int) - 1075
    some (if neg then -(m : Int) else (m : Int), ex)

/-- `⌊x / 90 + 1/2⌋` for `x = m * 2 ^ e`, on integers: `⌊(2x + 90) / 180⌋` (`/` on `Int` rounds
down for a positive divisor). -/
def rotationQuot (m e : Int) : Int :=
  if 0 ≤ e then (2 * m * 2 ^ e.toNat + 90) / 180
  else (2 * m + 90 * 2 ^ (-e).toNat) / (180 * 2 ^ (-e).toNat)

/-- "Parse Rotation" (§9.4.6): the rotation `m * 2 ^ e` degrees rounded to the nearest multiple of
90, a tie towards positive infinity, then brought into 0, 90, 180 or 270. -/
def parseRotation (m e : Int) : Nat := ((rotationQuot m e % 4) * 90).toNat

/-- "Add Rotations" (§9.4.6): a rotation applied to a frame that has a rotation and may be flipped. -/
def addRotations (base : Nat) (baseFlip : Bool) (r : Nat) : Nat :=
  if baseFlip then (base + (360 - r % 360)) % 360 else (base + r) % 360

/-- `a * num / den` rounded to the nearest integer, a half up. -/
def scaleRound (a num den : Nat) : Nat := (2 * a * num + den) / (2 * den)

/-- What a frame keeps besides its bytes. Display sizes are of the frame as shown (after its
rotation). -/
structure Meta where
  codedWidth : Nat
  codedHeight : Nat
  visible : Rect
  displayWidth : Nat
  displayHeight : Nat
  rotation : Nat
  flip : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The init members both constructors read. -/
structure Init where
  visibleRect : Option Rect := none
  /-- `displayWidth` and `displayHeight`; `some none` when only one of the two was given. -/
  display : Option (Option (Nat × Nat)) := none
  /-- The rotation as (mantissa, exponent); `none` when the page gave none (0). -/
  rotation : Option (Int × Int) := none
  flip : Bool := false
  deriving Repr, Inhabited

def quarter (rotation : Nat) : Bool := rotation == 90 || rotation == 270

/-- The display size an init gives, or the default `(w, h)` turned by the frame's rotation.
`none`: a TypeError (only one of the two given, or a zero). -/
def displayOf (init : Init) (rotation w h : Nat) : Option (Nat × Nat) :=
  match init.display with
  | some none => none
  | some (some (dw, dh)) => if dw == 0 || dh == 0 then none else some (dw, dh)
  | none => if w == 0 || h == 0 then none else some (if quarter rotation then (h, w) else (w, h))

/-- `new VideoFrame(data, init)` (§9.4.2, the second constructor): the frame's values and the plan
that copies the page's bytes (in the layout the page gave) into the frame's resource.
`none`: a TypeError. `dataSize` is the byte length of the page's buffer. -/
def ofBuffer (f : PixelFormat) (cw ch dataSize : Nat) (layout : Option (List PlaneLayout)) (init : Init) :
    Option (Meta × Plan) :=
  if cw == 0 || ch == 0 then none else
  let full : Rect := ⟨0, 0, cw, ch⟩
  let visible := init.visibleRect.getD full
  if !rectOk f.planes cw ch visible then none else
  match copyPlan f cw ch full layout with
  | none => none
  | some plan =>
    if dataSize < plan.allocationSize then none else
    let rotation := match init.rotation with | some (m, e) => parseRotation m e | none => 0
    match displayOf init rotation visible.width visible.height with
    | none => none
    | some (dw, dh) =>
      some ({ codedWidth := cw, codedHeight := ch, visible, displayWidth := dw, displayHeight := dh,
              rotation, flip := init.flip }, plan)

/-- `new VideoFrame(frame, init)` (§9.4.2, the first constructor, for a `VideoFrame` source; "Initialize
Visible Rect, Orientation, and Display Size"): the new frame's values. It shares the source's bytes.
`none`: a TypeError. -/
def derive (f : PixelFormat) (base : Meta) (init : Init) : Option Meta :=
  let visible := init.visibleRect.getD base.visible
  if !rectOk f.planes base.codedWidth base.codedHeight visible then none else
  let r := match init.rotation with | some (m, e) => parseRotation m e | none => 0
  let rotation := addRotations base.rotation base.flip r
  let flip := base.flip != init.flip
  -- The source's display size as scales of its visible size, taken before its rotation.
  let (bw, bh) := if quarter base.rotation then (base.displayHeight, base.displayWidth) else (base.displayWidth, base.displayHeight)
  let w := scaleRound visible.width bw base.visible.width
  let h := scaleRound visible.height bh base.visible.height
  match displayOf init rotation w h with
  | none => none
  | some (dw, dh) =>
    some { base with visible, displayWidth := dw, displayHeight := dh, rotation, flip }

/-! ## Theorems -/

/-- Range. Says: every rotation a frame gets from "Parse Rotation" is 0, 90, 180 or 270, for every
finite double. Does not say: which of the four (`parseRotation_mul90` and the tests). -/
theorem parseRotation_range (m e : Int) :
    parseRotation m e = 0 ∨ parseRotation m e = 90 ∨ parseRotation m e = 180 ∨ parseRotation m e = 270 := by
  unfold parseRotation
  generalize rotationQuot m e = q
  have h0 : 0 ≤ q % 4 := Int.emod_nonneg q (by decide)
  have h1 : q % 4 < 4 := Int.emod_lt_of_pos q (by decide)
  omega

/-- Exactness on the grid. Says: a rotation that is a whole multiple of 90 degrees is kept, modulo a
full turn. -/
theorem parseRotation_mul90 (k : Int) : (parseRotation (90 * k) 0 : Int) = (90 * k) % 360 := by
  have hq : rotationQuot (90 * k) 0 = k := by
    unfold rotationQuot
    simp only [Int.le_refl, if_true, Int.toNat_zero, Int.pow_zero, Int.mul_one]
    omega
  unfold parseRotation
  rw [hq]
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by decide)
  have h1 : k % 4 < 4 := Int.emod_lt_of_pos k (by decide)
  omega

/-- Range. Says: adding rotations that are below a full turn stays below a full turn. -/
theorem addRotations_lt (base : Nat) (flip : Bool) (r : Nat) : addRotations base flip r < 360 := by
  unfold addRotations
  split <;> exact Nat.mod_lt _ (by decide)

/-- Security statement of the buffer constructor. Says: when `ofBuffer` answers, the plan's moves,
turned to copy from the page's buffer into the resource, read only inside the page's `dataSize`
bytes and write only inside the resource's `resourceSize f cw ch` bytes; and the visible rectangle
lies inside the coded size. Does not say: anything about the page glue that performs the moves. -/
theorem ofBuffer_inBounds (f : PixelFormat) (cw ch dataSize : Nat) (layout : Option (List PlaneLayout))
    (init : Init) (mt : Meta) (plan : Plan) (h : ofBuffer f cw ch dataSize layout init = some (mt, plan)) :
    (∀ m ∈ plan.moves.map Move.swap, m.InBounds dataSize (resourceSize f cw ch)) ∧
    mt.visible.x + mt.visible.width ≤ cw ∧ mt.visible.y + mt.visible.height ≤ ch := by
  unfold ofBuffer at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h
    · rename_i hrect
      split at h
      · cases h
      · rename_i plan0 hplan
        split at h
        · cases h
        · rename_i hsize
          split at h
          · cases h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hok := rectOk_spec (by simpa using hrect)
            refine ⟨?_, hok.1, hok.2.1⟩
            intro m hm
            exact (copyPlan_inBounds_swap f cw ch _ layout plan0 hplan m hm).mono (Nat.le_of_not_lt hsize) (Nat.le_refl _)

/-! ## Tests (`webcodecs/videoFrame-rotation.any.js`, `videoFrame-construction.any.js`) -/

private def rot (bits : Nat) : Option Nat := (decodeDouble bits).map fun (m, e) => parseRotation m e
/-- A whole number of degrees, as (mantissa, exponent 0). -/
private def deg (d : Int) : Nat := parseRotation d 0
/-- A number of half degrees. -/
private def halfDeg (d : Int) : Nat := parseRotation d (-1)

#guard [deg (-315), deg (-360), deg (-90), deg (-45), deg (-135), deg (-1), deg 44, deg 45] == [90, 0, 270, 0, 270, 0, 0, 90]
#guard [deg 135, deg 315, deg 359, deg 360, deg 450, deg 720, deg 1125, deg (-1125)] == [180, 0, 0, 0, 90, 0, 90, 0]
#guard [halfDeg 1, halfDeg (-1), halfDeg 2161, halfDeg (-2161)] == [0, 0, 0, 0]
#guard [deg 1000000, deg (-1000000), deg (2 ^ 53), deg (2 ^ 53 + 2)] == [270, 90, 0, 0]
#guard [deg (10 ^ 15), deg (10 ^ 16), deg (10 ^ 17), deg (10 ^ 20)] == [270, 270, 270, 270]
-- Doubles by their bits: 90.0, 89.9, -0.0, 1e300, Number.MAX_VALUE, -Number.MAX_VALUE, Number.MIN_VALUE, NaN, Infinity.
#guard rot 0x4056800000000000 == some 90
#guard rot 0x405679999999999A == some 90
#guard rot 0x8000000000000000 == some 0
#guard rot 0x7E37E43C8800759C == some 0
#guard rot 0x7FEFFFFFFFFFFFFF == some 90
#guard rot 0xFFEFFFFFFFFFFFFF == some 270
#guard rot 1 == some 0
#guard rot 0x7FF8000000000000 == none
#guard rot 0x7FF0000000000000 == none
#guard addRotations 90 false 90 == 180
#guard addRotations 90 true 90 == 0
#guard addRotations 270 false 180 == 90

private def i420 : PixelFormat := .yuv .c420 false .d8
private def frame (cw ch : Nat) (init : Init := {}) : Option Meta := (ofBuffer i420 cw ch (cw * ch * 3 / 2) none init).map (·.1)
private def disp (m : Option Meta) : Option (Nat × Nat) := m.map fun m => (m.displayWidth, m.displayHeight)
-- "A VideoFrame created from data with a rotation of 90": 4 × 2 shows as 2 × 4.
#guard disp ((ofBuffer .rgba 4 2 32 none { rotation := some (90, 0) }).map (·.1)) == some (2, 4)
-- Rotated by 90, then by 90 more: 180, shown as 4 × 2 again.
#guard ((ofBuffer .rgba 4 2 32 none { rotation := some (90, 0) }).bind fun b => derive .rgba b.1 { rotation := some (90, 0) }).map
  (fun m => (m.rotation, m.displayWidth, m.displayHeight)) == some (180, 4, 2)
-- "visibleRect metadata override where source display width = 2 * visible width (anamorphic)".
#guard disp ((frame 4 2 { display := some (some (8, 2)) }).bind fun b => derive i420 b { visibleRect := some ⟨2, 0, 2, 2⟩ }) == some (4, 2)
-- "... with fractional display size scale".
#guard disp ((frame 1440 1080 { display := some (some (1920, 1080)) }).bind fun b => derive i420 b { visibleRect := some ⟨0, 0, 720, 540⟩ }) == some (960, 540)
#guard disp ((frame 640 480 { display := some (some (160, 480)) }).bind fun b => derive i420 b { visibleRect := some ⟨0, 0, 320, 240⟩ }) == some (80, 240)
-- "Test invalid buffer constructed VideoFrames".
#guard (frame 4 0).isNone
#guard (frame 0 4).isNone
#guard (ofBuffer i420 4294967295 4294967295 12 none {}).isNone
#guard (frame 4 2 { visibleRect := some ⟨100, 100, 1, 1⟩ }).isNone
#guard (frame 4 2 { visibleRect := some ⟨0, 0, 0, 2⟩ }).isNone
#guard (frame 4 2 { display := some none }).isNone
#guard (ofBuffer i420 4 2 11 none {}).isNone
#guard (frame 4 2).isSome

end L4Factoidal.WebCodecs
