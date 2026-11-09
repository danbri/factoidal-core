/-
L4Factoidal.PageCanvas.Paint: what a Canvas 2D fill or stroke paints with
(record: docs/designissues/2026-11-08-canvas-2d.md): a colour, a gradient (linear, radial
with two circles, conic) or a pattern, HTML §4.12.5.1.11.

Colours are premultiplied RGBA in 0..1 (`Px`). A gradient is sampled through a table of
`gradientTable` entries made once per draw; a pattern samples its bitmap, nearest or
bilinear (`imageSmoothingEnabled`).
-/
import L4Factoidal.PageCanvas.Color
import L4Factoidal.PageCanvas.Geometry

namespace L4Factoidal.PageCanvas

/-- A premultiplied colour, each part in 0..1. -/
structure Px where
  r : Float
  g : Float
  b : Float
  a : Float
  deriving Repr, Inhabited, BEq

def Px.zero : Px := ⟨0, 0, 0, 0⟩
def Px.scale (p : Px) (k : Float) : Px := ⟨p.r * k, p.g * k, p.b * k, p.a * k⟩
def RGBA.px (c : RGBA) : Px :=
  let a := Color.clamp01 c.a
  ⟨c.r / 255 * a, c.g / 255 * a, c.b / 255 * a, a⟩

/-- A bitmap: `width × height` pixels, four bytes each, premultiplied RGBA, rows from the
top. Every canvas, `ImageBitmap` and pattern source is one. -/
structure Bitmap where
  width : Nat
  height : Nat
  data : ByteArray
  deriving Inhabited

def Bitmap.blank (w h : Nat) : Bitmap := ⟨w, h, ByteArray.mk (Array.replicate (w * h * 4) 0)⟩

/-- The pixel at `(x, y)` (inside), premultiplied, in 0..1. -/
@[inline] def Bitmap.get (b : Bitmap) (x y : Nat) : Px :=
  let i := (y * b.width + x) * 4
  ⟨b.data[i]!.toFloat / 255, b.data[i+1]!.toFloat / 255, b.data[i+2]!.toFloat / 255, b.data[i+3]!.toFloat / 255⟩

/-- Bytes of non-premultiplied RGBA (`ImageData`) as a premultiplied bitmap. -/
def Bitmap.ofStraight (w h : Nat) (rgba : ByteArray) : Bitmap := Id.run do
  let mut out := ByteArray.emptyWithCapacity (w * h * 4)
  for i in [0:w*h] do
    let a := rgba[4*i+3]!.toNat
    let k := fun (v : UInt8) => ((v.toNat * a + 127) / 255).toUInt8
    out := (((out.push (k rgba[4*i]!)).push (k rgba[4*i+1]!)).push (k rgba[4*i+2]!)).push a.toUInt8
  return ⟨w, h, out⟩

/-- A colour stop: offset in 0..1 and colour. -/
structure Stop where
  offset : Float
  color : RGBA
  deriving Repr, Inhabited

inductive GradientKind where
  | linear (x0 y0 x1 y1 : Float)
  | radial (x0 y0 r0 x1 y1 r1 : Float)
  | conic (angle x y : Float)
  deriving Repr, Inhabited

structure Gradient where
  kind : GradientKind
  /-- In the order `addColorStop` added them; equal offsets keep that order (HTML §4.12.5.1.11). -/
  stops : Array Stop := #[]
  deriving Repr, Inhabited

/-- How a pattern repeats. -/
structure Repeat where
  x : Bool := true
  y : Bool := true
  deriving Repr, Inhabited, BEq

structure Pattern where
  image : Bitmap
  repetition : Repeat
  transform : Matrix := {}
  /-- Outside the image, the nearest edge pixel (for `drawImage`, HTML: "the value of
  the pixel is clamped to the source rectangle"), not transparent black. -/
  clampEdge : Bool := false
  deriving Inhabited

/-- A fill or stroke style. A gradient or pattern is named by its object id, so stops
added after it is set are used by later draws, as for the page's object. -/
inductive Style where
  | color (c : RGBA)
  | gradient (id : Nat)
  | pattern (id : Nat)
  deriving Inhabited, BEq

/-- Entries of the table a gradient is sampled through. -/
def gradientTable : Nat := 1024

/-- Stops sorted by offset, keeping the order of equal ones (insertion sort, few stops). -/
def sortStops (stops : Array Stop) : Array Stop :=
  stops.foldl (init := #[]) fun acc s =>
    let i := (acc.findIdx? (fun t => t.offset > s.offset)).getD acc.size
    acc.insertIdx! i s

/-- The colour at `t` of sorted stops, interpolated in premultiplied space (HTML: the
colours are interpolated "in the premultiplied RGBA space"). Before the first stop the
first colour, after the last the last; at an offset with several stops, the last one
after it and the first one before it. -/
def stopColor (stops : Array Stop) (t : Float) : Px := Id.run do
  if stops.isEmpty then return Px.zero
  if t < stops[0]!.offset then return stops[0]!.color.px
  for i in [0:stops.size - 1] do
    let s0 := stops[i]!
    let s1 := stops[i+1]!
    if t < s1.offset then
      let span := s1.offset - s0.offset
      let f := if span <= 0 then 1 else (t - s0.offset) / span
      let p := s0.color.px
      let q := s1.color.px
      return ⟨p.r + (q.r - p.r) * f, p.g + (q.g - p.g) * f, p.b + (q.b - p.b) * f, p.a + (q.a - p.a) * f⟩
  return stops[stops.size - 1]!.color.px

/-- A paint made ready for one draw: user space from device space (`inv`), and the
gradient table or the pattern. -/
inductive Ready where
  | solid (p : Px)
  | linear (inv : Matrix) (x0 y0 dx dy len2 : Float) (table : Array Px)
  | radial (inv : Matrix) (x0 y0 r0 cdx cdy dr a : Float) (table : Array Px)
  | conic (inv : Matrix) (angle x y : Float) (table : Array Px)
  | pattern (inv : Matrix) (p : Pattern) (smooth : Bool)
  | blank
  deriving Inhabited

def tableOf (g : Gradient) : Array Px :=
  let stops := sortStops (g.stops.map fun s => { s with offset := Color.clamp01 s.offset })
  (Array.range gradientTable).map fun i => stopColor stops (nf i / nf (gradientTable - 1))

/-- A pattern made ready under `ctm`. -/
def Ready.ofPattern (p : Pattern) (ctm : Matrix) (smooth : Bool) : Ready :=
    match (ctm.mul p.transform).inverse? with
    | Option.none => .blank
    | some inv => if p.image.width == 0 || p.image.height == 0 then .blank else .pattern inv p smooth

/-- Make a style ready for a draw under the transform `ctm` (device from user space). A
non-invertible transform paints nothing. -/
def Style.ready (s : Style) (gradient : Nat → Option Gradient) (pattern : Nat → Option Pattern)
    (ctm : Matrix) (smooth : Bool) : Ready :=
  match s with
  | .color c => .solid c.px
  | .gradient id =>
    match ctm.inverse?, gradient id with
    | Option.none, _ | _, Option.none => .blank
    | some inv, some g =>
      if g.stops.isEmpty then .solid Px.zero else
      let table := tableOf g
      match g.kind with
      | .linear x0 y0 x1 y1 =>
        let dx := x1 - x0
        let dy := y1 - y0
        let len2 := dx * dx + dy * dy
        -- HTML: a gradient with the same start and end paints nothing.
        if len2 == 0 then .solid Px.zero else .linear inv x0 y0 dx dy len2 table
      | .radial x0 y0 r0 x1 y1 r1 =>
        if x0 == x1 && y0 == y1 && r0 == r1 then .solid Px.zero else
        let cdx := x1 - x0
        let cdy := y1 - y0
        let dr := r1 - r0
        .radial inv x0 y0 r0 cdx cdy dr (cdx * cdx + cdy * cdy - dr * dr) table
      | .conic angle x y => .conic inv angle x y table
  | .pattern id =>
    match pattern id with
    | Option.none => .blank
    | some p => Ready.ofPattern p ctm smooth

@[inline] def lookup (table : Array Px) (t : Float) : Px :=
  let t := if t.isNaN then 0 else max 0 (min 1 t)
  table[(t * nf (gradientTable - 1)).round.toUInt64.toNat]!

/-- HTML §4.12.5.1.11, the radial gradient: the largest ω with r(ω) > 0 for which the
point is on the circle `(x(ω), y(ω), r(ω))`; none gives transparent black. -/
def radialT (x0 y0 r0 cdx cdy dr a px py : Float) : Option Float :=
  let pdx := px - x0
  let pdy := py - y0
  let b := pdx * cdx + pdy * cdy + r0 * dr
  let c := pdx * pdx + pdy * pdy - r0 * r0
  if a.abs < 1e-12 then
    if b == 0 then none else
    let t := c / (2 * b)
    if r0 + t * dr >= 0 then some t else none
  else
    let disc := b * b - a * c
    if disc < 0 then none else
    let sq := Float.sqrt disc
    let t1 := (b + sq) / a
    let t2 := (b - sq) / a
    let (hi, lo) := if t1 >= t2 then (t1, t2) else (t2, t1)
    if r0 + hi * dr >= 0 then some hi else if r0 + lo * dr >= 0 then some lo else none

private def wrap (v : Nat) (n : Nat) (rep : Bool) : Option Nat :=
  if v < n then some v else if rep then some (v % n) else none

/-- The pattern's pixel at integer coordinates, with repetition; outside a direction
that does not repeat, transparent. -/
@[inline] def patternTexel (p : Pattern) (ix iy : Int) : Px :=
  let w := p.image.width
  let h := p.image.height
  if p.clampEdge then
    let cx := if ix < 0 then 0 else min (w - 1) ix.toNat
    let cy := if iy < 0 then 0 else min (h - 1) iy.toNat
    p.image.get cx cy else
  let xi : Option Nat := if ix < 0 then (if p.repetition.x then some ((ix % w).toNat) else none) else wrap ix.toNat w p.repetition.x
  let yi : Option Nat := if iy < 0 then (if p.repetition.y then some ((iy % h).toNat) else none) else wrap iy.toNat h p.repetition.y
  match xi, yi with
  | some x, some y => p.image.get x y
  | _, _ => Px.zero

@[inline] private def floorInt (v : Float) : Int :=
  let f := v.floor
  if f < 0 then -(Int.ofNat (-f).toUInt64.toNat) else Int.ofNat f.toUInt64.toNat

def samplePattern (p : Pattern) (smooth : Bool) (u v : Float) : Px :=
  if !u.isFinite || !v.isFinite then Px.zero else
  if !smooth then patternTexel p (floorInt u) (floorInt v) else
  let fx := u - fHalf
  let fy := v - fHalf
  let x0 := floorInt fx
  let y0 := floorInt fy
  let tx := fx - fx.floor
  let ty := fy - fy.floor
  let a := patternTexel p x0 y0
  let b := patternTexel p (x0 + 1) y0
  let c := patternTexel p x0 (y0 + 1)
  let d := patternTexel p (x0 + 1) (y0 + 1)
  let mix := fun (p q : Float) (t : Float) => p + (q - p) * t
  let top := (⟨mix a.r b.r tx, mix a.g b.g tx, mix a.b b.b tx, mix a.a b.a tx⟩ : Px)
  let bot := (⟨mix c.r d.r tx, mix c.g d.g tx, mix c.b d.b tx, mix c.a d.a tx⟩ : Px)
  ⟨mix top.r bot.r ty, mix top.g bot.g ty, mix top.b bot.b ty, mix top.a bot.a ty⟩

/-- The paint at a point of device space. -/
def Ready.atF (r : Ready) (px py : Float) : Px :=
  match r with
  | .solid p => p
  | .blank => Px.zero
  | .linear inv x0 y0 dx dy len2 table =>
    let (u, v) := inv.apply px py
    lookup table (((u - x0) * dx + (v - y0) * dy) / len2)
  | .radial inv x0 y0 r0 cdx cdy dr a table =>
    let (u, v) := inv.apply px py
    match radialT x0 y0 r0 cdx cdy dr a u v with
    | some t => lookup table t
    | Option.none => Px.zero
  | .conic inv angle cx cy table =>
    let (u, v) := inv.apply px py
    let t := (Float.atan2 (v - cy) (u - cx) - angle) / tau
    lookup table (t - t.floor)
  | .pattern inv p smooth =>
    let (u, v) := inv.apply px py
    samplePattern p smooth u v

/-- The paint at the centre of device pixel `(x, y)`. -/
@[inline] def Ready.at (r : Ready) (x y : Nat) : Px :=
  match r with
  | .solid p => p
  | _ => r.atF (nf x + fHalf) (nf y + fHalf)

end L4Factoidal.PageCanvas
