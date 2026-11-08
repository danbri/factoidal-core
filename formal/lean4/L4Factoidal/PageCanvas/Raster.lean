/-
L4Factoidal.PageCanvas.Raster: coverage and compositing for Canvas 2D
(record: docs/designissues/2026-11-08-canvas-2d.md).

- `coverage`: the fraction of each device pixel inside polygons under a fill rule
  (nonzero or even-odd). Each pixel row is cut at `subRows` sample rows; along a sample
  row the inside intervals are exact, so a pixel's coverage is exact horizontally and
  in steps of `1/subRows` vertically. The work is only in the box of the polygons,
  clamped to the canvas (`Box`, theorem `boxOf_within`).
- `Op`, `composite`: the compositing and blending operators of Compositing and Blending
  Level 1 §9 and §10 on premultiplied colours, as HTML §4.12.5.1.15 asks: the shape is
  drawn onto transparent black with its coverage, composited with the operator, and the
  clip region decides where the result replaces the destination.
-/
import L4Factoidal.PageCanvas.Paint

namespace L4Factoidal.PageCanvas

inductive FillRule where | nonzero | evenodd
  deriving Repr, Inhabited, BEq

structure Edge where
  x0 : Float
  y0 : Float
  x1 : Float
  y1 : Float
  dir : Int
  deriving Inhabited

/-- The edges of polygons, each closed back to its first point; horizontal edges and
non-finite points are left out. -/
def edgesOf (polys : Array Poly) : Array Edge := Id.run do
  let mut out := #[]
  for p in polys do
    let n := p.count
    if n < 2 then continue
    for i in [0:n] do
      let j := if i + 1 == n then 0 else i + 1
      let ax := p.pts[2*i]!
      let ay := p.pts[2*i+1]!
      let bx := p.pts[2*j]!
      let by_ := p.pts[2*j+1]!
      if !(ax.isFinite && ay.isFinite && bx.isFinite && by_.isFinite) then continue
      if ay < by_ then out := out.push ⟨ax, ay, bx, by_, 1⟩
      else if by_ < ay then out := out.push ⟨bx, by_, ax, ay, -1⟩
  return out

/-- A box of device pixels: columns `x .. x+w`, rows `y .. y+h`. -/
structure Box where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Repr, Inhabited, BEq

/-- Clamp a coordinate to `0 .. n`. -/
def clampNat (v : Float) (n : Nat) : Nat :=
  if v.isNaN || v <= 0 then 0 else if v >= n.toFloat then n else v.toUInt64.toNat

/-- The pixels a box of floats touches, inside a canvas of `W × H`. -/
def boxOf (W H : Nat) (minX minY maxX maxY : Float) : Box :=
  let x0 := min (clampNat minX.floor W) W
  let y0 := min (clampNat minY.floor H) H
  let x1 := min (clampNat maxX.ceil W) W
  let y1 := min (clampNat maxY.ceil H) H
  ⟨x0, y0, x1 - x0, y1 - y0⟩

/-- Every box is inside its canvas. -/
theorem boxOf_within (W H : Nat) (a b c d : Float) :
    (boxOf W H a b c d).x + (boxOf W H a b c d).w ≤ W ∧ (boxOf W H a b c d).y + (boxOf W H a b c d).h ≤ H := by
  simp only [boxOf]
  constructor <;> omega

/-- The box of edges, inside the canvas. -/
def edgeBox (W H : Nat) (es : Array Edge) : Box :=
  if es.isEmpty then ⟨0, 0, 0, 0⟩ else
  let init := (es[0]!.x0, es[0]!.y0, es[0]!.x0, es[0]!.y0)
  let (a, b, c, d) := es.foldl (init := init) fun (a, b, c, d) e =>
    (min a (min e.x0 e.x1), min b e.y0, max c (max e.x0 e.x1), max d e.y1)
  boxOf W H a b c d

/-- Sample rows a pixel row is cut at. -/
def subRows : Nat := 16

/-- Coverage of the pixels of `box`, row by row (`box.w × box.h` values in 0..1). -/
structure Coverage where
  box : Box
  cov : FloatArray

/-- Insert a crossing into an array sorted by `x` (few crossings on one row). -/
private def insertSorted (xs : Array (Float × Int)) (x : Float) (d : Int) : Array (Float × Int) := Id.run do
  let mut i := xs.size
  while i > 0 && xs[i-1]!.1 > x do i := i - 1
  return xs.insertIdx! i (x, d)

/-- The coverage values of polygons with edges `es` under `rule`, in `box`. -/
def coverageIn (box : Box) (es : Array Edge) (rule : FillRule) : FloatArray := Id.run do
  if box.w == 0 || box.h == 0 then return FloatArray.empty
  -- Edges by their first row, for an active list.
  let sorted := es.qsort (fun a b => a.y0 < b.y0)
  let mut cov := FloatArray.mk (Array.replicate (box.w * box.h) 0)
  let mut active : Array Edge := #[]
  let mut next := 0
  let bx := box.x.toFloat
  let wgt := 1 / subRows.toFloat
  for j in [0:box.h] do
    let row := (box.y + j).toFloat
    -- Edges that reach this row.
    while next < sorted.size && sorted[next]!.y0 < row + 1 do
      active := active.push sorted[next]!
      next := next + 1
    active := active.filter (·.y1 > row)
    if active.isEmpty then continue
    let mut diff := FloatArray.mk (Array.replicate (box.w + 1) 0)
    let mut direct := FloatArray.mk (Array.replicate (box.w + 1) 0)
    for s in [0:subRows] do
      let ys := row + (s.toFloat + 0.5) * wgt
      let mut xs : Array (Float × Int) := #[]
      for e in active do
        if e.y0 <= ys && ys < e.y1 then
          let x := e.x0 + (ys - e.y0) * (e.x1 - e.x0) / (e.y1 - e.y0)
          xs := insertSorted xs x e.dir
      let mut wind : Int := 0
      let mut start := 0.0
      for (x, d) in xs do
        let before := wind
        wind := wind + d
        let wasIn := if rule == .nonzero then before != 0 else before % 2 != 0
        let isIn := if rule == .nonzero then wind != 0 else wind % 2 != 0
        if !wasIn && isIn then start := x
        else if wasIn && !isIn then
          -- The interval [start, x), relative to the box.
          let xa := max 0 (min box.w.toFloat (start - bx))
          let xb := max 0 (min box.w.toFloat (x - bx))
          if xb > xa then
            let ia := xa.floor.toUInt64.toNat
            let ib := xb.floor.toUInt64.toNat
            if ia == ib then
              direct := direct.set! ia (direct[ia]! + (xb - xa) * wgt)
            else
              direct := direct.set! ia (direct[ia]! + (ia.toFloat + 1 - xa) * wgt)
              diff := diff.set! (ia + 1) (diff[ia+1]! + wgt)
              diff := diff.set! ib (diff[ib]! - wgt)
              if xb > ib.toFloat then direct := direct.set! ib (direct[ib]! + (xb - ib.toFloat) * wgt)
    let mut run := 0.0
    let base := j * box.w
    for i in [0:box.w] do
      run := run + diff[i]!
      let c := run + direct[i]!
      cov := cov.set! (base + i) (if c <= 0 then 0 else if c >= 1 then 1 else c)
  return cov

/-- The coverage of polygons with edges `es` under `rule`, in the canvas `W × H`. -/
def coverage (W H : Nat) (es : Array Edge) (rule : FillRule) : Coverage :=
  let box := edgeBox W H es
  ⟨box, coverageIn box es rule⟩

theorem edgeBox_within (W H : Nat) (es : Array Edge) :
    (edgeBox W H es).x + (edgeBox W H es).w ≤ W ∧ (edgeBox W H es).y + (edgeBox W H es).h ≤ H := by
  unfold edgeBox
  split
  · simp
  · exact boxOf_within ..

/-- A fill visits only pixels of its canvas. -/
theorem coverage_within (W H : Nat) (es : Array Edge) (rule : FillRule) :
    (coverage W H es rule).box.x + (coverage W H es rule).box.w ≤ W ∧
    (coverage W H es rule).box.y + (coverage W H es rule).box.h ≤ H :=
  edgeBox_within W H es

/-- The coverage values of an axis-aligned rectangle (exact) in `box`. -/
def rectCoverageIn (box : Box) (x0 y0 x1 y1 : Float) : FloatArray := Id.run do
  let mut cov := FloatArray.mk (Array.replicate (box.w * box.h) 0)
  for j in [0:box.h] do
    let py := (box.y + j).toFloat
    let cy := max 0 (min (py + 1) y1 - max py y0)
    for i in [0:box.w] do
      let px := (box.x + i).toFloat
      let cx := max 0 (min (px + 1) x1 - max px x0)
      cov := cov.set! (j * box.w + i) (min 1 (cx * cy))
  return cov

/-- The coverage of an axis-aligned rectangle (exact). -/
def rectCoverage (W H : Nat) (x0 y0 x1 y1 : Float) : Coverage :=
  let box := boxOf W H x0 y0 x1 y1
  ⟨box, rectCoverageIn box x0 y0 x1 y1⟩

theorem rectCoverage_within (W H : Nat) (a b c d : Float) :
    (rectCoverage W H a b c d).box.x + (rectCoverage W H a b c d).box.w ≤ W ∧
    (rectCoverage W H a b c d).box.y + (rectCoverage W H a b c d).box.h ≤ H :=
  boxOf_within W H a b c d

/-! ### Compositing -/

/-- `globalCompositeOperation` values (HTML §4.12.5.1.15, Compositing and Blending §9-10). -/
inductive Op where
  | sourceOver | sourceIn | sourceOut | sourceAtop
  | destinationOver | destinationIn | destinationOut | destinationAtop
  | lighter | copy | xor
  | multiply | screen | overlay | darken | lighten | colorDodge | colorBurn
  | hardLight | softLight | difference | exclusion | hue | saturation | color | luminosity
  deriving Repr, Inhabited, BEq, DecidableEq

def Op.names : List (String × Op) := [
  ("source-over", .sourceOver), ("source-in", .sourceIn), ("source-out", .sourceOut), ("source-atop", .sourceAtop),
  ("destination-over", .destinationOver), ("destination-in", .destinationIn), ("destination-out", .destinationOut),
  ("destination-atop", .destinationAtop), ("lighter", .lighter), ("copy", .copy), ("xor", .xor),
  ("multiply", .multiply), ("screen", .screen), ("overlay", .overlay), ("darken", .darken), ("lighten", .lighten),
  ("color-dodge", .colorDodge), ("color-burn", .colorBurn), ("hard-light", .hardLight), ("soft-light", .softLight),
  ("difference", .difference), ("exclusion", .exclusion), ("hue", .hue), ("saturation", .saturation),
  ("color", .color), ("luminosity", .luminosity)]

def Op.ofName? (s : String) : Option Op := (Op.names.find? (·.1 == s)).map (·.2)
def Op.name (o : Op) : String := ((Op.names.find? (·.2 == o)).map (·.1)).getD "source-over"

/-- Operators that change the destination where the source is transparent: they run over
the whole clip region, not only under the shape. -/
def Op.unbounded : Op → Bool
  | .sourceIn | .sourceOut | .destinationIn | .destinationAtop | .copy => true
  | _ => false

/-- Separable blend functions B(Cb, Cs), Compositing and Blending §10.2. -/
def blendChannel (o : Op) (cb cs : Float) : Float :=
  let hard := fun (cb cs : Float) => if cs <= 0.5 then cb * 2 * cs else let s := 2 * cs - 1; cb + s - cb * s
  match o with
  | .multiply => cb * cs
  | .screen => cb + cs - cb * cs
  | .overlay => hard cs cb
  | .darken => min cb cs
  | .lighten => max cb cs
  | .colorDodge => if cb == 0 then 0 else if cs >= 1 then 1 else min 1 (cb / (1 - cs))
  | .colorBurn => if cb >= 1 then 1 else if cs <= 0 then 0 else 1 - min 1 ((1 - cb) / cs)
  | .hardLight => hard cb cs
  | .softLight =>
    if cs <= 0.5 then cb - (1 - 2 * cs) * cb * (1 - cb)
    else
      let d := if cb <= 0.25 then ((16 * cb - 12) * cb + 4) * cb else Float.sqrt cb
      cb + (2 * cs - 1) * (d - cb)
  | .difference => (cb - cs).abs
  | .exclusion => cb + cs - 2 * cb * cs
  | _ => cs

private def lum (r g b : Float) : Float := 0.3 * r + 0.59 * g + 0.11 * b
private def clipColor (r g b : Float) : Float × Float × Float :=
  let l := lum r g b
  let n := min r (min g b)
  let x := max r (max g b)
  let (r, g, b) := if n < 0 then (l + (r - l) * l / (l - n), l + (g - l) * l / (l - n), l + (b - l) * l / (l - n)) else (r, g, b)
  if x > 1 then (l + (r - l) * (1 - l) / (x - l), l + (g - l) * (1 - l) / (x - l), l + (b - l) * (1 - l) / (x - l)) else (r, g, b)
private def setLum (r g b l : Float) : Float × Float × Float :=
  let d := l - lum r g b
  clipColor (r + d) (g + d) (b + d)
private def sat (r g b : Float) : Float := max r (max g b) - min r (min g b)
private def setSat (r g b s : Float) : Float × Float × Float :=
  let mx := max r (max g b)
  let mn := min r (min g b)
  let f := fun (c : Float) => if mx == mn then 0 else if c == mx then s else if c == mn then 0 else (c - mn) * s / (mx - mn)
  if mx == mn then (0, 0, 0) else (f r, f g, f b)

/-- Non-separable blend functions, Compositing and Blending §10.3. -/
def blendNonSep (o : Op) (br bg bb sr sg sb : Float) : Float × Float × Float :=
  match o with
  | .hue => let (r, g, b) := setSat sr sg sb (sat br bg bb); setLum r g b (lum br bg bb)
  | .saturation => let (r, g, b) := setSat br bg bb (sat sr sg sb); setLum r g b (lum br bg bb)
  | .color => setLum sr sg sb (lum br bg bb)
  | .luminosity => setLum br bg bb (lum sr sg sb)
  | _ => (sr, sg, sb)

/-- Source `s` over destination `d` (both premultiplied) with operator `o`. -/
def compose (o : Op) (s d : Px) : Px :=
  let pd := fun (fa fb : Float) => (⟨s.r * fa + d.r * fb, s.g * fa + d.g * fb, s.b * fa + d.b * fb, s.a * fa + d.a * fb⟩ : Px)
  match o with
  | .sourceOver => pd 1 (1 - s.a)
  | .sourceIn => pd d.a 0
  | .sourceOut => pd (1 - d.a) 0
  | .sourceAtop => pd d.a (1 - s.a)
  | .destinationOver => pd (1 - d.a) 1
  | .destinationIn => pd 0 s.a
  | .destinationOut => pd 0 (1 - s.a)
  | .destinationAtop => pd (1 - d.a) s.a
  | .lighter => let p := pd 1 1; ⟨min 1 p.r, min 1 p.g, min 1 p.b, min 1 p.a⟩
  | .copy => s
  | .xor => pd (1 - d.a) (1 - s.a)
  | _ =>
    -- Blending: Cs' = (1 - ab) Cs + ab B(Cb, Cs), then source-over.
    let un := fun (c a : Float) => if a <= 0 then 0 else c / a
    let (cbr, cbg, cbb) := (un d.r d.a, un d.g d.a, un d.b d.a)
    let (csr, csg, csb) := (un s.r s.a, un s.g s.a, un s.b s.a)
    let (br, bg, bb) := match o with
      | .hue | .saturation | .color | .luminosity => blendNonSep o cbr cbg cbb csr csg csb
      | _ => (blendChannel o cbr csr, blendChannel o cbg csg, blendChannel o cbb csb)
    let mix := fun (cs b : Float) => (1 - d.a) * cs + d.a * b
    let sr := mix csr br * s.a
    let sg := mix csg bg * s.a
    let sb := mix csb bb * s.a
    ⟨sr + d.r * (1 - s.a), sg + d.g * (1 - s.a), sb + d.b * (1 - s.a), s.a + d.a * (1 - s.a)⟩

@[inline] def toByte (v : Float) : UInt8 :=
  if v.isNaN || v <= 0 then 0 else if v >= 1 then 255 else (v * 255).round.toUInt8

/-- One pixel: the destination `d`, the source `s` with coverage `c` (already times the
global alpha), the clip mask `m` in 0..1. The result replaces `d` where `m` is 1, and is
mixed with it where `m` is between. -/
@[inline] def blendPixel (o : Op) (s : Px) (c m : Float) (d : Px) : Px :=
  if m <= 0 then d else
  let r := compose o (s.scale c) d
  if m >= 1 then r else
  ⟨d.r + (r.r - d.r) * m, d.g + (r.g - d.g) * m, d.b + (r.b - d.b) * m, d.a + (r.a - d.a) * m⟩

/-- A pixel outside the clip region is the destination, whatever is drawn. -/
theorem blendPixel_outside_clip (o : Op) (s : Px) (c m : Float) (d : Px) (h : m <= 0) :
    blendPixel o s c m d = d := by
  simp [blendPixel, h]

/-- A clip mask: one byte per canvas pixel (255 inside). `none` is no clip. -/
abbrev Mask := Option ByteArray

@[inline] def maskAt (m : Mask) (i : Nat) : Float :=
  match m with
  | none => 1
  | some b => b[i]!.toFloat / 255

/-- What a draw paints: the paint, its coverage and alpha, the operator and the clip. -/
structure Draw where
  ready : Ready
  cov : Coverage
  alpha : Float
  op : Op
  clip : Mask

/-- The pixels a draw visits: its coverage box, or for an unbounded operator the canvas. -/
def Draw.visits (W H : Nat) (dr : Draw) : Box := if dr.op.unbounded then ⟨0, 0, W, H⟩ else dr.cov.box

/-- A draw whose coverage is inside the canvas visits only pixels of the canvas. -/
theorem Draw.visits_within (W H : Nat) (dr : Draw)
    (h : dr.cov.box.x + dr.cov.box.w ≤ W ∧ dr.cov.box.y + dr.cov.box.h ≤ H) :
    (dr.visits W H).x + (dr.visits W H).w ≤ W ∧ (dr.visits W H).y + (dr.visits W H).h ≤ H := by
  unfold Draw.visits; split <;> simp_all

/-- Composite one draw into `bm` (`W × H`). Only the pixels of `Draw.visits` are
visited; the clip mask decides the rest. -/
def composite (W H : Nat) (bm : ByteArray) (dr : Draw) : ByteArray := Id.run do
  let mut out := bm
  let box := dr.cov.box
  let v := dr.visits W H
  let (x0, y0, w, h) := (v.x, v.y, v.w, v.h)
  for j in [0:h] do
    let y := y0 + j
    for i in [0:w] do
      let x := x0 + i
      let idx := y * W + x
      let m := maskAt dr.clip idx
      if m <= 0 then continue
      let c := if x >= box.x && x < box.x + box.w && y >= box.y && y < box.y + box.h then
        dr.cov.cov[(y - box.y) * box.w + (x - box.x)]! else 0
      if c <= 0 && !dr.op.unbounded then continue
      let s := dr.ready.at x y
      let k := idx * 4
      let d : Px := ⟨out[k]!.toFloat / 255, out[k+1]!.toFloat / 255, out[k+2]!.toFloat / 255, out[k+3]!.toFloat / 255⟩
      let r := blendPixel dr.op s (c * dr.alpha) m d
      out := out.set! k (toByte r.r)
      out := out.set! (k+1) (toByte r.g)
      out := out.set! (k+2) (toByte r.b)
      out := out.set! (k+3) (toByte r.a)
  return out

/-- The draw's result, only when it has the size of the bitmap it was given (a final
check: every canvas command keeps its bitmap's size, `Canvas.apply_size`). -/
def sameSize (old new : ByteArray) : ByteArray := if new.size == old.size then new else old

theorem sameSize_size (old new : ByteArray) : (sameSize old new).size = old.size := by
  unfold sameSize; split <;> simp_all

end L4Factoidal.PageCanvas
