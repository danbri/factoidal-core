/-
L4Factoidal.PageCanvas.Geometry: matrices, paths and flattening for Canvas 2D
(record: docs/designissues/2026-11-08-canvas-2d.md).

- `Matrix`: the affine transform `[a c e; b d f]` of HTML §4.12.5.1.8 (DOMMatrix 2D form).
- `Seg`, `Path`: a path as segments (move, line, quadratic, cubic, close). Arcs and
  ellipses become cubic Béziers of at most a quarter turn each (`arcSegs`), so a path is
  closed under affine maps: `Path.map m` is exact.
- `Path.flatten`: polylines within `tolerance` pixels of the curves (Wang's bound).
-/
namespace L4Factoidal.PageCanvas

/-- The affine map `(x, y) ↦ (a x + c y + e, b x + d y + f)`. -/
structure Matrix where
  a : Float := 1
  b : Float := 0
  c : Float := 0
  d : Float := 1
  e : Float := 0
  f : Float := 0
  deriving Repr, Inhabited, BEq

namespace Matrix
def identity : Matrix := {}
@[inline] def apply (m : Matrix) (x y : Float) : Float × Float := (m.a * x + m.c * y + m.e, m.b * x + m.d * y + m.f)
/-- `m.mul n`: first `n`, then `m` (the matrix product m × n). -/
def mul (m n : Matrix) : Matrix :=
  { a := m.a * n.a + m.c * n.b, b := m.b * n.a + m.d * n.b,
    c := m.a * n.c + m.c * n.d, d := m.b * n.c + m.d * n.d,
    e := m.a * n.e + m.c * n.f + m.e, f := m.b * n.e + m.d * n.f + m.f }
def det (m : Matrix) : Float := m.a * m.d - m.b * m.c
def finite (m : Matrix) : Bool := [m.a, m.b, m.c, m.d, m.e, m.f].all Float.isFinite
/-- The inverse, when the determinant is a finite non-zero number. -/
def inverse? (m : Matrix) : Option Matrix :=
  let det := m.det
  if det == 0 || !det.isFinite || !m.finite then none else
  some { a := m.d / det, b := -m.b / det, c := -m.c / det, d := m.a / det,
         e := (m.c * m.f - m.d * m.e) / det, f := (m.b * m.e - m.a * m.f) / det }
def translate (x y : Float) : Matrix := { e := x, f := y }
def scale (x y : Float) : Matrix := { a := x, d := y }
def rotate (t : Float) : Matrix := { a := Float.cos t, b := Float.sin t, c := -Float.sin t, d := Float.cos t }
/-- The largest factor by which the map stretches a length (the spectral norm bound). -/
def stretch (m : Matrix) : Float :=
  let s := m.a * m.a + m.b * m.b + m.c * m.c + m.d * m.d
  let t := Float.sqrt (max 0 ((m.a * m.a + m.b * m.b - m.c * m.c - m.d * m.d) ^ 2 + 4 * (m.a * m.c + m.b * m.d) ^ 2))
  Float.sqrt (max 0 ((s + t) / 2))
end Matrix

inductive Seg where
  | move (x y : Float)
  | line (x y : Float)
  | quad (cx cy x y : Float)
  | cubic (c1x c1y c2x c2y x y : Float)
  | close
  deriving Repr, Inhabited, BEq

def Seg.map (m : Matrix) : Seg → Seg
  | .move x y => let (x, y) := m.apply x y; .move x y
  | .line x y => let (x, y) := m.apply x y; .line x y
  | .quad cx cy x y => let (cx, cy) := m.apply cx cy; let (x, y) := m.apply x y; .quad cx cy x y
  | .cubic ax ay bx by_ x y =>
    let (ax, ay) := m.apply ax ay; let (bx, by_) := m.apply bx by_; let (x, y) := m.apply x y
    .cubic ax ay bx by_ x y
  | .close => .close

/-- A path: its segments, the start of the current subpath and the last point, both in
the path's own space. `subpath` is false before the first `move` (HTML §4.12.5.1.9:
"the path has no subpaths"). -/
structure Path where
  segs : Array Seg := #[]
  startX : Float := 0
  startY : Float := 0
  lastX : Float := 0
  lastY : Float := 0
  subpath : Bool := false
  deriving Repr, Inhabited

namespace Path

def moveTo (p : Path) (x y : Float) : Path :=
  { p with segs := p.segs.push (.move x y), startX := x, startY := y, lastX := x, lastY := y, subpath := true }
/-- HTML: "ensure there is a subpath for (x, y)". -/
def ensure (p : Path) (x y : Float) : Path := if p.subpath then p else p.moveTo x y
def lineTo (p : Path) (x y : Float) : Path :=
  if !p.subpath then p.moveTo x y else
  { p with segs := p.segs.push (.line x y), lastX := x, lastY := y }
def quadTo (p : Path) (cx cy x y : Float) : Path :=
  let p := p.ensure cx cy
  { p with segs := p.segs.push (.quad cx cy x y), lastX := x, lastY := y }
def cubicTo (p : Path) (ax ay bx by_ x y : Float) : Path :=
  let p := p.ensure ax ay
  { p with segs := p.segs.push (.cubic ax ay bx by_ x y), lastX := x, lastY := y }
/-- HTML: close the subpath and start a new one at the same point. -/
def close (p : Path) : Path :=
  if !p.subpath then p else
  { p with segs := (p.segs.push .close).push (.move p.startX p.startY), lastX := p.startX, lastY := p.startY }
/-- Every segment through `m` (exact: affine maps keep Béziers). -/
def map (m : Matrix) (p : Path) : Path :=
  let (sx, sy) := m.apply p.startX p.startY
  let (lx, ly) := m.apply p.lastX p.lastY
  { segs := p.segs.map (Seg.map m), startX := sx, startY := sy, lastX := lx, lastY := ly, subpath := p.subpath }
/-- `addPath`: the segments of `q`, mapped, after those of `p`. -/
def append (p q : Path) : Path :=
  if q.segs.isEmpty then p else
  { segs := p.segs ++ q.segs, startX := q.startX, startY := q.startY, lastX := q.lastX, lastY := q.lastY, subpath := q.subpath }

end Path

def pi : Float := 3.141592653589793
def tau : Float := 6.283185307179586

/-- The cubic Béziers of an elliptical arc in a frame `m` (unit circle → user space),
from angle `a0` sweeping `sweep` radians (sign gives the direction): at most a quarter
turn each, control length `4/3 tan(θ/4)`. Gives the segments after the start point. -/
def arcSegs (m : Matrix) (a0 sweep : Float) : Array Seg := Id.run do
  let n := max 1 ((sweep.abs / (pi / 2) - 1e-9).ceil.toUInt64.toNat)
  let n := min n 64
  let step := sweep / Float.ofNat n
  let k := 4 / 3 * Float.tan (step / 4)
  let mut out := #[]
  let mut t := a0
  for _ in [0:n] do
    let t1 := t + step
    let (c0, s0, c1, s1) := (Float.cos t, Float.sin t, Float.cos t1, Float.sin t1)
    let (ax, ay) := m.apply (c0 - k * s0) (s0 + k * c0)
    let (bx, by_) := m.apply (c1 + k * s1) (s1 - k * c1)
    let (x, y) := m.apply c1 s1
    out := out.push (.cubic ax ay bx by_ x y)
    t := t1
  return out

/-- HTML §4.12.5.1.9 `ellipse()` sweep: from `start` to `end`, clockwise unless
`ccw`; a sweep of at least a full turn is a full turn. -/
def ellipseSweep (start end_ : Float) (ccw : Bool) : Float :=
  if !ccw && end_ - start ≥ tau then tau
  else if ccw && start - end_ ≥ tau then -tau
  else
    let d := end_ - start
    let r := d - tau * (d / tau).floor          -- in [0, τ)
    if ccw then (if r == 0 then 0 else r - tau) else r

/-- A flattened subpath: points `x0 y0 x1 y1 …` and whether it was closed. -/
structure Poly where
  pts : FloatArray
  closed : Bool

def Poly.count (p : Poly) : Nat := p.pts.size / 2

/-- The most line segments one curve becomes. -/
def maxCurveSteps : Nat := 256

private def stepsFor (dd tolerance : Float) : Nat :=
  let n := Float.sqrt (Float.sqrt dd / (8 * tolerance))
  if !n.isFinite then 1 else min maxCurveSteps (max 1 n.ceil.toUInt64.toNat)

/-- Polylines within `tolerance` of the path (in the path's own units). An empty or
one-point subpath keeps its point (a zero-length subpath strokes as caps). -/
def Path.flatten (p : Path) (tolerance : Float := 0.1) : Array Poly := Id.run do
  let mut out : Array Poly := #[]
  let mut cur := FloatArray.empty
  let mut closed := false
  let mut started := false
  let mut x := 0.0
  let mut y := 0.0
  for s in p.segs do
    match s with
    | .move nx ny =>
      if started then out := out.push ⟨cur, closed⟩
      cur := (FloatArray.empty.push nx).push ny
      closed := false; started := true; x := nx; y := ny
    | .line nx ny =>
      cur := (cur.push nx).push ny; x := nx; y := ny
    | .quad cx cy nx ny =>
      let ddx := x - 2 * cx + nx
      let ddy := y - 2 * cy + ny
      let n := stepsFor (4 * (ddx * ddx + ddy * ddy)) tolerance
      for i in [1:n+1] do
        let t := Float.ofNat i / Float.ofNat n
        let u := 1 - t
        cur := (cur.push (u * u * x + 2 * u * t * cx + t * t * nx)).push (u * u * y + 2 * u * t * cy + t * t * ny)
      x := nx; y := ny
    | .cubic ax ay bx by_ nx ny =>
      let d1x := x - 2 * ax + bx
      let d1y := y - 2 * ay + by_
      let d2x := ax - 2 * bx + nx
      let d2y := ay - 2 * by_ + ny
      let dd := 36 * max (d1x * d1x + d1y * d1y) (d2x * d2x + d2y * d2y)
      let n := stepsFor dd tolerance
      for i in [1:n+1] do
        let t := Float.ofNat i / Float.ofNat n
        let u := 1 - t
        let px := u * u * u * x + 3 * u * u * t * ax + 3 * u * t * t * bx + t * t * t * nx
        let py := u * u * u * y + 3 * u * u * t * ay + 3 * u * t * t * by_ + t * t * t * ny
        cur := (cur.push px).push py
      x := nx; y := ny
    | .close => closed := true
  if started then out := out.push ⟨cur, closed⟩
  return out

/-- Each point of each polyline through `m`. -/
def mapPolys (m : Matrix) (ps : Array Poly) : Array Poly :=
  ps.map fun p => Id.run do
    let mut out := FloatArray.emptyWithCapacity p.pts.size
    for i in [0:p.count] do
      let (x, y) := m.apply p.pts[2*i]! p.pts[2*i+1]!
      out := (out.push x).push y
    return ⟨out, p.closed⟩

end L4Factoidal.PageCanvas
