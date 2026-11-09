/-
L4Factoidal.PageCanvas.Stroke: the stroke of a path as polygons (HTML §4.12.5.1.7 "trace
a path"), for Canvas 2D (record: docs/designissues/2026-11-08-canvas-2d.md).

The input is flattened subpaths in user space; the output is polygons whose union under
the nonzero rule is the stroke: one quadrilateral for each segment, one polygon for each
join and cap, each turned to the same orientation (`orient`), so that overlaps never
cancel. Dashes cut the subpaths first (HTML: "dash pattern"). Zero-length segments are
pruned and empty subpaths ignored (HTML), so a subpath of one point draws nothing.
-/
import L4Factoidal.PageCanvas.Geometry

namespace L4Factoidal.PageCanvas

inductive Cap where | butt | round | square
  deriving Repr, Inhabited, BEq
inductive Join where | miter | round | bevel
  deriving Repr, Inhabited, BEq

structure StrokeStyle where
  width : Float := 1
  cap : Cap := .butt
  join : Join := .miter
  miterLimit : Float := 10
  dash : Array Float := #[]
  dashOffset : Float := 0
  deriving Repr, Inhabited

/-- Twice the signed area of a polygon. -/
def area2 (p : FloatArray) : Float := Id.run do
  let n := p.size / 2
  let mut s := 0.0
  for i in [0:n] do
    let j := if i + 1 == n then 0 else i + 1
    s := s + p[2*i]! * p[2*j+1]! - p[2*j]! * p[2*i+1]!
  return s

/-- The polygon with positive area (reversed when its area is negative). -/
def orient (p : FloatArray) : FloatArray := Id.run do
  if area2 p >= 0 then return p
  let n := p.size / 2
  let mut out := FloatArray.emptyWithCapacity p.size
  for k in [0:n] do
    let i := n - 1 - k
    out := (out.push p[2*i]!).push p[2*i+1]!
  return out

def polyOf (pts : List (Float × Float)) : FloatArray :=
  pts.foldl (fun a (x, y) => (a.push x).push y) FloatArray.empty

/-- A circle of `steps` points. -/
def circle (cx cy r : Float) (steps : Nat) : FloatArray := Id.run do
  let mut out := FloatArray.emptyWithCapacity (2 * steps)
  for i in [0:steps] do
    let t := tau * i.toFloat / steps.toFloat
    out := (out.push (cx + r * Float.cos t)).push (cy + r * Float.sin t)
  return out

/-- Points on a circle of radius `r` for an error at most `tol`. -/
def circleSteps (r tol : Float) : Nat :=
  if r <= tol || !r.isFinite then 8 else
  let n := pi / Float.acos (max (-1) (1 - tol / r))
  if !n.isFinite then 8 else min 256 (max 8 n.ceil.toUInt64.toNat)

/-- Points of a polyline without repeats (consecutive equal points). -/
def dedupe (p : FloatArray) : Array (Float × Float) := Id.run do
  let mut out : Array (Float × Float) := #[]
  for i in [0:p.size / 2] do
    let q := (p[2*i]!, p[2*i+1]!)
    if !(q.1.isFinite && q.2.isFinite) then continue
    match out.back? with
    | some (x, y) => if x == q.1 && y == q.2 then continue else out := out.push q
    | none => out := out.push q
  return out

/-- Cut a polyline (`closed` joins the last point to the first) by a dash pattern
starting `offset` into it. Gives the "on" pieces as open polylines. -/
def dashPieces (pts : Array (Float × Float)) (closed : Bool) (dash : Array Float) (offset : Float) :
    Array (Array (Float × Float)) := Id.run do
  let total := dash.foldl (· + ·) 0
  if pts.size < 2 || total <= 0 || !total.isFinite then return #[pts]
  let pts := if closed then pts.push pts[0]! else pts
  -- Where in the pattern the subpath starts.
  let mut phase := offset - total * (offset / total).floor
  let mut k := 0
  while k < dash.size && phase >= dash[k]! do
    phase := phase - dash[k]!
    k := k + 1
  if k >= dash.size then k := 0
  let mut left := dash[k]! - phase    -- what is left of the current dash or gap
  let mut on := k % 2 == 0
  let mut out : Array (Array (Float × Float)) := #[]
  let mut cur : Array (Float × Float) := if on then #[pts[0]!] else #[]
  for i in [0:pts.size - 1] do
    let (ax, ay) := pts[i]!
    let (bx, by_) := pts[i+1]!
    let len := Float.sqrt ((bx - ax) ^ 2 + (by_ - ay) ^ 2)
    let mut at_ := 0.0
    -- Bounded: each step ends a dash or a gap, or the segment.
    for _ in [0:100000] do
      if len - at_ <= left then
        left := left - (len - at_)
        if on then cur := cur.push (bx, by_)
        break
      at_ := at_ + left
      let t := if len > 0 then at_ / len else 0
      let p := (ax + (bx - ax) * t, ay + (by_ - ay) * t)
      if on then
        cur := cur.push p
        out := out.push cur
        cur := #[]
      else cur := #[p]
      on := !on
      k := (k + 1) % dash.size
      left := dash[k]!
  if on && cur.size >= 1 then out := out.push cur
  return out

/-- The stroke of one polyline. `tol` is the error allowed in user units. -/
def strokePolyline (s : StrokeStyle) (pts : Array (Float × Float)) (closed : Bool) (tol : Float) : Array FloatArray := Id.run do
  let hw := s.width / 2
  let mut out : Array FloatArray := #[]
  let n := pts.size
  -- HTML "trace a path": zero-length segments are pruned, and empty subpaths ignored.
  if n < 2 then return out
  let segCount := if closed then n else n - 1
  let dirOf := fun (i : Nat) =>
    let (ax, ay) := pts[i % n]!
    let (bx, by_) := pts[(i + 1) % n]!
    let l := Float.sqrt ((bx - ax) ^ 2 + (by_ - ay) ^ 2)
    ((bx - ax) / l, (by_ - ay) / l)
  for i in [0:segCount] do
    let (ax, ay) := pts[i]!
    let (bx, by_) := pts[(i + 1) % n]!
    let (dx, dy) := dirOf i
    let (nx, ny) := (-dy * hw, dx * hw)
    out := out.push (polyOf [(ax + nx, ay + ny), (bx + nx, by_ + ny), (bx - nx, by_ - ny), (ax - nx, ay - ny)])
  -- Joins at the inner points, and at every point of a closed polyline.
  let joinPoints := if closed then List.range n else (List.range (n - 2)).map (· + 1)
  for v in joinPoints do
    let (px, py) := pts[v]!
    let (d0x, d0y) := dirOf ((v + n - 1) % n)
    let (d1x, d1y) := dirOf v
    let cross := d0x * d1y - d0y * d1x
    let dot := d0x * d1x + d0y * d1y
    if cross.abs < 1e-12 && dot > 0 then continue
    -- The outer side of the turn.
    let o := if cross > 0 then -1.0 else 1.0
    let (n0x, n0y) := (-d0y * o, d0x * o)
    let (n1x, n1y) := (-d1y * o, d1x * o)
    let a := (px + n0x * hw, py + n0y * hw)
    let b := (px + n1x * hw, py + n1y * hw)
    let small := cross.abs < 0.02 && dot > 0
    match s.join with
    | .round =>
      if small then out := out.push (polyOf [(px, py), a, b])
      else out := out.push (circle px py hw (circleSteps hw tol))
    | .bevel => out := out.push (polyOf [(px, py), a, b])
    | .miter =>
      let sx := n0x + n1x
      let sy := n0y + n1y
      let s2 := sx * sx + sy * sy
      -- HTML: the miter length over the line width is 1/sin(θ/2) = 2/|n0+n1|.
      if s2 > 0 && 4 / s2 <= s.miterLimit * s.miterLimit then
        let tip := (px + sx * 2 * hw / s2, py + sy * 2 * hw / s2)
        out := out.push (polyOf [(px, py), a, tip, b])
      else out := out.push (polyOf [(px, py), a, b])
  -- Caps of an open polyline.
  if !closed then
    for (v, back) in [(0, true), (n - 1, false)] do
      let (px, py) := pts[v]!
      let (dx, dy) := if back then dirOf 0 else dirOf (n - 2)
      let (dx, dy) := if back then (-dx, -dy) else (dx, dy)
      let (nx, ny) := (-dy * hw, dx * hw)
      match s.cap with
      | .butt => pure ()
      | .round => out := out.push (circle px py hw (circleSteps hw tol))
      | .square =>
        out := out.push (polyOf [(px + nx, py + ny), (px + nx + dx * hw, py + ny + dy * hw),
          (px - nx + dx * hw, py - ny + dy * hw), (px - nx, py - ny)])
  return out

/-- The stroke of flattened subpaths, as polygons of one orientation. -/
def strokePolys (s : StrokeStyle) (subpaths : Array Poly) (tol : Float) : Array Poly := Id.run do
  if !(s.width > 0) || !s.width.isFinite then return #[]
  let mut out : Array Poly := #[]
  for sp in subpaths do
    let pts := dedupe sp.pts
    -- A closed subpath back at its start: the last point is the first.
    let pts := if sp.closed && pts.size > 1 && pts[0]! == pts[pts.size - 1]! then pts.pop else pts
    let closed := sp.closed && pts.size > 1
    let pieces := if s.dash.isEmpty then #[(pts, closed)]
      else (dashPieces pts closed s.dash s.dashOffset).map (·, false)
    for (piece, c) in pieces do
      for poly in strokePolyline s piece c tol do
        out := out.push ⟨orient poly, true⟩
  return out

end L4Factoidal.PageCanvas
