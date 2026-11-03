import SVGPathData
import L4Factoidal.Math.Affine

namespace NativeSVGCurves
open NativeSVG NativeSVGPath
abbrev Transform := L4Factoidal.Math.Affine2 Float
private def midpoint (a b : Point) : Point := ⟨(a.x+b.x)/2,(a.y+b.y)/2⟩
private def finitePoint (p : Point) : Bool := p.x.isFinite && p.y.isFinite
private def pointMagnitude (p : Point) : Float := max p.x.abs p.y.abs
private def delta (p q : Point) : Point := ⟨p.x-q.x,p.y-q.y⟩
private def screenMagnitude (screen : Transform) (p : Point) : Float :=
  max (screen.a*p.x+screen.c*p.y).abs (screen.b*p.x+screen.d*p.y).abs
private def numericPadding (screen : Transform) (points : List Point) : Float :=
  let norm := max (screen.a.abs+screen.c.abs) (screen.b.abs+screen.d.abs)
  let magnitude := points.foldl (fun n p => max n (pointMagnitude p)) 1
  -- A finite-resolution admission policy; no universal IEEE error theorem.
  norm*magnitude*0.00000000000001
private def flatQuadratic (screen : Transform) (a b c : Point) (tolerance : Float) : Bool :=
  let deviation := screenMagnitude screen (delta b (midpoint a c))
  let error := deviation + numericPadding screen [a,b,c]
  error.isFinite && error <= tolerance
private def flatCubic (screen : Transform) (a b c d : Point) (tolerance : Float) : Bool :=
  let firstLine : Point := ⟨(2*a.x+d.x)/3,(2*a.y+d.y)/3⟩
  let secondLine : Point := ⟨(a.x+2*d.x)/3,(a.y+2*d.y)/3⟩
  let deviation := max (screenMagnitude screen (delta b firstLine))
    (screenMagnitude screen (delta c secondLine))
  let error := deviation+numericPadding screen [a,b,c,d]
  error.isFinite && error <= tolerance

private inductive Bezier where
  | quadratic (a b c : Point)
  | cubic (a b c d : Point)
private def Bezier.endPoint : Bezier → Point
  | .quadratic _ _ c => c
  | .cubic _ _ _ d => d
private def Bezier.flat (screen : Transform) (tolerance : Float) : Bezier → Bool
  | .quadratic a b c => flatQuadratic screen a b c tolerance
  | .cubic a b c d => flatCubic screen a b c d tolerance
private def Bezier.split : Bezier → Bezier × Bezier
  | .quadratic a b c =>
    let ab := midpoint a b; let bc := midpoint b c; let mid := midpoint ab bc
    (.quadratic a ab mid,.quadratic mid bc c)
  | .cubic a b c d =>
    let ab := midpoint a b; let bc := midpoint b c; let cd := midpoint c d
    let abc := midpoint ab bc; let bcd := midpoint bc cd; let mid := midpoint abc bcd
    (.cubic a ab abc mid,.cubic mid bcd cd d)

/-- Depth-first de Casteljau subdivision preserves the final endpoint exactly.
    The admission threshold is expressed after the complete screen linear CTM.
    Failure never substitutes a chord for a non-flat curve. -/
private def flattenBezier (screen : Transform) (tolerance : Float) (curve : Bezier)
    (remainingPoints : Nat) : Except String (List Point) := do
  let mut pending := [(curve,0)]
  let mut out : Array Point := #[]
  for _ in [:2*remainingPoints+1] do
    match pending with
    | [] => return out.toList
    | (piece,depth)::rest =>
      if piece.flat screen tolerance then
        let point := piece.endPoint
        if !finitePoint point then throw "non-finite curve subdivision point"
        if out.size >= remainingPoints then throw "path point/edge count exceeds 512"
        out := out.push point
        pending := rest
      else
        if depth >= 20 then throw "curve flatness subdivision depth exceeds 20"
        let (first,last) := piece.split
        pending := (first,depth+1)::(last,depth+1)::rest
  if pending.isEmpty then return out.toList
  throw "path point/edge count exceeds 512"

private def pi : Float := 3.141592653589793
private def flattenArc (screen : Transform) (tolerance : Float) (start endPoint : Point)
    (rx0 ry0 rotation : Float) (largeArc sweep : Bool) (remainingPoints : Nat) : Except String (List Point) := do
  if start.x == endPoint.x && start.y == endPoint.y then return []
  let mut rx := rx0.abs
  let mut ry := ry0.abs
  if rx == 0 || ry == 0 then
    if remainingPoints == 0 then throw "path point/edge count exceeds 512"
    return [endPoint]
  let angle := (rotation-(rotation/360).floor*360)*pi/180
  let cos := angle.cos; let sin := angle.sin
  let dx := (start.x-endPoint.x)/2; let dy := (start.y-endPoint.y)/2
  let x := cos*dx+sin*dy; let y := -sin*dx+cos*dy
  let scale := x*x/(rx*rx)+y*y/(ry*ry)
  if !scale.isFinite then throw "arc radii correction exceeds finite numeric range"
  if scale > 1 then
    let factor := scale.sqrt
    rx := rx*factor
    ry := ry*factor
  let numerator := max 0 (rx*rx*ry*ry-rx*rx*y*y-ry*ry*x*x)
  let denominator := rx*rx*y*y+ry*ry*x*x
  if denominator <= 0 || !denominator.isFinite then throw "arc center denominator exceeds numeric resolution"
  let factor := (if largeArc == sweep then -1 else 1) * (numerator/denominator).sqrt
  let cx := factor*rx*y/ry
  let cy := -factor*ry*x/rx
  let center : Point := ⟨cos*cx-sin*cy+(start.x+endPoint.x)/2,
    sin*cx+cos*cy+(start.y+endPoint.y)/2⟩
  let ux := (x-cx)/rx; let uy := (y-cy)/ry
  let vx := (-x-cx)/rx; let vy := (-y-cy)/ry
  let firstAngle := Float.atan2 uy ux
  let mut sweepAngle := Float.atan2 (ux*vy-uy*vx) (ux*vx+uy*vy)
  if !sweep && sweepAngle > 0 then sweepAngle := sweepAngle-2*pi
  if sweep && sweepAngle < 0 then sweepAngle := sweepAngle+2*pi
  let ax := cos*rx; let ay := sin*rx
  let bx := -sin*ry; let axisBY := cos*ry
  let radiusBound := max ((screen.a*ax+screen.c*ay).abs+(screen.a*bx+screen.c*axisBY).abs)
    ((screen.b*ax+screen.d*ay).abs+(screen.b*bx+screen.d*axisBY).abs)
  let padding := numericPadding screen [start,endPoint,center,⟨rx,ry⟩]
  if !radiusBound.isFinite || !padding.isFinite || !firstAngle.isFinite || !sweepAngle.isFinite then
    throw "arc screen metric exceeds finite numeric range"
  let mut pieces := 1
  let mut admitted := false
  for _ in [:21] do
    if !admitted then
      let step := sweepAngle/Float.ofNat pieces
      if radiusBound*step*step/8+padding <= tolerance then admitted := true
      else pieces := pieces*2
  if !admitted then throw "arc flatness subdivision depth exceeds 20"
  if pieces > remainingPoints then throw "path point/edge count exceeds 512"
  let mut out : Array Point := #[]
  for index in [:pieces] do
    if index+1 == pieces then out := out.push endPoint
    else
      let theta := firstAngle+sweepAngle*Float.ofNat (index+1)/Float.ofNat pieces
      let point : Point := ⟨center.x+ax*theta.cos+bx*theta.sin,center.y+ay*theta.cos+axisBY*theta.sin⟩
      if !finitePoint point then throw "non-finite arc subdivision point"
      out := out.push point
  return out.toList

/-- Full canonical contour compilation, with one shared output point budget.
    This flatness/budget witness is distinct from a theorem on ideal real curves
    or GPU Float32 rounding. -/
def flatten (screen : Transform) (contours : List Contour) (tolerance : Float := 0.015625) : Except String (List LinearContour) := do
  if !tolerance.isFinite || tolerance <= 0 then throw "invalid curve flatness threshold"
  if contours.length > 128 then throw "path subpath count exceeds 128"
  let mut result : Array LinearContour := #[]
  let mut count := 0
  for contour in contours do
    match contour with
    | .empty closed => result := result.push ⟨[],closed⟩
    | .path start segments closed =>
      if !finitePoint start then throw "non-finite curve start"
      if segments.length > 512 then throw "path segment count exceeds 512"
      if count >= 512 then throw "path point/edge count exceeds 512"
      count := count+1
      let mut points : Array Point := #[start]
      let mut current := start
      for segment in segments do
        let tail ← match segment with
          | .line endPoint =>
            if count >= 512 then throw "path point/edge count exceeds 512"
            if !finitePoint endPoint then throw "non-finite curve endpoint"
            pure [endPoint]
          | .quadratic control endPoint => flattenBezier screen tolerance (.quadratic current control endPoint) (512-count)
          | .cubic first second endPoint => flattenBezier screen tolerance (.cubic current first second endPoint) (512-count)
          | .arc rx ry rotation largeArc sweep endPoint => flattenArc screen tolerance current endPoint rx ry rotation largeArc sweep (512-count)
        points := points ++ tail.toArray
        count := count+tail.length
        current := match segment with
          | .line p | .quadratic _ p | .cubic _ _ p | .arc _ _ _ _ _ p => p
      result := result.push ⟨points.toList,closed⟩
  return result.toList
end NativeSVGCurves
