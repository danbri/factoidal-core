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
        if out.size >= remainingPoints then throw s!"path point/edge count exceeds {maxPathPoints}"
        out := out.push point
        pending := rest
      else
        if depth >= 20 then throw "curve flatness subdivision depth exceeds 20"
        let (first,last) := piece.split
        pending := (first,depth+1)::(last,depth+1)::rest
  if pending.isEmpty then return out.toList
  throw s!"path point/edge count exceeds {maxPathPoints}"

private def pi : Float := 3.141592653589793
private def flattenArc (screen : Transform) (tolerance : Float) (start endPoint : Point)
    (rx0 ry0 rotation : Float) (largeArc sweep : Bool) (remainingPoints : Nat) : Except String (List Point) := do
  if start.x == endPoint.x && start.y == endPoint.y then return []
  let mut rx := rx0.abs
  let mut ry := ry0.abs
  if rx == 0 || ry == 0 then
    if remainingPoints == 0 then throw s!"path point/edge count exceeds {maxPathPoints}"
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
  if pieces > remainingPoints then throw s!"path point/edge count exceeds {maxPathPoints}"
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
def flattenRef (screen : Transform) (contours : List Contour) (tolerance : Float := 0.015625) : Except String (List LinearContour) := do
  if !tolerance.isFinite || tolerance <= 0 then throw "invalid curve flatness threshold"
  if contours.length > 128 then throw "path subpath count exceeds 128"
  let mut result : Array LinearContour := #[]
  let mut count := 0
  for contour in contours do
    match contour with
    | .empty closed => result := result.push ⟨[],closed⟩
    | .path start segments closed =>
      if !finitePoint start then throw "non-finite curve start"
      if segments.length > maxPathPoints then throw s!"path segment count exceeds {maxPathPoints}"
      if count >= maxPathPoints then throw s!"path point/edge count exceeds {maxPathPoints}"
      count := count+1
      let mut points : Array Point := #[start]
      let mut current := start
      for segment in segments do
        let tail ← match segment with
          | .line endPoint =>
            if count >= maxPathPoints then throw s!"path point/edge count exceeds {maxPathPoints}"
            if !finitePoint endPoint then throw "non-finite curve endpoint"
            pure [endPoint]
          | .quadratic control endPoint => flattenBezier screen tolerance (.quadratic current control endPoint) (maxPathPoints-count)
          | .cubic first second endPoint => flattenBezier screen tolerance (.cubic current first second endPoint) (maxPathPoints-count)
          | .arc rx ry rotation largeArc sweep endPoint => flattenArc screen tolerance current endPoint rx ry rotation largeArc sweep (maxPathPoints-count)
        points := points ++ tail.toArray
        count := count+tail.length
        current := match segment with
          | .line p | .quadratic _ p | .cubic _ _ p | .arc _ _ _ _ _ p => p
      result := result.push ⟨points.toList,closed⟩
  return result.toList

/-! ### Flattening with no list or array for each segment (issue 1268)

`flattenRef` makes, for each segment, a list of its points, then an array of it, then
appends that array. `flatten` pushes each point onto the contour array. The checks,
the Float operations and their order are those of `flattenRef`; the count of points of
a curve is the growth of the array. Not proved: differential `#guard`s below compare
the two, point bits and error text, on lines, curves, arcs and the budget errors. -/

/-- `flattenBezier`, pushing its points onto `out`. -/
private def flattenBezierInto (screen : Transform) (tolerance : Float) (curve : Bezier)
    (remainingPoints : Nat) (out : Array Point) : Except String (Array Point) := do
  let mut pending := [(curve,0)]
  let mut out := out
  let mut added := 0
  for _ in [:2*remainingPoints+1] do
    match pending with
    | [] => return out
    | (piece,depth)::rest =>
      if piece.flat screen tolerance then
        let point := piece.endPoint
        if !finitePoint point then throw "non-finite curve subdivision point"
        if added >= remainingPoints then throw s!"path point/edge count exceeds {maxPathPoints}"
        out := out.push point
        added := added+1
        pending := rest
      else
        if depth >= 20 then throw "curve flatness subdivision depth exceeds 20"
        let (first,last) := piece.split
        pending := (first,depth+1)::(last,depth+1)::rest
  if pending.isEmpty then return out
  throw s!"path point/edge count exceeds {maxPathPoints}"

/-- `flattenArc`, pushing its points onto `out`. -/
private def flattenArcInto (screen : Transform) (tolerance : Float) (start endPoint : Point)
    (rx0 ry0 rotation : Float) (largeArc sweep : Bool) (remainingPoints : Nat) (out : Array Point) :
    Except String (Array Point) := do
  if start.x == endPoint.x && start.y == endPoint.y then return out
  let mut rx := rx0.abs
  let mut ry := ry0.abs
  if rx == 0 || ry == 0 then
    if remainingPoints == 0 then throw s!"path point/edge count exceeds {maxPathPoints}"
    return out.push endPoint
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
  if pieces > remainingPoints then throw s!"path point/edge count exceeds {maxPathPoints}"
  let mut out := out
  for index in [:pieces] do
    if index+1 == pieces then out := out.push endPoint
    else
      let theta := firstAngle+sweepAngle*Float.ofNat (index+1)/Float.ofNat pieces
      let point : Point := ⟨center.x+ax*theta.cos+bx*theta.sin,center.y+ay*theta.cos+axisBY*theta.sin⟩
      if !finitePoint point then throw "non-finite arc subdivision point"
      out := out.push point
  return out

/-- Full canonical contour compilation, with one shared output point budget: the
    result of `flattenRef` (differential guards below). -/
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
      if segments.length > maxPathPoints then throw s!"path segment count exceeds {maxPathPoints}"
      if count >= maxPathPoints then throw s!"path point/edge count exceeds {maxPathPoints}"
      count := count+1
      let mut points : Array Point := #[start]
      let mut current := start
      for segment in segments do
        let before := points.size
        points ← match segment with
          | .line endPoint =>
            if count >= maxPathPoints then throw s!"path point/edge count exceeds {maxPathPoints}"
            if !finitePoint endPoint then throw "non-finite curve endpoint"
            pure (points.push endPoint)
          | .quadratic control endPoint =>
            flattenBezierInto screen tolerance (.quadratic current control endPoint) (maxPathPoints-count) points
          | .cubic first second endPoint =>
            flattenBezierInto screen tolerance (.cubic current first second endPoint) (maxPathPoints-count) points
          | .arc rx ry rotation largeArc sweep endPoint =>
            flattenArcInto screen tolerance current endPoint rx ry rotation largeArc sweep (maxPathPoints-count) points
        count := count+(points.size-before)
        current := match segment with
          | .line p | .quadratic _ p | .cubic _ _ p | .arc _ _ _ _ _ p => p
      result := result.push ⟨points.toList,closed⟩
  return result.toList

-- Differential guards, not a proof: `flatten` against `flattenRef`, by point bits and
-- error text.
private def curveBits : Except String (List LinearContour) → Except String (List (List (UInt64 × UInt64) × Bool))
  | .ok cs => .ok (cs.map fun c => (c.points.map fun p => (p.x.toBits,p.y.toBits),c.closed))
  | .error e => .error e
private def sameFlatten (screen : Transform) (cs : List Contour) (tolerance : Float := 0.015625) : Bool :=
  match curveBits (flatten screen cs tolerance), curveBits (flattenRef screen cs tolerance) with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false
private def probeScreens : List Transform :=
  [⟨1,0,0,1,0,0⟩,⟨2,0,0,2,5,7⟩,⟨0.7,0.3,-0.2,1.9,0,0⟩,⟨100,0,0,100,0,0⟩,⟨1.0e-3,0,0,1.0e-3,0,0⟩]
private def p (x y : Float) : Point := ⟨x,y⟩
private def probeContours : List (List Contour) :=
  [[.empty true],
   [.path (p 0 0) [.line (p 10 0),.line (p 10 10),.line (p 0 10)] true],
   [.path (p 0 0) [.quadratic (p 50 80) (p 100 0),.cubic (p 120 40) (p 160 (-40)) (p 200 0),.line (p 0 0)] true,
    .empty false,
    .path (p 5 5) [.quadratic (p 5.5 5.2) (p 6 5),.cubic (p 7 9) (p 3 9) (p 5 5)] false],
   [.path (p 50 10) [.arc 40 40 0 false true (p 50 90),.arc 40 40 0 false true (p 50 10)] true],
   [.path (p 0 0) [.arc 30 10 33 true false (p 20 20),.arc 0 5 0 false false (p 30 20),.arc 5 5 0 false true (p 30 20),
     .arc 1 1 400 true true (p 90 0)] false],
   [.path (p 0 0) [.cubic (p 1.0e6 0) (p 0 1.0e6) (p 1 1)] false],
   [.path (p 0 0) ((List.range 300).map fun i => .quadratic (p (Float.ofNat i*3+1) 40) (p (Float.ofNat i*3+3) 0)) false]]
#guard probeScreens.all fun screen => probeContours.all fun cs => sameFlatten screen cs
#guard probeContours.all fun cs => sameFlatten ⟨1,0,0,1,0,0⟩ cs 0.25 && sameFlatten ⟨1,0,0,1,0,0⟩ cs 1.0e-9
-- The point budget and its error, and a non-finite point.
private def longLines (n : Nat) (y : Float) : List Segment := (List.range n).map fun i => .line (p (Float.ofNat i) y)
#guard sameFlatten ⟨1,0,0,1,0,0⟩ [.path (p 0 0) (longLines 8000 1) false,.path (p 0 0) (longLines 400 2) false]
#guard sameFlatten ⟨1,0,0,1,0,0⟩ [.path (p 0 0) (longLines 8100 1 ++ [.cubic (p 0 900) (p 900 900) (p 900 0)]) false]
#guard sameFlatten ⟨1,0,0,1,0,0⟩ [.path (p 0 0) (longLines 8180 1 ++ [.arc 400 400 0 true true (p 9000 0)]) false]
#guard sameFlatten ⟨1,0,0,1,0,0⟩ [.path (p 0 0) [.line (p (1.0/0.0) 0)] false]
#guard (flatten ⟨1,0,0,1,0,0⟩ [.path (p 0 0) (longLines 8000 1) false,.path (p 0 0) (longLines 400 2) false]).toOption.isNone
#guard (flatten ⟨1,0,0,1,0,0⟩ [.path (p 0 0) (longLines 8100 1 ++ [.cubic (p 0 900) (p 900 900) (p 900 0)]) false]).toOption.isNone
end NativeSVGCurves
