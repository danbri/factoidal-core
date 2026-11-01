import SVGPath
import SVGDash
namespace NativeSVGStroke
open NativeSVG NativeSVGPath
inductive Piece where
  | strip (first last : Point)
  | disk (center : Point) (radius : Float)
  | triangle (a b c : Point)
  deriving Repr
private def delta (a b : Point) : Point := ⟨b.x-a.x,b.y-a.y⟩
private def cross (a b : Point) := a.x*b.y-a.y*b.x
private def magnitude (a : Point) := Float.sqrt (a.x*a.x+a.y*a.y)
private def interpolate (a b : Point) (t : Float) : Point := ⟨a.x+(b.x-a.x)*t,a.y+(b.y-a.y)*t⟩
/-- Stroke edges close only explicit closed contours; fill edges are separate.
    Zero edges do not provide a direction for joins. Their point survives for caps. -/
def edges (c : Contour) : List (Point × Point) :=
  let pairs := c.points.zip (c.points.drop 1 ++ if c.closed then c.points.take 1 else [])
  pairs.filter (fun (a,b) => a.x != b.x || a.y != b.y)
def length (c : Contour) : Float := (edges c).foldl (fun n (a,b) => n+magnitude (delta a b)) 0

/-- Default miter join, with required bevel fallback beyond the limit. -/
def join (a vertex b : Point) (half limit : Float) : List Piece := Id.run do
  let u0 := delta a vertex
  let v0 := delta vertex b
  let ul := magnitude u0
  let vl := magnitude v0
  if ul==0 || vl==0 then return []
  let u := Point.mk (u0.x/ul) (u0.y/ul)
  let v := Point.mk (v0.x/vl) (v0.y/vl)
  let turn := cross u v
  if turn==0 then return []
  let side : Float := if turn > 0 then 1 else -1
  let p := Point.mk (vertex.x+side*u.y*half) (vertex.y-side*u.x*half)
  let q := Point.mk (vertex.x+side*v.y*half) (vertex.y-side*v.x*half)
  let t := cross (delta p q) v / turn
  let tip := Point.mk (p.x+t*u.x) (p.y+t*u.y)
  if !tip.x.isFinite || !tip.y.isFinite || magnitude (delta vertex tip) > limit*half then
    return [.triangle vertex p q]
  return [.triangle vertex p tip,.triangle vertex tip q]

/-- All pieces remain one stroke region. Dash phase restarts per contour;
    callers calibrate author distances using total element length first. -/
def retain (contours : List Contour) (pattern : List Float) (offset width : Float)
    (roundCaps : Bool) (miterLimit : Float := 4) : Except String (List Piece) := do
  if !width.isFinite || width < 0 || !miterLimit.isFinite || miterLimit < 1 then throw "invalid stroke dimensions"
  if width==0 then return []
  if contours.length > 128 || (contours.foldl (fun n c => n+c.points.length) 0) > 512 then throw "stroke contour/point count exceeds profile bound"
  let half := width/2
  let mut pieces : Array Piece := #[]
  for contour in contours do
    let segments := edges contour
    let sizes := segments.map (fun (a,b) => magnitude (delta a b))
    let total : Float := sizes.foldl (·+·) 0
    let spans ← NativeSVGDash.intervals pattern offset total
    let seam := contour.closed && total > 0 && spans.any (fun a => a.first==0 && a.last>0) && spans.any (fun a => a.last==total && a.first<total)
    let pointAt := fun (distance : Float) => Id.run do
      let mut left := distance
      for ((a,b),size) in segments.zip sizes do
        if left <= size then return interpolate a b (left/size)
        left := left-size
      return contour.points.headD ⟨0,0⟩
    for span in spans do
      let mut start : Float := 0
      for ((a,b),size) in segments.zip sizes do
        let lo := max start span.first
        let hi := min (start+size) span.last
        if hi > lo then pieces := pieces.push (.strip (interpolate a b ((lo-start)/size)) (interpolate a b ((hi-start)/size)))
        start := start+size
      if roundCaps && !contour.points.isEmpty then
        for endpoint in [span.first,span.last] do
          if !(seam && (endpoint==0 || endpoint==total)) then pieces := pieces.push (.disk (pointAt endpoint) half)
      if pieces.size > 4096 then throw "stroke union exceeds 4096 pieces"
    let mut distance : Float := 0
    let incoming := if contour.closed then segments else segments.dropLast
    let outgoing := segments.drop 1 ++ if contour.closed then segments.take 1 else []
    for (((a,vertex),(_,b)),size) in (incoming.zip outgoing).zip sizes do
      distance := distance+size
      if (contour.closed && distance==total && seam) || spans.any (fun s => s.first < distance && s.last > distance) then
        pieces := pieces ++ (join a vertex b half miterLimit).toArray
    if pieces.size > 4096 then throw "stroke union exceeds 4096 pieces"
  return pieces.toList
end NativeSVGStroke
