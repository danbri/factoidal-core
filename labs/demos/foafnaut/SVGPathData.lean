import Init

namespace NativeSVG
structure Point where
  x : Float
  y : Float
  deriving Repr
end NativeSVG

namespace NativeSVGPath
open NativeSVG
inductive Segment where
  | line (endPoint : Point)
  | quadratic (control endPoint : Point)
  | cubic (firstControl secondControl endPoint : Point)
  | arc (rx ry rotation : Float) (largeArc sweep : Bool) (endPoint : Point)
  deriving Repr
inductive Contour where
  | empty (closed : Bool)
  | path (start : Point) (segments : List Segment) (closed : Bool)
  deriving Repr
structure LinearContour where
  points : List Point
  closed : Bool
  deriving Repr

def ofLinear (c : LinearContour) : Contour :=
  match c.points with
  | [] => .empty c.closed
  | start::rest => .path start (rest.map Segment.line) c.closed
private def lineEndpoints : List Segment → Except String (List Point)
  | [] => pure []
  | .line point::rest => (point::·) <$> lineEndpoints rest
  | _ => throw "nonlinear contour requires checked tessellation"
def toLinear : Contour → Except String LinearContour
  | .empty closed => pure ⟨[],closed⟩
  | .path start segments closed => do pure ⟨start::(← lineEndpoints segments),closed⟩
private theorem lineEndpoints_map (points : List Point) :
    lineEndpoints (points.map Segment.line) = .ok points := by
  induction points with
  | nil => rfl
  | cons point rest ih => simp [lineEndpoints,ih]; rfl
theorem linear_roundtrip (c : LinearContour) : toLinear (ofLinear c) = .ok c := by
  rcases c with ⟨points,closed⟩
  cases points with
  | nil => rfl
  | cons point rest => simp [ofLinear,toLinear,lineEndpoints_map]; rfl

def Contour.closed : Contour → Bool
  | .empty closed | .path _ _ closed => closed

def toLinears : List Contour → Except String (List LinearContour)
  | [] => pure []
  | c::rest => do pure ((← toLinear c)::(← toLinears rest))

#print axioms linear_roundtrip
end NativeSVGPath
