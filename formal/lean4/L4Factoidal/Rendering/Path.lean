import Init

/-! The sole canonical retained path data shared by HTML, SVG and fonts.
Canonical curves retain every Float parameter. LinearContour is a distinct
checked-backend representation, never an implicit chord fallback. -/
namespace L4Factoidal.Rendering
structure Point where
  x : Float
  y : Float
  deriving Repr
inductive PathSegment where
  | line (endPoint : Point)
  | quadratic (control endPoint : Point)
  | cubic (firstControl secondControl endPoint : Point)
  | arc (rx ry rotation : Float) (largeArc sweep : Bool) (endPoint : Point)
  deriving Repr
inductive Contour where
  | empty (closed : Bool)
  | path (start : Point) (segments : List PathSegment) (closed : Bool)
  deriving Repr
structure LinearContour where
  points : List Point
  closed : Bool
  deriving Repr

def Contour.closed : Contour → Bool
  | .empty closed | .path _ _ closed => closed

def Contour.ofLinear (contour : LinearContour) : Contour :=
  match contour.points with
  | [] => .empty contour.closed
  | start::rest => .path start (rest.map PathSegment.line) contour.closed
private def lineEndpointsRev : List PathSegment → List Point → Except String (List Point)
  | [], acc => .ok acc.reverse
  | .line point::rest, acc => lineEndpointsRev rest (point::acc)
  | _::_, _ => .error "nonlinear contour requires checked tessellation"

private def lineEndpoints (segments : List PathSegment) : Except String (List Point) :=
  lineEndpointsRev segments []

def Contour.toLinear : Contour → Except String LinearContour
  | .empty closed => pure ⟨[],closed⟩
  | .path start segments closed => do pure ⟨start::(← lineEndpoints segments),closed⟩

private theorem lineEndpointsRev_map (points acc : List Point) :
    lineEndpointsRev (points.map PathSegment.line) acc = .ok (acc.reverse ++ points) := by
  induction points generalizing acc with
  | nil => simp [lineEndpointsRev]
  | cons point rest ih =>
    simp [lineEndpointsRev, ih, List.reverse_cons, List.append_assoc]

private theorem lineEndpoints_map (points : List Point) :
    lineEndpoints (points.map PathSegment.line) = .ok points := by
  simpa [lineEndpoints] using lineEndpointsRev_map points []
/-- Every legacy linear contour survives, including empty+closed values. -/
theorem Contour.linear_roundtrip (contour : LinearContour) :
    (Contour.ofLinear contour).toLinear = .ok contour := by
  rcases contour with ⟨points,closed⟩
  cases points with
  | nil => rfl
  | cons point rest => simp [Contour.ofLinear,Contour.toLinear,lineEndpoints_map]; rfl
#print axioms Contour.linear_roundtrip
end L4Factoidal.Rendering
