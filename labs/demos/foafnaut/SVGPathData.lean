import L4Factoidal.Rendering.Path

/- SVG, HTML and font frontends share these exact canonical types. The aliases
   preserve existing public names and constructors without a second path IR. -/
namespace NativeSVG
abbrev Point := L4Factoidal.Rendering.Point
namespace Point
@[match_pattern] abbrev mk := L4Factoidal.Rendering.Point.mk
end Point
end NativeSVG

namespace NativeSVGPath
open NativeSVG
abbrev Segment := L4Factoidal.Rendering.PathSegment
namespace Segment
@[match_pattern] abbrev line := L4Factoidal.Rendering.PathSegment.line
@[match_pattern] abbrev quadratic := L4Factoidal.Rendering.PathSegment.quadratic
@[match_pattern] abbrev cubic := L4Factoidal.Rendering.PathSegment.cubic
@[match_pattern] abbrev arc := L4Factoidal.Rendering.PathSegment.arc
end Segment
abbrev Contour := L4Factoidal.Rendering.Contour
namespace Contour
@[match_pattern] abbrev empty := L4Factoidal.Rendering.Contour.empty
@[match_pattern] abbrev path := L4Factoidal.Rendering.Contour.path
abbrev closed := L4Factoidal.Rendering.Contour.closed
end Contour
abbrev LinearContour := L4Factoidal.Rendering.LinearContour
namespace LinearContour
@[match_pattern] abbrev mk := L4Factoidal.Rendering.LinearContour.mk
end LinearContour
abbrev ofLinear := L4Factoidal.Rendering.Contour.ofLinear
abbrev toLinear := L4Factoidal.Rendering.Contour.toLinear

theorem linear_roundtrip (c : LinearContour) : toLinear (ofLinear c) = .ok c :=
  L4Factoidal.Rendering.Contour.linear_roundtrip c

def toLinears : List Contour → Except String (List LinearContour)
  | [] => pure []
  | c::rest => do pure ((← toLinear c)::(← toLinears rest))

#print axioms linear_roundtrip
end NativeSVGPath
