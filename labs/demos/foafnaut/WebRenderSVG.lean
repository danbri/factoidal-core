import SVG
import L4Factoidal.Rendering.Scene

/-! Lossless adapters between SVG semantic values and the shared scene algebra.
No SVG serialization or parser is used to lower HTML paint. -/
namespace WebRenderSVG
open L4Factoidal

def fromPoint (p : NativeSVG.Point) : Rendering.Point := ⟨p.x,p.y⟩
def toPoint (p : Rendering.Point) : NativeSVG.Point := ⟨p.x,p.y⟩
def fromColor (p : NativeGraphics.FloatRGB) : Rendering.Color := ⟨p.r,p.g,p.b⟩
def toColor (p : Rendering.Color) : NativeGraphics.FloatRGB := ⟨p.r,p.g,p.b⟩
def fromContour (p : NativeSVGPath.Contour) : Rendering.Contour := ⟨p.points.map fromPoint,p.closed⟩
def toContour (p : Rendering.Contour) : NativeSVGPath.Contour := ⟨p.points.map toPoint,p.closed⟩
def fromGeometry : NativeSVG.Geometry → Rendering.Geometry
  | .rect x y w h => .rect x y w h
  | .circle x y r => .circle x y r
  | .ellipse x y rx ry => .ellipse x y rx ry
  | .line a b c d => .line a b c d
  | .polygon points => .polygon (points.map fromPoint)
  | .path contours => .path (contours.map fromContour)
def toGeometry : Rendering.Geometry → NativeSVG.Geometry
  | .rect x y w h => .rect x y w h
  | .circle x y r => .circle x y r
  | .ellipse x y rx ry => .ellipse x y rx ry
  | .line a b c d => .line a b c d
  | .polygon points => .polygon (points.map toPoint)
  | .path contours => .path (contours.map toContour)
def fromPaint : NativeSVG.Paint → Rendering.Paint
  | .none => .none | .current => .current | .solid c => .solid (fromColor c)
def toPaint : Rendering.Paint → NativeSVG.Paint
  | .none => .none | .current => .current | .solid c => .solid (toColor c)
def fromLength (v : NativeSVGDash.Length) : Rendering.Length := ⟨v.value,v.percentage⟩
def toLength (v : Rendering.Length) : NativeSVGDash.Length := ⟨v.value,v.percentage⟩
def fromPiece : NativeSVGStroke.Piece → Rendering.StrokePiece
  | .strip a b => .strip (fromPoint a) (fromPoint b)
  | .disk a r => .disk (fromPoint a) r
  | .triangle a b c => .triangle (fromPoint a) (fromPoint b) (fromPoint c)
def toPiece : Rendering.StrokePiece → NativeSVGStroke.Piece
  | .strip a b => .strip (toPoint a) (toPoint b)
  | .disk a r => .disk (toPoint a) r
  | .triangle a b c => .triangle (toPoint a) (toPoint b) (toPoint c)
def fromStyle (s : NativeSVG.Style) : Rendering.Style :=
  {fill := fromPaint s.fill,stroke := fromPaint s.stroke,currentColor := fromColor s.currentColor,
   strokeWidth := s.strokeWidth,dashArray := s.dashArray.map fromLength,dashOffset := fromLength s.dashOffset,
   fillOpacity := s.fillOpacity,strokeOpacity := s.strokeOpacity,visible := s.visible,
   rule := match s.rule with | .nonzero => .nonzero | .evenodd => .evenodd,
   lineCap := match s.lineCap with | .butt => .butt | .round => .round}
def toStyle (s : Rendering.Style) : NativeSVG.Style :=
  {fill := toPaint s.fill,stroke := toPaint s.stroke,currentColor := toColor s.currentColor,
   strokeWidth := s.strokeWidth,dashArray := s.dashArray.map toLength,dashOffset := toLength s.dashOffset,
   fillOpacity := s.fillOpacity,strokeOpacity := s.strokeOpacity,visible := s.visible,
   rule := match s.rule with | .nonzero => .nonzero | .evenodd => .evenodd,
   lineCap := match s.lineCap with | .butt => .butt | .round => .round}
def fromPrimitive (p : NativeSVG.Primitive) : Rendering.Primitive :=
  ⟨fromGeometry p.geometry,fromStyle p.style,p.opacity,p.transform,p.dashParts.map (·.map fromPiece),p.groupPath⟩
def toPrimitive (p : Rendering.Primitive) : NativeSVG.Primitive :=
  ⟨toGeometry p.geometry,toStyle p.style,p.opacity,p.transform,p.dashParts.map (·.map toPiece),p.groupPath⟩

def fromNode : NativeSVG.DisplayNode → Rendering.Node
  | .paint p => .paint ⟨none,fromPrimitive p⟩
  | .group id t children => .group id t (children.map fromNode)
termination_by n => sizeOf n

def toNode : Rendering.Node → NativeSVG.DisplayNode
  | .paint p => .paint (toPrimitive p.primitive)
  | .group id t children => .group id t (children.map toNode)
termination_by n => sizeOf n

def fromMapping (m : NativeSVG.Mapping) : Rendering.Mapping :=
  ⟨m.sx,m.sy,m.tx,m.ty,m.minX,m.minY,m.viewportWidth,m.viewportHeight⟩
def toMapping (m : Rendering.Mapping) : NativeSVG.Mapping :=
  ⟨m.sx,m.sy,m.tx,m.ty,m.minX,m.minY,m.viewportWidth,m.viewportHeight⟩
def fromScene (s : NativeSVG.Scene) : Rendering.Scene :=
  ⟨s.width,s.height,fromMapping s.mapping,s.tree.map fromNode,#[],#[]⟩
def toScene (s : Rendering.Scene) : NativeSVG.Scene :=
  let tree := s.tree.map toNode
  ⟨s.width,s.height,toMapping s.mapping,tree,
    NativeSVG.DisplayNode.lowerFromRootList tree,rfl⟩

@[simp] theorem point_roundtrip (p : NativeSVG.Point) : toPoint (fromPoint p) = p := by cases p; rfl
@[simp] theorem color_roundtrip (p : NativeGraphics.FloatRGB) : toColor (fromColor p) = p := by cases p; rfl
@[simp] theorem contour_roundtrip (p : NativeSVGPath.Contour) : toContour (fromContour p) = p := by
  cases p
  simp [toContour,fromContour,List.map_map,Function.comp_def]
@[simp] theorem geometry_roundtrip (g : NativeSVG.Geometry) : toGeometry (fromGeometry g) = g := by
  cases g <;> simp [toGeometry,fromGeometry,List.map_map,Function.comp_def]
@[simp] theorem paint_roundtrip (p : NativeSVG.Paint) : toPaint (fromPaint p) = p := by
  cases p <;> simp [toPaint,fromPaint]
@[simp] theorem length_roundtrip (p : NativeSVGDash.Length) : toLength (fromLength p) = p := by cases p; rfl
@[simp] theorem piece_roundtrip (p : NativeSVGStroke.Piece) : toPiece (fromPiece p) = p := by
  cases p <;> simp [toPiece,fromPiece]
@[simp] theorem style_roundtrip (s : NativeSVG.Style) : toStyle (fromStyle s) = s := by
  cases s with
  | mk fill stroke color width dash offset fillOpacity strokeOpacity visible rule cap =>
    cases rule <;> cases cap <;>
      simp [toStyle,fromStyle,List.map_map,Function.comp_def]
@[simp] theorem primitive_roundtrip (p : NativeSVG.Primitive) : toPrimitive (fromPrimitive p) = p := by
  cases p with
  | mk geometry style opacity transform parts groups =>
    cases parts <;> simp [toPrimitive,fromPrimitive,List.map_map,Function.comp_def]

@[simp] theorem node_roundtrip (node : NativeSVG.DisplayNode) : toNode (fromNode node) = node := by
  refine NativeSVG.DisplayNode.rec
    (motive_1 := fun node => toNode (fromNode node) = node)
    (motive_2 := fun nodes => (nodes.map fromNode).map toNode = nodes)
    ?_ ?_ ?_ ?_ node
  · intro p
    simp [fromNode,toNode]
  · intro id transform children ih
    simp only [fromNode,toNode]
    rw [ih]
  · rfl
  · intro head tail ihHead ihTail
    simp only [List.map_cons,ihHead,ihTail]

/-- Every original retained SVG paint value and its painter position survives
passage through the shared algebra and back to the existing raster backend. -/
theorem scene_roundtrip (s : NativeSVG.Scene) : toScene (fromScene s) = s := by
  have tree : (s.tree.map fromNode).map toNode = s.tree := by
    simp [List.map_map,Function.comp_def]
  cases s with
  | mk width height mapping nodes primitives correct =>
    simp only [fromScene,toScene] at *
    simp only [tree]
    cases mapping
    simp only [toMapping,fromMapping]
    subst primitives
    rfl

theorem toPrimitive_preserves_geometry (p : Rendering.Primitive) :
    (toPrimitive p).geometry = toGeometry p.geometry := rfl

theorem fromScene_preserves_tree_order (s : NativeSVG.Scene) :
    (fromScene s).tree = s.tree.map fromNode := rfl

#print axioms geometry_roundtrip
#print axioms style_roundtrip
#print axioms primitive_roundtrip
#print axioms scene_roundtrip
end WebRenderSVG
