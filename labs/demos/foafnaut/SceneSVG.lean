import Graphics

/- Exact vector serialization of the existing lab scene vocabulary. No host
geometry, external resources, SVG text/font dependency, or curve flattening.
SVG curve strokes retain their Bezier path semantics; the old native curve
renderer samples polylines, so pixel equivalence is not claimed for curves.
Analytic segment coverage is retained, but Float projection/cross-product
roundoff can disagree at exact boundaries. No universal raster-equivalence
theorem or browser antialiasing equivalence is claimed. -/
namespace NativeSceneSVG
open NativeGraphics

private def colorOK (c : RGB) := c.r <= 255 && c.g <= 255 && c.b <= 255
private def color (c : RGB) : String := s!"rgb({c.r},{c.g},{c.b})"
private def xy (p : Point) : String := s!"{p.x} {p.y}"
private def rect (p size : Point) (c : RGB) : String :=
  s!"<rect x=\"{p.x}\" y=\"{p.y}\" width=\"{size.x}\" height=\"{size.y}\" fill=\"{color c}\"/>"
private def stroke (width : Nat) (c : RGB) : String :=
  s!"fill=\"none\" stroke=\"{color c}\" stroke-width=\"{width}\" stroke-linecap=\"round\""
private def rows (bits : GlyphRows) : List Nat :=
  [bits.row0,bits.row1,bits.row2,bits.row3,bits.row4,bits.row5,bits.row6]

/-- Glyphs become filled cells, preserving one geometric square per painted
bit. Blank and zero-scale glyphs emit no geometry. Zero-radius circles,
zero-size rectangles and zero-width strokes are refused: their degenerate
native predicates are not generally SVG's disabled-rendering semantics. -/
def shapeElements (s : Shape) : Except String (List String) := do
  if !colorOK s.color then throw "SceneSVG color component exceeds 255"
  match s with
  | .circle p radius c =>
    if radius == 0 then throw "SceneSVG zero-radius circle has no faithful SVG fill"
    return [s!"<circle cx=\"{p.x}\" cy=\"{p.y}\" r=\"{radius}\" fill=\"{color c}\"/>"]
  | .rectangle p size c =>
    if size.x == 0 || size.y == 0 then throw "SceneSVG zero-size rectangle has no faithful SVG fill"
    return [rect p size c]
  | .segment a b width c =>
    if width == 0 then throw "SceneSVG zero-width stroke has no faithful SVG stroke"
    return [s!"<line x1=\"{a.x}\" y1=\"{a.y}\" x2=\"{b.x}\" y2=\"{b.y}\" {stroke width c}/>"]
  | .quadratic a b c width paint =>
    if width == 0 then throw "SceneSVG zero-width stroke has no faithful SVG stroke"
    return [s!"<path d=\"M {xy a} Q {xy b} {xy c}\" {stroke width paint}/>"]
  | .cubic a b c d width paint =>
    if width == 0 then throw "SceneSVG zero-width stroke has no faithful SVG stroke"
    return [s!"<path d=\"M {xy a} C {xy b} {xy c} {xy d}\" {stroke width paint}/>"]
  | .glyph p size bits paint =>
    if (rows bits).any (· > 31) then throw "SceneSVG glyph rows must contain five bits"
    if size == 0 then return []
    let mut out := []
    for (bits,row) in (rows bits).zipIdx do
      for col in List.range 5 do
        if (bits >>> (4-col)) &&& 1 == 1 then
          out := out ++ [rect ⟨p.x+col*size,p.y+row*size⟩ ⟨size,size⟩ paint]
    return out

/-- Standalone self-contained static SVG. Consumer limits remain independent:
the current SVG compiler accepts 12,288 painted primitives, 1,048,576 input
chars, 262,144 read-only-storage floats and a <=4096 raster viewport. Curves serialize as real
Q/C paths but remain an explicit unsupported feature of that compiler. Large
glyph scenes may exceed its budget; serialization is not native acceptance. -/
def serialize (s : Scene) : Except String String := do
  if s.width == 0 || s.height == 0 then throw "SceneSVG viewport must be positive"
  if !colorOK s.background then throw "SceneSVG background component exceeds 255"
  let elements ← s.shapes.mapM shapeElements
  return s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{s.width}\" height=\"{s.height}\" viewBox=\"0 0 {s.width} {s.height}\">" ++
    rect ⟨0,0⟩ ⟨s.width,s.height⟩ s.background ++ String.join elements.flatten ++ "</svg>"

end NativeSceneSVG
