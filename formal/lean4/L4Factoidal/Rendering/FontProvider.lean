import L4Factoidal.Rendering.FontData
import L4Factoidal.Rendering.Scene

/-! Typed font-data consumption, separate from line breaking and CSS.
The initial geometry adapter admits closed linear font outlines only. It
refuses curves and vertical/RTL shaping rather than flattening or reshaping
font-library results. This module is not yet imported by the HTML engine. -/
namespace L4Factoidal.Rendering.FontProvider

structure Glyph where
  index : Nat
  /-- Position in font units relative to the word's top-left metric origin. -/
  x : Float
  y : Float
  advance : Float
  clusterStart : Nat
  clusterEnd : Nat
  geometry : List Geometry
  deriving Repr

structure Word where
  text : String
  fontSha256 : String
  faceIndex : Nat
  family : String
  style : String
  pixelSize : Nat
  unitsPerEm : Float
  ascent : Float
  descent : Float
  lineGap : Float
  glyphs : Array Glyph
  advance : Float
  deriving Repr

private def fromInt (value : Int) : Float :=
  if value < 0 then -(Float.ofNat value.natAbs) else Float.ofNat value.toNat

/-- Convert actual font-unit points to the common y-down geometry convention.
The subtraction establishes a metric top origin; no host font/layout API is
called, and the original outlines remain available in FontData.ShapedWord. -/
def linearOutline (ascent : Float) (outline : FontData.Outline) : Except String (List Geometry) := do
  let mut contours : List Contour := []
  let mut points : Array Point := #[]
  let mut opened := false
  for command in outline.commands do
    match command with
    | .move x y =>
      if opened then throw "font provider: contour not closed before move"
      opened := true
      points := #[⟨fromInt x,ascent-fromInt y⟩]
    | .line x y =>
      if !opened then throw "font provider: line outside contour"
      points := points.push ⟨fromInt x,ascent-fromInt y⟩
    | .close =>
      if !opened then throw "font provider: close outside contour"
      contours := ⟨points.toList,true⟩ :: contours
      opened := false
      points := #[]
    | .quadratic .. | .cubic .. =>
      throw "unsupported font outline curve: checked curve backend required"
  if opened then throw "font provider: unclosed outline"
  return if contours.isEmpty then [] else [.path contours.reverse]

/-- Consume one already-shaped horizontal LTR word. Glyph IDs, advances,
ligature/mark source spans and offsets come from the typed font adapter; this
function neither substitutes characters nor computes shaping. -/
def prepare (input : FontData.ShapedWord) : Except String Word := do
  if input.direction != "ltr" then throw "unsupported font direction: horizontal LTR required"
  if input.pixelSize == 0 || input.pixelSize > 512 then throw "unsupported shaped font size: require 1 to 512 pixels"
  let m := input.metrics
  if ![m.upem,m.ascender,m.descender,m.lineGap,input.advance].all Float.isFinite ||
      m.upem <= 0 || m.ascender <= 0 || m.ascender <= m.descender || m.descender > 0 then
    throw "font provider: invalid finite horizontal metrics"
  if input.glyphs.size > 65536 || input.outlines.size > 65536 then
    throw "font provider: glyph resource bound exceeded"
  let mut outlines : Std.TreeMap Nat (List Geometry) := {}
  let mut commands := 0
  for outline in input.outlines do
    if outlines.contains outline.id then throw "font provider: duplicate glyph outline"
    commands := commands+outline.commands.size
    if commands > 2097152 then throw "font provider: aggregate outline bound exceeded"
    outlines := outlines.insert outline.id (← linearOutline m.ascender outline)
  let mut glyphs := #[]
  let mut pen : Float := 0
  for glyph in input.glyphs do
    if glyph.id == 0 then throw "font provider: missing glyph0 requires fallback policy"
    if ![glyph.xAdvance,glyph.yAdvance,glyph.xOffset,glyph.yOffset].all Float.isFinite ||
        glyph.yAdvance != 0 || glyph.xAdvance < 0 then
      throw "unsupported font glyph advance: finite horizontal nonnegative advance required"
    if glyph.clusterChar >= glyph.clusterEndChar || glyph.clusterEndChar > input.text.length then
      throw "font provider: invalid source cluster span"
    let some geometry := outlines.get? glyph.id | throw "font provider: missing glyph outline"
    glyphs := glyphs.push ⟨glyph.id,pen+glyph.xOffset,-glyph.yOffset,glyph.xAdvance,
      glyph.clusterChar,glyph.clusterEndChar,geometry⟩
    pen := pen+glyph.xAdvance
  if pen != input.advance then throw "font provider: inconsistent shaped advance"
  if !input.text.isEmpty && glyphs.isEmpty then throw "font provider: nonempty word has no glyphs"
  return ⟨input.text,input.fontSha256,input.faceIndex,input.family,input.style,input.pixelSize,m.upem,
    m.ascender,-m.descender,m.lineGap,glyphs,input.advance⟩

/-- JSON always passes through the checked native font-data schema decoder. -/
def decode (source : String) : Except String Word := do
  prepare (← FontData.decode source)

end L4Factoidal.Rendering.FontProvider
