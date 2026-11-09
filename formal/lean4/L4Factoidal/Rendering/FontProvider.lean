import L4Factoidal.Rendering.FontData
import L4Factoidal.Rendering.Scene

/-! Typed font-data consumption, separate from line breaking and CSS.
Font outlines retain canonical line/quadratic/cubic segments. The shared
backend compiler alone tessellates them; this adapter never drops controls
or reshapes the font-library results. Vertical/RTL layout remains refused. -/
namespace L4Factoidal.Rendering.FontProvider

/-- A colour glyph drawn at one size (`ColrRaster`): its pixels, straight RGBA with rows
from the top, where its top-left corner is in pixels from the glyph's origin on the
baseline (y down), and an image id that no other bitmap of the scene has. -/
structure ColourImage where
  bitmap : Bitmap
  left : Int
  top : Int
  id : Nat

/-- A colour glyph (COLR): drawn as an image of its paint, not as `geometry`. -/
structure Colour where
  /-- The colour font's em in units of the word: its pixel size is the word's times this. -/
  em : Float
  /-- How far the baseline is below the glyph's top, in units of the word. -/
  baseline : Float
  /-- The image at a pixel size (pixels to the colour font's em) and a text colour, for
  palette index 0xFFFF. Each image is drawn once and kept with the font. -/
  image : Nat → Color → Option ColourImage

instance : Repr Colour where
  reprPrec c _ := s!"Colour (em {c.em}, baseline {c.baseline})"

structure Glyph where
  index : Nat
  /-- Position in font units relative to the word's top-left metric origin. -/
  x : Float
  y : Float
  advance : Float
  clusterStart : Nat
  clusterEnd : Nat
  geometry : List Geometry
  /-- A colour glyph's paint; `geometry` is then its monochrome form, for SVG text. -/
  colour : Option Colour := none
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
def outlineGeometry (ascent : Float) (outline : FontData.Outline) : Except String (List Geometry) := do
  let mut contours : List Contour := []
  let mut start : Option Point := none
  let mut segments : Array PathSegment := #[]
  let point := fun x y => (⟨fromInt x,ascent-fromInt y⟩ : Point)
  for command in outline.commands do
    match command with
    | .move x y =>
      if start.isSome then throw "font provider: contour not closed before move"
      start := some (point x y)
      segments := #[]
    | .line x y =>
      if start.isNone then throw "font provider: line outside contour"
      segments := segments.push (.line (point x y))
    | .quadratic cx cy x y =>
      if start.isNone then throw "font provider: quadratic outside contour"
      segments := segments.push (.quadratic (point cx cy) (point x y))
    | .cubic ax ay bx cy x y =>
      if start.isNone then throw "font provider: cubic outside contour"
      segments := segments.push (.cubic (point ax ay) (point bx cy) (point x y))
    | .close =>
      let some first := start | throw "font provider: close outside contour"
      contours := .path first segments.toList true :: contours
      start := none
      segments := #[]
  if start.isSome then throw "font provider: unclosed outline"
  return if contours.isEmpty then [] else [.path contours.reverse]

/-- Consume one already-shaped horizontal word. Glyph IDs, advances,
ligature/mark source spans and offsets come from the typed font adapter; this
function neither substitutes characters nor computes shaping. A right-to-left
word (`rtl`) has its glyphs in drawing order, left to right, as HarfBuzz gives
them; only its clusters run the other way. With `notdef`, a character the font
lacks shows as the font's own .notdef glyph. -/
def prepare (input : FontData.ShapedWord) (notdef : Bool := false) : Except String Word := do
  if input.direction != "ltr" && input.direction != "rtl" then throw "unsupported font direction: horizontal LTR or RTL required"
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
    outlines := outlines.insert outline.id (← outlineGeometry m.ascender outline)
  let mut glyphs := #[]
  let mut pen : Float := 0
  for glyph in input.glyphs do
    if glyph.id == 0 && !notdef then throw "font provider: missing glyph0 requires fallback policy"
    if ![glyph.xAdvance,glyph.yAdvance,glyph.xOffset,glyph.yOffset].all Float.isFinite ||
        glyph.yAdvance != 0 || glyph.xAdvance < 0 then
      throw "unsupported font glyph advance: finite horizontal nonnegative advance required"
    if glyph.clusterChar >= glyph.clusterEndChar || glyph.clusterEndChar > input.text.length then
      throw "font provider: invalid source cluster span"
    let some geometry := outlines.get? glyph.id | throw "font provider: missing glyph outline"
    glyphs := glyphs.push ⟨glyph.id,pen+glyph.xOffset,-glyph.yOffset,glyph.xAdvance,
      glyph.clusterChar,glyph.clusterEndChar,geometry,none⟩
    pen := pen+glyph.xAdvance
  if pen != input.advance then throw "font provider: inconsistent shaped advance"
  if !input.text.isEmpty && glyphs.isEmpty then throw "font provider: nonempty word has no glyphs"
  return ⟨input.text,input.fontSha256,input.faceIndex,input.family,input.style,input.pixelSize,m.upem,
    m.ascender,-m.descender,m.lineGap,glyphs,input.advance⟩

/-- JSON always passes through the checked native font-data schema decoder. -/
def decode (source : String) : Except String Word := do
  prepare (← FontData.decode source)

end L4Factoidal.Rendering.FontProvider
