import L4Factoidal.JSON.Parser
import Std.Data.TreeMap

/-! Checked transport for the native HarfBuzz/FreeType data adapter.
No shaping or CSS layout is duplicated here. All numeric input is integral
font data; conversion to Float occurs only after signed32-bit bounds checks.
Source clusters retain both UTF-8 byte and Unicode scalar offsets. -/
namespace L4Factoidal.Rendering.FontData
open JSON

structure FontMetrics where
  upem : Float
  ascender : Float
  descender : Float
  lineGap : Float
  deriving Repr
structure ShapedGlyph where
  id : Nat
  clusterByte : Nat
  clusterChar : Nat
  clusterEndChar : Nat
  xAdvance : Float
  yAdvance : Float
  xOffset : Float
  yOffset : Float
  deriving Repr
inductive OutlineCommand where
  | move (x y : Int) | line (x y : Int)
  | quadratic (cx cy x y : Int)
  | cubic (c1x c1y c2x c2y x y : Int)
  | close
  deriving Repr
structure Outline where
  id : Nat
  commands : Array OutlineCommand
  deriving Repr
structure Bitmap where
  id : Nat
  pixelSize : Nat
  width : Nat
  height : Nat
  left : Int
  top : Int
  alpha : Array Nat
  deriving Repr
structure ShapedWord where
  text : String
  fontSha256 : String
  fontPath : String
  faceIndex : Nat
  family : String
  style : String
  metrics : FontMetrics
  direction : String
  script : String
  language : String
  harfbuzzVersion : String
  freeTypeVersion : String
  pixelSize : Nat
  glyphs : Array ShapedGlyph
  outlines : Array Outline
  bitmaps : Array Bitmap
  advance : Float
  deriving Repr

/-- Includes the end boundary; glyph starts separately require a strict bound. -/
def byteToCharMap (text : String) : Std.TreeMap Nat Nat := Id.run do
  let mut out : Std.TreeMap Nat Nat := {}
  let mut byte := 0
  let mut char := 0
  out := out.insert 0 0
  for c in text.toList do
    byte := byte+c.utf8Size
    char := char+1
    out := out.insert byte char
  return out

def byteOffsetToChar? (text : String) (offset : Nat) : Option Nat :=
  (byteToCharMap text).get? offset

private def object (j : Json) : Except String Unit := do
  let .object fields := j | throw "font data: expected object"
  let keys := fields.map Prod.fst
  if keys.eraseDups.length != keys.length then throw "font data: duplicate object key"
private def field (j : Json) (key : String) : Except String Json :=
  match j.field? key with
  | some value => .ok value
  | none => .error s!"font data: missing {key}"
private def string (j : Json) : Except String String :=
  match j.asString? with
  | some value => .ok value
  | none => .error "font data: expected string"
private def str (j : Json) (key : String) : Except String String := do string (← field j key)
private def integer (j : Json) : Except String Int := do
  let .number value := j | throw "font data: expected integer"
  let some n := value.toInt? | throw "font data: integer lexeme required"
  if n.natAbs > 2147483647 then throw "font data: integer exceeds signed32-bit bounds"
  return n
private def natural (j : Json) (maximum : Nat := 2147483647) : Except String Nat := do
  let n ← integer j
  if n < 0 || n.toNat > maximum then throw "font data: natural exceeds bounds"
  return n.toNat
private def natField (j : Json) (key : String) (maximum : Nat := 2147483647) : Except String Nat := do
  natural (← field j key) maximum
private def asFloat (n : Int) : Float :=
  if n < 0 then -(Float.ofNat n.natAbs) else Float.ofNat n.toNat
private def floatField (j : Json) (key : String) : Except String Float := do
  return asFloat (← integer (← field j key))
private def array (j : Json) (maximum : Nat) : Except String (List Json) := do
  let .array xs := j | throw "font data: expected array"
  if xs.length > maximum then throw "font data: array exceeds resource bound"
  return xs
private def arrayField (j : Json) (key : String) (maximum : Nat) : Except String (List Json) := do
  array (← field j key) maximum
private def expectString (j : Json) (key value : String) : Except String Unit := do
  if (← str j key) != value then throw s!"font data: wrong {key}"

private def command (j : Json) : Except String OutlineCommand := do
  let xs ← array j 7
  match xs with
  | [.string "M",x,y] => return .move (← integer x) (← integer y)
  | [.string "L",x,y] => return .line (← integer x) (← integer y)
  | [.string "Q",a,b,x,y] => return .quadratic (← integer a) (← integer b) (← integer x) (← integer y)
  | [.string "C",a,b,c,d,x,y] => return .cubic (← integer a) (← integer b) (← integer c) (← integer d) (← integer x) (← integer y)
  | [.string "Z"] => return .close
  | _ => throw "font data: invalid outline command or arity"
private def outline (j : Json) : Except String Outline := do
  object j
  let id ← natField j "id"
  let input ← arrayField j "commands" 1048576
  let mut out := #[]
  let mut opened := false
  for item in input do
    let cmd ← command item
    match cmd with
    | .move .. =>
      if opened then throw "font data: contour not closed before move"
      opened := true
    | .close =>
      if !opened then throw "font data: close outside contour"
      opened := false
    | _ => if !opened then throw "font data: drawing command outside contour"
    out := out.push cmd
  if opened then throw "font data: unclosed outline contour"
  return ⟨id,out⟩
private def bitmap (j : Json) (px : Nat) : Except String Bitmap := do
  object j
  let id ← natField j "id"
  let size ← natField j "pixelSize" 512
  if size != px then throw "font data: bitmap pixel size differs from run"
  let width ← natField j "width" 65536
  let height ← natField j "height" 65536
  if width*height > 16777216 then throw "font data: bitmap exceeds resource bound"
  let values ← arrayField j "alpha" 16777216
  if values.length != width*height then throw "font data: wrong bitmap coverage length"
  let mut alpha := #[]
  for value in values do alpha := alpha.push (← natural value 255)
  return ⟨id,size,width,height,← integer (← field j "left"),← integer (← field j "top"),alpha⟩

private def glyph (j : Json) (textBytes : Nat) (boundaries : Std.TreeMap Nat Nat) : Except String ShapedGlyph := do
  object j
  let id ← natField j "id"
  let cluster ← natField j "cluster" 65536
  if cluster >= textBytes then throw "font data: glyph cluster outside text"
  let some char := boundaries.get? cluster | throw "font data: cluster splits a UTF-8 scalar"
  return ⟨id,cluster,char,char,← floatField j "xAdvance",← floatField j "yAdvance",
    ← floatField j "xOffset",← floatField j "yOffset"⟩

/-- Decode the schema, validate transport invariants and retain source order.
Setting rejectMissing=false preserves glyph0 for a caller implementing fallback;
the default refuses it. This does not validate font shaping against the spec. -/
def decodeValue (j : Json) (rejectMissing : Bool := true) : Except String ShapedWord := do
  object j
  expectString j "schema" "factoidal-font-data-v1"
  expectString j "clusterUnits" "UTF-8 byte offsets"
  expectString j "coordinateSystem" "font units, positive y up"
  expectString j "rasterMode" "FreeType normal grayscale, no hinting, no embedded bitmap"
  let hash ← str j "fontSha256"
  if hash.length != 64 || !hash.toList.all (fun c => c.isDigit || c >= 'a' && c <= 'f') then
    throw "font data: expected lowercase SHA256 identity"
  let fontBytes ← natField j "fontBytes" 134217728
  if fontBytes == 0 then throw "font data: empty font"
  let text ← str j "text"
  if text.utf8ByteSize > 65536 then throw "font data: text exceeds resource bound"
  let upem ← natField j "unitsPerEm" 65535
  if upem == 0 then throw "font data: zero unitsPerEm"
  let ascent ← floatField j "ascender"
  let descent ← floatField j "descender"
  if ascent <= descent then throw "font data: invalid ascender/descender metrics"
  let px ← natField j "bitmapPixelSize" 512
  if px == 0 then throw "font data: zero bitmap pixel size"
  let direction ← str j "direction"
  if !["ltr","rtl","ttb","btt","invalid"].contains direction then throw "font data: unknown direction"
  let input ← arrayField j "glyphs" 65536
  let boundaries := byteToCharMap text
  let mut glyphs := #[]
  let mut advance : Float := 0
  let mut glyphIDs : Std.TreeMap Nat Unit := {}
  let mut previous : Option Nat := none
  for item in input do
    let g ← glyph item text.utf8ByteSize boundaries
    if rejectMissing && g.id == 0 then throw "font data: missing glyph requires fallback"
    if let some p := previous then
      if (["ltr","ttb"].contains direction && g.clusterByte < p) ||
          (["rtl","btt"].contains direction && g.clusterByte > p) then
        throw "font data: clusters violate monotone grapheme order"
    previous := some g.clusterByte
    glyphIDs := glyphIDs.insert g.id ()
    advance := advance+g.xAdvance
    glyphs := glyphs.push g
  if !text.isEmpty && glyphs.isEmpty then throw "font data: nonempty text has no shaped glyphs"
  if direction == "invalid" && !text.isEmpty then throw "font data: nonempty run has invalid direction"
  -- Resolve source spans by sorted distinct byte clusters, independent of
  -- visual direction. Repeated ligature/mark clusters receive the same span.
  let mut clusters : Std.TreeMap Nat Nat := {}
  for g in glyphs do clusters := clusters.insert g.clusterByte g.clusterChar
  let mut ends : Std.TreeMap Nat Nat := {}
  let mut previousCluster : Option Nat := none
  for (byte,char) in clusters.toList do
    if let some last := previousCluster then ends := ends.insert last char
    previousCluster := some byte
  if let some last := previousCluster then ends := ends.insert last text.length
  glyphs := glyphs.map fun g => {g with clusterEndChar := (ends.get? g.clusterByte).getD g.clusterChar}
  let mut outlines := #[]
  let mut outlinesSeen : Std.TreeMap Nat Unit := {}
  let mut commands := 0
  for value in ← arrayField j "outlines" 65536 do
    let o ← outline value
    if !glyphIDs.contains o.id || outlinesSeen.contains o.id then throw "font data: duplicate or unused outline"
    commands := commands+o.commands.size
    if commands > 2097152 then throw "font data: aggregate outline exceeds resource bound"
    outlinesSeen := outlinesSeen.insert o.id ()
    outlines := outlines.push o
  let mut bitmaps := #[]
  let mut bitmapsSeen : Std.TreeMap Nat Unit := {}
  let mut pixels := 0
  for value in ← arrayField j "bitmaps" 65536 do
    let b ← bitmap value px
    if !glyphIDs.contains b.id || bitmapsSeen.contains b.id then throw "font data: duplicate or unused bitmap"
    pixels := pixels+b.width*b.height
    if pixels > 16777216 then throw "font data: aggregate bitmap exceeds resource bound"
    bitmapsSeen := bitmapsSeen.insert b.id ()
    bitmaps := bitmaps.push b
  if outlinesSeen.size != glyphIDs.size || bitmapsSeen.size != glyphIDs.size then
    throw "font data: missing used glyph outline or bitmap"
  let fontPath ← str j "fontPath"
  let faceIndex ← natField j "faceIndex" 65535
  let family ← str j "family"
  let style ← str j "style"
  let lineGap ← floatField j "lineGap"
  let script ← str j "script"
  let language ← str j "language"
  let hbVersion ← str j "harfbuzzVersion"
  let ftVersion ← str j "freeTypeVersion"
  return {
    text := text
    fontSha256 := hash
    fontPath := fontPath
    faceIndex := faceIndex
    family := family
    style := style
    metrics := ⟨Float.ofNat upem,ascent,descent,lineGap⟩
    direction := direction
    script := script
    language := language
    harfbuzzVersion := hbVersion
    freeTypeVersion := ftVersion
    pixelSize := px
    glyphs := glyphs
    outlines := outlines
    bitmaps := bitmaps
    advance := advance }

def decode (source : String) (rejectMissing : Bool := true) : Except String ShapedWord := do
  if source.utf8ByteSize > 16777216 then throw "font data: JSON exceeds16MiB transport bound"
  let value ← (JSON.parseJson source).mapError (fun e => s!"font data JSON: {e}")
  decodeValue value rejectMissing

end L4Factoidal.Rendering.FontData
