import L4Factoidal.Rendering.Layout
import L4Factoidal.Rendering.SfntShape
import L4Factoidal.Rendering.SfntOutline

/-! A font profile from the bytes of a font file. Lean reads the file, shapes
each word and takes the outlines, so no font library and no host runs.

A page never fails because of a word. Text the shaper refuses, such as
right-to-left text, shows with one glyph for each character, and a character
the font lacks shows as the font's .notdef glyph. -/
namespace L4Factoidal.Rendering.SfntProfile

structure Font where
  bytes : ByteArray
  dir : Array FontPolicy.TableRecord
  face : SfntMetrics.Face
  cff : Option SfntCff.Font
  family : String
  sha256 : String
  faceIndex : Nat := 0

/-- One glyph, with its position in font units and its first source character. -/
private structure Placed where
  id : Nat
  advance : Nat
  xOffset : Int
  yOffset : Int
  cluster : Nat

private def ofInt (v : Int) : Float :=
  if v < 0 then -(Float.ofNat v.natAbs) else Float.ofNat v.natAbs

private def sextet (c : UInt8) : Option Nat :=
  if 65 ≤ c && c ≤ 90 then some (c.toNat-65)
  else if 97 ≤ c && c ≤ 122 then some (c.toNat-71)
  else if 48 ≤ c && c ≤ 57 then some (c.toNat+4)
  else if c == 43 then some 62
  else if c == 47 then some 63
  else none

/-- Standard base64 with padding, in one pass over the bytes. `none` for anything else. -/
def decodeBase64 (text : String) : Option ByteArray := Id.run do
  let source := text.toUTF8
  if source.size % 4 != 0 then return none
  let padding := if source.size == 0 then 0
    else if source[source.size-2]! == 61 && source[source.size-1]! == 61 then 2
    else if source[source.size-1]! == 61 then 1 else 0
  let mut out := ByteArray.emptyWithCapacity (source.size/4*3)
  let mut bits := 0
  let mut held := 0
  for i in [0:source.size-padding] do
    let some v := sextet source[i]! | return none
    bits := bits*64+v
    held := held+6
    if held ≥ 8 then
      held := held-8
      out := out.push (bits/2^held).toUInt8
      bits := bits%2^held
  return some out

/-- The font policy decides first, as it does for the native adapter. -/
def Font.read (bytes : ByteArray) (family sha256 : String) (faceIndex : Nat := 0) : Except String Font := do
  let dir ← FontPolicy.readDirectory bytes faceIndex
  unless (FontPolicy.decide FontPolicy.Policy.standard ⟨family,"",sha256⟩ dir).fontUsed do
    throw "font.file.refused"
  return ⟨bytes,dir,← SfntMetrics.Face.read bytes dir,← SfntOutline.cffFont bytes dir,family,sha256,faceIndex⟩

private def shaped (f : Font) (text : String) : Except String (String × Array Placed) := do
  let s ← SfntShape.shape f.bytes f.dir f.face text
  let chars := FontData.byteToCharMap text
  let mut out := #[]
  for (g,byte) in s.glyphs.zip s.clusterBytes do
    let some cluster := chars.get? byte | throw "font profile: cluster inside a character"
    out := out.push ⟨g.id,g.advance.toNat,g.xOffset,g.yOffset,cluster⟩
  return (s.script,out)

/-- One glyph for each character, in visual order for right-to-left text. -/
private def nominal (f : Font) (text : String) : Except String (String × Array Placed) := do
  let run ← f.face.nominalRun f.bytes text
  let glyphs := run.map fun g => ({id := g.id,advance := g.advance,xOffset := 0,yOffset := 0,cluster := g.cluster} : Placed)
  return ("",if text.toList.any (SfntShape.isStrongRtl ·.toNat) then glyphs.reverse else glyphs)

/-- The word as the font provider takes it. Only the outlines and the shaper
touch font data; `prepare` checks the record, as for the native adapter. -/
def Font.word (f : Font) (text : String) (pixelSize : Nat) : Except String FontProvider.Word := do
  let (script,placed) ← match shaped f text with
    | .ok value => pure value
    | .error _ => nominal f text
  let length := text.length
  -- A TreeMap gives each cluster once, in order, with no recursive sort.
  let clusters : Std.TreeMap Nat Unit := placed.foldl (fun seen g => seen.insert g.cluster ()) {}
  let starts := (clusters.toList.map Prod.fst).toArray
  let finish := fun (c : Nat) => (starts.find? (· > c)).getD length
  let mut outlines : Std.TreeMap Nat FontData.Outline := {}
  for g in placed do
    unless outlines.contains g.id do
      outlines := outlines.insert g.id ⟨g.id,← SfntOutline.outline f.bytes f.dir g.id f.cff⟩
  let glyphs := placed.map fun g =>
    ({id := g.id,clusterByte := 0,clusterChar := g.cluster,clusterEndChar := finish g.cluster,
      xAdvance := Float.ofNat g.advance,yAdvance := 0,xOffset := ofInt g.xOffset,yOffset := ofInt g.yOffset} : FontData.ShapedGlyph)
  let face := f.face
  FontProvider.prepare {
    text,fontSha256 := f.sha256,fontPath := "",faceIndex := f.faceIndex,family := f.family,style := "",
    metrics := ⟨Float.ofNat face.unitsPerEm,ofInt face.ascender,ofInt face.descender,ofInt face.lineGap⟩,
    direction := "ltr",script,language := "",harfbuzzVersion := "none (Lean shaper)",freeTypeVersion := "none (Lean outlines)",
    pixelSize,glyphs,outlines := outlines.toList.toArray.map Prod.snd,bitmaps := #[],
    advance := glyphs.foldl (fun total g => total+g.xAdvance) 0} (notdef := true)

/-- The words of a document's text nodes, each once, for the memo of `profile`. -/
def wordsOf (dom : DOM.Dom) (limit : Nat := 8192) : Array String := Id.run do
  let mut seen : Std.TreeMap String Unit := {}
  for node in dom.nodes do
    if node.type == .text then
      for word in node.data.splitToList Char.isWhitespace do
        if !word.isEmpty && seen.size < limit then seen := seen.insert word ()
  return (seen.toList.map Prod.fst).toArray

private def curveSteps (distance tolerance : Float) : Nat :=
  max 1 (min 16 (distance/tolerance).sqrt.ceil.toUInt32.toNat)

private def gap (a b c : Point) : Float :=
  let x := a.x-2*b.x+c.x
  let y := a.y-2*b.y+c.y
  (x*x+y*y).sqrt

/-- Lines within `tolerance` of the curve, by Wang's bound on the steps needed. -/
private def lines (start : Point) (segment : PathSegment) (tolerance : Float) : List PathSegment :=
  let at_ (steps : Nat) (point : Float → Point) := (List.range steps).map fun i =>
    PathSegment.line (point (Float.ofNat (i+1)/Float.ofNat steps))
  match segment with
  | .quadratic c p =>
    at_ (curveSteps (gap start c p) (4*tolerance)) fun t =>
      let u := 1-t
      ⟨u*u*start.x+2*u*t*c.x+t*t*p.x,u*u*start.y+2*u*t*c.y+t*t*p.y⟩
  | .cubic a b p =>
    at_ (curveSteps (max (gap start a b) (gap a b p)) (4*tolerance/3)) fun t =>
      let u := 1-t
      ⟨u*u*u*start.x+3*u*u*t*a.x+3*u*t*t*b.x+t*t*t*p.x,u*u*u*start.y+3*u*u*t*a.y+3*u*t*t*b.y+t*t*t*p.y⟩
  | other => [other]

private def endOf : PathSegment → Point
  | .line p | .quadratic _ p | .cubic _ _ p => p
  | .arc _ _ _ _ _ p => p

private def flatGeometry (tolerance : Float) : Geometry → Geometry
  | .path contours => .path (contours.map fun
    | .path first segments closed => Id.run do
      let mut current := first
      let mut out : Array PathSegment := #[]
      for segment in segments do
        out := out ++ (lines current segment tolerance).toArray
        current := endOf segment
      return .path first out.toList closed
    | other => other)
  | other => other

/-- Below `flatBelow` pixels a word is drawn with lines, which cost a fraction of
curves and differ from them by at most `flatPixels` on the screen. Larger text keeps
its curves, so that it stays smooth. The shared backend flattens those for SVG accuracy. -/
def flatBelow : Nat := 32
def flatPixels : Float := 0.25

private def flatWord (word : FontProvider.Word) : FontProvider.Word :=
  let tolerance := flatPixels*word.unitsPerEm/Float.ofNat flatBelow
  {word with glyphs := word.glyphs.map fun g => {g with geometry := g.geometry.map (flatGeometry tolerance)}}

/-- What a word costs to shape, kept: the record with curves and the one with lines. -/
structure Shaped where
  curves : FontProvider.Word
  flat : FontProvider.Word

abbrev Memo := Std.TreeMap String Shaped

/-- Add `texts` to the memo. Outlines are in font units, so one record serves every size.
The space is always added: `wordsOf` splits on it, and layout asks for it at every gap,
which was 42% of a frame of the status page. -/
def remember (f : Font) (memo : Memo) (texts : Array String) (limit : Nat := 65536) : Memo := Id.run do
  let mut out := if memo.size > limit then {} else memo
  for text in #[" "] ++ texts do
    unless out.contains text do
      if let .ok word := f.word text 16 then out := out.insert text ⟨word,flatWord word⟩
  return out

/-- The memo is only a shortcut: a word that is not in it is shaped when asked for. -/
def profile (f : Font) (memo : Memo) : Except String Layout.FontProfile := do
  let space ← match memo.get? " " with
    | some shaped => pure shaped.curves
    | none => f.word " " 16
  return {
    family := f.family,unitsPerEm := space.unitsPerEm,advance := 0,ascent := space.ascent,
    descent := space.descent,outline := fun _ => [],admits := fun _ => false,cssFamilies := [f.family],
    fontSha256 := some f.sha256,faceIndex := f.faceIndex,scalable := true,
    shapedWord := some fun text px => do
      let word ← match memo.get? text with
        | some shaped => pure (if px < flatBelow then shaped.flat else shaped.curves)
        | none => do
          let word ← f.word text px
          pure (if px < flatBelow then flatWord word else word)
      return {word with pixelSize := px}}

end L4Factoidal.Rendering.SfntProfile
