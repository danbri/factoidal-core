import L4Factoidal.Rendering.Layout
import L4Factoidal.Rendering.SfntShape
import L4Factoidal.Rendering.SfntOutline

/-! A font profile from the bytes of a font file. Lean reads the file, shapes
each word and takes the outlines, so no font library and no host runs.

A page never fails because of a word. Text the shaper refuses shows with one
glyph for each character, and a character the font lacks shows as the font's
.notdef glyph. A word is shaped in the direction asked for, or with none, in
the direction of its script; its glyphs are always in drawing order, left to
right (https://github.com/danbri/factoidal/issues/1275). -/
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

private def shaped (f : Font) (text : String) (rtl : Option Bool) :
    Except String (String × Bool × Array Placed) := do
  let s ← SfntShape.shape f.bytes f.dir f.face text (direction := rtl)
  let chars := FontData.byteToCharMap text
  let mut out := #[]
  for (g,byte) in s.glyphs.zip s.clusterBytes do
    let some cluster := chars.get? byte | throw "font profile: cluster inside a character"
    out := out.push ⟨g.id,g.advance.toNat,g.xOffset,g.yOffset,cluster⟩
  return (s.script,s.rtl,out)

/-- One glyph for each character, in visual order for right-to-left text. -/
private def nominal (f : Font) (text : String) (rtl : Option Bool) : Except String (String × Bool × Array Placed) := do
  let run ← f.face.nominalRun f.bytes text
  let glyphs := run.map fun g => ({id := g.id,advance := g.advance,xOffset := 0,yOffset := 0,cluster := g.cluster} : Placed)
  let backward := rtl.getD (Unicode.ScriptDirection.guessRtl text)
  return ("",backward,if backward then glyphs.reverse else glyphs)

/-- The word as the font provider takes it, shaped in direction `rtl` (`none`:
the script's). Only the outlines and the shaper touch font data; `prepare`
checks the record, as for the native adapter. -/
def Font.word (f : Font) (text : String) (pixelSize : Nat) (rtl : Option Bool := none) :
    Except String FontProvider.Word := do
  let (script,backward,placed) ← match shaped f text rtl with
    | .ok value => pure value
    | .error _ => nominal f text rtl
  let length := text.length
  -- A TreeMap gives each cluster once, in order, with no recursive sort.
  let clusters : Std.TreeMap Nat Unit := placed.foldl (fun seen g => seen.insert g.cluster ()) {}
  let starts := (clusters.toList.map Prod.fst).toArray
  -- The end of each cluster: the start of the next, by one pass (a search for each
  -- glyph was quadratic in the length of a long word).
  let nextStart : Std.TreeMap Nat Nat := (starts.zipIdx.map fun (c,k) => (c,starts.getD (k+1) length)).foldl
    (fun m (c,e) => m.insert c e) {}
  let finish := fun (c : Nat) => nextStart.getD c length
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
    direction := if backward then "rtl" else "ltr",script,language := "",
    harfbuzzVersion := "none (Lean shaper)",freeTypeVersion := "none (Lean outlines)",
    pixelSize,glyphs,outlines := outlines.toList.toArray.map Prod.snd,bitmaps := #[],
    advance := glyphs.foldl (fun total g => total+g.xAdvance) 0} (notdef := true)

/-! ### Fallback fonts

A page names one font, but its text can need several: Noto Sans has no Armenian,
for example. The engine holds an ordered list of fonts, the first one being the
primary font. `runsOf` gives each character to a font, and `wordIn` shapes each run
with its font and joins the runs into one word in the units and metrics of the
primary font, so layout sees one font, as before. -/

/-- The font's cmap has a glyph other than .notdef for the character. -/
def Font.has (f : Font) (c : Char) : Bool :=
  match f.face.glyphCp f.bytes c.toNat with
  | .ok g => g != 0
  | .error _ => false

/-- Characters that stay in the run before them when that font has them: the
combining marks that many scripts share, joiners and variation selectors. Script
fonts carry the marks of their own script, so this list is short. -/
def staysWithBase (c : Nat) : Bool :=
  (0x300 ≤ c && c ≤ 0x36F) || (0x1AB0 ≤ c && c ≤ 0x1AFF) || (0x1DC0 ≤ c && c ≤ 0x1DFF) ||
  (0x20D0 ≤ c && c ≤ 0x20FF) || (0xFE20 ≤ c && c ≤ 0xFE2F) || c == 0x200C || c == 0x200D ||
  (0xFE00 ≤ c && c ≤ 0xFE0F) || (0xE0100 ≤ c && c ≤ 0xE01EF)

/-- Characters after a base that ask for a font with an emoji form of it: the
emoji presentation selector U+FE0F and the combining enclosing keycap U+20E3. -/
def asksForEmoji (c : Nat) : Bool := c == 0xFE0F || c == 0x20E3

/-- A word in runs: the index of a font in `fonts`, and the characters it draws.
Each character goes to the first font that has it. A character in `staysWithBase`
keeps the font of the run before it when that font has it. A character followed by
U+FE0F or U+20E3 (`asksForEmoji`) goes to the first font that has both, when one
does: the digit of a keycap and a symbol with emoji presentation (U+2665 U+FE0F)
come from the emoji font with their selector, not from the text font, so the
font's sequences can form. A character that no font has stays in the run before
it (the first font at the start), and shows as that font's .notdef glyph. -/
def runsOf (fonts : Array Font) (text : String) : Array (Nat × String) := Id.run do
  let mut runs : Array (Nat × String) := #[]
  let chars := text.toList.toArray
  for k in [0:chars.size] do
    let c := chars[k]!
    let last := runs.back?.map (·.1)
    let keep := match last with
      | some i => staysWithBase c.toNat && (fonts[i]?.map fun (f : Font) => f.has c).getD false
      | none => false
    let emoji := match chars[k + 1]? with
      | some n => if asksForEmoji n.toNat && !staysWithBase c.toNat then
          fonts.findIdx? fun (f : Font) => f.has c && f.has n else none
      | none => none
    let pick := if keep then last.getD 0 else
      match emoji with
      | some i => i
      | none => (fonts.findIdx? fun (f : Font) => f.has c).getD (last.getD 0)
    runs := match runs.back? with
      | some (i,s) => if i == pick then runs.pop.push (i,s.push c) else runs.push (pick,c.toString)
      | none => runs.push (pick,c.toString)
  return runs

private def scalePoint (k : Float) (p : Point) : Point := ⟨k*p.x,k*p.y⟩

private def scaleSegment (k : Float) : PathSegment → PathSegment
  | .line p => .line (scalePoint k p)
  | .quadratic c p => .quadratic (scalePoint k c) (scalePoint k p)
  | .cubic a b p => .cubic (scalePoint k a) (scalePoint k b) (scalePoint k p)
  | .arc rx ry rotation large sweep p => .arc (k*rx) (k*ry) rotation large sweep (scalePoint k p)

/-- Glyph geometry `k` times as large, about the glyph's own origin. -/
def scaleGeometry (k : Float) : Geometry → Geometry
  | .rect x y w h => .rect (k*x) (k*y) (k*w) (k*h)
  | .circle cx cy r => .circle (k*cx) (k*cy) (k*r)
  | .ellipse cx cy rx ry => .ellipse (k*cx) (k*cy) (k*rx) (k*ry)
  | .line x1 y1 x2 y2 => .line (k*x1) (k*y1) (k*x2) (k*y2)
  | .polygon points => .polygon (points.map (scalePoint k))
  | .path contours => .path (contours.map fun
    | .path start segments closed => .path (scalePoint k start) (segments.map (scaleSegment k)) closed
    | other => other)

/-- The word drawn with `fonts`, the first being the primary font. A word that the
primary font draws alone is `Font.word` of that font, unchanged. Otherwise each run
is shaped by its own font, and its glyphs are put in the primary font's units: the
outlines and advances are scaled by the ratio of the units per em, and each glyph
moves down by the difference of the ascents, so that the baselines are one line.
The word keeps the primary font's name, units and metrics, which layout checks.
Each run is shaped in direction `rtl` (`none`: its own script's), and the runs
are drawn right to left when the word is (`rtl`, or with none, its script's). -/
def wordIn (fonts : Array Font) (text : String) (pixelSize : Nat) (rtl : Option Bool := none) :
    Except String FontProvider.Word := do
  let some primary := fonts[0]? | throw "font profile: no font"
  let runs := runsOf fonts text
  if runs.all (·.1 == 0) then return ← primary.word text pixelSize rtl
  let face := primary.face
  let units := Float.ofNat face.unitsPerEm
  let ascent := ofInt face.ascender
  let mut glyphs : Array FontProvider.Glyph := #[]
  let mut pen : Float := 0
  -- The first character of each run, in logical order.
  let mut starts : Array Nat := #[]
  let mut at_ := 0
  for (_,part) in runs do
    starts := starts.push at_
    at_ := at_+part.length
  let backward := rtl.getD (Unicode.ScriptDirection.guessRtl text)
  let order := if backward then (List.range runs.size).reverse else List.range runs.size
  for r in order do
    let (i,part) := runs[r]!
    let start := starts[r]!
    let some f := fonts[i]? | throw "font profile: run names no font"
    let w ← f.word part pixelSize rtl
    let k := units/w.unitsPerEm
    let down := ascent-k*w.ascent
    for g in w.glyphs do
      let placed : FontProvider.Glyph := ⟨g.index,pen+k*g.x,k*g.y+down,k*g.advance,
        start+g.clusterStart,start+g.clusterEnd,g.geometry.map (scaleGeometry k)⟩
      glyphs := glyphs.push placed
    pen := pen+k*w.advance
  -- FontProvider.Word in field order: text, font, face, family, style, size, units,
  -- ascent, descent, line gap, glyphs, advance.
  return ⟨text,primary.sha256,primary.faceIndex,primary.family,"",pixelSize,units,
    ascent,-ofInt face.descender,ofInt face.lineGap,glyphs,pen⟩

/-- Elements whose text is never drawn as text: script and style data, the
inert content of `template`, `noscript` (scripts run here, so its content is not
rendered), and `title` (the tab, not the page). -/
def unrenderedText : List String := ["script","style","template","noscript","title"]

/-- The text node `id` is inside an element of `unrenderedText` or a document
fragment (the content of a `template`). The walk is bounded by the arena size. -/
def inUnrendered (dom : DOM.Dom) (id : Nat) : Bool := Id.run do
  let mut at_ := (dom.get id).parent
  for _ in [:dom.size+1] do
    let some p := at_ | return false
    let n := dom.get p
    if n.type == .fragment then return true
    if n.type == .element && unrenderedText.contains n.lname then return true
    at_ := n.parent
  return false

/-- The words of a document's drawn text, each once, for the memo of `profile`:
not the text of `unrenderedText` elements, which is data (a JSON script of a page can
be one word of thousands of characters). -/
def wordsOf (dom : DOM.Dom) (limit : Nat := 8192) : Array String := Id.run do
  let mut seen : Std.TreeMap String Unit := {}
  for id in [:dom.size] do
    let node := dom.get id
    if node.type == .text && !inUnrendered dom id then
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

/-- Add `texts` to the memo of the font list `fonts` (see `wordIn`). Outlines are in
font units, so one record serves every size. The space is always added: `wordsOf`
splits on it, and layout asks for it at every gap, which was 42% of a frame of the
status page. -/
def remember (fonts : Array Font) (memo : Memo) (texts : Array String) (limit : Nat := 65536) : Memo := Id.run do
  let mut out := if memo.size > limit then {} else memo
  for text in #[" "] ++ texts do
    unless out.contains text do
      if let .ok word := wordIn fonts text 16 then out := out.insert text ⟨word,flatWord word⟩
  return out

/-- The memo is only a shortcut: a word that is not in it is shaped when asked for.
The profile is named by the first font of `fonts`; the others draw what it lacks. -/
def profile (fonts : Array Font) (memo : Memo) : Except String Layout.FontProfile := do
  let some f := fonts[0]? | throw "font profile: no font"
  let space ← match memo.get? " " with
    | some shaped => pure shaped.curves
    | none => wordIn fonts " " 16
  let shapedWord := fun (text : String) (px : Nat) => do
    let word ← match memo.get? text with
      | some shaped => pure (if px < flatBelow then shaped.flat else shaped.curves)
      | none => do
        let word ← wordIn fonts text px
        pure (if px < flatBelow then flatWord word else word)
    return {word with pixelSize := px}
  -- A word in a direction other than its script's (bidi levels in layout) is not in the memo.
  let shapedWordDir := fun (text : String) (px : Nat) (rtl : Bool) => do
    let word ← wordIn fonts text px (some rtl)
    return {(if px < flatBelow then flatWord word else word) with pixelSize := px}
  return {
    family := f.family,unitsPerEm := space.unitsPerEm,advance := 0,ascent := space.ascent,
    descent := space.descent,outline := fun _ => [],admits := fun _ => false,cssFamilies := [f.family],
    fontSha256 := some f.sha256,faceIndex := f.faceIndex,scalable := true,
    shapedWord := some shapedWord,shapedWordDir := some shapedWordDir}

end L4Factoidal.Rendering.SfntProfile
