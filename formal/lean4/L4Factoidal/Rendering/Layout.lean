import L4Factoidal.Rendering.Style
import L4Factoidal.Rendering.Generated
import L4Factoidal.Rendering.InlineBox
import L4Factoidal.Rendering.MarginCollapse
import L4Factoidal.Rendering.TextCase
import L4Factoidal.Rendering.FontFace
import L4Factoidal.Rendering.TableLayout
import L4Factoidal.Rendering.FlexLayout
import L4Factoidal.Rendering.OffsetParent
import L4Factoidal.Rendering.AspectRatio
import L4Factoidal.Rendering.ScrollGeometry
import L4Factoidal.Rendering.GridLayout
import L4Factoidal.Rendering.SelfPlace
import L4Factoidal.Unicode.ScriptDirection
import L4Factoidal.Unicode.LineBreak

/-! Block flow and inline word wrapping over the existing DOM arena. This
profile excludes floats, positioning, flex/grid, margin collapse and inline box
decorations. Those features are refused rather than approximated.

Bidirectional text (UAX #9, `Unicode.Bidi`; https://github.com/danbri/factoidal/issues/1275):
the paragraph direction is the block container's `direction` (from CSS or the HTML
`dir` attribute; `unicode-bidi: plaintext` takes it from the first strong character).
An inline box with `unicode-bidi` (an element with `dir`, `bdi`, `bdo`) adds the bidi
control characters of CSS Writing Modes 3 §2.4.2 around its content. Each word is cut
where its resolved level changes, and each piece is shaped in the direction of its
level. Lines break as before, never inside a word; each line is then reordered by
rule L1 and L2 (`Unicode.reorderByLevels`) by moving its items, which stay in logical
order in the result, so selection and hit testing read glyph runs in document order.
`text-align: start` and `end` follow the direction. A block with no right-to-left
character, no bidi control and direction ltr takes none of this path. -/
namespace L4Factoidal.Rendering.Layout
open DOM CSS

structure FontProfile where
  family : String
  /-- Advance and painted em box in font units; this profile is monospace. -/
  unitsPerEm : Float
  advance : Float
  ascent : Float
  descent : Float
  /-- Glyph geometry comes from a Lean font adapter, never from host layout. -/
  outline : Nat → List Geometry
  admits : Nat → Bool
  cssFamilies : List String := ["monospace","ascii-bitmap"]
  fontSha256 : Option String := none
  faceIndex : Nat := 0
  /-- A pure lookup of externally shaped, checked font data, never host layout. -/
  shapedWord : Option (String → Nat → Except String FontProvider.Word) := none
  /-- The same, shaped right to left (`true`) or left to right: for a piece of text
  whose bidi level is not the direction of its script (`shapedWord` takes the
  script's direction). With none, `shapedWord` serves. -/
  shapedWordDir : Option (String → Nat → Bool → Except String FontProvider.Word) := none
  /-- Outlines scale to any size, so a fractional size is not refused. -/
  scalable : Bool := false
  /-- Words of an element whose `font-family` value (`Computed.fontFamily`) names a
  web font (CSS Fonts 4 §4): shaped with its faces first, in this profile's units and
  metrics, as fallback runs are (`SfntProfile.wordWith`), with the bidi direction
  when it is not the script's. `none`: the family list names no web font, and
  `shapedWord` serves. -/
  familyWord : String → Option (String → Nat → Option Bool → Except String FontProvider.Word) := fun _ => none
  /-- The ascent and descent, in this profile's units, of the first font of a `font-family`
  value (`Computed.fontFamily`) when that font is not this profile's own (a web font, the
  serif or the monospace face): CSS 2.1 §10.8.1, the inline box of text is the content area
  of its font, with the half-leading of that font. `none`: the profile's own metrics. -/
  familyMetrics : String → Option (Float × Float) := fun _ => none

def FontProfile.ofFace (face : FontProvider.Face) : FontProfile :=
  {family := face.family,unitsPerEm := face.unitsPerEm,advance := 0,
   ascent := face.ascent,descent := face.descent,outline := fun _ => [],admits := fun _ => false,
   cssFamilies := [face.family],fontSha256 := some face.fontSha256,faceIndex := face.faceIndex,
   shapedWord := some face.lookup}

/-- CSS Text 3 §8.2: `extra` font units after each typographic character unit of `word` (its
letter spacing), here each cluster of the shaped word, so that a base and its combining marks
are one unit. A glyph moves by the extra of the clusters before it on the line, and the word's
advance grows by the extra of all its clusters. Before 2026-11-23 `letter-spacing` was not
read. -/
def letterSpaced (word : FontProvider.Word) (extra : Float) : FontProvider.Word := Id.run do
  if extra == 0 || !extra.isFinite then return word
  let mut glyphs : Array FontProvider.Glyph := #[]
  let mut shift := 0.0
  let mut cluster : Option Nat := none
  let mut clusters := 0
  -- Zero-width format and bidi controls take no spacing, and neither do the cursive scripts,
  -- whose letters join (CSS Text 3 §8.1): Arabic, Syriac, NKo, Mandaic, Mongolian, Adlam.
  let chars := word.text.toList.toArray
  let within (c lo hi : Nat) : Bool := lo <= c && c <= hi
  let ignorable (i : Nat) : Bool :=
    let c := (chars.getD i ' ').toNat
    c == 0xAD || c == 0xFEFF || within c 0x200B 0x200F || within c 0x202A 0x202E ||
    within c 0x2060 0x2064 || within c 0x2066 0x206F ||
    within c 0x0600 0x077F || within c 0x07C0 0x07FF || within c 0x0840 0x08FF || within c 0xFB50 0xFDFF || within c 0xFE70 0xFEFE ||
    within c 0x1800 0x18AF || within c 0x1E900 0x1E95F
  let mut spaced := false
  for g in word.glyphs do
    if cluster != some g.clusterStart then
      if spaced then shift := shift+extra
      cluster := some g.clusterStart
      spaced := !ignorable g.clusterStart
      if spaced then clusters := clusters+1
    glyphs := glyphs.push {g with x := g.x+shift}
  return {word with glyphs, advance := word.advance+extra*Float.ofNat clusters}

/-- A word shaped by the font. `rtl`: the direction of its bidi level, when that is
not the direction of its script (see `shapedWordDir`). -/
private def FontProfile.word (font : FontProfile) (style : Computed) (text : String)
    (rtl : Option Bool := none) : Except String (Option FontProvider.Word) := do
  match font.shapedWord with
  | none => return none
  | some shape =>
    let size := if font.scalable then max 1 (min 512 style.fontSize.round.toUInt32.toNat) else style.fontSize.toUInt32.toNat
    if !font.scalable && (Float.ofNat size != style.fontSize || size == 0 || size > 512) then
      throw "unsupported shaped font size: integer pixels 1 to 512 required"
    let word ← match font.familyWord style.fontFamily with
      | some shapeIn =>
        shapeIn text size (match rtl with
          | some r => if r == Unicode.ScriptDirection.guessRtl text then none else some r
          | none => none)
      | none =>
      match rtl, font.shapedWordDir with
      | some r, some shapeDir =>
        if r == Unicode.ScriptDirection.guessRtl text then shape text size else shapeDir text size r
      | _, _ => shape text size
    if word.text != text || word.pixelSize != size || font.fontSha256 != some word.fontSha256 ||
        word.faceIndex != font.faceIndex || word.family != font.family ||
        word.unitsPerEm != font.unitsPerEm || word.ascent != font.ascent || word.descent != font.descent then
      throw "font profile: shaped word identity, size or metrics mismatch"
    return some (letterSpaced word (style.letterSpacingPx*word.unitsPerEm/style.fontSize))


private def spaceWidth (font : FontProfile) (style : Computed) : Except String Float := do
  -- CSS Text 3 §8.1: `word-spacing` is added to each word separator (its letter spacing is
  -- in the shaped space's advance)
  match ← font.word style " " with
  | none => return (font.advance*style.fontSize/font.unitsPerEm+style.letterSpacingPx+style.wordSpacingPx)
  | some word =>
    if word.glyphs.any (fun glyph => !glyph.geometry.isEmpty) then
      throw "unsupported painted whitespace glyph in collapsed space profile"
    return word.advance*style.fontSize/font.unitsPerEm+style.wordSpacingPx

/-- The ascent and descent, in the profile's units, of the font of `style`'s text: its family's
first font (`familyMetrics`), else the profile's. Before 2026-11-22 every line box used the
profile's (Noto Sans: 1.069 and 0.293 em), so a line of `font: 20px/1 Ahem` put its baseline
0.088 em too low and failed the CSS2 reftests drawn with Ahem by 2 px. -/
def FontProfile.metricsOf (font : FontProfile) (style : Computed) : Float × Float :=
  (font.familyMetrics style.fontFamily).getD (font.ascent,font.descent)

/-- CSS leading surrounds the actual ascent+descent metric box, which need
not equal one em (ordinary real fonts often differ). -/
private def lineLeading (font : FontProfile) (style : Computed) : Float :=
  let (a,d) := font.metricsOf style
  (style.lineHeight-(a+d)*style.fontSize/font.unitsPerEm)/2

/-- CSS Overflow 3 §3.1: `overflow: hidden` and `overflow: clip` clip the content of a
box to its padding box (`paddingBox`); the box's own background and border are drawn
whole (`decorations`). With `clip` false the content is drawn whole. Each primitive of
clipped content carries the padding box (`ClipTheorems.clipContent_clips`). -/
def clipContent (clip : Bool) (decorations content : Array Node) (paddingBox : ClipRect) : Array Node :=
  if clip then decorations.push (.clipped none identity paddingBox content.toList) else decorations ++ content

-- `Box` and `Result` are in `Rendering/Fragment.lean`, with the interface between
-- formatting contexts (`Constraints`, `Item`, `Children`, `ContentBox`).
abbrev Embedding := Nat → CSS.Computed → Float → Float → Except String (List Node)

/-- SVG's natural dimensions are literal non-negative numbers or absolute lengths.
The CSS presentation hints are cascaded separately, so an authored `auto` can
discard a presentation hint without discarding the natural dimension. -/
def svgNaturalPixels (source : String) : Option Rat :=
  let pixels := match (CssValues.tokenize source).filter (· != .ws) with
    | [.num n _] => some n
    | [.dim n _ unit] => do
      let (factor, canonical) ← CssValues.absFactor (CssValues.lower unit)
      if canonical == "px" then some (n*factor) else none
    | _ => none
  pixels.filter (fun v => 0 ≤ v)

theorem svgNaturalPixels_nonnegative (source : String) (px : Rat)
    (h : svgNaturalPixels source = some px) : 0 ≤ px := by
  unfold svgNaturalPixels at h
  exact of_decide_eq_true (Option.filter_eq_some_iff.mp h).2

#print axioms svgNaturalPixels_nonnegative

#guard svgNaturalPixels " 1e2pX " == some 100
#guard svgNaturalPixels "2.54cm" == some 96
#guard svgNaturalPixels "101.6Q" == some 96
#guard svgNaturalPixels "-0px" == some 0
#guard (svgNaturalPixels "-1px").isNone
#guard (svgNaturalPixels "0em").isNone
#guard (svgNaturalPixels "100%").isNone
#guard (svgNaturalPixels "calc(1px)").isNone
#guard (svgNaturalPixels "1s").isNone

private def svgNaturalLength (source : String) : Option Float := do
  let px ← svgNaturalPixels source
  let size := Float.ofNat px.num.toNat / Float.ofNat px.den
  if size.isFinite then some size else none

/-- Replaced SVG dimensions share the same calculation in inline and block
flow. A positive viewBox supplies the ratio for an auto CSS dimension.
Positive natural dimensions give a ratio when no viewBox supplies one.
The ratio-only case uses the available containing width.
Presentation lengths participate in the CSS cascade before this calculation. -/
def svgSize (node : DOM.Node) (style : Computed) (available : Float) : Except String (Float × Float) := do
  let width := CSS.resolve available style.width
  -- CSS 2.1 §10.5: a percentage height whose containing block has no definite height
  -- computes to `auto` (the height then follows from the width and the `viewBox`). It was
  -- refused, and with it every inline icon styled `height: 100%` (BBC News: 179).
  let height := match style.height with
    | .percent _ => none
    | other => CSS.resolve 0 other
  if let (some w,some h) := (width,height) then return (max 0 w,max 0 h)
  let naturalWidth := svgNaturalLength (CSS.attrValue node "width")
  let naturalHeight := svgNaturalLength (CSS.attrValue node "height")
  let source := CSS.attrValue node "viewBox"
  let mut ratio : Option (Float × Float) := none
  if !source.isEmpty then
    let fields := (source.replace "," " ").splitOn " " |>.flatMap (fun s => (s.replace "\n" " " |>.replace "\t" " " |>.replace "\r" " ").splitOn " ") |>.filter (!·.isEmpty)
    let [_,_,w,h] := fields | throw "unsupported SVG intrinsic viewBox: four numbers required"
    let w ← CSS.number w
    let h ← CSS.number h
    if w > 0 && h > 0 then ratio := some (w,h)
  if ratio.isNone then
    if let (some w, some h) := (naturalWidth, naturalHeight) then
      if w > 0 && h > 0 then ratio := some (w,h)
  let (width,height) := if width.isSome || height.isSome then (width,height)
    else (naturalWidth,naturalHeight)
  match width,height,ratio with
  | some w,none,some (rw,rh) => return (max 0 w,max 0 (w*rh/rw))
  | none,some h,some (rw,rh) => return (max 0 (h*rw/rh),max 0 h)
  | none,none,some (rw,rh) => return (max 0 available,max 0 (available*rh/rw))
  | _,_,_ => return (max 0 (width.getD (naturalWidth.getD 300)),max 0 (height.getD (naturalHeight.getD 150)))


/-- The offsets of colour stops on a gradient line `length` px long (CSS Images 3 §3.5.1):
a percentage is of the line, a length of px; with none, the first is 0, the last 1, and
those between are spaced evenly between their neighbours that have one. An offset before an
earlier one is moved up to it (`Scene.normalizeStops` does the same). -/
def stopOffsets (length : Float) (stops : List (Option (Float × Bool))) : List Float := Id.run do
  let given := stops.toArray.map fun p => p.map fun (v,percent) => if percent then v else if length > 0 then v/length else 0
  let n := given.size
  if n == 0 then return []
  let mut out := given
  if out[0]!.isNone then out := out.set! 0 (some 0)
  if out[n-1]!.isNone then out := out.set! (n-1) (some 1)
  -- each run of stops with no position, between two that have one
  let mut i := 1
  for _ in [0:n] do
    if i ≥ n then break
    if out[i]!.isSome then i := i+1; continue
    let start := i-1
    let mut stop := i
    for _ in [0:n] do
      if stop < n && out[stop]!.isNone then stop := stop+1
    let a := (out[start]!).getD 0
    let b := (out[stop]!).getD 1
    for k in [i:stop] do
      out := out.set! k (some (a+(b-a)*Float.ofNat (k-start)/Float.ofNat (stop-start)))
    i := stop+1
  let mut last := 0
  let mut result : List Float := []
  for o in out do
    let v := max last (o.getD last)
    result := result ++ [v]
    last := v
  return result

/-- The paint of a `linear-gradient()` over a box at `(x,y)`, `w` by `h` (CSS Images 3
§3.1.1): the line through the box's centre in the gradient's direction, as long as the
box's extent along it, so that the corners take the first and last colours. -/
def gradientPaint (g : CSS.BackgroundGradient) (x y w h : Float) : Paint :=
  let (dx,dy) := match g.corner with
    | some (cx,cy) =>
      -- §3.1.1: perpendicular to the diagonal between the two corners beside the named one
      let vx := (if cx < 0 then -h else if cx > 0 then h else 0)
      let vy := (if cy < 0 then -w else if cy > 0 then w else 0)
      let n := Float.sqrt (vx*vx+vy*vy)
      if n > 0 then (vx/n,vy/n) else (0,1)
    | none =>
      -- the four sides exactly (sin and cos of a multiple of 90 degrees are not exact in Float)
      let turn := g.angle-360*(g.angle/360).floor
      if turn == 0 then (0,-1) else if turn == 90 then (1,0) else if turn == 180 then (0,1)
      else if turn == 270 then (-1,0) else
      let a := g.angle*3.141592653589793/180
      (Float.sin a,-Float.cos a)
  let length := (w*dx).abs+(h*dy).abs
  let cx := x+w/2
  let cy := y+h/2
  let offsets := stopOffsets length (g.stops.map (·.2.2))
  let stops := (g.stops.zip offsets).map fun ((c,opacity,_),offset) => ({offset,color := c,opacity} : GradientStop)
  .gradient {shape := .linear (cx-dx*length/2) (cy-dy*length/2) (cx+dx*length/2) (cy+dy*length/2),
             boundingBoxUnits := false,stops}

/-- Most tiles of one background image that a box paints (`backgroundTiles`); a box that
would need more paints its colour only. -/
def maxBackgroundTiles : Nat := 4096

/-- The size of a background tile (CSS Backgrounds 3 §3.9, by the default sizing algorithm of
CSS Images 3 §5.3) from `background-size`, the image's natural width, height and ratio
(`nw`, `nh`, `ratio`: width over height; any may be missing) and the positioning area `w`
by `h`. A missing size with no ratio takes the area's. -/
def backgroundTileSize (size : BackgroundSize) (nw nh ratio : Option Float) (w h : Float) : Float × Float :=
  let r := ratio.bind fun r => if r > 0 && r.isFinite then some r else none
  let fit := fun (cover : Bool) => match r with
    | some r => if (w/r <= h) != cover then (w,w/r) else (h*r,h)
    | none => (w,h)
  match size with
  | .cover => fit true
  | .contain => fit false
  | .dimensions width height =>
    match CSS.resolve w width, CSS.resolve h height with
    | some tw, some th => (tw,th)
    | some tw, none => (tw, match r with | some r => tw/r | none => nh.getD h)
    | none, some th => ((match r with | some r => th*r | none => nw.getD w), th)
    | none, none => match nw, nh, r with
      | some a, some b, _ => (a,b)
      | some a, none, some r => (a,a/r)
      | none, some b, some r => (b*r,b)
      | some a, none, none => (a,h)
      | none, some b, none => (w,b)
      | none, none, some _ => fit false
      | none, none, none => (w,h)

#guard backgroundTileSize (.dimensions .auto .auto) (some 10) (some 20) (some 0.5) 100 100 == (10,20)
#guard backgroundTileSize (.dimensions .auto .auto) none none none 256 768 == (256,768)
#guard backgroundTileSize (.dimensions .auto .auto) none none (some 2) 256 768 == (256,128)
#guard backgroundTileSize (.dimensions .auto (.px 32)) none none none 256 768 == (256,32)
#guard backgroundTileSize (.dimensions .auto (.px 32)) (some 8) none (some 0.125) 256 768 == (4,32)
#guard backgroundTileSize .cover none none (some 2) 100 100 == (200,100)
#guard backgroundTileSize .contain none none (some 2) 100 100 == (100,50)

/-- The tiles of a background image (`backgroundTiles`): none when nothing is drawn; `.solid`
for a repeated opaque 1×1 image, which is a colour; else the first tile's corner, the tile
size and the columns and rows. -/
inductive TileGrid where
  | none
  | solid (c : Color)
  | grid (startX startY tw th : Float) (cols rows : Nat)

def tileGrid (b : Bitmap) (s : Computed) (x y w h : Float) : TileGrid := Id.run do
  if b.width == 0 || b.height == 0 then return .none
  let iw := Float.ofNat b.width
  let ih := Float.ofNat b.height
  let e := s.borderEdges
  let areaW := max 0 (w-e.left-e.right)
  let areaH := max 0 (h-e.top-e.bottom)
  let (nw,nh,ratio) := s.backgroundNatural.getD (some iw,some ih,some (iw/ih))
  let (tw,th) := backgroundTileSize s.backgroundSize nw nh ratio areaW areaH
  if tw <= 0 || th <= 0 then return .none
  let (repeatX,repeatY) := s.backgroundRepeat
  if repeatX && repeatY && b.width == 1 && b.height == 1 && b.rgba.size >= 4 && b.rgba.get! 3 == 255 then
    return .solid ⟨Float.ofNat (b.rgba.get! 0).toNat/255,Float.ofNat (b.rgba.get! 1).toNat/255,Float.ofNat (b.rgba.get! 2).toNat/255⟩
  -- CSS Backgrounds 3 §2.6 resolves each axis against the area minus the sized image.
  let ox := x+e.left+(s.backgroundPositionX.resolve (areaW-tw)).getD 0
  let oy := y+e.top+(s.backgroundPositionY.resolve (areaH-th)).getD 0
  let startX := if repeatX then ox-((ox-x)/tw).ceil*tw else ox
  let startY := if repeatY then oy-((oy-y)/th).ceil*th else oy
  let cols := if repeatX then ((x+w-startX)/tw).ceil.toUInt64.toNat else 1
  let rows := if repeatY then ((y+h-startY)/th).ceil.toUInt64.toNat else 1
  return .grid startX startY tw th cols rows

/-- The number of tiles a box's background image needs (0 for none or a colour): what
`maxBackgroundTiles` bounds, for the report of a box past it (issue 865). -/
def backgroundTileCount (b : Bitmap) (s : Computed) (x y w h : Float) : Nat :=
  match tileGrid b s x y w h with
  | .grid _ _ _ _ cols rows => cols*rows
  | _ => 0

/-- The first background layer is sized against the padding box and clipped to the
border box. Repeated axes may need a tile before the origin to cover the border. -/
def backgroundTiles (id pic : Nat) (b : Bitmap) (s : Computed) (x y w h : Float) : Array Node := Id.run do
  let (startX,startY,tw,th,cols,rows) ← match tileGrid b s x y w h with
    | .none => return #[]
    | .solid c => return #[.paint ⟨some id,{geometry := .rect x y w h,style := {fill := .solid c}}⟩]
    | .grid sx sy tw th cols rows => pure (sx,sy,tw,th,cols,rows)
  if cols*rows > maxBackgroundTiles then return #[]
  let sx := Float.ofNat b.width/tw
  let sy := Float.ofNat b.height/th
  let mut out := #[]
  for j in [0:rows] do
    for i in [0:cols] do
      let tx := startX+Float.ofNat i*tw
      let ty := startY+Float.ofNat j*th
      let l := max x tx
      let t := max y ty
      let r := min (x+w) (tx+tw)
      let bo := min (y+h) (ty+th)
      if r > l && bo > t then
        let image : ImageRecord := ⟨⟨sx,0,0,sy,-tx*sx,-ty*sy⟩,pic,b⟩
        out := out.push (.paint ⟨some id,{geometry := .rect l t (r-l) (bo-t),style := {fill := .image image}}⟩)
  return out

private def backgroundColour (id : Nat) (s : Computed) (x y w h : Float) : Array Node :=
  if !s.visible || w <= 0 || h <= 0 then #[] else
  match s.background with
  | none => #[]
  | some c => #[.paint ⟨some id,{geometry := .rect x y w h,style := {fill := .solid c}}⟩]


/-- The box `background-clip` paints in (CSS Backgrounds 3 §3.7), for a border box at
`(x,y)`, `w` by `h`: the border box, or that less the border (padding box), or less the
border and the padding (content box). -/
def backgroundArea (s : Computed) (x y w h : Float) : Float × Float × Float × Float :=
  if s.colorClip == 0 then (x,y,w,h) else
  let b := s.borderEdges
  let p := if s.colorClip == 2 then s.padding else {}
  let l := b.left+p.left
  let t := b.top+p.top
  (x+l,y+t,w-l-b.right-p.right,h-t-b.bottom-p.bottom)

private def background (id : Nat) (s : Computed) (x y w h : Float) : Array Node :=
  if !s.visible || w <= 0 || h <= 0 then #[] else
  let (cx,cy,cw,ch) := backgroundArea s x y w h
  if cw <= 0 || ch <= 0 then #[] else
  let colour := backgroundColour id s cx cy cw ch
  -- CSS Backgrounds 3 §3.2: the image over the colour (a gradient fills the clip box)
  let withGradient := match s.backgroundGradient with
    | none => colour
    | some g => colour.push (.paint ⟨some id,{geometry := .rect cx cy cw ch,style := {fill := gradientPaint g cx cy cw ch}}⟩)
  match s.backgroundBitmap with
  | none => withGradient
  | some (pic,b) =>
    let tiles := backgroundTiles id pic b s x y w h
    if s.colorClip == 0 then withGradient ++ tiles
    else withGradient.push (.clipped none identity ⟨cx,cy,cw,ch,identity⟩ tiles.toList)

/-- The two colours of a 3D border (CSS Backgrounds 3 §4.2 leaves them to the user
agent): the colour moved 60% of the way to white, and 60% of the colour. -/
def lighter (c : Color) : Color := ⟨c.r+(1-c.r)*0.6,c.g+(1-c.g)*0.6,c.b+(1-c.b)*0.6⟩
def darker (c : Color) : Color := ⟨c.r*0.6,c.g*0.6,c.b*0.6⟩

/-- The bands of one side of a border across its width, from the outer edge (0) to the inner
edge (1), each with its colour (CSS Backgrounds 3 §4.2). `start` is the top or the left side.
`outset` and `ridge` are light at the top and left, `inset` and `groove` dark; `groove` and
`ridge` are two halves; `double` is two lines of a third each, solid below 3 px. -/
def borderBands (st : BorderStyle) (c : Color) (start : Bool) (width : Float) : List (Float × Float × Color) :=
  let (near,far) := if start then (lighter c,darker c) else (darker c,lighter c)
  match st with
  | .none => []
  | .outset => [(0,1,near)]
  | .inset => [(0,1,far)]
  | .ridge => [(0,0.5,near),(0.5,1,far)]
  | .groove => [(0,0.5,far),(0.5,1,near)]
  | .double => if width < 3 then [(0,1,c)] else
      let line := (width/3).round/width
      [(0,line,c),(1-line,1,c)]
  | _ => [(0,1,c)]

private def sameBands (a b : List (Float × Float × Color)) : Bool :=
  a.length == b.length && (a.zip b).all fun ((a0,a1,ca),(b0,b1,cb)) =>
    a0 == b0 && a1 == b1 && ca.r == cb.r && ca.g == cb.g && ca.b == cb.b

/-- Dashes or dots along one side, `length` long and `thick` wide (CSS Backgrounds 3 §4.2:
the spacing is the user agent's): dots `thick` long with gaps of `thick`, dashes 3 x `thick`
with equal gaps, the gaps stretched so that the side starts and ends with a mark. Each is
`(offset, length)` along the side. -/
def dashMarks (dotted : Bool) (length thick : Float) : Array (Float × Float) := Id.run do
  if length <= 0 || thick <= 0 then return #[]
  let mark := if dotted then thick else 3*thick
  if length <= mark then return #[(0,length)]
  let n := (((length+mark)/(2*mark)).round).toUInt64.toNat |> max 2 |> min 4096
  let gap := (length-n.toFloat*mark)/(n.toFloat-1)
  let mut out := #[]
  for i in [0:n] do out := out.push (i.toFloat*(mark+gap), mark)
  return out

/-- The border of a border box at `(x,y)`, size `w` by `h`. Each side has its own style and
colour. Where two sides meet with the same bands, the top and bottom sides take the corner,
as rectangles; where they differ, the corner is split on its diagonal (CSS Backgrounds 3
§4.5 leaves the join to the user agent; browsers split it), with polygons. Dotted and dashed
sides are marks along the side, without the diagonal. -/
def borderNodes (id : Nat) (s : Computed) (x y w h : Float) : Array Node := Id.run do
  let b := s.borderEdges
  if !s.visible || w <= 0 || h <= 0 || !s.hasBorder then return #[]
  let st := s.borderStyles
  let pc := s.borderColors
  let bands := fun (style : BorderStyle) (paint : BorderColor) (start : Bool) (thick : Float) =>
    if thick <= 0 then [] else match paint.resolve s.color with
      | some c => borderBands style c start thick
      | none => []
  let top := bands st.top pc.top true b.top
  let right := bands st.right pc.right false b.right
  let bottom := bands st.bottom pc.bottom false b.bottom
  let left := bands st.left pc.left true b.left
  -- a corner is split when the two sides' bands differ and both are drawn
  let split := fun (p q : List (Float × Float × Color)) => !p.isEmpty && !q.isEmpty && !sameBands p q
  let tl := split top left
  let tr := split top right
  let bl := split bottom left
  let br := split bottom right
  let paint := fun (c : Color) (g : Geometry) => Node.paint ⟨some id,{geometry := g,style := {fill := .solid c}}⟩
  let quad := fun (c : Color) (p : List Point) =>
    -- an axis-aligned quadrilateral is drawn as a rectangle (exact edges)
    match p with
    | [a,b',c',d] =>
      if a.y == b'.y && c'.y == d.y && a.x == d.x && b'.x == c'.x then
        (if b'.x > a.x && d.y > a.y then #[paint c (.rect a.x a.y (b'.x-a.x) (d.y-a.y))] else #[])
      else #[paint c (.polygon p)]
    | _ => #[]
  let mut out : Array Node := #[]
  let marks := fun (style : BorderStyle) => style == .dotted || style == .dashed
  -- top: x runs from the left corner to the right corner
  for (f0,f1,c) in top do
    if marks st.top then
      for (o,l) in dashMarks (st.top == .dotted) w b.top do
        out := out.push (paint c (.rect (x+o) y l b.top))
    else
      let ol := if tl then x+f0*b.left else x
      let il := if tl then x+f1*b.left else x
      let or' := if tr then x+w-f0*b.right else x+w
      let ir := if tr then x+w-f1*b.right else x+w
      out := out ++ quad c [⟨ol,y+f0*b.top⟩,⟨or',y+f0*b.top⟩,⟨ir,y+f1*b.top⟩,⟨il,y+f1*b.top⟩]
  for (f0,f1,c) in bottom do
    if marks st.bottom then
      for (o,l) in dashMarks (st.bottom == .dotted) w b.bottom do
        out := out.push (paint c (.rect (x+o) (y+h-b.bottom) l b.bottom))
    else
      let ol := if bl then x+f0*b.left else x
      let il := if bl then x+f1*b.left else x
      let or' := if br then x+w-f0*b.right else x+w
      let ir := if br then x+w-f1*b.right else x+w
      out := out ++ quad c [⟨il,y+h-f1*b.bottom⟩,⟨ir,y+h-f1*b.bottom⟩,⟨or',y+h-f0*b.bottom⟩,⟨ol,y+h-f0*b.bottom⟩]
  -- left and right: between the top and the bottom sides, or to the diagonal of a split corner
  for (f0,f1,c) in left do
    if marks st.left then
      for (o,l) in dashMarks (st.left == .dotted) (h-b.top-b.bottom) b.left do
        out := out.push (paint c (.rect x (y+b.top+o) b.left l))
    else
      let ot := if tl then y+f0*b.top else y+b.top
      let it := if tl then y+f1*b.top else y+b.top
      let ob := if bl then y+h-f0*b.bottom else y+h-b.bottom
      let ib := if bl then y+h-f1*b.bottom else y+h-b.bottom
      out := out ++ quad c [⟨x+f0*b.left,ot⟩,⟨x+f1*b.left,it⟩,⟨x+f1*b.left,ib⟩,⟨x+f0*b.left,ob⟩]
  for (f0,f1,c) in right do
    if marks st.right then
      for (o,l) in dashMarks (st.right == .dotted) (h-b.top-b.bottom) b.right do
        out := out.push (paint c (.rect (x+w-b.right) (y+b.top+o) b.right l))
    else
      let ot := if tr then y+f0*b.top else y+b.top
      let it := if tr then y+f1*b.top else y+b.top
      let ob := if br then y+h-f0*b.bottom else y+h-b.bottom
      let ib := if br then y+h-f1*b.bottom else y+h-b.bottom
      out := out ++ quad c [⟨x+w-f1*b.right,it⟩,⟨x+w-f0*b.right,ot⟩,⟨x+w-f0*b.right,ob⟩,⟨x+w-f1*b.right,ib⟩]
  return out

-- Dots and dashes start and end the side: 100 px of 2 px dots is 26 dots 3.92 px apart.
#guard (dashMarks true 100 2).size == 26
#guard (dashMarks true 100 2).back?.map (fun (o,l) => o+l) == some 100
#guard (dashMarks false 10 5) == #[(0,10)]
-- double: two lines of a third each; groove: dark outside at the top, light outside at the bottom
#guard (borderBands .double ⟨1,0,0⟩ true 9).map (fun (a,b,_) => ((a*9).round,(b*9).round)) == [(0,3),(6,9)]
#guard (borderBands .groove ⟨1,1,1⟩ true 4).map (fun (_,_,c) => c.r) == [0.6,1]
#guard (borderBands .groove ⟨1,1,1⟩ false 4).map (fun (_,_,c) => c.r) == [1,0.6]

/-- Background, then border, of a border box. None for a box whose mask image is not drawn
(`Computed.masked`): unmasked, the background of an icon would be a filled box. -/
private def decorations (id : Nat) (s : Computed) (x y w h : Float) : Array Node :=
  if s.masked then #[] else background id s x y w h ++ borderNodes id s x y w h

/-- Kind: safety of the paint (no undrawn mask shows as a filled box). Says: a box whose
mask image is not drawn paints no background and no border. Does not say: anything about
its content or its layout, which are as before. -/
theorem decorations_masked (id : Nat) (s : Computed) (x y w h : Float) (hm : s.masked = true) :
    decorations id s x y w h = #[] := by
  simp [decorations, hm]

/-- Kind: property (pages with no such mask pay nothing). Says: with no undrawn mask the
decorations are the background and the border, as before. -/
theorem decorations_plain (id : Nat) (s : Computed) (x y w h : Float) (hm : s.masked = false) :
    decorations id s x y w h = background id s x y w h ++ borderNodes id s x y w h := by
  simp [decorations, hm]

/-- The content of a replaced element that Lean decoded or drew: the image of an
`img`, and in time the poster or frame of a `video` or the bitmap of a `canvas`.
`id` names the bitmap in the paint table, so one bitmap used twice is stored once. -/
structure Picture where
  id : Nat
  bitmap : Bitmap
  /-- The size of the image in CSS pixels, when `bitmap` holds fewer pixels than the image
  has (a host that keeps a large image reduced); none: the size of `bitmap`. -/
  natural : Option (Nat × Nat) := none
/-- The picture of an element, by DOM node. `none` when it has none, or when its
image is missing, broken or refused: an `img` then shows its `alt` text. -/
abbrev Pictures := Nat → Option Picture
def noPictures : Pictures := fun _ => none

/-- No maximum (`max-width: none`). -/
def unbounded : Float := 1.0e30

/-- CSS 2.1 §10.4, the table for a replaced element whose `width` and `height` are
both auto: the intrinsic size `w` by `h` within the limits, with its ratio kept where
the limits allow it. -/
def constrainBoth (w h minW maxW minH maxH : Float) : Float × Float :=
  let maxW := max minW maxW
  let maxH := max minH maxH
  if w <= 0 || h <= 0 then (min maxW (max minW w),min maxH (max minH h))
  else if w > maxW && h > maxH then
    if maxW/w <= maxH/h then (maxW,max minH (maxW*h/w)) else (max minW (maxH*w/h),maxH)
  else if w < minW && h < minH then
    if minW/w <= minH/h then (min maxW (minH*w/h),minH) else (minW,min maxH (minW*h/w))
  else if w < minW && h > maxH then (minW,maxH)
  else if w > maxW && h < minH then (maxW,minH)
  else if w > maxW then (maxW,max (maxW*h/w) minH)
  else if w < minW then (minW,min (minW*h/w) maxH)
  else if h > maxH then (max (maxH*w/h) minW,maxH)
  else if h < minH then (min (minH*w/h) maxW,minH)
  else (w,h)

/-- CSS 2.1 §10.3.2 and §10.6.2, with the limits of §10.4 and §10.7: the used content
width and height of a replaced element. `intrinsic` is the size of its content when it
has one, which gives the ratio too; with none, 300 by 150. `available` is the width of
the containing block. It is 0 while widths are measured, and then a percentage counts
as auto (CSS Sizing 3 §5.2.1). A percentage height counts as auto: this profile has
no definite containing block height. -/
def replacedNatural (s : Computed) (intrinsic : Option (Float × Float)) (available : Float) : Float × Float :=
  let horizontal := fun (l : CSS.Length) => match l with
    | .px n => some n
    | .percent p => if available <= 0 then none else some (available*p)
    -- `stretch` (CSS Sizing 4 §6.1): the margin box fills the containing block
    | .stretch => if available <= 0 then none else
      some (max 0 (available-s.margin.left-s.margin.right-s.borderEdges.left-s.borderEdges.right-s.padding.left-s.padding.right))
    | _ => none
  let vertical := fun (l : CSS.Length) => match l with | .px n => some n | _ => none
  let minW := (horizontal s.minWidth).getD 0
  let maxW := (horizontal s.maxWidth).getD unbounded
  let minH := (vertical s.minHeight).getD 0
  let maxH := (vertical s.maxHeight).getD unbounded
  -- §10.4: a minimum wins over a maximum.
  let clampW := fun (w : Float) => max 0 (max minW (min maxW w))
  let clampH := fun (h : Float) => max 0 (max minH (min maxH h))
  let ratio := intrinsic.bind fun (w,h) => if w > 0 && h > 0 then some (w/h) else none
  match horizontal s.width,vertical s.height with
  | some w,some h => (clampW w,clampH h)
  | some w,none =>
    let w := clampW w
    (w,clampH (match ratio with | some r => w/r | none => (intrinsic.map Prod.snd).getD 150))
  | none,some h =>
    let h := clampH h
    (clampW (match ratio with | some r => h*r | none => (intrinsic.map Prod.fst).getD 300),h)
  | none,none => match intrinsic with
    | some (w,h) => constrainBoth w h minW maxW minH maxH
    | none => (clampW 300,clampH 150)

/-- The used content width and height of a replaced element: `replacedNatural`, or with
`aspect-ratio` (CSS Sizing 4 §5) the sizes that the preferred ratio gives (`Ratio`, on
layout units): a given width or height gives the other, and with both auto the natural
width is taken within the limits of both axes. `aspect-ratio: auto <ratio>` keeps the
ratio of content that has one. An element with no `aspect-ratio` costs one test. -/
def replacedSize (s : Computed) (intrinsic : Option (Float × Float)) (available : Float) : Float × Float :=
  match s.pos.ratio with
  | none => replacedNatural s intrinsic available
  | some (rn,rd) =>
    let natural := intrinsic.any fun (w,h) => w > 0 && h > 0
    if rn == 0 || rd == 0 || (s.pos.ratioAuto && natural) then replacedNatural s intrinsic available else
    let horizontal := fun (l : CSS.Length) => match l with
      | .px n => some n
      | .percent p => if available <= 0 then none else some (available*p)
      | .stretch => if available <= 0 then none else
        some (max 0 (available-s.margin.left-s.margin.right-s.borderEdges.left-s.borderEdges.right-s.padding.left-s.padding.right))
      | _ => none
    let vertical := fun (l : CSS.Length) => match l with | .px n => some n | _ => none
    let minW := LU.ofPx (max 0 ((horizontal s.minWidth).getD 0))
    let maxW := (horizontal s.maxWidth).map fun m => LU.ofPx (max 0 m)
    let minH := LU.ofPx (max 0 ((vertical s.minHeight).getD 0))
    let maxH := (vertical s.maxHeight).map fun m => LU.ofPx (max 0 m)
    let size : Int × Int := (match horizontal s.width,vertical s.height with
      | some w,some h => (LU.clamp minW maxW (LU.ofPx (max 0 w)),LU.clamp minH maxH (LU.ofPx (max 0 h)))
      | some w,none => Ratio.fromWidth rn rd (LU.ofPx (max 0 w)) minW maxW minH maxH
      | none,some h => Ratio.fromHeight rn rd (LU.ofPx (max 0 h)) minW maxW minH maxH
      | none,none => Ratio.autoSize rn rd (LU.ofPx (max 0 ((intrinsic.map Prod.fst).getD 300))) minW maxW minH maxH)
    (LU.toPx size.1,LU.toPx size.2)

/-- A replaced element with no decoded content here, and its natural size when it has one.
A `canvas` has the natural size of its `width` and `height` attributes, 300 by 150 without
them (HTML §4.12.5.1). An `iframe`, and a `video` with no frame or poster drawn, are
replaced elements (HTML §15.4.1) with no natural size and no natural ratio: `some none`,
so `replacedSize` gives them the default object size, 300 by 150 (CSS Images 3 §4.1), and
a `width` without a `height` keeps the default height (as `video-intrinsic-width-height`
of WPT says). Their boxes are laid out as a picture's are, and are empty: the engine does
not draw a child document or a video frame in its container yet. -/
def blankReplaced (n : DOM.Node) : Option (Option (Float × Float)) :=
  if DOM.Dom.isHtmlElement n "canvas" then
    let whole := fun (name : String) (fallback : Nat) =>
      let digits := ((CSS.attrValue n name).toList.dropWhile fun c => c == ' ' || c == '\t' || c == '\n').takeWhile Char.isDigit
      if digits.isEmpty || digits.length > 5 then fallback else digits.foldl (fun k c => k*10+(c.toNat-48)) 0
    some (some (Float.ofNat (whole "width" 300),Float.ofNat (whole "height" 150)))
  else if DOM.Dom.isHtmlElement n "iframe" || DOM.Dom.isHtmlElement n "video" then some none
  else none

/-- Kind: property. Says: an `iframe` is a replaced box with no natural size. -/
theorem blankReplaced_iframe (n : DOM.Node) (h : DOM.Dom.isHtmlElement n "iframe" = true) :
    blankReplaced n = some none := by
  have hl : n.lname = "iframe" := by simp [DOM.Dom.isHtmlElement] at h; exact h.2
  have hc : DOM.Dom.isHtmlElement n "canvas" = false := by simp [DOM.Dom.isHtmlElement, hl]
  simp [blankReplaced, hc, h]

/-- Kind: value. Says: a replaced box with no natural size, no `width` or `height` and no
limits is 300 by 150, the default object size (CSS Images 3 §4.1). -/
theorem replacedNatural_default (s : Computed) (a : Float) (hw : s.width = .auto) (hh : s.height = .auto)
    (hmw : s.minWidth = .auto) (hxw : s.maxWidth = .auto) (hmh : s.minHeight = .auto) (hxh : s.maxHeight = .auto) :
    replacedNatural s none a = (max 0 (max 0 (min unbounded 300)), max 0 (max 0 (min unbounded 150))) := by
  simp [replacedNatural, hw, hh, hmw, hxw, hmh, hxh]

/-- The intrinsic size of a picture: its pixels, one CSS pixel each; for a picture held
reduced, the size of the image it was made from (`natural`). -/
def Picture.size (p : Picture) : Float × Float :=
  match p.natural with
  | some (w,h) => (Float.ofNat w,Float.ofNat h)
  | none => (Float.ofNat p.bitmap.width,Float.ofNat p.bitmap.height)

/-- A picture that is not held reduced has the size of its bitmap, as before. -/
theorem Picture.size_whole (p : Picture) (h : p.natural = none) :
    p.size = (Float.ofNat p.bitmap.width,Float.ofNat p.bitmap.height) := by
  simp [Picture.size, h]

/-- CSS Images 3 §5.5: the scale of content of `iw` by `ih` in a box of `w` by `h`. -/
def fitScale (fit : ObjectFit) (iw ih w h : Float) : Float × Float :=
  match fit with
  | .fill => (w/iw,h/ih)
  | .contain => let k := min (w/iw) (h/ih); (k,k)
  | .cover => let k := max (w/iw) (h/ih); (k,k)
  | .none => (1,1)
  | .scaleDown => let k := min 1 (min (w/iw) (h/ih)); (k,k)

/-- CSS Images 3 §5.6 resolves position percentages against the space left by the
fitted object. That space can be negative when the object exceeds the box. -/
def pictureOffset (position : Option (CSS.Length × CSS.Length)) (roomX roomY : Float) : Float × Float :=
  match position with
  | none => (roomX/2,roomY/2)
  | some (x,y) => ((CSS.resolve roomX x).getD (roomX/2), (CSS.resolve roomY y).getD (roomY/2))

theorem pictureOffset_default (roomX roomY : Float) :
    pictureOffset none roomX roomY = (roomX/2,roomY/2) := rfl

theorem pictureOffset_percent (roomX roomY x y : Float) :
    pictureOffset (some (.percent x,.percent y)) roomX roomY = (roomX*x,roomY*y) := rfl

/-- Paint the fitted image at its object position, clipped to its content box. -/
def pictureNodes (id : Nat) (s : Computed) (picture : Picture) (x y w h : Float) : List Node :=
  let (iw,ih) := picture.size
  if !s.visible || w <= 0 || h <= 0 || iw <= 0 || ih <= 0 then [] else
  let (sx,sy) := fitScale s.objectFit iw ih w h
  let (offsetX,offsetY) := pictureOffset s.objectPosition (w-iw*sx) (h-ih*sy)
  let dx := x+offsetX
  let dy := y+offsetY

  let left := max x dx
  let top := max y dy
  let right := min (x+w) (dx+iw*sx)
  let bottom := min (y+h) (dy+ih*sy)
  if right <= left || bottom <= top then [] else
  -- `map` goes to pixels of the bitmap: for a picture held reduced, a pixel of the bitmap
  -- covers `iw/width` by `ih/height` pixels of the image.
  let (kx,ky) := match picture.natural with
    | some _ => (Float.ofNat picture.bitmap.width/iw,Float.ofNat picture.bitmap.height/ih)
    | none => (1,1)
  let map : Transform := ⟨kx/sx,0,0,ky/sy,-dx*kx/sx,-dy*ky/sy⟩
  let paint : Paint := .image ⟨map,picture.id,picture.bitmap⟩
  [Node.paint ⟨some id,{geometry := .rect left top (right-left) (bottom-top),style := {fill := paint}}⟩]

/-- A replaced element's margin box at the origin, for content `w` by `h`: its outer
width and height, and its background, border and content. `content` paints the
content box at the point it is given. -/
def replacedBox (id : Nat) (s : Computed) (w h : Float) (content : Float → Float → List Node) :
    Float × Float × List Node :=
  let m := s.margin
  let b := s.borderEdges
  let p := s.padding
  let bw := b.left+p.left+w+p.right+b.right
  let bh := b.top+p.top+h+p.bottom+b.bottom
  (m.left+bw+m.right,m.top+bh+m.bottom,
   (decorations id s m.left m.top bw bh).toList ++ content (m.left+b.left+p.left) (m.top+b.top+p.top))

/-- CSS 2.1 §10.3.3: how far `margin-left: auto` moves a block-level box whose margin
box is `outer` wide in a containing block `available` wide. Both auto: half the room
each, so the box is centred; only the left: all of it. No room: none. -/
def autoMarginShift (s : Computed) (available outer : Float) : Float :=
  let free := available-outer
  if free <= 0 || !s.autoMarginLeft then 0
  else if s.autoMarginRight then free/2 else free

/-- Resolve the used left margin of a horizontal block in normal flow.
With specified margins the containing block's direction selects the side that
absorbs the remaining space. On overflow, auto margins first become zero
(CSS 2.2 §10.3.3). -/
def blockMarginShift (s : Computed) (rtl : Bool) (available outer : Float) : Float :=
  let free := available-outer
  if rtl && (free < 0 || (!s.autoMarginLeft && !s.autoMarginRight)) then free
  else autoMarginShift s available outer

#guard blockMarginShift {} true 100 52 == 48
#guard blockMarginShift {} false 100 52 == 0
#guard blockMarginShift {autoMarginLeft := true, autoMarginRight := true} true 100 40 == 30
#guard blockMarginShift {autoMarginRight := true} true 100 120 == -20

/-- The width that margins, borders and padding add to a box. -/
private def horizontalEdges (s : Computed) : Float :=
  s.margin.left+s.margin.right+s.borderEdges.left+s.borderEdges.right+s.padding.left+s.padding.right

/-- The owner of a text item, for paint and for layout fragments. A control's
anonymous label is painted for the control, with no node of its own in the arena.
Its fragments use the first index outside the layout arena. They still take space,
for example when sizing an auto-width button. -/
structure TextSource where
  paint : Nat
  geometry : Nat
  deriving Repr

def TextSource.node (id : Nat) : TextSource := ⟨id,id⟩

def TextSource.control (dom : Dom) (id : Nat) : TextSource := ⟨id,dom.size⟩

inductive Inline where
  | word (source : TextSource) (style : Computed) (text : String) (start : Nat)
  | space (source : TextSource) (style : Computed)
  | lineBreak (style : Computed)
  /-- The edge of a block box inside an inline box (CSS 2.1 §9.2.1.1): it ends the line
  when the line has content, and is nothing on an empty line. -/
  | blockBreak (style : Computed)
  /-- A replaced element (`img`, inline `svg`): its margin box and paint at the origin. -/
  | replaced (source : Nat) (style : Computed) (width height : Float) (nodes : List Node)
  /-- An `inline-block` from `openAtomic` to `closeAtomic`, laid out (`atomize`): its
  margin box and its content at the origin. -/
  | atomic (source : Nat) (style : Computed) (width height : Float) (inner : Result)
  /-- Bounds of an `inline-block` in the flat list that `inlineItems` gives. -/
  | openAtomic (source : Nat) (style : Computed)
  | closeAtomic
  /-- A bidi control character that an inline box with `unicode-bidi` adds (CSS
  Writing Modes 3 §2.4.2): no width, no paint. -/
  | bidiMark (c : Char)
  /-- An absolutely positioned element inside inline content: no width, no paint; its
  place in the line is its static position (`Result.pending`). -/
  | outOfFlow (source : Nat)
  /-- The start of an inline box (a `span`, an `a`; CSS 2.1 §9.2.2): the line gives room
  for its left margin, border and padding (`inlineLead`). `continued`: the box began on an
  earlier line, and has no edge here. -/
  | openInline (source : Nat) (style : Computed) (continued : Bool)
  /-- The end of an inline box: room for its right padding, border and margin. -/
  | closeInline (source : Nat) (style : Computed)
  deriving Repr
instance : Inhabited Inline := ⟨.closeAtomic⟩

/-- What the start of an inline box adds to its line: the left margin, border and padding. -/
def inlineLead (s : Computed) : Float := s.margin.left+s.borderEdges.left+s.padding.left

/-- What the end of an inline box adds to its line: the right padding, border and margin. -/
def inlineTrail (s : Computed) : Float := s.padding.right+s.borderEdges.right+s.margin.right

/-- Split one CSS text token at its internal UAX 14 break opportunities, retaining
code-point offsets for selection. CSS spaces and explicit line breaks are handled
by the caller. Plain ASCII letters and digits have no internal break. -/
def wordPieces (word : String) (mode : Unicode.LineBreak.Mode := .strict) : List (Nat × String) :=
  let chars := word.toList
  if chars.all (fun c => c.isAlpha || c.isDigit) then [(0, word)] else Id.run do
    let cs := chars.toArray
    let mut out : List (Nat × String) := []
    let mut from_ := 0
    for i in Unicode.LineBreak.breaks cs mode do
      if i < cs.size then
        out := (from_, String.ofList (cs.extract from_ i).toList) :: out
        from_ := i
    out := (from_, String.ofList (cs.extract from_ cs.size).toList) :: out
    return out.reverse

/-- Plain alphanumeric text keeps its original token and offset in every line-break mode. -/
theorem wordPieces_alnum (word : String) (mode : Unicode.LineBreak.Mode)
    (alnum : word.toList.all (fun c => c.isAlpha || c.isDigit) = true) :
    wordPieces word mode = [(0, word)] := by
  simp [wordPieces, alnum]

#print axioms wordPieces_alnum

#guard wordPieces "word-break" == [(0, "word-"), (5, "break")]
#guard wordPieces "alpha\u200Bbeta" == [(0, "alpha\u200B"), (6, "beta")]
#guard wordPieces "alpha\u2003beta" == [(0, "alpha\u2003"), (6, "beta")]
#guard wordPieces "alpha\u2060beta" == [(0, "alpha\u2060beta")]
#guard wordPieces "alpha\u00A0beta" == [(0, "alpha\u00A0beta")]
#guard wordPieces "مرحبا" == [(0, "مرحبا")]
#guard (wordPieces "你好，世界").map (·.2) == ["你", "好，", "世", "界"]
-- Small kana and the middle dot do not start a line (UAX 14 NS, CJ as NS).
#guard (wordPieces "こんにちは世界・カタカナ・漢字").map (·.2) ==
  ["こ", "ん", "に", "ち", "は", "世", "界・", "カ", "タ", "カ", "ナ・", "漢", "字"]
#guard (wordPieces "Unicode漢字").map (·.1) == [0, 7, 8]
-- `line-break: normal` lets a small kana start a line (CSS Text 3 §5.3)
#guard (wordPieces "文文ぁ字" .normal).map (·.2) == ["文", "文", "ぁ", "字"]
#guard (wordPieces "文文ぁ字").map (·.2) == ["文", "文ぁ", "字"]

/-- The UAX 14 tailoring of a box's `line-break`. -/
def lineBreakMode (s : Computed) : Unicode.LineBreak.Mode :=
  match s.pos.lineBreak with
  | .auto | .strict => .strict
  | .normal => .normal
  | .loose => .loose

/-- The visible fallback for controls that reach the text shaper (CSS Text 3 §4).
Use the replacement glyph so a font without Control Pictures still draws them.
The one-code-point substitution retains text offsets. -/
private def visibleControl (c : Char) : Char :=
  let n := c.toNat
  if (0x7F ≤ n && n ≤ 0x9F) || (n < 0x20 && n != 0x09 && n != 0x0A && n != 0x0D) then
    Char.ofNat 0xFFFD
  else c

#guard (visibleControl (Char.ofNat 0x01)).toNat == 0xFFFD
#guard (visibleControl (Char.ofNat 0x7F)).toNat == 0xFFFD
#guard (visibleControl (Char.ofNat 0x85)).toNat == 0xFFFD
#guard visibleControl '\t' == '\t' && visibleControl '\n' == '\n' &&
  visibleControl '\r' == '\r' && visibleControl (Char.ofNat 0x200D) == Char.ofNat 0x200D

private def textItems (id : TextSource) (style : Computed) (text : String) : List Inline := Id.run do
  let mut result : List Inline := []
  let mut word := ""
  let mut start := 0
  let mut index := 0
  let mut spaced := false
  -- The column in the line, for the tab stops of preformatted text (every 8 columns).
  let mut column := 0
  for c in text.toList do
    if [' ','\n','\r','\t'].contains c || c.toNat == 12 then
      if !word.isEmpty then
        for (off, piece) in wordPieces word (lineBreakMode style) do result := .word id style piece (start+off) :: result
        word := ""
      if c == '\n' && (style.preformatted || style.preserveSegmentBreaks) then
        result := .lineBreak style :: result
        column := 0
      else if style.preformatted then
        if c != '\r' then
          let count := if c == '\t' then 8-column%8 else 1
          for _ in [0:count] do result := .space id style :: result
          column := column+count
      else if !spaced then
        result := .space id style :: result
      spaced := true
    else
      if word.isEmpty then start := index
      -- `text-transform`: one character for one, so positions in the text stand
      let shown := match style.pos.textTransform with
        | .none => c
        | .uppercase => TextCase.upper c
        | .lowercase => TextCase.lower c
        | .capitalize => if word.isEmpty then TextCase.upper c else c
      word := word.push (visibleControl shown)
      spaced := false
      column := column+1
    index := index+1
  if !word.isEmpty then
    for (off, piece) in wordPieces word (lineBreakMode style) do result := .word id style piece (start+off) :: result
  return result.reverse

/-- Collapsing intervening spaces does not remove a preserved blank line. -/
theorem textItems_preLine_blankLine (id : TextSource) (style : Computed)
    (keep : style.preserveSegmentBreaks = true) (collapse : style.preformatted = false) :
    textItems id style "\n \n" = [.lineBreak style, .lineBreak style] := by
  simp [textItems, keep, collapse]

#print axioms textItems_preLine_blankLine

-- Compare tokens and source offsets, keeping geometry and the inline breaker out of this check.
#guard (textItems (.node 1) {preserveSegmentBreaks := true} "a  b\n \n  c").map
    (fun
      | .word _ _ word start => (word, start)
      | .lineBreak _ | .blockBreak _ => ("\n", 0)
      | .space .. => (" ", 0)
      | _ => ("?", 0)) == [("a", 0), (" ", 0), ("b", 3), ("\n", 0), ("\n", 0), ("c", 9)]

/-- What an `img` with no picture shows: its `alt` text in brackets, nothing for
`alt=""` (an image that adds nothing), and `[image]` with no `alt`. -/
private def altItems (id : Nat) (s : Computed) (n : DOM.Node) : Array Inline :=
  if !CSS.hasAttribute n "alt" then (textItems (.node id) s "[image]").toArray
  else
    let alt := CSS.attrValue n "alt"
    if alt.isEmpty then #[] else (textItems (.node id) s s!"[{alt}]").toArray

/-- What a form control shows in its box (`CSS.controlText`): its value or label on one
line in its own colour, a placeholder in the grey of other engines (`#757575`). Nothing for
any other element. -/
private def controlItems (dom : Dom) (id : Nat) (s : Computed) : Array Inline :=
  match CSS.controlText dom id with
  | none => #[]
  | some (text, placeholder) =>
    let grey : Color := ⟨0.459,0.459,0.459⟩
    let pos := {s.pos with nowrap := true}
    let t : Computed := { s with
      background := none
      underline := false
      preformatted := false
      preserveSegmentBreaks := false
      color := if placeholder then grey else s.color
      pos
    }
    (textItems (.control dom id) t text).toArray

/-- An inline element's background goes behind its text (CSS 2.1 §14.2). Text has no
background of its own, so its words and spaces take the element's. -/
private def withBackground (s : Computed) : Inline → Inline
  | .word id t text start => if t.background.isNone then .word id {t with background := s.background} text start else .word id t text start
  | .space id t => if t.background.isNone then .space id {t with background := s.background} else .space id t
  | other => other

/-- CSS Writing Modes 3 §2.4.2: the bidi control characters at the start of an
inline box with `unicode-bidi`, and at its end. -/
def bidiOpen (s : Computed) : Array Char :=
  let rtl := s.direction == .rtl
  let iso := if rtl then '\u2067' else '\u2066'
  let emb := if rtl then '\u202B' else '\u202A'
  let ovr := if rtl then '\u202E' else '\u202D'
  match s.unicodeBidi with
  | .normal => #[]
  | .embed => #[emb]
  | .isolate => #[iso]
  | .bidiOverride => #[ovr]
  | .isolateOverride => #[iso, ovr]
  | .plaintext => #['\u2068']
def bidiClose (s : Computed) : Array Char :=
  match s.unicodeBidi with
  | .normal => #[]
  | .embed | .bidiOverride => #['\u202C']
  | .isolate | .plaintext => #['\u2069']
  | .isolateOverride => #['\u202C', '\u2069']

/-- Inline descendants are flattened in DOM order; the nesting budget is a
profile error, never a silent truncation. Siblings use a fold. The recursive
call receives the predecessor `fuel`; the compiled sibling fold is a loop.
This lower-level API accepts arbitrary fuel and therefore has stack depth
O(fuel), not a universal constant bound. Production rendering shares the
fixed 64-level budget from `render` with `block`; FontRequests uses fuel 1
only for a text node. See `docs/20261103-layout-stack-audit.md`. -/
def inlineItems (dom : Dom) (styles : Array Computed) (embedding : Embedding) (pictures : Pictures)
    (available : Float) : Nat → Nat → Except String (Array Inline)
  | 0, _ => throw "unsupported HTML nesting depth (maximum 64)"
  | fuel+1, id => do
    let n := dom.get id
    let s := styles[id]!
    if s.display == .none then return #[]
    if n.type == .text then return (textItems (.node id) s n.data).toArray
    if n.type != .element then return #[]
    if s.pos.isAbsolute then return #[.outOfFlow id]
    -- A replaced element with a picture: an `img`, and later a `video` or `canvas`.
    if let some picture := pictures id then
      let (w,h) := replacedSize s (some picture.size) available
      let (ow,oh,nodes) := replacedBox id s w h (fun x y => pictureNodes id s picture x y w h)
      return #[.replaced id s ow oh nodes]
    -- A `canvas`: a replaced box of its natural size, with nothing drawn in it here.
    if let some size := blankReplaced n then
      let (w,h) := replacedSize s size available
      let (ow,oh,nodes) := replacedBox id s w h (fun _ _ => [])
      return #[.replaced id s ow oh nodes]
    -- An image that is missing, broken or refused stands as its description, and stays a link.
    if n.lname == "img" then return altItems id s n
    if n.lname == "br" then return #[.lineBreak s]
    if n.ns == some DOM.svgNS then
      let (width,height) ← svgSize n s available
      let inner ← if width <= 0 || height <= 0 then pure [] else embedding id s width height
      -- The SVG producer paints the root's background itself.
      let (ow,oh,nodes) := replacedBox id {s with background := none} width height
        (fun x y => [.group none ⟨1,0,0,1,x,y⟩ inner])
      return #[.replaced id s ow oh nodes]
    -- A block inside an inline (old pages often have one) breaks the line around it.
    -- An inline-block is one atomic box: `atomize` lays out what is between its bounds.
    -- An inline box with `unicode-bidi` is wrapped in its bidi control characters.
    -- An inline box is between its bounds, which give it its boxes and its edges on the lines.
    -- A block box inside an inline box (CSS 2.1 §9.2.1.1) keeps its own box: it is laid out
    -- as an atomic box on a line of its own, as wide as the line (`AtomicFrame.opened`),
    -- with its background, borders, padding and size. Until 2026-11-23 only its contents
    -- were kept: `<a><div class=votearrow></div></a>` drew nothing (Hacker News).
    let sized := fun (l : CSS.Length) => match l with | .auto => false | _ => true
    -- a block of zero height with no border or padding collapses through (CSS 2.1 §8.3.1): no box
    let collapsing := (match s.height with | .px h => h == 0 | _ => false) && s.padding.top == 0 && s.padding.bottom == 0 &&
      s.borderEdges.top == 0 && s.borderEdges.bottom == 0
    let boxed := s.display.isBlockLevel && !collapsing && (sized s.width || sized s.height || s.background.isSome ||
      s.backgroundImage.isSome || s.backgroundGradient.isSome || s.borderEdges.top > 0 || s.borderEdges.bottom > 0 ||
      s.borderEdges.left > 0 || s.borderEdges.right > 0)
    let mut out : Array Inline := if boxed then #[.blockBreak s, .openAtomic id s]
      else if s.display.isBlockLevel then #[.lineBreak s]
      else if s.display == .inlineBlock then #[.openAtomic id s]
      else (if s.display == .inline then #[.openInline id s false] else #[]) ++ (bidiOpen s).map .bidiMark
    for child in n.kids do out := out ++ (← inlineItems dom styles embedding pictures available fuel child)
    -- a form control's own text (its value, label or placeholder)
    out := out ++ controlItems dom id s
    if s.display == .inline && s.background.isSome && !s.masked then out := out.map (withBackground s)
    return if boxed then (out.push .closeAtomic).push (.blockBreak s)
      else if s.display.isBlockLevel then out.push (.lineBreak s)
      else if s.display == .inlineBlock then out.push .closeAtomic
      else out ++ (bidiClose s).map .bidiMark ++ (if s.display == .inline then #[.closeInline id s] else #[])

private def translate (x y : Float) : Transform := ⟨1,0,0,1,x,y⟩

/-- The paint of a glyph of text in style `s`: its colour; for bold text (`font-weight` of
600 and up) the outline is also stroked with the colour, which is the bold face the engine
makes from the regular one it holds (`FontSynthesis.embolden`: the stroke's width for the
font size; `scale` is px to the glyph's unit). Other text is painted as before. -/
def glyphStyle (s : Computed) (fontSize scale : Float) : Rendering.Style :=
  if FontSynthesis.isBold s.fontWeight && scale > 0 then
    let width := Float.ofNat (FontSynthesis.embolden (fontSize*64).round.toUInt32.toNat)/64
    {fill := .solid s.color, stroke := .solid s.color, strokeWidth := width/scale}
  else {fill := .solid s.color}

/-- The place of a glyph of text in style `s`: its outline scaled and moved to `(x,y)`, the
top of its line; for slanted text (`font-style: italic` or `oblique`) also sheared about
the baseline, `rise` px below `y`, which is the oblique face the engine makes
(`FontSynthesis.shear`: a point moves along the line by a quarter of its height above the
baseline). Upright text is placed as before. -/
def glyphTransform (s : Computed) (scale x y rise : Float) : Transform :=
  if s.oblique then
    let slant := Float.ofInt FontSynthesis.slantNum/Float.ofInt FontSynthesis.slantDen
    ⟨scale,0,-slant*scale,scale,x+slant*rise,y⟩
  else ⟨scale,0,0,scale,x,y⟩

private def glyphNodes (font : FontProfile) (run : GlyphRun) (s : Computed) : Array Node := Id.run do
  let mut out := #[]
  if !s.visible then return out
  let scale := run.fontSize/font.unitsPerEm
  for g in run.glyphs do
    for geometry in font.outline g.index do
      -- `rise`: text of a `sup` or `sub` (CSS 2.1 §10.8.1) drawn above or below the baseline
      let primitive : Primitive := {geometry,style := glyphStyle s run.fontSize scale,transform := glyphTransform s scale g.x (g.y-s.rise) (font.ascent*scale)}
      out := out.push (.paint ⟨some run.source,primitive⟩)
  if s.underline && !run.glyphs.isEmpty then
    let left := (run.glyphs[0]?).map (·.x) |>.getD 0
    let top := ((run.glyphs[0]?).map (·.y) |>.getD 0)-s.rise
    let width := run.glyphs.foldl (fun w g => w+g.advance) 0
    let thickness := max 1 (run.fontSize/14)
    let baseline := top+font.ascent*scale
    out := out.push (.paint ⟨some run.source,{geometry := .rect left (baseline+thickness) width thickness,style := {fill := .solid (s.decorationColor.getD s.color)}}⟩)
  return out

private def itemWidth (font : FontProfile) (rtl : Option Bool := none) : Inline → Except String Float
  | .word _ s text _ => do
    match ← font.word s text rtl with
    | none => return (font.advance*s.fontSize/font.unitsPerEm+s.letterSpacingPx)*Float.ofNat text.length
    | some word => return word.advance*s.fontSize/font.unitsPerEm
  | .replaced _ _ w _ _ | .atomic _ _ w _ _ => pure w
  | .openInline _ s continued => pure (if continued then 0 else inlineLead s)
  | .closeInline _ s => pure (inlineTrail s)
  | _ => pure 0

/-- A colour glyph as one rectangle filled with its image (`ColrRaster`), drawn at the
pixel size nearest to its em at `scale`; `none` when it has no colour or no image.
The image's pixels map onto the rectangle one to one when the size is whole. -/
def colourNode (source : Nat) (glyph : FontProvider.Glyph) (x y scale : Float) (color : Color) : Option Node := do
  let c ← glyph.colour
  let em := scale*c.em
  if !(em > 0) || !em.isFinite then none
  let px := max 1 (min 512 em.round.toUInt32.toNat)
  let image ← c.image px color
  let f := em/Float.ofNat px
  let toF := fun (v : Int) => if v < 0 then -(Float.ofNat v.natAbs) else Float.ofNat v.natAbs
  let left := x+f*toF image.left
  let top := y+scale*c.baseline+f*toF image.top
  let w := f*Float.ofNat image.bitmap.width
  let h := f*Float.ofNat image.bitmap.height
  let map : Transform := ⟨1/f,0,0,1/f,-left/f,-top/f⟩
  return .paint ⟨some source,{geometry := .rect left top w h,style := {fill := .image ⟨map,image.id,image.bitmap⟩}}⟩

private def shapedNodes (word : FontProvider.Word) (run : GlyphRun) (s : Computed)
    (left baseline width : Float) : Array Node := Id.run do
  if !s.visible then return #[]
  let scale := run.fontSize/word.unitsPerEm
  let mut out := #[]
  for (glyph,position) in word.glyphs.zip run.glyphs do
    if let some node := colourNode run.source glyph position.x (position.y-s.rise) scale s.color then
      out := out.push node
      continue
    for geometry in glyph.geometry do
      let place := glyphTransform s scale position.x (position.y-s.rise) (baseline-position.y)
      out := out.push (.paint ⟨some run.source,{geometry,style := glyphStyle s run.fontSize scale,transform := place}⟩)
  if s.underline && width > 0 then
    let thickness := max 1 (run.fontSize/14)
    out := out.push (.paint ⟨some run.source,{geometry := .rect left (baseline-s.rise+thickness) width thickness, style := {fill := .solid (s.decorationColor.getD s.color)}}⟩)
  return out

/-- A laid-out box moved by `(dx,dy)`: its paint in a translated group, its boxes and
its glyph positions moved by the same amount. -/
private def shiftResult (dx dy : Float) (r : Result) : Result :=
  let boxes := r.boxes.map fun b => {b with x := b.x+dx, y := b.y+dy}
  let runs := r.runs.map fun run => {run with glyphs := run.glyphs.map fun g => {g with x := g.x+dx, y := g.y+dy}}
  {r with nodes := #[.group none (translate dx dy) r.nodes.toList], boxes, runs,
          pending := r.pending.map fun p => {p with x := p.x+dx, y := p.y+dy},
          baseline := r.baseline.map (·+dy), lastBaseline := r.lastBaseline.map (·+dy)}

/-- CSS 2.1 §10.8.1: where the baseline of an atomic inline box is, from the top of its
margin box `height` high: for an inline-block, the baseline of its last line box when it
has one and does not clip; for an inline flex or grid container, its first baseline; else
its bottom margin edge. -/
private def atomicBaseline (s : Computed) (height : Float) (inner : Result) : Float :=
  let own := if s.display == .inlineBlock then (if s.clipOverflow then none else inner.lastBaseline) else inner.baseline
  match own with
  | some b => if b >= 0 && b <= height then b else height
  | none => height

/-- CSS 2.1 §10.6.1: the background of inline text covers its content area, the
font's ascent and descent, from `top`. -/
private def textBackground (font : FontProfile) (source : Nat) (s : Computed) (x top width : Float) : Array Node :=
  match s.background with
  | some c =>
    if !s.visible || width <= 0 then #[] else
    let (a,d) := font.metricsOf s
    #[.paint ⟨some source,{geometry := .rect x top width ((a+d)*s.fontSize/font.unitsPerEm),style := {fill := .solid c}}⟩]
  | none => #[]

/-- All inline participants share the line baseline, computed before any glyph
position or replaced-element position is emitted. -/
private def lineLayout (font : FontProfile) (items : Array (Float × Inline))
    (x y : Float) (strut : Option Computed) (dirs : Array (Option Bool) := #[]) : Except String Result := do
  let mut ascent : Float := 0
  let mut descent : Float := 0
  let mut tallTop : Float := 0
  let mut tallBottom : Float := 0
  if let some style := strut then
    let leading := lineLeading font style
    let (a,d) := font.metricsOf style
    ascent := a*style.fontSize/font.unitsPerEm+leading
    descent := d*style.fontSize/font.unitsPerEm+leading
  for (_,item) in items do
    match item with
    | .word _ s _ _ | .space _ s | .lineBreak s | .blockBreak s =>
      let leading := lineLeading font s
      let (a,d) := font.metricsOf s
      ascent := max ascent (a*s.fontSize/font.unitsPerEm+leading)
      descent := max descent (d*s.fontSize/font.unitsPerEm+leading)
    -- An atomic box (an inline-block, an inline flex or grid container) sits on the line by
    -- `vertical-align`: on its own baseline (`atomicBaseline`), or by its margin box.
    | .atomic _ s _ h inner => match s.verticalAlign with
      | .baseline =>
        let b := atomicBaseline s h inner
        ascent := max ascent b
        descent := max descent (h-b)
      | .middle =>
        ascent := max ascent (h/2+s.fontSize/4)
        descent := max descent (h/2-s.fontSize/4)
      | .top => tallTop := max tallTop h
      | .bottom => tallBottom := max tallBottom h
    -- A replaced element sits on the line by `vertical-align`, with the bottom margin edge
    -- as its baseline.
    | .replaced _ s _ h _ => match s.verticalAlign with
      | .baseline => ascent := max ascent h
      -- CSS 2.1 §10.8.1: the middle on the baseline plus half the x-height, here half an em.
      | .middle =>
        ascent := max ascent (h/2+s.fontSize/4)
        descent := max descent (h/2-s.fontSize/4)
      | .top => tallTop := max tallTop h
      | .bottom => tallBottom := max tallBottom h
    | .openAtomic _ _ | .closeAtomic | .bidiMark _ | .outOfFlow _ | .openInline .. | .closeInline .. => pure ()
  -- A box aligned to the top or bottom of the line makes the line tall enough for it.
  if tallBottom > ascent+descent then ascent := tallBottom-descent
  if tallTop > ascent+descent then descent := tallTop-ascent
  let mut out : Result := {height := ascent+descent, baseline := some (y+ascent), lastBaseline := some (y+ascent)}
  -- The inline boxes open at this point of the line, innermost first, each with its
  -- extent so far (`InlineBox`), and their backgrounds and borders, which go under the text.
  let mut frames : List (InlineBox.Frame Float × Computed) := []
  let mut under : Array Node := #[]
  -- On a line reordered by bidi an inline box may be in pieces: its words paint its
  -- background, and its box is the extent of all of them.
  let reordered := !dirs.isEmpty
  -- The box of an inline box on this line and its decorations: the content area of its
  -- font with its padding and borders (CSS 2.1 §10.6.1), the side borders only where the
  -- box starts or ends on this line.
  let fragment := fun (f : InlineBox.Frame Float) (s : Computed) (ended : Bool) =>
    let b := s.borderEdges
    let scale := s.fontSize/font.unitsPerEm
    let (a,d) := font.metricsOf s
    let top := y+ascent-a*scale-s.padding.top-b.top
    let height := (a+d)*scale+s.padding.top+s.padding.bottom+b.top+b.bottom
    let left := f.lo
    -- never past the box's right edge by a rounding of the subtraction: the width of a
    -- container that shrinks to fit is read from these boxes
    let span := f.hi-f.lo
    let width := if left+span > f.hi then span-(left+span-f.hi) else span
    -- most inline boxes have nothing to paint
    let nodes := if (s.background.isNone || reordered) && !s.hasBorder then #[] else
      decorations f.id {s with background := if reordered then none else s.background,
                               borderWidth := {s.borderWidth with left := if f.start then s.borderWidth.left else 0,
                                                                  right := if ended then s.borderWidth.right else 0}}
        left top width height
    ((⟨f.id,left,top,width,height⟩ : Box),nodes)
  for k in [0:items.size] do
    let (offset,item) := items[k]!
    let rtl := dirs[k]?.getD none
    -- what the item covers of the line, for the inline boxes it is in
    let mut extent : Option (Float × Float) := none
    match item with
    | .word source s text start =>
      -- `top`: where the glyphs' em boxes start in the profile's units (the glyphs are drawn
      -- at the baseline); `areaTop`: the content area of the text's own font, and `boxTop` its
      -- line-height box (CSS 2.1 §10.6.1, §10.8.1).
      let top := y+ascent-font.ascent*s.fontSize/font.unitsPerEm
      let leading := lineLeading font s
      let areaTop := y+ascent-(font.metricsOf s).1*s.fontSize/font.unitsPerEm
      let boxTop := areaTop-leading
      if reordered && s.background.isSome then
        out := {out with nodes := out.nodes ++ textBackground font source.paint s (x+offset) areaTop (← itemWidth font rtl item)}
      match ← font.word s text rtl with
      | none =>
        -- A character this font has no glyph for shows as a question mark.
        let chars := text.toList.map fun c => if font.admits c.toNat then c else '?'
        let advance := font.advance*s.fontSize/font.unitsPerEm+s.letterSpacingPx
        let glyphs := chars.toArray.mapIdx fun i c =>
          ({index := c.toNat, x := x+offset+Float.ofNat i*advance, y := top, advance, clusterStart := start+i, clusterEnd := start+i+1} : Glyph)
        let run : GlyphRun := ⟨source.paint,font.family,s.fontSize,text,glyphs⟩
        out := {out with nodes := out.nodes ++ glyphNodes font run s, runs := out.runs.push run, boxes := out.boxes.push ⟨source.geometry,x+offset,boxTop,advance*Float.ofNat chars.length,s.lineHeight⟩}
        extent := some (x+offset,x+offset+advance*Float.ofNat chars.length)
      | some word =>
        let scale := s.fontSize/word.unitsPerEm
        let width := word.advance*s.fontSize/font.unitsPerEm
        let glyphs := word.glyphs.map fun glyph =>
          ({index := glyph.index,x := x+offset+glyph.x*scale,y := top+glyph.y*scale, advance := glyph.advance*scale,clusterStart := start+glyph.clusterStart,clusterEnd := start+glyph.clusterEnd} : Glyph)
        let run : GlyphRun := ⟨source.paint,font.family,s.fontSize,text,glyphs⟩
        out := {out with nodes := out.nodes ++ shapedNodes word run s (x+offset) (y+ascent) width, runs := out.runs.push run,boxes := out.boxes.push ⟨source.geometry,x+offset,boxTop,width,s.lineHeight⟩}
        extent := some (x+offset,x+offset+width)
    | .space source s =>
      let advance ← spaceWidth font s
      let leading := lineLeading font s
      let top := y+ascent-(font.metricsOf s).1*s.fontSize/font.unitsPerEm-leading
      out := {out with nodes := if reordered then out.nodes ++ textBackground font source.paint s (x+offset) (top+leading) advance else out.nodes,
                       boxes := out.boxes.push ⟨source.geometry,x+offset,top,advance,s.lineHeight⟩}
      extent := some (x+offset,x+offset+advance)
      if s.underline && s.visible then
        let thickness := max 1 (s.fontSize/14)
        out := {out with nodes := out.nodes.push (.paint ⟨some source.paint,{geometry := .rect (x+offset) (y+ascent+thickness) advance thickness,style := {fill := .solid (s.decorationColor.getD s.color)}}⟩)}
    | .replaced source s width height nodes =>
      let top := match s.verticalAlign with
        | .baseline => y+ascent-height
        | .middle => y+ascent-s.fontSize/4-height/2
        | .top => y
        | .bottom => y+ascent+descent-height
      -- The box is the border box, inside the margins.
      let m := s.margin
      out := {out with nodes := out.nodes.push (.group none (translate (x+offset) top) nodes),
                       boxes := out.boxes.push ⟨source,x+offset+m.left,top+m.top,width-m.left-m.right,height-m.top-m.bottom⟩}
      extent := some (x+offset,x+offset+width)
    | .atomic _ s width height inner =>
      let top := match s.verticalAlign with
        | .baseline => y+ascent-atomicBaseline s height inner
        | .middle => y+ascent-s.fontSize/4-height/2
        | .top => y
        | .bottom => y+ascent+descent-height
      let moved := shiftResult (x+offset) top inner
      -- `inner` holds the border box of the inline-block first, then its content boxes.
      out := {out with nodes := out.nodes ++ moved.nodes, runs := out.runs ++ moved.runs, boxes := out.boxes ++ moved.boxes,
                       pending := out.pending ++ moved.pending, work := out.work+moved.work, rough := out.rough || moved.rough}
      extent := some (x+offset,x+offset+width)
    | .outOfFlow source => out := {out with pending := out.pending.push {id := source, x := x+offset, y}}
    | .openInline id s continued =>
      let edge := x+offset+(if continued then 0 else s.margin.left)
      frames := (InlineBox.Frame.opened id edge (s.borderEdges.left+s.padding.left) (!continued),s) :: frames
    | .closeInline _ s =>
      match frames with
      | (f,fs) :: rest =>
        let f := f.close (x+offset) (s.padding.right+s.borderEdges.right)
        let (box,nodes) := fragment f fs true
        out := {out with boxes := out.boxes.push box}
        under := under ++ nodes
        frames := InlineBox.merge rest f fs.margin.left fs.margin.right true
      | [] => pure ()
    | _ => pure ()
    if let some (a,b) := extent then frames := InlineBox.place frames a b
  -- The inline boxes still open go on to the next line: their boxes here have no right edge.
  for _ in [0:frames.length] do
    match frames with
    | (f,fs) :: rest =>
      let (box,nodes) := fragment f fs false
      out := {out with boxes := out.boxes.push box}
      under := under ++ nodes
      frames := InlineBox.merge rest f fs.margin.left 0 false
    | [] => break
  return if under.isEmpty then out else {out with nodes := under ++ out.nodes}

private def appendResult (a b : Result) : Result :=
  {nodes := a.nodes ++ b.nodes, boxes := a.boxes ++ b.boxes, runs := a.runs ++ b.runs, height := a.height+b.height,
   pending := a.pending ++ b.pending, baseline := a.baseline <|> b.baseline,
   lastBaseline := b.lastBaseline <|> a.lastBaseline, work := a.work+b.work, rough := a.rough || b.rough}

/-- A word of preformatted text: it never wraps. -/
private def preformatted : Inline → Bool
  | .word _ s _ _ => s.preformatted
  | _ => false

/-- No line break before `item` (CSS Text 3 §3 `white-space: nowrap`): the space before
it is text that does not wrap, or with no space there the item itself is. -/
private def heldByNowrap (space : Option (TextSource × Computed)) : Inline → Bool
  | .word _ s _ _ => match space with
    | some (_,spaceStyle) => spaceStyle.pos.nowrap
    | none => s.pos.nowrap
  | _ => match space with
    | some (_,spaceStyle) => spaceStyle.pos.nowrap
    | none => false

/-- The characters an item stands for in its paragraph, for UAX #9: a forced line
break is a paragraph separator, a replaced or atomic box an object replacement
character (CSS Writing Modes 3 §2.4.1). -/
private def bidiChars : Inline → Array Char
  | .word _ _ text _ => text.toList.toArray
  | .space _ _ => #[' ']
  | .lineBreak _ | .blockBreak _ => #[' ']
  | .replaced .. | .atomic .. => #['￼']
  | .bidiMark c => #[c]
  | .openAtomic _ _ | .closeAtomic | .outOfFlow _ | .openInline .. | .closeInline .. => #[]

/-- A class that makes a block take the bidi path: right-to-left letters, Arabic
digits and the explicit formatting characters. -/
private def bidiClassNeeds (c : Char) : Bool :=
  match Unicode.bidiClassOf c with
  | .R | .AL | .AN | .LRE | .LRO | .RLE | .RLO | .PDF | .LRI | .RLI | .FSI | .PDI => true
  | _ => false

/-- The block needs UAX #9: it is right to left or plaintext, or has an inline box
with `unicode-bidi`, or a character of `bidiClassNeeds`. Otherwise every level is 0
and the order is logical (`Unicode.reorderByLevels_even`). -/
def needsBidi (rtl plain : Bool) (items : Array Inline) : Bool :=
  rtl || plain || items.any fun
    | .bidiMark _ => true
    | .word _ _ text _ => text.any bidiClassNeeds
    | _ => false

/-- Items with their resolved levels: words cut where the level changes, the level
of each item, whether it continues the word before it (no break opportunity), and
its paragraph level. -/
structure BidiItems where
  items : Array Inline
  levels : Array Nat
  glue : Array Bool
  paraLevels : Array Nat

/-- UAX #9 P1 to I2 over the items of a block (`Unicode.levelsOfText`). A character
that X9 removes takes the level before it. -/
def bidiItems (items : Array Inline) (paraDir : Unicode.ParaDir) : BidiItems := Id.run do
  let mut cs : Array Char := #[]
  let mut starts : Array Nat := #[]
  for it in items do
    starts := starts.push cs.size
    cs := cs ++ bidiChars it
  let mut lv : Array Nat := Array.replicate cs.size 0
  let mut pl : Array Nat := Array.replicate cs.size 0
  for ((a, b), lvs, p) in Unicode.levelsOfText cs paraDir do
    let mut last := p
    for k in [0:b-a] do
      let l := (lvs[k]?.getD none).getD last
      lv := lv.set! (a+k) l
      pl := pl.set! (a+k) p
      last := l
  let mut out : BidiItems := ⟨#[], #[], #[], #[]⟩
  for i in [0:items.size] do
    let st := starts[i]!
    let para := pl[st]?.getD (pl.back?.getD 0)
    match items[i]! with
    | .word source s text start =>
      let chars := text.toList.toArray
      let mut from_ := 0
      for k in [1:chars.size+1] do
        if k == chars.size || lv[st+k]! != lv[st+from_]! then
          out := {items := out.items.push (.word source s (String.ofList (chars.extract from_ k).toList) (start+from_)),
                  levels := out.levels.push lv[st+from_]!, glue := out.glue.push (from_ > 0),
                  paraLevels := out.paraLevels.push para}
          from_ := k
    | other =>
      out := {items := out.items.push other, levels := out.levels.push (lv[st]?.getD para),
              glue := out.glue.push false, paraLevels := out.paraLevels.push para}
  return out

/-- UAX #9 L1 and L2 for one line of `line` (offsets in logical order, the line
`lineEnd` wide), whose items have `levels` and paragraph levels `paras`: trailing
spaces, the line break and trailing bidi controls get the paragraph level, then
each item moves to its place in visual order. Items stay in logical order; each
gets its new offset and its direction (odd level: right to left). -/
def bidiLine (line : Array (Float × Inline)) (levels paras : Array Nat) (lineEnd : Float) :
    Array (Float × Inline) × Array (Option Bool) := Id.run do
  let n := line.size
  let mut ls := levels
  for q in [0:n] do
    let j := n-1-q
    match line[j]!.2 with
    | .space _ _ | .lineBreak _ | .blockBreak _ | .bidiMark _ | .openInline .. | .closeInline .. => ls := ls.set! j (paras[j]?.getD 0)
    | _ => break
  let order := Unicode.reorderByLevels (Array.range n) ls
  let width := fun (j : Nat) => (if j+1 < n then line[j+1]!.1 else lineEnd) - line[j]!.1
  let mut xs : Array Float := Array.replicate n 0
  let mut pen : Float := 0
  for j in order do
    xs := xs.set! j pen
    pen := pen+width j
  return ((Array.range n).map fun j => (xs[j]!, line[j]!.2), ls.map fun l => some (l % 2 == 1))

/-- The starts of inline boxes `starts` (index, node, style) placed on a line at `cursor`,
one after the other: each takes the room of its left margin, border and padding. -/
private def placeStarts (starts : Array (Nat × Nat × Computed)) (line : Array (Float × Inline)) (lineIdx : Array Nat)
    (cursor : Float) : Array (Float × Inline) × Array Nat × Float :=
  starts.foldl (fun (acc : Array (Float × Inline) × Array Nat × Float) (st : Nat × Nat × Computed) =>
    (acc.1.push (acc.2.2,.openInline st.2.1 st.2.2 false),acc.2.1.push st.1,acc.2.2+inlineLead st.2.2)) (line,lineIdx,cursor)

/-- The start of a new line inside the inline boxes `open`: each goes on, with no edge. -/
private def continuedStarts (open_ : Array (Nat × Nat × Computed)) : Array (Float × Inline) × Array Nat :=
  if open_.isEmpty then (#[],#[]) else (open_.map fun st => (0,.openInline st.2.1 st.2.2 true),open_.map (·.1))

/-- Word wrapping constructs line participants first. The font profile and
positioned glyph runs are consumed to paint the actual word geometry. With bidi
(`needsBidi`), words are cut by level first, a word's pieces stay on one line, and
each line is reordered (`bidiLine`). -/
def inlineLayout (font : FontProfile) (items0 : Array Inline) (x y available : Float)
    (strut : Option Computed := none)
    (band : Float → Float × Float := fun _ => (0,available)) : Except String Result := do
  let rtlBlock := strut.any (·.direction == .rtl)
  let plain := strut.any (·.unicodeBidi == .plaintext)
  let bidi := needsBidi rtlBlock plain items0
  let bi : BidiItems := if bidi then bidiItems items0 (if plain then .auto else if rtlBlock then .rtl else .ltr)
    else ⟨items0, #[], #[], #[]⟩
  let items := bi.items
  let dirOf := fun (k : Nat) => if bidi then (bi.levels[k]?.map (· % 2 == 1)) else none
  let glued := fun (k : Nat) => bi.glue[k]?.getD false
  -- CSS Text 3 §6.1 `text-align` of the block container (`strut`): a line `w` wide starts
  -- this far in; `start` and `end` follow the direction. A line wider than the room
  -- starts at the left edge.
  let rtlAlign := if plain then (bi.paraLevels[0]?.getD 0) % 2 == 1 else rtlBlock
  -- `band dy` is the room of a line that starts `dy` below `y`: its offset from `x` and its
  -- width, less than `available` beside floats (CSS 2.1 §9.5).
  -- CSS Text 3 §8.3: the first line of the block container starts `textIndent` in from its
  -- start edge (a percentage of `available`), and has that much less room.
  let firstIndent := (strut.bind fun s => CSS.resolve available s.textIndent).getD 0
  let bandAt := fun (dy : Float) (first : Bool) =>
    let (offset,room) := band dy
    if !first || firstIndent == 0 then (offset,room)
    else if rtlAlign then (offset,room-firstIndent) else (offset+firstIndent,room-firstIndent)
  let indent := fun (w dy : Float) (first : Bool) =>
    let (offset,room) := bandAt dy first
    offset+match (strut.map (·.textAlign)).getD .start with
    | .start => if rtlAlign then max 0 (room-w) else 0
    | .end_ => if rtlAlign then 0 else max 0 (room-w)
    | .left => 0
    | .right => max 0 (room-w)
    | .center => max 0 ((room-w)/2)
  -- A finished line: reordered when there is bidi.
  let place := fun (line : Array (Float × Inline)) (idx : Array Nat) (lineEnd : Float) =>
    if bidi then bidiLine line (idx.map fun k => bi.levels[k]?.getD 0) (idx.map fun k => bi.paraLevels[k]?.getD 0) lineEnd
    else (line, #[])
  let mut out : Result := {}
  let mut cursorX : Float := 0
  let mut pendingSpace : Option (TextSource × Computed) := none
  let mut pendingK : Nat := 0
  let mut line : Array (Float × Inline) := #[]
  let mut lineIdx : Array Nat := #[]
  -- Inline boxes: those that have begun and not ended (index of the start, node, style),
  -- which a new line continues; those whose start waits for the item it begins with, so
  -- that a start and its edge are never left at the end of a line.
  let mut openBoxes : Array (Nat × Nat × Computed) := #[]
  let mut waiting : Array (Nat × Nat × Computed) := #[]
  -- The line has something that gives it height (CSS 2.1 §9.4.2: a line with only empty
  -- inline boxes that have no margin, border or padding is as if it were not there), or
  -- an inline box that starts on it.
  let mut content := false
  let mut fresh := false
  let mut first := true
  for k in [0:items.size] do
    let item := items[k]!
    match item with
    | .openInline id s _ => waiting := waiting.push (k,id,s)
    | .closeInline _ s =>
      -- An inline box with nothing in it starts here too.
      if !waiting.isEmpty then
        (line,lineIdx,cursorX) := placeStarts waiting line lineIdx cursorX
        if waiting.any fun (_,_,ws) => inlineLead ws != 0 then content := true
        openBoxes := openBoxes ++ waiting
        waiting := #[]
        fresh := true
      line := line.push (cursorX,item)
      lineIdx := lineIdx.push k
      let trail := inlineTrail s
      cursorX := cursorX+trail
      if trail != 0 then content := true
      openBoxes := openBoxes.pop
    | .space source s =>
      if s.preformatted then
        -- A preserved space is placed where it stands, and lines do not wrap.
        if let some (source,s) := pendingSpace then
          if cursorX > 0 then
            line := line.push (cursorX,.space source s)
            lineIdx := lineIdx.push pendingK
            cursorX := cursorX+(← spaceWidth font s)
        line := line.push (cursorX,item)
        lineIdx := lineIdx.push k
        cursorX := cursorX+(← spaceWidth font s)
        pendingSpace := none
        content := true
      else
        pendingSpace := some (source,s)
        pendingK := k
    | .outOfFlow _ =>
      -- No width and no break, and white space collapses across it: it stands after a
      -- pending space, which the next word still places (once).
      let gap ← if cursorX > 0 then match pendingSpace with
        | some (_,s) => spaceWidth font s
        | none => pure 0
        else pure 0
      line := line.push (cursorX+gap,item)
      lineIdx := lineIdx.push k
      content := true
    | .bidiMark _ =>
      -- No width and no break: a space before it is placed first, to keep logical order.
      if let some (source,s) := pendingSpace then
        if cursorX > 0 then
          line := line.push (cursorX,.space source s)
          lineIdx := lineIdx.push pendingK
          cursorX := cursorX+(← spaceWidth font s)
        pendingSpace := none
      line := line.push (cursorX,item)
      lineIdx := lineIdx.push k
      content := true
    | .blockBreak _ =>
      -- the starts and ends of inline boxes are not content: a line of only those is empty
      let real := line.any fun (_, it) => match it with
        | .openInline .. | .closeInline .. | .bidiMark _ | .outOfFlow _ => false
        | _ => true
      if content && real then
        if !waiting.isEmpty then
          (line,lineIdx,cursorX) := placeStarts waiting line lineIdx cursorX
          openBoxes := openBoxes ++ waiting
          waiting := #[]
        let (row,dirs) := place line lineIdx cursorX
        let row ← lineLayout font row (x+indent cursorX out.height first) (y+out.height) strut dirs
        out := appendResult out row
        first := false
        (line,lineIdx) := continuedStarts openBoxes
        cursorX := 0
        pendingSpace := none
        content := false
        fresh := false
    | .lineBreak _ =>
      if !waiting.isEmpty then
        (line,lineIdx,cursorX) := placeStarts waiting line lineIdx cursorX
        openBoxes := openBoxes ++ waiting
        waiting := #[]
      let (row,dirs) := place (line.push (cursorX,item)) (lineIdx.push k) cursorX
      let row ← lineLayout font row (x+indent cursorX out.height first) (y+out.height) strut dirs
      out := appendResult out {row with height := if row.height > 0 then row.height else 19.2}
      first := false
      (line,lineIdx) := continuedStarts openBoxes
      cursorX := 0
      pendingSpace := none
      content := false
      fresh := false
    | _ =>
      let width ← itemWidth font (dirOf k) item
      -- The item goes on a line with the starts of the inline boxes it begins.
      let lead := if waiting.isEmpty then 0 else waiting.foldl (fun w (_,_,ws) => w+inlineLead ws) 0
      -- The pieces of a word cut by bidi levels go on one line together.
      let mut whole := width+lead
      if bidi && !glued k then
        let mut j := k+1
        for _ in [0:items.size] do
          if j < items.size && glued j then
            whole := whole+(← itemWidth font (dirOf j) items[j]!)
            j := j+1
          else break
      let gap ← if cursorX > 0 then match pendingSpace with
        | some (_,s) => spaceWidth font s
        | none => pure 0
        else pure 0
      -- A line may break before this item: then what follows it with no break between
      -- (`white-space: nowrap`) must fit on the line with it. Only the first item of such a
      -- run looks ahead, so a run is measured once.
      let held := heldByNowrap pendingSpace item
      if !bidi && !held && cursorX > 0 then
        let mut between : Option Computed := none
        for j in [k+1:items.size] do
          match items[j]! with
          | .space _ ss => if ss.preformatted then break else between := some ss
          | .openInline _ ws _ => whole := whole+inlineLead ws
          | .closeInline _ ws => whole := whole+inlineTrail ws
          | .word source ws text start =>
            match between with
            | some ss =>
              if ss.pos.nowrap then
                whole := whole+(← spaceWidth font ss)+(← itemWidth font none (.word source ws text start))
                between := none
              else break
            | none => break
          | _ => break
      if cursorX > 0 && cursorX+gap+whole > (bandAt out.height first).2 && !preformatted item && !glued k && !held then
        let (row,dirs) := place line lineIdx cursorX
        out := appendResult out (← lineLayout font row (x+indent cursorX out.height first) (y+out.height) strut dirs)
        (line,lineIdx) := continuedStarts openBoxes
        cursorX := 0
        fresh := false
        first := false
      else
        if gap > 0 then
          if let some (source,s) := pendingSpace then
            line := line.push (cursorX,.space source s)
            lineIdx := lineIdx.push pendingK
        cursorX := cursorX+gap
      if !waiting.isEmpty then
        (line,lineIdx,cursorX) := placeStarts waiting line lineIdx cursorX
        openBoxes := openBoxes ++ waiting
        waiting := #[]
        fresh := true
      line := line.push (cursorX,item)
      lineIdx := lineIdx.push k
      cursorX := cursorX+width
      pendingSpace := none
      content := true
  if !line.isEmpty && (content || fresh) then
    let (row,dirs) := place line lineIdx cursorX
    let row ← lineLayout font row (x+indent cursorX out.height first) (y+out.height) strut dirs
    out := appendResult out (if content then row else {row with height := 0})
  return out

private def append (a b : Result) : Result :=
  {nodes := a.nodes ++ b.nodes,boxes := a.boxes ++ b.boxes,runs := a.runs ++ b.runs, height := a.height+b.height,
   pending := a.pending ++ b.pending, baseline := a.baseline <|> b.baseline,
   lastBaseline := b.lastBaseline <|> a.lastBaseline, work := a.work+b.work, rough := a.rough || b.rough}

/-- An inline-block's border and decorations around its already positioned content. -/
def framedAtomic (id : Nat) (s : Computed) (w h : Float) (inner : Result) : Inline :=
  let m := s.margin
  let box : Box := ⟨id,m.left,m.top,w,h⟩
  .atomic id s (m.left+w+m.right) (m.top+h+m.bottom)
    {inner with nodes := decorations id s m.left m.top w h ++ inner.nodes, boxes := #[box] ++ inner.boxes}

/-- Kind: frame. Says: framing an inline-block retains its own border box followed by
all positioned child boxes in order, with the child's glyph runs and baselines.
Does not say: which dimensions or glyph positions layout computes. -/
theorem framedAtomic_preserves (id : Nat) (s : Computed) (w h : Float) (inner : Result) :
    match framedAtomic id s w h inner with
    | .atomic owner _ _ _ r =>
      owner = id ∧ r.boxes = #[⟨id,s.margin.left,s.margin.top,w,h⟩] ++ inner.boxes ∧
        r.runs = inner.runs ∧ r.baseline = inner.baseline ∧ r.lastBaseline = inner.lastBaseline
    | _ => False := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Kind: sizing. Says: the enclosing line measures the framed inline-block as one
item of its margin-box width. Does not say: how its content width was chosen. -/
theorem framedAtomic_lineWidth (font : FontProfile) (rtl : Option Bool) (id : Nat)
    (s : Computed) (w h : Float) (inner : Result) :
    itemWidth font rtl (framedAtomic id s w h inner) = .ok (s.margin.left+w+s.margin.right) := rfl

#print axioms framedAtomic_preserves
#print axioms framedAtomic_lineWidth

/-- An open inline-block. Its line width supplies the containing width of a nested
inline-block. The preceding siblings receive the finished box as one inline item. -/
private structure AtomicFrame where
  source : Nat
  style : Computed
  before : Array Inline
  fixed : Option Float
  lineWidth : Float

private def AtomicFrame.opened (id : Nat) (s : Computed) (before : Array Inline)
    (available : Float) : AtomicFrame :=
  let b := s.borderEdges
  let p := s.padding
  let m := s.margin
  let room := max 0 (available-m.left-m.right-b.left-b.right-p.left-p.right)
  -- a block box (a block inside an inline, `inlineItems`) is as wide as the line
  let fixed := (CSS.resolve available s.width).orElse fun _ => if s.display.isBlockLevel then some room else none
  ⟨id,s,before,fixed,fixed.getD room⟩

/-- CSS 2.2 §10.3.9 and §10.6.6: an inline-block with `width:auto` is as wide as its
widest line (at most the room); its content is laid out at the origin inside its
border and padding. Its bottom margin edge sits on the line's baseline, as a
replaced element does here. -/
private def atomicBox (font : FontProfile) (frame : AtomicFrame) (items : Array Inline) : Except String Inline := do
  let s := frame.style
  let b := s.borderEdges
  let p := s.padding
  let m := s.margin
  let content ← inlineLayout font items 0 0 frame.lineWidth (some {s with textAlign := .left})
  let used := frame.fixed.getD (content.boxes.foldl (fun w box => max w (box.x+box.width)) 0)
  -- Lines are aligned in the width the box has (`text-align`), once it is known.
  let leftAligned := s.textAlign == .left || (s.textAlign == .start && s.direction == .ltr) ||
    (s.textAlign == .end_ && s.direction == .rtl)
  let content ← if leftAligned then pure content else inlineLayout font items 0 0 used (some s)
  let height := match s.height with
    | .percent _ => content.height
    | _ => max 0 ((CSS.resolve 0 s.height).getD content.height)
  let w := b.left+p.left+used+p.right+b.right
  let h := b.top+p.top+height+p.bottom+b.bottom
  let inner := shiftResult (m.left+b.left+p.left) (m.top+b.top+p.top) content
  return framedAtomic frame.source s w h inner

/-- Each matched inline-block becomes one atomic item in its parent's line. The stack
holds one frame per open bound, limited by the DOM depth budget of `inlineItems`. -/
def atomize (font : FontProfile) (items : Array Inline) (available : Float) : Except String (Array Inline) := do
  let mut out : Array Inline := #[]
  let mut frames : List AtomicFrame := []
  for item in items do
    match item with
    | .openAtomic id s =>
      let room := match frames with | parent :: _ => parent.lineWidth | [] => available
      frames := AtomicFrame.opened id s out room :: frames
      out := #[]
    | .closeAtomic =>
      if let frame :: parents := frames then
        let child ← atomicBox font frame out
        out := frame.before.push child
        frames := parents
    | other => out := out.push other
  -- Bounds always pair in `inlineItems`; an unpaired open keeps its content inline.
  return frames.foldl (fun rest frame => frame.before ++ rest) out

/-- A wrapper to see through: an inline element (not a link, not replaced, not SVG) with no
margin, border, padding or background of its own, that has a block-level child in flow.
`liftBlocks` gives its children to the block flow of its parent. -/
def seeThrough (dom : Dom) (styles : Array Computed) (id : Nat) : Bool :=
  let n := dom.get id
  let s := styles[id]!
  n.type == .element && s.display == .inline && !s.pos.isAbsolute && s.pos.float == .none &&
  n.lname != "a" && n.ns != some DOM.svgNS && (blankReplaced n).isNone && n.lname != "img" &&
  s.background.isNone && s.backgroundImage.isNone && s.backgroundGradient.isNone &&
  s.borderEdges.top == 0 && s.borderEdges.right == 0 && s.borderEdges.bottom == 0 && s.borderEdges.left == 0 &&
  s.padding.left == 0 && s.padding.right == 0 && s.margin.left == 0 && s.margin.right == 0 &&
  n.kids.any fun k =>
    let ks := styles[k]!
    (dom.get k).type == .element && ks.display.isBlockLevel && !ks.pos.isAbsolute && ks.pos.float == .none

/-- The children of a block flow with each `seeThrough` wrapper replaced by its children, in
order, to any depth (CSS 2.1 §9.2.1.1: a block box inside an inline box breaks the inline
box around it; the block keeps its own layout). Before 2026-11-24 the wrapper's contents
were laid out as inline content: GitHub's header, a flex column inside the inline custom
element `react-partial`, drew each of its items on a line of its own. At most `dom.size`
steps. -/
def liftBlocks (dom : Dom) (styles : Array Computed) (kids : Array Nat) : Array Nat := Id.run do
  if !kids.any (seeThrough dom styles) then return kids
  let mut out : Array Nat := #[]
  let mut pending : List Nat := kids.toList
  for _ in [0:dom.size + kids.size + 1] do
    match pending with
    | [] => break
    | k :: rest =>
      if seeThrough dom styles k then pending := (dom.get k).kids.toList ++ rest
      else
        out := out.push k
        pending := rest
  return out ++ pending.toArray

/-- What goes before a list item (CSS Lists 3 §3.1 `list-style-type`): nothing with
`none`; its number with a numbering style, or by default in an ordered list; else a
bullet: the one that `list-style-type` names, or by default the disc, circle or square of
a list nested one, two or more deep (HTML §15.3.7). A font with no glyph for the bullet
(`FontProfile.admits`) gets a star. -/
def listMarker (dom : Dom) (font : FontProfile) (style : CSS.ListStyle) (id : Nat) : String := Id.run do
  if style == .none then return ""
  let some parent := (dom.get id).parent | return "* "
  if style != .number && !(style == .auto && (dom.get parent).lname == "ol") then
    let mut depth := 0
    let mut cur := parent
    for _ in [0:64] do
      if ["ul","ol","menu","dir"].contains (dom.get cur).lname then depth := depth+1
      match (dom.get cur).parent with
      | some up => cur := up
      | none => break
    let bullet : Char := match style with
      | .disc => '•'
      | .circle => '◦'
      | .square => '▪'
      | _ => if depth >= 3 then '▪' else if depth == 2 then '◦' else '•'
    -- A shaped font draws the bullet, or a fallback face does (`SfntProfile`); only a
    -- fixed font without it shows `*`.
    return if font.admits bullet.toNat || font.shapedWord.isSome then s!"{bullet} " else "* "
  let mut number := 1
  for kid in (dom.get parent).kids do
    if kid == id then break
    if (dom.get kid).lname == "li" then number := number+1
  return s!"{number}. "

/-- What `layoutTask` and `intrinsic` lay out: an element's box, the contents of a
block container (a cell's contents, or an anonymous cell's), or a table (an element,
or the anonymous table of a run of internal table boxes, CSS 2.1 §17.2.1). -/
inductive Task where
  | box (id : Nat)
  /-- The children `kids` in the block formatting context of `container`, with its style. -/
  | contents (container : Nat) (kids : Array Nat)
  /-- A table: `element` is the table element, or `none` for an anonymous table of the
  children `kids` of `container`. -/
  | table (element : Option Nat) (container : Nat) (kids : Array Nat)
  /-- An element's box with the border-box `width` (and `height`) that its parent
  formatting context imposes (`Constraints`): its own `width`, `min-width` and `max-width`
  (and `height`) are not read. -/
  | sized (id : Nat) (width : Float) (height : Option Float)
  /-- The contents only of the box of `id` for a border box `width` wide: no decorations
  and no box of its own; the result's `height` is the content height (`Children.content`). -/
  | inner (id : Nat) (width : Float)
  /-- Absolutely positioned boxes laid out in the containing block `(cx,cy,cw,ch)`: for
  the root, whose containing block is the viewport (`render`). -/
  | positioned (content : Result) (cx cy cw ch : Float)
  /-- `box id` in a block formatting context that has `floats` already (CSS 2.1 §9.5): the
  lines of the box and of its descendants are beside them. -/
  | flowed (id : Nat) (floats : Array Floats.Box)
  /-- `task` laid out only to be measured (`Constraints.measure`): everything inside is
  laid out in that mode too, and no item is laid out a second time. -/
  | rough (task : Task)
  deriving Repr

/-- The right edge of what a line layout placed, from its left edge `0`. -/
private def lineExtent (r : Result) : Float := r.boxes.foldl (fun m b => max m (b.x+b.width)) 0

/-! ### Multi-column layout (CSS Multi-column Layout 1)

A block container with `column-count` or `column-width` lays its contents out in one column
of the column width; the column is then cut between in-flow children into as many pieces
as there are columns, balanced (§7.1: `column-fill: balance`), and the pieces are set side
by side, `column-gap` apart. A child is never cut (most multi-column pages hold lists and
sections, often with `break-inside: avoid`); a column with one tall child is that tall.
The children of each piece are then laid out again in their column, so each is painted
once (a margin at the top of a column is kept, where the standard truncates it). A
multi-column box costs two layouts of its contents; a box with neither property pays one
test. -/

/-- §3.4: the number of columns and their width in a content box `avail` wide, from
`column-count`, `column-width` and the gap; none for one column (not a multi-column box). -/
def columnCountFor (count : Option Nat) (width : Option Float) (gap avail : Float) : Nat :=
  let fit := fun (w : Float) => if w+gap <= 0 then 1 else max 1 ((avail+gap)/(w+gap)).floor.toUInt64.toNat
  let n : Nat := match count,width with
    | some c,none => c
    | none,some w => fit w
    | some c,some w => min c (fit w)
    | none,none => 1
  min n 1000

def columnPlan (count : Option Nat) (width : Option Float) (gap avail : Float) : Option (Nat × Float) :=
  let n := columnCountFor count width gap avail
  if n ≤ 1 then none else some (n,max 0 ((avail+gap)/Float.ofNat n-gap))

/-- The column count is at least two and at most 1000 when there is a plan: the work of
a multi-column layout is bounded by it. -/
theorem columnPlan_count (count : Option Nat) (width : Option Float) (gap avail : Float) (n : Nat) (w : Float)
    (h : columnPlan count width gap avail = some (n,w)) : 2 ≤ n ∧ n ≤ 1000 := by
  have hle : columnCountFor count width gap avail ≤ 1000 := Nat.min_le_right _ _
  unfold columnPlan at h
  by_cases hn : columnCountFor count width gap avail ≤ 1
  · simp [hn] at h
  · simp only [hn, if_false, Option.some.injEq, Prod.mk.injEq] at h
    omega

/-- The children that begin a column after the first (greedy, §7.1), as indices of `spans`
(the children's `(top,bottom)` offsets in order) for a column height `h`: a child that ends
past its column's start plus `h` begins the next column, unless it is the column's first. -/
def columnFirsts (spans : Array (Float × Float)) (h : Float) : Array Nat := Id.run do
  let mut firsts : Array Nat := #[]
  let mut start : Float := 0
  for k in [0:spans.size] do
    let (top,bottom) := spans[k]!
    if k > 0 && bottom-start > h then
      firsts := firsts.push k
      start := top
  return firsts

/-- The columns that a cut at `h` makes (greedy, §7.1): the start of each column, as offsets
from the top of the content, from the children's spans `(top,bottom)` in order. A child that
ends past the column's start plus `h` begins the next column, unless it is the column's
first. -/
def columnStarts (spans : Array (Float × Float)) (h : Float) : Array Float :=
  #[0] ++ (columnFirsts spans h).map fun k => (spans[k]!).1

/-- The least column height (within 1/64 px) at which the children fit `count` columns, from
the height of the content over `count` up to all of it: a bisection of 24 steps. -/
def balancedHeight (spans : Array (Float × Float)) (total : Float) (count : Nat) : Float := Id.run do
  let mut lo := total/Float.ofNat (max 1 count)
  let mut hi := total
  if (columnStarts spans lo).size ≤ count then return lo
  for _ in [0:24] do
    if hi-lo < 1/64 then break
    let mid := (lo+hi)/2
    if (columnStarts spans mid).size ≤ count then hi := mid else lo := mid
  return hi

/-- The children of each column: `single` is the contents laid out in one column at `y`; the
in-flow children with a box are the places it may be cut (`balancedHeight`, `columnStarts`).
Each child, with the text and the boxless children before the next cut, goes to one column,
in order. One group: nothing to cut. -/
def columnKids (single : Result) (kids : Array Nat) (count : Nat) (y : Float) : Array (Array Nat) := Id.run do
  -- the first box of each source: a child's own box comes before those inside it
  let first := single.boxes.foldl (fun (m : Std.TreeMap Nat Box) b => if m.contains b.source then m else m.insert b.source b) {}
  let mut spans : Array (Float × Float) := #[]
  let mut at_ : Array Nat := #[]
  for i in [0:kids.size] do
    if let some b := first.get? kids[i]! then
      spans := spans.push (b.y-y,b.y+b.height-y)
      at_ := at_.push i
  let h := balancedHeight spans single.height count
  let cuts := ((columnFirsts spans h).extract 0 (count-1)).map (at_[·]!)
  let mut groups : Array (Array Nat) := #[#[]]
  for i in [0:kids.size] do
    if cuts.contains i then groups := groups.push #[]
    groups := groups.modify (groups.size-1) (·.push kids[i]!)
  return groups

/-- The used `column-gap` of a multi-column container: `normal` is 1em (§5.1). -/
def columnGapPx (s : Computed) (width : Float) : Float :=
  match s.align.columnGap with
  | .px v => max 0 v
  | .percent p => max 0 (p*width)
  | _ => s.fontSize

/-- A result moved down by `dy`: its paint in a translated group, its boxes and glyphs moved. -/
private def Result.shiftY (r : Result) (dy : Float) : Result :=
  if dy == 0 then r else
  {r with nodes := if r.nodes.isEmpty then #[] else #[.group none (translate 0 dy) r.nodes.toList],
          boxes := r.boxes.map fun b => {b with y := b.y+dy},
          runs := r.runs.map fun run => {run with glyphs := run.glyphs.map fun g => {g with y := g.y+dy}},
          pending := r.pending.map fun p => {p with y := p.y+dy},
          baseline := r.baseline.map (·+dy), lastBaseline := r.lastBaseline.map (·+dy)}

/-- The style of the contents of a cell: the cell's own, or for an anonymous cell
its parent's, with no box edges (an anonymous box has none). -/
private def anonymousBox (base : Computed) : Computed :=
  {base with padding := {}, margin := {}, background := none, width := .auto, height := .auto,
             verticalAlign := .baseline, autoMarginLeft := false, autoMarginRight := false}
/-- The style of an anonymous flex or grid item (a run of text): its container's
inherited values, with no box edges, limits, or flex and alignment values of its own. -/
private def anonymousItem (base : Computed) : Computed :=
  {anonymousBox base with display := .block, borderStyles := .all .none, clipOverflow := false,
                          minWidth := .auto, maxWidth := .auto, minHeight := .auto, maxHeight := .auto,
                          autoMarginTop := false, autoMarginBottom := false, align := {}, flex := {}}

/-- The box of element `id` around its laid-out contents: its decorations (under the
contents, which are clipped to the padding box when the box clips), its border box at
`(outerX,outerY)` of `borderWidth` by `borderHeight`, and the height of its margin box. -/
def frameBox (id : Nat) (s : Computed) (outerX outerY borderWidth borderHeight : Float) (content : Result) : Result :=
  let border := s.borderEdges
  let nodes := clipContent s.clipOverflow (decorations id s outerX outerY borderWidth borderHeight) content.nodes
    ⟨outerX+border.left,outerY+border.top,borderWidth-border.left-border.right,borderHeight-border.top-border.bottom,identity⟩
  {content with nodes, boxes := #[⟨id,outerX,outerY,borderWidth,borderHeight⟩] ++ content.boxes,
                height := s.margin.top+borderHeight+s.margin.bottom, marginBottom := s.margin.bottom}

/-- CSS 2.1 §8.3.1: the top margin of a block adjoins the top margin of its first in-flow
block child when no border, padding or clearance is between them and the block does not
establish a new block formatting context. A list item's marker is content before it. -/
def collapsesTop (dom : Dom) (s : Computed) (id : Nat) : Bool :=
  let n := dom.get id
  s.display == .block && s.borderEdges.top == 0 && s.padding.top == 0 && !s.clipOverflow && !s.pos.formattingRoot &&
    !s.pos.isAbsolute && s.pos.float == .none && n.lname != "li" && n.ns != some DOM.svgNS &&
    (n.parent.map fun p => (dom.get p).type == .element).getD false

/-- The same for the bottom margin and the last in-flow block child: also no height or
minimum height (CSS 2.1 §8.3.1). -/
def collapsesBottom (dom : Dom) (s : Computed) (id : Nat) : Bool :=
  let n := dom.get id
  let auto := fun (l : CSS.Length) => match l with | .auto => true | _ => false
  s.display == .block && s.borderEdges.bottom == 0 && s.padding.bottom == 0 && !s.clipOverflow && !s.pos.formattingRoot &&
    !s.pos.isAbsolute && s.pos.float == .none && auto s.height && auto s.minHeight &&
    n.ns != some DOM.svgNS && (n.parent.map fun p => (dom.get p).type == .element).getD false

/-- The first child of `id` when it is an in-flow block box with nothing in flow before
it: white space, comments, boxes with `display: none` and absolutely positioned boxes
are not in flow. -/
def firstBlock (dom : Dom) (styles : Array Computed) (id : Nat) : Option Nat := Id.run do
  for k in (dom.get id).kids do
    let n := dom.get k
    if n.type == .text then
      if !blankText n.data then return none
    else if n.type == .element then
      let s := styles[k]!
      if s.display == .none || s.pos.isAbsolute then continue
      return if s.display.isBlockLevel then some k else none
  return none

/-- The margin that two adjoining margins make (CSS 2.1 §8.3.1): the larger when neither
is negative, the more negative when both are, their sum when one is. The same text as
`MarginCollapse.collapse`, where it is proved against the rule, on `Float`. -/
def collapsePx (a b : Float) : Float :=
  if a >= 0 && b >= 0 then max a b else if a < 0 && b < 0 then min a b else a+b

/-- How far a box moves into the margin `before` it by its own top margin `top`
(`MarginCollapse.overlap` on `Float`): the smaller of the two when neither is negative.
`before` at `unbounded` is the top of a flow whose container shows the margin already:
all of `top` is taken out. -/
def overlapPx (before top : Float) : Float :=
  if before >= unbounded/2 then top
  else if before >= 0 && top >= 0 then min before top else if before < 0 && top < 0 then max before top else 0

/-- The top margin that the box of `id` shows to what is before it: its own, collapsed
with those of the first blocks nested at its top that adjoin it (CSS 2.1 §8.3.1, two at a
time: `MarginCollapse`). `fuel` bounds the nesting. -/
def leadMargin (dom : Dom) (styles : Array Computed) (fuel id : Nat) : Float := Id.run do
  let mut best := (styles[id]!).margin.top
  let mut cur := id
  -- a loop down the first blocks: no stack depth in the nesting
  for _ in [0:fuel] do
    if !collapsesTop dom (styles[cur]!) cur then break
    match firstBlock dom styles cur with
    | some k =>
      best := collapsePx best (styles[k]!).margin.top
      cur := k
    | none => break
  return best

/-- A replaced element, a table or a flex or grid container: a box whose contents depend
on its height, or that sizes itself (`Children.heightSensitive`). -/
private def sizesItself (dom : Dom) (styles : Array Computed) (pictures : Pictures) (id : Nat) : Bool :=
  let s := styles[id]!
  let n := dom.get id
  s.display.isFlex || s.display.isGrid || s.display.isTable || (pictures id).isSome ||
    (blankReplaced n).isSome || n.ns == some DOM.svgNS || n.lname == "hr" || s.pos.containsAbsolutes

private def cellStyle (styles : Array Computed) : Table.Source → Computed
  | .element id => styles[id]!
  | .anonymous parent _ => anonymousBox styles[parent]!
private def cellContents (dom : Dom) : Table.Source → Nat × Array Nat
  | .element id => (id,(dom.get id).kids)
  | .anonymous parent kids => (parent,kids)

/-- The space between the content and border edges of a table or cell. The
  collapsing border model keeps its existing sizing until it resolves shared edges. -/
private def tableInsets (s : Computed) (collapsed : Bool) : Edges :=
  if collapsed then s.padding else
  let b := s.borderEdges
  ⟨s.padding.top+b.top, s.padding.right+b.right, s.padding.bottom+b.bottom, s.padding.left+b.left⟩

/-- Intrinsic column contributions include the cell's padding and separated borders. -/
private def cellMeasure (s : Computed) (collapsed : Bool) (widths : Float × Float) : Table.Measure :=
  let insets := tableInsets s collapsed
  let pad := insets.left+insets.right
  {min := widths.1+pad, max := widths.2+pad,
   fixed := match s.width with | .px w => some (w+pad) | _ => none,
   percent := match s.width with | .percent p => some p | _ => none}
private def columnMeasure (styles : Array Computed) : Option Nat → Table.Measure
  | none => {}
  | some id => match (styles[id]!).width with
    | .px w => {fixed := some w}
    | .percent p => {percent := some p}
    | _ => {}

/-- Table width inputs shared by measuring and laying out. -/
private structure TableFrame where
  style : Computed
  margin : Edges
  insets : Edges
  borderBox : Bool
  hs : Float
  vs : Float

private def tableFrame (styles : Array Computed) (element : Option Nat) (container : Nat) : TableFrame :=
  let s := match element with
    | some id => styles[id]!
    | none => {anonymousBox styles[container]! with display := .table, tableFixed := false}
  let edges := element.isSome
  { style := s
    margin := if edges then s.margin else {}
    insets := if edges then tableInsets s s.borderCollapse else {}
    borderBox := s.pos.borderBox || s.borderCollapse
    hs := if s.borderCollapse then 0 else s.borderSpacingX
    vs := if s.borderCollapse then 0 else s.borderSpacingY }

/-- A content width within the box's `min-width` and `max-width` when they are lengths
(a percentage or a keyword limit does not bound an intrinsic contribution); the minimum
wins over the maximum (CSS 2.1 §10.4). -/
def intrinsicLimits (s : Computed) (w : Float) : Float :=
  let w := match s.maxWidth with
    | .px m => min w m
    | _ => w
  match s.minWidth with
  | .px m => max w m
  | _ => w

/-- With no length limit the width stands. -/
theorem intrinsicLimits_none (s : Computed) (w : Float) (hi : ∀ m, s.maxWidth ≠ .px m) (lo : ∀ m, s.minWidth ≠ .px m) :
    intrinsicLimits s w = w := by
  unfold intrinsicLimits
  cases hmax : s.maxWidth <;> cases hmin : s.minWidth <;>
    first | rfl | exact absurd hmax (hi _) | exact absurd hmin (lo _)

/-- A `min-width` that is a length is the last word: the result is the larger of it and
the width within the maximum. -/
theorem intrinsicLimits_min (s : Computed) (w m : Float) (lo : s.minWidth = .px m) :
    ∃ v, intrinsicLimits s w = max v m := by
  unfold intrinsicLimits
  simp only [lo]
  exact ⟨_, rfl⟩

/-- A `width` or `max-width` that is a percentage (CSS Sizing 3 §5.2.2). -/
def compressibleWidth (s : Computed) : Bool :=
  (match s.width with | .percent _ => true | _ => false) || (match s.maxWidth with | .percent _ => true | _ => false)

/-- CSS Sizing 3 §5.2.2: a replaced element whose `width` or `max-width` is a percentage is
compressible. Its percentage is of a width that depends on its own, so its min-content
contribution is its size against zero: its `min-width` when that is a length, else 0, with
its edges. In a line (an `img` inside a block, as most pages have it) the atom of the
picture is that wide for the min-content width; its max-content width keeps its natural
size. Any other item is as it was. -/
def compressInline : Inline → Inline
  | .replaced id s ow oh nodes =>
    if compressibleWidth s then .replaced id s (min ow (intrinsicLimits s 0+horizontalEdges s)) oh nodes
    else .replaced id s ow oh nodes
  | other => other

/-- A replaced atom whose `width` and `max-width` are not percentages is not changed. -/
theorem compressInline_fixed (id : Nat) (s : Computed) (ow oh : Float) (nodes : List Node)
    (h : compressibleWidth s = false) :
    compressInline (.replaced id s ow oh nodes) = .replaced id s ow oh nodes := by
  simp [compressInline, h]

/-- Words, spaces and every item that is not a replaced atom are not changed. -/
theorem compressInline_word (id : TextSource) (s : Computed) (text : String) (start : Nat) :
    compressInline (.word id s text start) = .word id s text start := rfl

/-- Min-content and max-content widths (CSS Sizing 3 §5), margins included for a box.
Text is measured with `inlineLayout` itself: with no room, every break opportunity is
taken (min-content); with unbounded room, none is (max-content). A table's widths are
those of its columns (`Table.columns`). Fuel is shared with `layoutTask`: one level per
element or table. -/
def intrinsic (dom : Dom) (styles : Array Computed) (font : FontProfile) (embedding : Embedding) (pictures : Pictures) :
    Nat → Task → Except String (Float × Float)
  | 0, _ => throw "unsupported HTML nesting depth (maximum 64)"
  | fuel+1, task => do
    -- CSS Text 3 §8.3: the first line's `text-indent` counts in both widths (a percentage
    -- counts as 0 here, CSS Sizing 3 §5.2.1, cyclic percentages)
    let inlineWidths (items : Array Inline) (indent : Float := 0) : Except String (Float × Float) := do
      if items.isEmpty then return (0,0)
      let strut : Option Computed := if indent == 0 then none else some {textIndent := .px indent, textAlign := .left}
      let narrow ← inlineLayout font (← atomize font (items.map compressInline) 0) 0 0 0 strut
      let wide ← inlineLayout font (← atomize font items 1.0e9) 0 0 1.0e9 strut
      return (lineExtent narrow,lineExtent wide)
    let flowWidths (container : Nat) (kids : Array Nat) (lead : Array Inline) : Except String (Float × Float) := do
      let mut widths : Float × Float := (0,0)
      let mut inline := lead
      -- The max-content widths of the floats so far that nothing has cleared (CSS 2.1
      -- §9.5): with all the room they sit side by side, and the lines and boxes after them
      -- are beside them. With no float in the flow this stays 0.
      let mut beside : Float := 0
      for seg in Table.segments dom styles (liftBlocks dom styles kids) do
        match seg with
        | .run run =>
          let (a,b) ← inlineWidths inline (match (styles[container]?.map (·.textIndent)) with | some (CSS.Length.px n) => n | _ => 0)
          inline := #[]
          let (c,d) ← intrinsic dom styles font embedding pictures fuel (.table none container run)
          widths := (max widths.1 (max a c),max widths.2 (max (b+beside) (d+beside)))
        | .node k =>
          if (styles[k]!).pos.isAbsolute then pure ()
          else if (styles[k]!).pos.float != .none then
            let (c,d) ← intrinsic dom styles font embedding pictures fuel (.box k)
            if (styles[k]!).pos.clear != .none then
              widths := (widths.1,max widths.2 beside)
              beside := 0
            widths := (max widths.1 c,widths.2)
            beside := beside+d
          else if (styles[k]!).display.isBlockLevel || (styles[k]!).display.isInlineContainer then
            let (a,b) ← inlineWidths inline (match (styles[container]?.map (·.textIndent)) with | some (CSS.Length.px n) => n | _ => 0)
            inline := #[]
            widths := (max widths.1 a,max widths.2 (b+beside))
            if (styles[k]!).pos.clear != .none then beside := 0
            let (c,d) ← intrinsic dom styles font embedding pictures fuel (.box k)
            widths := (max widths.1 c,max widths.2 (d+beside))
          else
            inline := inline ++ (← inlineItems dom styles embedding pictures 0 fuel k)
      let (a,b) ← inlineWidths inline (match (styles[container]?.map (·.textIndent)) with | some (CSS.Length.px n) => n | _ => 0)
      return (max widths.1 a,max widths.2 (b+beside))
    let tableWidths (element : Option Nat) (container : Nat) (kids : Array Nat) : Except String (Float × Float) := do
      let frame := tableFrame styles element container
      let grid := Table.build dom styles (element.getD container) kids
      let mut measures : Array Table.Measure := #[]
      for cell in grid.cells do
        let (c,ks) := cellContents dom cell.source
        measures := measures.push (cellMeasure (cellStyle styles cell.source) frame.style.borderCollapse (← intrinsic dom styles font embedding pictures fuel (.contents c ks)))
      let cols := Table.columns grid.columns grid.cells measures (grid.columnElements.map (columnMeasure styles)) frame.hs
      let spacing := if grid.columns == 0 then 0 else frame.hs*Float.ofNat (grid.columns+1)
      let edges := frame.insets.left+frame.insets.right
      let low := Table.total (cols.map (·.min))+spacing+edges
      let high := max low (Table.total ((Table.guesses cols 0)[3]!)+spacing+edges)
      let margins := frame.margin.left+frame.margin.right
      match frame.style.width with
      | .px w =>
        let borderWidth := if frame.borderBox then w else w+edges
        let result := max borderWidth low+margins
        return (result,result)
      | _ => return (low+margins,high+margins)
    -- What a flex or grid container may ask of its items while widths are measured.
    let children : Children := {
      style := fun item => match item with
        | .element id => styles[id]!
        | .anonymous container _ => anonymousItem styles[container]!
      intrinsic := fun item => match item with
        | .element id => intrinsic dom styles font embedding pictures fuel (.box id)
        | .anonymous container kids => intrinsic dom styles font embedding pictures fuel (.contents container kids)
      contentIntrinsic := fun item => match item with
        | .element id => intrinsic dom styles font embedding pictures fuel (.inner id 0)
        | .anonymous container kids => intrinsic dom styles font embedding pictures fuel (.contents container kids)
      layout := fun _ _ _ _ => throw "layout asked of an item while widths are measured"
      content := fun _ _ _ _ => throw "layout asked of an item while widths are measured"
      frame := fun _ _ _ _ _ r => r
      heightSensitive := fun _ => true}
    -- The widths of an element's box. `outer`: of its margin box, as its `width` has it;
    -- else of its contents alone, whatever its `width` says (`Children.contentIntrinsic`).
    let boxWidths (id : Nat) (outer : Bool) : Except String (Float × Float) := do
      let n := dom.get id
      let s := styles[id]!
      if s.display == .none then return (0,0)
      let edges := horizontalEdges s
      -- What the box adds to its contents' widths.
      let add := if outer then edges else 0
      if s.display.isTable then
        -- A table's widths are those of its border box with its margins (`tableWidths`).
        let (a,b) ← tableWidths (some id) (n.parent.getD 0) n.kids
        let margins := if outer then 0 else s.margin.left+s.margin.right
        return (a-margins,b-margins)
      -- A replaced element whose `width` or `max-width` is a percentage is compressible
      -- (CSS Sizing 3 §5.2.2): the percentage is of a width that depends on this one, so its
      -- min-content contribution is what is left of it against zero, its `min-width`.
      let compressible := fun (w : Float) => match s.width,s.maxWidth with
        | .percent _,_ | _,.percent _ => min w (intrinsicLimits s 0)
        | _,_ => w
      if let some picture := pictures id then
        let w := (replacedSize s (some picture.size) 0).1
        return (compressible w+add,w+add)
      if let some size := blankReplaced n then
        let w := (replacedSize s size 0).1
        return (compressible w+add,w+add)
      if n.ns == some DOM.svgNS then
        let w := (← svgSize n s 0).1+add
        return (w,w)
      -- The contribution of a box is within its `min-width` and `max-width` when they are
      -- lengths (CSS Sizing 3 §5.1): a box is never laid out outside them, so its container
      -- must not be sized as if it were.
      let within := fun (w : Float) => if outer then intrinsicLimits s w else w
      match outer,s.width with
      | true,.px w => return (within w+edges,within w+edges)
      | _,_ =>
        if s.display.isFlex then
          let (a,b) ← flexIntrinsic children s (collectItems dom styles id)
          return (within a+add,within b+add)
        if s.display.isGrid then
          let (a,b) ← gridIntrinsic children s (collectItems dom styles id)
          return (within a+add,within b+add)
        -- an outside marker (the default) takes no room in the item's lines
        let lead := if n.lname == "li" && s.pos.listInside then (textItems (.node id) s (listMarker dom font s.pos.listStyle id)).toArray
          else if n.lname == "img" then altItems id s n else controlItems dom id s
        let (a,b) ← flowWidths id n.kids lead
        return (within a+add,within b+add)
    match task with
    | .contents container kids => flowWidths container kids #[]
    | .table element container kids => tableWidths element container kids
    | .sized id _ _ | .box id | .flowed id _ => boxWidths id true
    | .inner id _ => boxWidths id false
    | .positioned _ _ _ _ _ => return (0,0)
    | .rough inner => intrinsic dom styles font embedding pictures fuel inner

/-- HTML §15.5.13: the rendered legend of a `fieldset` is its first `legend` child that is
in flow (not floated, not absolutely positioned). Its width shrinks to fit. One test of
the name for any other element. -/
def renderedLegend (dom : Dom) (styles : Array Computed) (id : Nat) : Bool :=
  let n := dom.get id
  n.lname == "legend" && n.type == .element &&
  match n.parent with
  | some p =>
    (dom.get p).lname == "fieldset" &&
      ((dom.get p).kids.find? fun k =>
        (dom.get k).type == .element && (dom.get k).lname == "legend" && (styles[k]!).display != .none &&
          !(styles[k]!).pos.isAbsolute && (styles[k]!).pos.float == .none) == some id
  | none => false

/-- Is the physical axis's logical start at its far edge? -/
private def axisStartIsFar (s : Computed) (horizontal : Bool) : Bool :=
  SelfPlace.startsAtEnd horizontal (s.pos.writingMode != .horizontalTb)
    (s.pos.writingMode == .verticalRl) (s.direction == .rtl)

#guard axisStartIsFar {pos := {writingMode := .verticalRl}} true
#guard !(axisStartIsFar {pos := {writingMode := .verticalLr}, direction := .rtl} true)
#guard axisStartIsFar {pos := {writingMode := .verticalLr}, direction := .rtl} false

/-- The fraction of an anchor box's size, from its top or left edge, at which the side an
`anchor()` names lies (CSS Anchor Positioning 1 §3.2), for an inset of the horizontal axis or
the vertical one, on the far side (`right`, `bottom`) or not. `start` and `end` are of the
containing block's writing mode (`startFar`), `self-start` and `self-end` of
its own writing mode (`selfStartFar`). A percentage is from the start side. `none`: a side of the other axis. -/
def anchorFraction (side : AnchorSide) (horizontal far startFar selfStartFar : Bool) : Option Float :=
  let flip := fun (f : Float) (r : Bool) => if r then 1 - f else f
  match side with
  | .left => if horizontal then some 0 else none
  | .right => if horizontal then some 1 else none
  | .top => if horizontal then none else some 0
  | .bottom => if horizontal then none else some 1
  | .center => some 0.5
  | .start => some (flip 0 startFar)
  | .end_ => some (flip 1 startFar)
  | .selfStart => some (flip 0 selfStartFar)
  | .selfEnd => some (flip 1 selfStartFar)
  | .inside => some (if far then 1 else 0)
  | .outside => some (if far then 0 else 1)
  | .fraction f => some (flip f startFar)

#guard anchorFraction .right true false false false == some 1 && anchorFraction .right false false false false == none
#guard anchorFraction .start true false true false == some 1 && anchorFraction .outside false true false false == some 0

/-- The border box `(x, y, width, height)` of the anchor named `name` among `boxes`: of the
last element in tree order whose `anchor-name` holds it (an element's first box is its own
border box). -/
def anchorBoxIn (styles : Array Computed) (boxes : Array Box) (name : String) :
    Option (Float × Float × Float × Float) := Id.run do
  let mut found : Option (Float × Float × Float × Float) := none
  let mut last : Option Nat := none
  for b in boxes do
    if last != some b.source && ((styles[b.source]?).map (·.pos.anchorNames.contains name)).getD false then
      found := some (b.x, b.y, b.width, b.height)
      last := some b.source
  return found

/-- The style of the box whose padding box is the containing block of the absolutely
positioned box `id` (CSS 2.1 §10.1): its nearest ancestor that holds absolutely positioned
boxes (`containsAbsolutes`), else the root element's. A loop up the ancestors. -/
def absoluteContainer (dom : Dom) (styles : Array Computed) (id : Nat) : Computed := Id.run do
  let mut cur := id
  let mut last := styles[id]!
  for _ in [0:dom.size+1] do
    match (dom.get cur).parent with
    | some p =>
      if (dom.get p).type != .element then return last
      let s := styles[p]!
      if s.pos.containsAbsolutes then return s
      last := s
      cur := p
    | none => return last
  return last

/-- Block children stack vertically, and adjacent inline children share an
anonymous inline formatting context. Width/height use the CSS content box.
Tables are laid out by the table model (`Table`): see `layoutTask`'s `.table` case.
Every descent to `layoutTask`, `intrinsic` or `inlineItems` passes the predecessor
`fuel`, and the compiled sibling folds are loops. This lower-level API has
stack depth O(fuel); production `render` starts it with the fixed budget 64.
The budget is shared across block, table and inline descendants, never reset for
a formatting context. See `docs/20261103-layout-stack-audit.md`. -/
def layoutTask (dom : Dom) (styles : Array Computed) (font : FontProfile) (embedding : Embedding) (pictures : Pictures) :
    Nat → Task → Float → Float → Float → Except String Result
  | 0, _, _, _, _ => throw "unsupported HTML nesting depth (maximum 64)"
  | fuel+1, task, x, y, available => do
    -- A task wrapped in `Task.rough` is a measuring pass (`Constraints.measure`): what it
    -- lays out is in that mode too (`sub`), so no nested container doubles the work.
    let measure := match task with
      | .rough _ => true
      | _ => false
    let task := match task with
      | .rough inner => inner
      | other => other
    let sub := fun (t : Task) => if measure then Task.rough t else t
    -- The flow of `kids` in a block container with style `s`: block-level children
    -- stack, inline children share line boxes, runs of internal table boxes are tables.
    -- `before` is the margin that adjoins the top of the flow (the container's own, when it
    -- collapses with its first child; else 0); the result's `marginBottom` is the margin at
    -- the end of the flow. Adjoining margins of sibling blocks collapse: the larger stands.
    let flow (s : Computed) (container : Nat) (kids : Array Nat) (lead : Array Inline)
        (innerX innerY width : Float) (before : Float := 0) (around : Array Floats.Box := #[])
        (definite : Option Float := none) : Except String Result := do
      let mut content : Result := {}
      let mut previous : Float := before
      let mut inline : Array Inline := lead
      -- The floats of this block formatting context so far (CSS 2.1 §9.5): those it began
      -- with (`around`) and those of this flow. Lines, and boxes that establish a formatting
      -- context of their own, take the room beside them.
      let mut floats : Array Floats.Box := around
      for seg in Table.segments dom styles (liftBlocks dom styles kids) do
        match seg with
        | .run run =>
          if !inline.isEmpty then
            let top := innerY+content.height
            let lines ← inlineLayout font (← atomize font inline width) innerX top width (some s)
              (fun dy => floatBand floats innerX width (top+dy) s.lineHeight)
            content := append content lines
            inline := #[]
          let (offset,room) := floatBand floats innerX width (innerY+content.height) 1
          content := append content (← layoutTask dom styles font embedding pictures fuel (sub <| .table none container run) (innerX+offset) (innerY+content.height) room)
          previous := 0
        | .node child =>
          -- CSS 2.1 §10.5: a percentage height that the styles alone left open (`percentHeights`)
          -- is of this container's content height when layout made that definite (`definite`:
          -- a stretched flex item, a box between two insets). The child is laid out with the
          -- length; a flow with no such child copies nothing.
          let styles := match definite with
            | none => styles
            | some h =>
              let c := styles[child]!
              if c.pos.isAbsolute then styles else
              match c.height with
              | .percent p => styles.set! child {c with height := .px (max 0 (h*p))}
              | .calc p v => styles.set! child {c with height := .px (max 0 (h*p+v))}
              | _ => styles
          let cs := styles[child]!
          if cs.pos.isAbsolute then
            -- Out of flow (CSS 2.1 §9.6): pending at its static position, which is where the
            -- flow has got to, or its place in the open line.
            if inline.isEmpty then content := {content with pending := content.pending.push {id := child, x := innerX, y := innerY+content.height}}
            else inline := inline.push (.outOfFlow child)
          else if cs.pos.float != .none then
            -- A float (CSS 2.1 §9.5.1): out of flow, as wide as its `width` or its content
            -- (§10.3.5), at the first place beside the earlier floats where it fits, not
            -- above them. Text of the same block that comes before it goes round it too.
            let outer ← match CSS.resolve width cs.width with
              | some w => pure (clampOpt ((CSS.resolve width cs.minWidth).getD 0) (CSS.resolve width cs.maxWidth) w+horizontalEdges cs)
              | none => do
                let (lo,hi) ← intrinsic dom styles font embedding pictures fuel (.box child)
                pure (shrinkWidth cs.width lo hi width)
            let top := floats.foldl (fun t f => max t (LU.toPx f.y)) (innerY+content.height)
            let top := match cs.pos.clear with
              | .none => top
              | c => LU.toPx (Floats.clearY floats.toList (c != .right && c != .inlineEnd) (c != .left && c != .inlineStart) (LU.ofPx top))
            let r ← layoutTask dom styles font embedding pictures fuel
              (sub <| .sized child (max 0 (outer-cs.margin.left-cs.margin.right)) none) innerX top width
            let ltr := s.direction == .ltr
            let left := match cs.pos.float with
              | .left => true
              | .right => false
              | .inlineStart => ltr
              | _ => !ltr
            -- a float's margin box has no negative size here (negative margins on a float pull nothing)
            let (fx,fy) := Floats.place floats.toList left (LU.ofPx innerX) (LU.ofPx width) (LU.ofPx (max 0 outer)) (LU.ofPx (max 0 r.height)) (LU.ofPx top)
            let r := r.shift (LU.toPx fx-innerX) (LU.toPx fy-top)
            content := {content with nodes := content.nodes ++ r.nodes, boxes := content.boxes ++ r.boxes,
                                     runs := content.runs ++ r.runs, pending := content.pending ++ r.pending,
                                     work := content.work+r.work, rough := content.rough || r.rough}
            floats := floats.push ⟨left,fx,fy,LU.ofPx (max 0 outer),LU.ofPx (max 0 r.height)⟩
          else if cs.display.isBlockLevel then
            if !inline.isEmpty then
              let top := innerY+content.height
              let lines ← inlineLayout font (← atomize font inline width) innerX top width (some s)
                (fun dy => floatBand floats innerX width (top+dy) s.lineHeight)
              content := append content lines
              inline := #[]
              -- white space between blocks makes no line: the margins still adjoin
              if lines.height > 0 then previous := 0
            -- CSS 2.1 §9.5.2: `clear` moves the box below the floats of those sides; the
            -- clearance keeps its margin apart from the one before.
            if cs.pos.clear != .none then
              let c := cs.pos.clear
              let here := innerY+content.height
              let cleared := LU.toPx (Floats.clearY floats.toList (c != .right && c != .inlineEnd) (c != .left && c != .inlineStart) (LU.ofPx here))
              if cleared > here then
                content := {content with height := content.height+(cleared-here)}
                previous := 0
            -- CSS 2.1 §8.3.1: the margin before this box and its own top margin collapse.
            let lead := if cs.display == .block then leadMargin dom styles fuel child else cs.margin.top
            let overlap := overlapPx previous lead
            let top := innerY+content.height-overlap
            -- §9.5: a plain block is part of this formatting context: it is laid out under the
            -- floats with its lines beside them, and floats inside it stay in the context for
            -- what follows it (`Task.flowed`). A box with a formatting context of its own (a
            -- table, a flex container, a box that clips, a replaced element) is beside the floats.
            let cn := dom.get child
            let plain := cs.display == .block && !cs.clipOverflow && !cs.pos.formattingRoot && (pictures child).isNone &&
              (blankReplaced cn).isNone && cn.ns != some DOM.svgNS && cn.lname != "hr"
            let r ← if plain then layoutTask dom styles font embedding pictures fuel (sub <| .flowed child floats) innerX top width
              else if floats.isEmpty then layoutTask dom styles font embedding pictures fuel (sub <| .box child) innerX top width
              else do
                let (offset,room) := floatBand floats innerX width top 1
                layoutTask dom styles font embedding pictures fuel (sub <| .box child) (innerX+offset) top room
            -- the floats of a context only grow
            if plain && r.floats.size >= floats.size then floats := r.floats
            -- CSS 2.1 §8.3.1: a block with no height, border, padding or line box collapses
            -- through: its own two margins are one margin, which joins the margin before it
            -- (and, as `previous`, the one after it). At the top of a flow whose container
            -- shows the first margin (`unbounded`) it is stacked as before.
            let through := cs.display == .block && previous < unbounded/2 && r.runs.isEmpty &&
              collapsesTop dom cs child && collapsesBottom dom cs child && (r.height-lead-r.marginBottom).abs < 0.001
            if through then
              let joined := collapsePx previous (collapsePx lead r.marginBottom)
              content := {append content r with height := content.height-previous+joined}
              previous := joined
            else
              content := {append content r with height := content.height-overlap+r.height}
              previous := r.marginBottom
          else if cs.display.isInlineContainer || (cs.display == .inlineBlock && blockInside dom styles child) then
            -- An inline-level flex or grid container, or an inline-block with blocks inside:
            -- one atomic box, as wide as its content (shrink-to-fit, CSS 2.1 §10.3.9) unless
            -- its width is given.
            let edges := cs.margin.left+cs.margin.right
            let outer ← match CSS.resolve width cs.width with
              | some w => pure (clampOpt ((CSS.resolve width cs.minWidth).getD 0) (CSS.resolve width cs.maxWidth) w+horizontalEdges cs)
              | none => do
                let (lo,hi) ← intrinsic dom styles font embedding pictures fuel (.box child)
                pure (shrinkWidth cs.width lo hi width)
            let r ← layoutTask dom styles font embedding pictures fuel (sub <| .sized child (max 0 (outer-edges)) none) 0 0 width
            inline := inline.push (.atomic child cs outer r.height r)
          else
            inline := inline ++ (← inlineItems dom styles embedding pictures width fuel child)
      if !inline.isEmpty then
        let top := innerY+content.height
        let lines ← inlineLayout font (← atomize font inline width) innerX top width (some s)
          (fun dy => floatBand floats innerX width (top+dy) s.lineHeight)
        content := append content lines
        if lines.height > 0 then previous := 0
      content := {content with floats}
      -- no block was laid out: `previous` is still `before`, which is not a margin of this flow
      return {content with marginBottom := if content.height <= 0 || previous >= unbounded/2 then 0 else previous}
    -- A table box (CSS 2.1 §17): captions, then the grid, then bottom captions.
    let table (element : Option Nat) (container : Nat) (kids : Array Nat)
        (imposedWidth imposedHeight : Option Float) : Except String Result := do
      let frame := tableFrame styles element container
      let ts := frame.style
      let grid := Table.build dom styles (element.getD container) kids
      let (hs,vs) := (frame.hs,frame.vs)
      -- Column widths from the cells' min-content and max-content widths.
      let mut measures : Array Table.Measure := #[]
      for cell in grid.cells do
        let (c,ks) := cellContents dom cell.source
        measures := measures.push (cellMeasure (cellStyle styles cell.source) frame.style.borderCollapse (← intrinsic dom styles font embedding pictures fuel (.contents c ks)))
      let elements := grid.columnElements.map (columnMeasure styles)
      let cols := Table.columns grid.columns grid.cells measures elements hs
      let spacing := if grid.columns == 0 then 0 else hs*Float.ofNat (grid.columns+1)
      let padX := frame.insets.left+frame.insets.right
      let padY := frame.insets.top+frame.insets.bottom
      let lowest := Table.total (cols.map (·.min))+spacing
      let authoredWidth := CSS.resolve available ts.width
      let specified := match imposedWidth with
        | some w => some (w-padX)
        | none => authoredWidth.map fun w => if frame.borderBox then w-padX else w
      let room := available-frame.margin.left-frame.margin.right-padX
      let contentWidth := match specified with
        | some w => max w lowest
        | none => max lowest (min room (Table.total ((Table.guesses cols room)[3]!)+spacing))
      let target := max 0 (contentWidth-spacing)
      let widths := if ts.tableFixed && authoredWidth.isSome then
          let firstRow := (grid.cells.zip measures).filter (·.1.row == 0)
          Table.fixedWidths grid.columns firstRow elements target hs
        else Table.distribute cols target
      let contentWidth := max contentWidth (Table.extent widths hs)
      let borderWidth := contentWidth+padX
      let shift := if imposedWidth.isSome then 0
        else autoMarginShift ts available (frame.margin.left+borderWidth+frame.margin.right)
      let outerX := x+shift+frame.margin.left
      let innerX := outerX+frame.insets.left
      let colX := Table.offsets widths hs
      -- Each cell laid out once, at its column and at the top; moved down when the rows are known.
      let mut laid : Array (Result × Float) := #[]
      for cell in grid.cells do
        let cs := cellStyle styles cell.source
        let (c,ks) := cellContents dom cell.source
        let w := Table.spanSize widths cell.col cell.colSpan hs
        let insets := tableInsets cs ts.borderCollapse
        let left := innerX+colX.getD cell.col 0+insets.left
        let r ← layoutTask dom styles font embedding pictures fuel (sub <| .contents c ks)
          left insets.top (max 0 (w-insets.left-insets.right))
        let own := (CSS.resolve 0 cs.height).getD 0
        let outer := max r.height own+insets.top+insets.bottom
        laid := laid.push (r,outer)
      let minimum := grid.rows.map fun row => match row.element with
        | some id => (CSS.resolve 0 (styles[id]!).height).getD 0
        | none => 0
      let rows := Table.rowHeights minimum grid.cells (laid.map (·.2)) vs
      let gridHeight := Table.extent rows vs
      let specifiedBorderHeight := imposedHeight.orElse fun _ =>
        (CSS.resolve 0 ts.height).map fun h => if frame.borderBox then h else h+padY
      let rows := match specifiedBorderHeight with
        | some h => Table.stretch rows (h-padY-gridHeight)
        | none => rows
      let gridHeight := Table.extent rows vs
      let borderHeight := max (gridHeight+padY) (specifiedBorderHeight.getD 0)
      let rowY := Table.offsets rows vs
      -- Captions above and below, as wide as the table's border box.
      let mut out : Result := {}
      let mut top := y+frame.margin.top
      for caption in grid.captions do
        if !(styles[caption]!).captionBottom then
          let r ← layoutTask dom styles font embedding pictures fuel (sub <| .box caption) outerX top borderWidth
          out := append out r
          top := top+r.height
      let innerY := top+frame.insets.top
      let tableId := element.getD container
      let mut nodes : Array Node := if ts.borderCollapse then background tableId ts outerX top borderWidth borderHeight
        else decorations tableId ts outerX top borderWidth borderHeight
      let mut paints : Array Node := #[]
      let mut boxes : Array Box := #[]
      let mut runs : Array GlyphRun := #[]
      let mut pending : Array Pending := #[]
      let mut work : Nat := 0
      let mut rough := false
      for (cell,(r,outer)) in grid.cells.zip laid do
        let cs := cellStyle styles cell.source
        let cx := innerX+colX.getD cell.col 0
        let cy := innerY+rowY.getD cell.row 0
        let w := Table.spanSize widths cell.col cell.colSpan hs
        let h := Table.spanSize rows cell.row cell.rowSpan vs
        -- The originating column and group paint under the row layers, within the
        -- cell's area even for a spanning cell (CSS 2.2 §17.5.1). A group with
        -- no child columns supplies the sizing ID; paint its colour only once.
        let columnGroup := grid.columnGroups.getD cell.col none
        let column := grid.columnElements.getD cell.col none
        if let some id := columnGroup then
          nodes := nodes ++ backgroundColour id styles[id]! cx cy w h
        if column != columnGroup then
          if let some id := column then
            nodes := nodes ++ backgroundColour id styles[id]! cx cy w h
        let row := grid.rows.getD cell.row ⟨none,none⟩
        for layer in [row.group,row.element] do
          if let some id := layer then nodes := nodes ++ background id (styles[id]!) cx cy w h
        if let .element id := cell.source then
          nodes := nodes ++ decorations id cs cx cy w h
          boxes := boxes.push ⟨id,cx,cy,w,h⟩
        let moved := r.shiftY (cy+Table.alignOffset cs.verticalAlign h outer)
        paints := paints ++ moved.nodes
        boxes := boxes ++ moved.boxes
        runs := runs ++ moved.runs
        pending := pending ++ moved.pending
        work := work+r.work
        rough := rough || r.rough
      let tableBox : Array Box := match element with
        | some id => #[⟨id,outerX,top,borderWidth,borderHeight⟩]
        | none => #[]
      out := {out with nodes := out.nodes ++ nodes ++ paints, boxes := out.boxes ++ tableBox ++ boxes,
                       runs := out.runs ++ runs, height := out.height+borderHeight,
                       pending := out.pending ++ pending, work := out.work+work, rough := out.rough || rough}
      top := top+borderHeight
      for caption in grid.captions do
        if (styles[caption]!).captionBottom then
          let r ← layoutTask dom styles font embedding pictures fuel (sub <| .box caption) outerX top borderWidth
          out := append out r
          top := top+r.height
      return {out with height := top-y+frame.margin.bottom}
    -- What a flex or grid container may ask of its items (`Rendering/Fragment.lean`): every
    -- callback descends with the smaller fuel.
    let children : Children := {
      style := fun item => match item with
        | .element id => styles[id]!
        | .anonymous container _ => anonymousItem styles[container]!
      intrinsic := fun item => match item with
        | .element id => intrinsic dom styles font embedding pictures fuel (.box id)
        | .anonymous container kids => intrinsic dom styles font embedding pictures fuel (.contents container kids)
      contentIntrinsic := fun item => match item with
        | .element id => intrinsic dom styles font embedding pictures fuel (.inner id 0)
        | .anonymous container kids => intrinsic dom styles font embedding pictures fuel (.contents container kids)
      layout := fun item ix iy c => match item with
        | .element id => match c.width with
          | some w => layoutTask dom styles font embedding pictures fuel
              (if c.measure then Task.rough (.sized id w c.height) else sub <| .sized id w c.height) ix iy c.available
          | none => layoutTask dom styles font embedding pictures fuel
              (if c.measure then Task.rough (.box id) else sub <| .box id) ix iy c.available
        | .anonymous container kids =>
          layoutTask dom styles font embedding pictures fuel (sub <| .contents container kids) ix iy (c.width.getD c.available)
      content := fun item ix iy w => match item with
        | .element id => layoutTask dom styles font embedding pictures fuel (sub <| .inner id w) ix iy w
        | .anonymous container kids => layoutTask dom styles font embedding pictures fuel (sub <| .contents container kids) ix iy w
      frame := fun item ix iy w h content => match item with
        | .element id => let s := styles[id]!; frameBox id s (ix+s.margin.left) (iy+s.margin.top) w h content
        | .anonymous _ _ => {content with height := h}
      heightSensitive := fun item => match item with
        | .element id => sizesItself dom styles pictures id
        | .anonymous _ _ => false}
    -- An absolutely positioned box (CSS 2.1 §10.3.7 and §10.6.4) in the containing block
    -- `(cx,cy,cw,ch)`; `at'` has its static position.
    let absolute (at' : Pending) (cx cy cw ch : Float)
        (anchors : String → Option (Float × Float × Float × Float) := fun _ => none) : Except String Result := do
      let id := at'.id
      let s := styles[id]!
      if s.display == .none then return {}
      let m := s.margin
      let b := s.borderEdges
      let p := s.padding
      let edgesX := b.left+b.right+p.left+p.right
      let edgesY := b.top+b.bottom+p.top+p.bottom
      -- `anchor()` insets (CSS Anchor Positioning 1 §3.2): the distance from the containing
      -- block's edge to the named side of the anchor's border box; with no such anchor (or a
      -- side of the other axis), the inset's own length, its fallback
      -- `position-area` (CSS Anchor Positioning 1 §3.1): the containing block is the area of the
      -- 3 × 3 grid that the default anchor's edges cut from it, and `auto` insets are 0
      let area := s.pos.positionArea.bind fun ((x0, x1), (y0, y1)) =>
        (s.pos.positionAnchor.bind anchors).map fun (ax, ay, aw, ah) =>
          let xs := #[cx, ax, ax+aw, cx+cw]
          let ys := #[cy, ay, ay+ah, cy+ch]
          (xs[x0]!, ys[y0]!, max 0 (xs[x1]!-xs[x0]!), max 0 (ys[y1]!-ys[y0]!))
      let (cx, cy, cw, ch) := area.getD (cx, cy, cw, ch)
      let autoInset : Option Float := if area.isSome then some 0 else none
      let containing := absoluteContainer dom styles id
      let anchored := fun (ref : Option AnchorRef) (horizontal far : Bool) => (show Option Float from
        ref.bind fun a => ((a.name.orElse fun _ => s.pos.positionAnchor).bind anchors).bind fun (ax, ay, aw, ah) =>
          (anchorFraction a.side horizontal far (axisStartIsFar containing horizontal) (axisStartIsFar s horizontal)).map fun f =>
            let (lo, size, cLo, cSize) := if horizontal then (ax, aw, cx, cw) else (ay, ah, cy, ch)
            let edge := lo + f * size
            if far then cLo + cSize - edge else edge - cLo)
      let left := ((anchored s.pos.anchorLeft true false).orElse fun _ => CSS.resolve cw s.pos.left).orElse fun _ => autoInset
      let right := ((anchored s.pos.anchorRight true true).orElse fun _ => CSS.resolve cw s.pos.right).orElse fun _ => autoInset
      let top := ((anchored s.pos.anchorTop false false).orElse fun _ => CSS.resolve ch s.pos.top).orElse fun _ => autoInset
      let bottom := ((anchored s.pos.anchorBottom false true).orElse fun _ => CSS.resolve ch s.pos.bottom).orElse fun _ => autoInset
      let specified := CSS.resolve cw s.width
      -- CSS Box Alignment 3 §6.1.2 and §6.2.2: `justify-self` and `align-self` of an
      -- absolutely positioned box; `auto` and `normal` are `stretch`.
      -- `justify-self` is for the inline axis of the containing block's writing mode and
      -- `align-self` for its block axis; `start` and `end` are sides of that writing mode,
      -- `self-start` and `self-end` of the box's own, `left` and `right` of the page.
      let plain := fun (a : CSS.ItemAlign) => a == .auto || a == .normal || a == .stretch
      let container := if plain s.align.justifySelf && plain s.align.alignSelf then s else containing
      let placeOn := fun (horizontalAxis : Bool) =>
        let inlineAxis := horizontalAxis != (container.pos.writingMode != .horizontalTb)
        let a := if inlineAxis then s.align.justifySelf else s.align.alignSelf
        -- in a `position-area`, `normal` aligns toward the anchor (CSS Anchor Positioning 1
        -- §3.1.3): the end of an area before it, the start of one after it, the centre of its own
        let toward := if area.isNone then none else
          s.pos.positionArea.map fun ((x0, x1), (y0, y1)) =>
            match if horizontalAxis then (x0, x1) else (y0, y1) with
            | (0, 1) | (0, 2) => SelfPlace.Place.end_
            | (2, 3) | (1, 3) => SelfPlace.Place.start
            | _ => SelfPlace.Place.center
        match a, toward with
        | .auto, some t | .normal, some t => t
        | .auto, _ | .normal, _ | .stretch, _ => SelfPlace.Place.stretch
        | .center, _ => .center
        | .end_, _ | .flexEnd, _ | .lastBaseline, _ => SelfPlace.Place.end_.physical (axisStartIsFar container horizontalAxis)
        | .selfStart, _ => SelfPlace.Place.start.physical (axisStartIsFar s horizontalAxis)
        | .selfEnd, _ => SelfPlace.Place.end_.physical (axisStartIsFar s horizontalAxis)
        | .left, _ => .start
        | .right, _ => .end_
        | _, _ => SelfPlace.Place.start.physical (axisStartIsFar container horizontalAxis)
      let placeX := placeOn true
      let placeY := placeOn false
      -- §10.3.7: the width is given, or fills the room between `left` and `right`, or
      -- shrinks to fit the content.
      let widthC ← match specified with
        | some w => pure w
        | none => match left,right with
          | some l,some r =>
            -- between two insets the box fills the room, unless its width is a keyword or
            -- it is aligned (then it is as wide as its content: fit-content)
            if s.width.isKeyword || placeX != .stretch then do
              let (lo,hi) ← intrinsic dom styles font embedding pictures fuel (.box id)
              pure (shrinkWidth s.width lo hi (cw-l-r)-m.left-m.right-edgesX)
            else pure (cw-l-r-m.left-m.right-edgesX)
          | _,_ => do
            let (lo,hi) ← intrinsic dom styles font embedding pictures fuel (.box id)
            pure (shrinkWidth s.width lo hi (cw-left.getD 0-right.getD 0)-m.left-m.right-edgesX)
      let widthC := max 0 (clampOpt ((CSS.resolve cw s.minWidth).getD 0) (CSS.resolve cw s.maxWidth) widthC)
      let borderW := widthC+edgesX
      let outerW := borderW+m.left+m.right
      let bx := match left,right with
        | some l,some r =>
          -- both insets: the room that is left goes to auto margins, else by `justify-self`
          cx+l+LU.toPx (SelfPlace.offset (LU.ofPx (cw-l-r)) (LU.ofPx outerW) s.autoMarginLeft s.autoMarginRight placeX)
        | some l,none => cx+l
        | none,some r => cx+cw-r-outerW
        | none,none => at'.x+at'.fx*(at'.width-outerW)
      -- §10.6.4: the height likewise; with none of these, the height of the content.
      let minH := (CSS.resolve ch s.minHeight).getD 0
      let maxH := CSS.resolve ch s.maxHeight
      let given := CSS.resolve ch s.height
      let imposed : Option Float := match given with
        | some h => some (clampOpt minH maxH (max 0 h)+edgesY)
        | none => match top,bottom with
          | some t,some e =>
            -- between two insets the box fills the room, unless its height is a keyword
            -- of the content or it is aligned (then it is as high as its content)
            let fills : Bool := match s.height with
              | .minContent | .maxContent | .fitContent => false
              | _ => placeY == .stretch
            if fills then some (max edgesY (clampOpt (minH+edgesY) (maxH.map (·+edgesY)) (ch-t-e-m.top-m.bottom))) else none
          | _,_ => none
      let by' := match top with
        | some t => cy+t
        | none => if bottom.isSome then cy else at'.y
      let r ← layoutTask dom styles font embedding pictures fuel (sub <| .sized id borderW imposed) bx by' cw
      match top,bottom with
      | none,none => return r.shift 0 (at'.fy*(at'.height-r.height))
      | none,some e => return r.shift 0 (cy+ch-e-r.height-by')
      | some t,some e =>
        -- both insets: the room that is left goes to auto margins, else by `align-self`
        return r.shift 0 (LU.toPx (SelfPlace.offset (LU.ofPx (ch-t-e)) (LU.ofPx r.height) s.autoMarginTop s.autoMarginBottom placeY))
      | _,_ => return r
    -- The pending absolutely positioned boxes of `content` laid out in the containing block
    -- `(cx,cy,cw,ch)`: those with a negative `z-index` under the content, the others over it,
    -- each group in `z-index` order, then tree order (CSS 2.1 Appendix E, in part). A `fixed`
    -- box stays pending until the root, whose containing block is the viewport.
    -- `area`: a containing block of its own for a pending box (a grid area, CSS Grid 2 §9.1).
    let place (content : Result) (cx cy cw ch : Float) (root : Bool)
        (area : Pending → Option (Float × Float × Float × Float)) : Except String Result := do
      if content.pending.isEmpty then return content
      let keyed := content.pending.map fun p => (((styles[p.id]!).pos.zIndex.getD 0 : Int),p)
      -- a stable sort: equal `z-index` keeps tree order
      let ordered := if keyed.all (fun k => k.1 == 0) then keyed
        else (keyed.toList.mergeSort fun a b => decide (a.1 ≤ b.1)).toArray
      let mut below : Result := {}
      let mut above : Result := {}
      let mut kept : Array Pending := #[]
      -- the anchors of `content` (CSS Anchor Positioning 1 §2): by name, the border box of the
      -- last element in tree order with that `anchor-name`; read only for an `anchor()` inset
      let anchors := fun (name : String) => anchorBoxIn styles content.boxes name
      for (z,p) in ordered do
        if (styles[p.id]!).pos.position == .fixed && !root then kept := kept.push p
        else
          let r ← match area p with
            | some (ax,ay,aw,ah) => absolute p ax ay aw ah anchors
            | none => absolute p cx cy cw ch anchors
          if z < 0 then below := below.over r else above := above.over r
      return {content with nodes := below.nodes ++ content.nodes ++ above.nodes,
                           boxes := content.boxes ++ below.boxes ++ above.boxes,
                           runs := content.runs ++ below.runs ++ above.runs,
                           pending := kept ++ below.pending ++ above.pending,
                           work := content.work+below.work+above.work}
    -- An element's box. `imposedWidth` and `imposedHeight` are the border-box sizes that the
    -- parent formatting context decided (`Task.sized`); with `contentOnly` the contents alone
    -- (`Task.inner`).
    let box (id : Nat) (imposedWidth imposedHeight : Option Float) (contentOnly : Bool)
        (around : Array Floats.Box := #[]) (participates : Bool := false) : Except String Result := do
      let n := dom.get id
      let s := styles[id]!
      if s.display == .none then return {}
      -- HTML §15.5.13: the rendered legend of a fieldset shrinks to fit its contents.
      let s := match s.width with
        | .auto => if renderedLegend dom styles id then {s with width := .fitContent} else s
        | _ => s
      if s.display.isTable then
        -- Collapsed tables still size their grid without resolving shared border edges.
        -- Keep their available-width input until the parent and table agree on those edges.
        if s.borderCollapse then
          match imposedWidth with
          | none => return (← table (some id) (n.parent.getD 0) n.kids none none)
          | some w =>
            return (← layoutTask dom styles font embedding pictures fuel
              (sub <| .table (some id) (n.parent.getD 0) n.kids) x y w)
        -- Separated tables consume the used border-box dimensions chosen by placement.
        return (← table (some id) (n.parent.getD 0) n.kids imposedWidth imposedHeight)
      let margin := s.margin
      let padding := s.padding
      let border := s.borderEdges
      let edgesX := border.left+border.right+padding.left+padding.right
      let edgesY := border.top+border.bottom+padding.top+padding.bottom
      if n.lname == "hr" then
        let w := imposedWidth.getD available
        return {nodes := #[.paint ⟨some id,{geometry := .rect x (y+8) w 1,style := {fill := .solid ⟨0.5,0.5,0.5⟩}}⟩],height := 17}
      -- CSS 2.1 §10.4: the width, then `max-width`, then `min-width` (a minimum wins).
      -- CSS Sizing 3 §3.2: `width`, `min-width` or `max-width` given as a keyword is a
      -- width of the contents (measured only when a keyword is used) or the fill width.
      let fill := available-margin.left-margin.right-edgesX
      let keyed := imposedWidth.isNone && (s.width.isKeyword || s.minWidth.isKeyword || s.maxWidth.isKeyword)
      let (contentLo,contentHi) ← if keyed then intrinsic dom styles font embedding pictures fuel (.inner id 0)
        else pure (0,0)
      let widthOf := fun (l : CSS.Length) => match keywordWidth l contentLo contentHi fill with
        | some w => some w
        | none => CSS.resolve available l
      let width := match imposedWidth with
        | some w => max 0 (w-edgesX)
        | none =>
          let width := (widthOf s.width).getD fill
          let width := match widthOf s.maxWidth with
            | some m => min width m
            | none => width
          max 0 (max ((widthOf s.minWidth).getD 0) width)
      -- The parent resolves an imposed box's margins. In horizontal normal flow,
      -- use the containing block's direction, even when the child has its own.
      let move := fun outer =>
        if imposedWidth.isSome then 0 else
        let containing := (n.parent.bind fun id => styles[id]?).getD s
        let rtl := s.display.isBlockLevel && containing.pos.writingMode == .horizontalTb &&
          containing.direction == .rtl
        blockMarginShift s rtl available outer
      let shift := move (margin.left+width+edgesX+margin.right)
      -- CSS 2.1 §8.3.1: a block in a block formatting context whose top margin adjoins its
      -- first child's shows the larger of the two, and the child starts at its top edge.
      let joinsTop := imposedWidth.isNone && !contentOnly && collapsesTop dom s id
      let marginTop := if joinsTop then leadMargin dom styles fuel id else margin.top
      let outerX := x+shift+margin.left
      let outerY := y+marginTop
      let innerX := outerX+border.left+padding.left
      let innerY := outerY+border.top+padding.top
      -- A block-level replaced element: its margin box at the start of the line, or where
      -- its auto margins put it.
      let replaced := fun (w h : Float) (content : Float → Float → List Node) (s : Computed) =>
        let (ow,oh,nodes) := replacedBox id s w h content
        let dx := move ow
        ({nodes := #[.group none (translate (x+dx) y) nodes],
          boxes := #[⟨id,x+dx+margin.left,outerY,ow-margin.left-margin.right,oh-margin.top-margin.bottom⟩],height := oh,
          marginBottom := margin.bottom} : Result)
      -- The style a replaced element is sized with: its own, or the imposed content box.
      let sized : Computed := match imposedWidth with
        | none => s
        | some _ => {s with width := .px width, minWidth := .auto, maxWidth := .auto,
                            height := match imposedHeight with | some h => .px (max 0 (h-edgesY)) | none => s.height}
      if let some picture := pictures id then
        let (w,h) := replacedSize sized (some picture.size) available
        return replaced w h (fun cx cy => pictureNodes id s picture cx cy w h) s
      if let some size := blankReplaced n then
        let (w,h) := replacedSize sized size available
        return replaced w h (fun _ _ => []) s
      if n.ns == some DOM.svgNS then
        let (sw,sh) ← svgSize n sized available
        let nodes ← if sw <= 0 || sh <= 0 then pure [] else embedding id s sw sh
        return replaced sw sh (fun cx cy => [.group none (translate cx cy) nodes]) {s with background := none}
      -- A list item's marker (CSS Lists 3 §3): the first thing in the first line with
      -- `list-style-position: inside`, else outside the box beside that line (below).
      let markerItems := if n.lname == "li" then (textItems (.node id) s (listMarker dom font s.pos.listStyle id)).toArray else #[]
      let lead := if n.lname == "img" then altItems id s n else if s.pos.listInside then markerItems else controlItems dom id s
      -- CSS 2.1 §10.7: the height within `min-height` and `max-height` (px; a percentage has
      -- no definite basis here). An imposed height is the parent's and is not clamped again.
      let minHeight := match s.minHeight with | .px h => h | _ => 0
      let maxHeight := match s.maxHeight with | .px h => some h | _ => none
      -- CSS Sizing 4 §5.1: with `aspect-ratio` and `height: auto` the height is that of the
      -- width by the ratio (of the border box with `box-sizing: border-box`). It is the least
      -- height (§5.2: the automatic minimum is the content) unless the box clips or has a
      -- `min-height` of its own: then it is the height.
      let ratioHeight : Option Float := match s.pos.ratio,s.height with
        | some (rn,rd),.auto =>
          if imposedHeight.isSome || rn == 0 || rd == 0 then none else
          let across := if s.pos.borderBox then width+edgesX else width
          let h := LU.toPx (Ratio.heightFor rn rd (LU.ofPx across))
          some (max 0 (if s.pos.borderBox then h-edgesY else h))
        | _,_ => none
      let ratioFixed := ratioHeight.isSome && (s.clipOverflow || (match s.minHeight with | .auto => false | _ => true))
      let minHeight := match ratioHeight with
        | some h => if ratioFixed then minHeight else max minHeight h
        | none => minHeight
      -- `min-height` or `max-height` of `min-content`, `max-content` or `fit-content` (CSS
      -- Sizing 3 §3.2): the limit is the height of the content, known after it is laid out.
      let contentKeyword := fun (l : CSS.Length) => match l with
        | .minContent | .maxContent | .fitContent => true
        | _ => false
      let contentLimits := contentKeyword s.minHeight || contentKeyword s.maxHeight
      let definite : Option Float := match imposedHeight with
        | some h => some (max 0 (h-edgesY))
        | none => match s.height with
          | .px h => if contentLimits then none else some (clampOpt minHeight maxHeight (max 0 h))
          | _ => if ratioFixed then ratioHeight.map (clampOpt minHeight maxHeight) else none
      let content ← if s.display.isFlex then
          flexLayout children s (collectItems dom styles id)
            {x := innerX, y := innerY, width, height := definite, minHeight, maxHeight, measure}
        else if s.display.isGrid then
          gridLayout children s (collectItems dom styles id)
            {x := innerX, y := innerY, width, height := definite, minHeight, maxHeight, source := some id, measure}
        else if s.columnCount.isNone && s.columnWidth.isNone then
          flow s id n.kids lead innerX innerY width (if joinsTop then unbounded else 0) around definite
        else
          let gap := columnGapPx s width
          match columnPlan s.columnCount s.columnWidth gap width with
          | none => flow s id n.kids lead innerX innerY width (if joinsTop then unbounded else 0) around definite
          | some (count,cw) => do
            -- a multi-column container is the root of its own block formatting context: its
            -- contents in one column first, then each column's children laid out in their place
            let single ← flow s id n.kids lead innerX innerY cw 0 #[] none
            let single := {single with height := max single.height (floatsHeight single.floats innerY), floats := #[]}
            let groups := columnKids single n.kids count innerY
            if groups.size ≤ 1 then pure single else do
            let mut out : Result := {work := single.work}
            for i in [0:groups.size] do
              let r ← flow s id groups[i]! (if i == 0 then lead else #[]) (innerX+Float.ofNat i*(cw+gap)) innerY cw 0 #[] none
              out := {out with nodes := out.nodes ++ r.nodes, boxes := out.boxes ++ r.boxes, runs := out.runs ++ r.runs,
                               pending := out.pending ++ r.pending, work := out.work+r.work,
                               height := max out.height (max r.height (floatsHeight r.floats innerY)),
                               baseline := if i == 0 then r.baseline else out.baseline, lastBaseline := r.lastBaseline}
            pure out
      -- CSS 2.1 §10.6.7: a box that is the root of its block formatting context (one laid
      -- out with no floats around it) is as high as its floats; one in a context with floats
      -- hands them on to the flow after it.
      let content := if !participates then
          {content with height := max content.height (floatsHeight content.floats innerY), floats := #[],
                        marginBottom := if floatsHeight content.floats innerY > content.height then 0 else content.marginBottom}
        else content
      -- An outside marker: beside the first line, ending half an em before the content edge
      -- (after it in a right-to-left item). It takes no room in the line and is not part of
      -- the item's box; an item with nothing else in it is one line high.
      let content ← if markerItems.isEmpty || s.pos.listInside then pure content else do
        let marker ← inlineLayout font markerItems 0 innerY unbounded (some {s with textAlign := .left})
        let gap := s.fontSize/2
        let dx := if s.direction == .rtl then innerX+width+gap else innerX-lineExtent marker-gap
        let marker := marker.shift dx 0
        pure {content with nodes := content.nodes ++ marker.nodes, runs := marker.runs ++ content.runs,
                           height := max content.height marker.height}
      -- One more box laid out. A document whose layout takes more work than its limit is
      -- refused here (`workLimit`), with what it has done so far bounded by that limit.
      let content := {content with work := content.work+1}
      if overWork dom.size content.work then
        throw "layout work limit: the page's boxes take too many layouts (nested containers that are laid out again and again)"
      if contentOnly then return content
      -- The same at the bottom: the last child's margin sticks out of a block with no height.
      let joinsBottom := imposedWidth.isNone && imposedHeight.isNone && collapsesBottom dom s id && !s.display.isFlex && !s.display.isGrid
      let marginBottom := if joinsBottom then collapsePx margin.bottom content.marginBottom else margin.bottom
      let content := if joinsBottom then {content with height := content.height-content.marginBottom} else content
      let height := match definite with
        | some h => h
        | none =>
          if contentLimits && imposedHeight.isNone then
            let own := match s.height with
              | .px h => max 0 h
              | _ => content.height
            clampOpt (if contentKeyword s.minHeight then content.height else minHeight)
              (if contentKeyword s.maxHeight then some content.height else maxHeight) own
          else clampOpt minHeight maxHeight content.height
      -- The absolutely positioned children of a flex or grid container are not its items.
      let content := if s.display.isFlex then
          {content with pending := content.pending ++ flexAbsolutes dom styles id innerX innerY width height}
        else if s.display.isGrid then
          {content with pending := content.pending ++ gridAbsolutes dom styles id innerX innerY width height}
        else content
      -- A positioned box is the containing block of its absolutely positioned descendants:
      -- its padding box (CSS 2.1 §10.1).
      let content ← if s.pos.containsAbsolutes then
          let (cx,cy,cw,ch) := (outerX+border.left,outerY+border.top,width+padding.left+padding.right,
            height+padding.top+padding.bottom)
          -- an absolutely positioned child of a grid starts at its grid area (CSS Grid 2 §9.1)
          let content := match content.grid with
            | some f => {content with pending := content.pending.map fun p =>
                let child := (dom.get p.id).parent == some id && (styles[p.id]!).pos.position == .absolute
                if child then gridStatic f cx cy cw ch (styles[p.id]!).grid p else p}
            | none => content
          place content cx cy cw ch false fun p => content.grid.map fun f => gridAbsBlock f cx cy cw ch (styles[p.id]!).grid
        else pure content
      let content := {content with grid := none}
      let framed := frameBox id s outerX outerY (width+edgesX) (height+edgesY) content
      let framed := {framed with height := marginTop+height+edgesY+marginBottom, marginBottom}
      -- CSS Transforms 1 §6: the box is laid out as if it had no transform; what is drawn
      -- of it is transformed about its `transform-origin`, a point of its border box.
      let framed := if s.pos.transform.isEmpty then framed else
        let bw := width+edgesX
        let bh := height+edgesY
        let (ox,ofWidth,oy,ofHeight) := s.pos.transformOrigin
        framed.transformed (CSS.BoxTransform.about .float (CSS.BoxTransform.matrixOf s.pos.transform bw bh)
          (outerX+ox+ofWidth*bw) (outerY+oy+ofHeight*bh))
      -- CSS 2.1 §9.4.3: a relatively positioned box is moved from where it was laid out; the
      -- flow after it is as if it had not moved. `left` wins over `right`, `top` over `bottom`.
      if s.pos.position == .relative then
        let dx := match CSS.resolve available s.pos.left with
          | some l => l
          | none => match CSS.resolve available s.pos.right with | some r => -r | none => 0
        -- a percentage `top` or `bottom` is of the containing block's height when the styles
        -- make it definite, else it is `auto` (CSS Positioned Layout 3 §3.1)
        let basis := match n.parent with
          | some parent => if (dom.get parent).type == .element then definiteHeight dom styles parent else none
          | none => none
        let dy := match resolveOpt basis s.pos.top with
          | some t => t
          | none => match resolveOpt basis s.pos.bottom with | some e => -e | none => 0
        -- the floats of the context do not move with it
        return {framed.shift dx dy with floats := framed.floats}
      return framed
    match task with
    | .contents container kids =>
      let content ← flow (styles[container]!) container kids #[] x y available
      return {content with height := max content.height (floatsHeight content.floats y), floats := #[]}
    | .table element container kids => table element container kids none none
    | .flowed id floats => box id none none false floats true
    | .box id => box id none none false
    | .sized id width height => box id (some width) height false
    | .inner id width => box id (some width) none true
    | .positioned content cx cy cw ch => place content cx cy cw ch true fun _ => none
    | .rough inner => layoutTask dom styles font embedding pictures fuel (.rough inner) x y available

/-- An element's block box: `layoutTask` of `.box id`. -/
def block (dom : Dom) (styles : Array Computed) (font : FontProfile) (embedding : Embedding)
    (pictures : Pictures) (fuel id : Nat) (x y available : Float) : Except String Result :=
  layoutTask dom styles font embedding pictures fuel (.box id) x y available

/-- The layout of a document in a viewport `vw` by `vh`: the root's block box, then the
absolutely positioned boxes with no positioned ancestor and the `fixed` boxes, whose
containing block is the initial one, the viewport (CSS 2.1 §10.1). A box laid out there
may leave `fixed` descendants pending: a few rounds. A document with no such box is
`block` alone. -/
def layoutRoot (dom : Dom) (styles : Array Computed) (font : FontProfile) (embedding : Embedding)
    (pictures : Pictures) (vw vh : Float) : Except String Result := do
  -- CSS 2.1 §10.5: percentage heights against heights that the styles make definite.
  let styles := percentHeights dom styles
  let mut laid ← block dom styles font embedding pictures 64 0 0 0 vw
  for _ in [0:4] do
    if laid.pending.isEmpty then break
    -- The same paint ordering used for a local containing block applies at the root.
    laid ← layoutTask dom styles font embedding pictures 64 (.positioned laid 0 0 vw vh) 0 0 vw
  return laid

/-- The nearest HTML anchor with an href attribute, including href="". -/
def anchorAncestor (dom : Dom) : Nat → Nat → Option (Nat × String)
  | 0, _ => none
  | fuel+1, id =>
    let n := dom.get id
    if DOM.Dom.isHtmlElement n "a" && CSS.hasAttribute n "href" then
      some (id,CSS.attrValue n "href")
    else n.parent.bind (anchorAncestor dom fuel)

/-- A resolved target is an actual HTML anchor with an href attribute in
this DOM arena, and the returned URL is that attribute's exact value. -/
theorem anchorAncestor_is_anchor (dom : Dom) (fuel start id : Nat) (href : String)
    (found : anchorAncestor dom fuel start = some (id,href)) :
    DOM.Dom.isHtmlElement (dom.get id) "a" = true ∧
      CSS.hasAttribute (dom.get id) "href" = true ∧ CSS.attrValue (dom.get id) "href" = href := by
  induction fuel generalizing start with
  | zero => simp [anchorAncestor] at found
  | succ fuel ih =>
    simp only [anchorAncestor] at found
    split at found
    · rename_i condition
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      rcases found with ⟨rfl,rfl⟩
      have both := Bool.and_eq_true_iff.mp condition
      exact ⟨both.1,both.2,rfl⟩
    · cases parent : (dom.get start).parent with
      | none => simp [parent] at found
      | some p => exact ih p (by simpa [parent] using found)

/-- A link box cut to the boxes of its ancestors that clip their overflow (`clips`, by
source node), walking up the parents with `fuel` steps. -/
def clipLinkBox (dom : Dom) (clips : Std.TreeMap Nat Box) : Nat → Nat → Box → Box
  | 0, _, box => box
  | fuel+1, id, box =>
    let box := match clips.get? id with
      | none => box
      | some clip =>
        let left := max box.x clip.x
        let top := max box.y clip.y
        {box with x := left,y := top,width := max 0 (min (box.x+box.width) (clip.x+clip.width)-left), height := max 0 (min (box.y+box.height) (clip.y+clip.height)-top)}
    match (dom.get id).parent with
    | none => box
    | some parent => clipLinkBox dom clips fuel parent box

/-- The boxes of the elements that clip their overflow, by source node. -/
def linkClips (dom : Dom) (styles : Array Computed) (boxes : Array Box) : Std.TreeMap Nat Box :=
  boxes.foldl (fun (out : Std.TreeMap Nat Box) box =>
    if (styles[box.source]!).clipOverflow && (dom.get box.source).type == .element then out.insert box.source box else out) {}

/-- The link region of one layout box: none when the box is in no anchor, is hidden, or
is empty once clipped by its ancestors and by `[0,width) × [0,height)`. -/
def linkRegionOf (dom : Dom) (styles : Array Computed) (clips : Std.TreeMap Nat Box)
    (width height : Float) (box : Box) : Option LinkRegion :=
  match anchorAncestor dom (dom.size+1) box.source with
  | none => none
  | some (source,href) =>
    let box := clipLinkBox dom clips (dom.size+1) box.source box
    if (styles[box.source]!).visible && box.width > 0 && box.height > 0 then
      let left := max 0 box.x
      let top := max 0 box.y
      let right := min width (box.x+box.width)
      let bottom := min height (box.y+box.height)
      if right > left && bottom > top then some ⟨source,href,left,top,right-left,bottom-top⟩ else none
    else none

/-- An element whose boxes are those of an inline box, one on each line that holds part
of it (`Inline.openInline`): an inline element that is not replaced. -/
def isInlineBox (dom : Dom) (styles : Array Computed) (id : Nat) : Bool :=
  let n := dom.get id
  n.type == .element && ((styles[id]?).map (·.display == .inline)).getD false &&
    !["img","br","canvas","video","iframe"].contains n.lname && n.ns != some DOM.svgNS

/-- The boxes that link regions are cut from: the boxes of text, of replaced elements and
of block-level and atomic boxes. The box of an inline box is left out: what is inside it
has boxes of its own, so a link has a region for each piece of its content, as it had
before inline boxes had boxes. Anonymous control text has no node from which to take
a link target. -/
def linkSources (dom : Dom) (styles : Array Computed) (boxes : Array Box) : Array Box :=
  boxes.filter fun b => b.source < dom.size && !isInlineBox dom styles b.source

/-- Link fragments come from the same visible layout boxes as glyphs and
replaced elements. Collapsed spaces produce boxes only when retained on a line.
In box order, one region per box at most (`LinkTheorems.mem_linkRegions`). -/
def linkRegions (dom : Dom) (styles : Array Computed) (boxes : Array Box)
    (width height : Float) : Array LinkRegion :=
  boxes.filterMap (linkRegionOf dom styles (linkClips dom styles boxes) width height)

/-- The height down to which `render` keeps link regions: the foot of the document, or the
viewport when the document is shorter. A host that scrolls a band of the page with no new
layout (the Hub, issue 1268) hit-tests links below the first screen with this list, so it
must not be the viewport alone (`LinkTheorems.render_link_complete`). -/
def linkHeight (viewport document : Float) : Float := max viewport document

/-- CSS 2.1 §14.2: the background of the root element, or of `body` when the root
has none, paints the whole canvas, and not the element's own box. -/
def canvasBackground (dom : Dom) (styles : Array Computed) : Option (Nat × Color) := Id.run do
  let some root := (dom.get 0).kids.find? (fun k => (dom.get k).type == .element) | return none
  if let some c := (styles[root]?).bind (·.background) then return some (root,c)
  if (dom.get root).lname != "html" then return none
  let some body := (dom.get root).kids.find? (fun k => (dom.get k).lname == "body") | return none
  return ((styles[body]?).bind (·.background)).map (body,·)

/-- The scene of a tree whose styles are computed: existing DOM input, explicit viewport
and font data, immutable scene output. `pictures` holds the decoded content of replaced
elements. -/
def renderStyled (dom : Dom) (computed : Array Computed) (font : FontProfile) (embedding : Embedding)
    (width height : Nat) (pictures : Pictures := noPictures) : Except String (Scene × Array Box) := do
  if width == 0 || height == 0 || width > 4096 || height > 4096 then throw "unsupported viewport: require dimensions 1 to 4096"
  let vw := Float.ofNat width
  let vh := Float.ofNat height
  let styles := computed.map fun s =>
    {s with width := s.width.atViewport vw vh, height := s.height.atViewport vw vh,
            minWidth := s.minWidth.atViewport vw vh, maxWidth := s.maxWidth.atViewport vw vh,
            minHeight := s.minHeight.atViewport vw vh, maxHeight := s.maxHeight.atViewport vw vh,
            backgroundSize := s.backgroundSize.atViewport vw vh,
            backgroundPositionX := s.backgroundPositionX.atViewport vw vh,
            backgroundPositionY := s.backgroundPositionY.atViewport vw vh,
            objectPosition := s.objectPosition.map fun (x,y) => (x.atViewport vw vh, y.atViewport vw vh),
            align := (flexAtViewport vw vh s).align, flex := (flexAtViewport vw vh s).flex,
            pos := (flexAtViewport vw vh s).pos}
  -- Percentage margins and padding, where the containing block's width is definite.
  let styles := percentEdges dom styles vw
  -- `box-sizing: border-box`: the layout reads content-box sizes.
  let styles := styles.map contentBoxed
  let canvas := canvasBackground dom styles
  let styles := match canvas with
    | some (id,_) => styles.modify id fun s => {s with background := none}
    | none => styles
  let result ← layoutRoot dom styles font embedding pictures vw vh
  let result : Result := match canvas with
    | some (id,c) => {result with nodes := #[Node.paint ⟨some id,{geometry := .rect 0 0 vw (max vh result.height),style := {fill := .solid c}}⟩] ++ result.nodes}
    | none => result
  if result.nodes.size > 1048576 then throw "HTML paint count exceeds 1048576"
  -- Links are kept down to the foot of the document, not the viewport: a host that scrolls
  -- a band of the page with no new layout (the Hub, issue 1268) hit-tests links below the
  -- first screen with this list.
  let links := linkRegions dom styles (linkSources dom styles result.boxes) (Float.ofNat width) (linkHeight vh result.height)
  if links.size > 49152 || links.any (fun link => link.href.utf8ByteSize > 2048) then
    throw "unsupported link region count or href exceeding 2048 UTF-8 bytes"
  return (⟨width,height,⟨1,1,0,0,0,0,Float.ofNat width,Float.ofNat height⟩, result.nodes.toList,result.runs,links⟩,result.boxes)

/-- The boxes of the original page's nodes, used by script geometry and frame
answers. The limit also excludes generated content and anonymous control text. -/
def pageBoxes (nodes : Nat) (boxes : Array Box) : Array Box :=
  boxes.filter (·.source < nodes)

/-- Kind: equivalence. Says: page geometry retains exactly the boxes sourced to a
node in the original page. Does not say: which boxes the layout emits. -/
theorem mem_pageBoxes {nodes : Nat} {boxes : Array Box} {b : Box} :
    b ∈ pageBoxes nodes boxes ↔ b ∈ boxes ∧ b.source < nodes := by
  simp [pageBoxes, Array.mem_filter]

/-- Kind: separation. Says: a control label's anonymous text fragment is never
reported as a box of the page. Does not say: how the text is shaped, laid out or painted. -/
theorem controlText_geometry_excluded (dom : Dom) (id pageSize : Nat) (h : pageSize ≤ dom.size)
    (b : Box) (boxes : Array Box) (source : b.source = (TextSource.control dom id).geometry) :
    b ∉ pageBoxes pageSize boxes := by
  intro mem
  have lt := (mem_pageBoxes.mp mem).2
  rw [source] at lt
  exact Nat.not_lt_of_ge h lt

#print axioms mem_pageBoxes
#print axioms controlText_geometry_excluded

/-- The scene of a page and the boxes of its nodes. A page with shadow trees is laid out
on its flat tree (`DOM.Dom.flat`), with `treeScope` its node tree for selectors
(`CSS.TreeScope`). The tree that is laid out has the page's `::before` and `::after`
boxes too (`Generated.styled`): they paint, and a link's region covers them, but the
boxes answered are those of the page's own nodes, so a point over generated content is a
point in its originating element. -/
def render (dom : Dom) (rules : List CSS.Rule) (font : FontProfile) (embedding : Embedding)
    (width height : Nat) (textScale : Float := 1) (state : CSS.ElementState := {})
    (pictures : Pictures := noPictures) (treeScope : Option CSS.TreeScope := none) : Except String (Scene × Array Box) := do
  let made ← Generated.styled treeScope dom rules textScale state
  let drawn ← renderStyled (Generated.flattenContents made.1 made.2) made.2 font embedding width height pictures
  return (drawn.1,pageBoxes dom.size drawn.2)

/-- `render`, and with its answer the computed styles of the page's own nodes: those the
layout was made with (`Generated.styled`). A caller that reads styles of the laid out page
(the border edges of a box, the styles a pointer state is compared with) takes them from
here and does not cascade the document a second time. -/
def renderWithStyles (dom : Dom) (rules : List CSS.Rule) (font : FontProfile) (embedding : Embedding)
    (width height : Nat) (textScale : Float := 1) (state : CSS.ElementState := {})
    (pictures : Pictures := noPictures) (treeScope : Option CSS.TreeScope := none) :
    Except String ((Scene × Array Box) × Array Computed) := do
  let made ← Generated.styled treeScope dom rules textScale state
  let drawn ← renderStyled (Generated.flattenContents made.1 made.2) made.2 font embedding width height pictures
  return ((drawn.1,pageBoxes dom.size drawn.2),made.2.extract 0 dom.size)

/-- Kind: correctness of the shared styles. Says: on a page whose sheet makes no
generated content, the layout is the layout of the styles of `CSS.computeFor`, and the
styles answered are those styles (their first `dom.size`, which is all of them when the
cascade gives one style a node). Does not say: the same for a page with `::before` or
`::after` content, where the styles are those of `Generated.styled`'s own cascade over
the page's nodes (the same rules and the same animated values; not proved equal). -/
theorem renderWithStyles_unused (dom : Dom) (rules : List CSS.Rule) (font : FontProfile) (embedding : Embedding)
    (width height : Nat) (textScale : Float) (state : CSS.ElementState) (pictures : Pictures)
    (treeScope : Option CSS.TreeScope) (h : Generated.used rules = false) :
    renderWithStyles dom rules font embedding width height textScale state pictures treeScope =
      (CSS.computeFor treeScope dom rules textScale state).bind fun styles =>
        (renderStyled (Generated.flattenContents dom styles) styles font embedding width height pictures).bind fun drawn =>
          Except.ok ((drawn.1,pageBoxes dom.size drawn.2),styles.extract 0 dom.size) := by
  unfold renderWithStyles
  rw [Generated.styled_unused treeScope dom rules textScale state h]
  cases CSS.computeFor treeScope dom rules textScale state <;> rfl

end L4Factoidal.Rendering.Layout
