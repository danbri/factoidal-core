import L4Factoidal.Rendering.Style
import L4Factoidal.Rendering.FontFace
import L4Factoidal.Rendering.TableLayout
import L4Factoidal.Unicode.ScriptDirection

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

def FontProfile.ofFace (face : FontProvider.Face) : FontProfile :=
  {family := face.family,unitsPerEm := face.unitsPerEm,advance := 0,
   ascent := face.ascent,descent := face.descent,outline := fun _ => [],admits := fun _ => false,
   cssFamilies := [face.family],fontSha256 := some face.fontSha256,faceIndex := face.faceIndex,
   shapedWord := some face.lookup}

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
    return some word

private def spaceWidth (font : FontProfile) (style : Computed) : Except String Float := do
  match ← font.word style " " with
  | none => return font.advance*style.fontSize/font.unitsPerEm
  | some word =>
    if word.glyphs.any (fun glyph => !glyph.geometry.isEmpty) then
      throw "unsupported painted whitespace glyph in collapsed space profile"
    return word.advance*style.fontSize/font.unitsPerEm

/-- CSS leading surrounds the actual ascent+descent metric box, which need
not equal one em (ordinary real fonts often differ). -/
private def lineLeading (font : FontProfile) (style : Computed) : Float :=
  (style.lineHeight-(font.ascent+font.descent)*style.fontSize/font.unitsPerEm)/2

/-- CSS Overflow 3 §3.1: `overflow: hidden` and `overflow: clip` clip the content of a
box to its padding box (`paddingBox`); the box's own background and border are drawn
whole (`decorations`). With `clip` false the content is drawn whole. Each primitive of
clipped content carries the padding box (`ClipTheorems.clipContent_clips`). -/
def clipContent (clip : Bool) (decorations content : Array Node) (paddingBox : ClipRect) : Array Node :=
  if clip then decorations.push (.clipped none identity paddingBox content.toList) else decorations ++ content

structure Box where
  source : Nat
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr
structure Result where
  nodes : Array Node := #[]
  boxes : Array Box := #[]
  runs : Array GlyphRun := #[]
  height : Float := 0
  deriving Repr
abbrev Embedding := Nat → CSS.Computed → Float → Float → Except String (List Node)

private def checkSVGBox (s : Computed) : Except String Unit := do
  if let .percent _ := s.height then
    throw "unsupported percentage SVG height without definite containing height"

/-- Replaced SVG dimensions share the same calculation in inline and block
flow. A positive viewBox supplies the intrinsic ratio when a dimension is auto.
The ratio-only case uses the definite available containing width (CSS 2.2 10.3.2).
Presentation lengths participate in the CSS cascade before this calculation. -/
def svgSize (node : DOM.Node) (style : Computed) (available : Float) : Except String (Float × Float) := do
  checkSVGBox style
  let width := CSS.resolve available style.width
  let height := CSS.resolve 0 style.height
  if let (some w,some h) := (width,height) then return (max 0 w,max 0 h)
  let source := CSS.attrValue node "viewBox"
  let mut ratio : Option (Float × Float) := none
  if !source.isEmpty then
    let fields := (source.replace "," " ").splitOn " " |>.flatMap (fun s => (s.replace "\n" " " |>.replace "\t" " " |>.replace "\r" " ").splitOn " ") |>.filter (!·.isEmpty)
    let [_,_,w,h] := fields | throw "unsupported SVG intrinsic viewBox: four numbers required"
    let w ← CSS.number w
    let h ← CSS.number h
    if w > 0 && h > 0 then ratio := some (w,h)
  match width,height,ratio with
  | some w,none,some (rw,rh) => return (max 0 w,max 0 (w*rh/rw))
  | none,some h,some (rw,rh) => return (max 0 (h*rw/rh),max 0 h)
  | none,none,some (rw,rh) => return (max 0 available,max 0 (available*rh/rw))
  | _,_,_ => return (max 0 (width.getD 300),max 0 (height.getD 150))


private def background (id : Nat) (s : Computed) (x y w h : Float) : Array Node :=
  match s.background with
  | none => #[]
  | some c => if !s.visible || w <= 0 || h <= 0 then #[] else
    #[.paint ⟨some id,{geometry := .rect x y w h,style := {fill := .solid c}}⟩]

/-- The two colours of a 3D border (CSS Backgrounds 3 §4.2 leaves them to the user
agent): the colour moved 60% of the way to white, and 60% of the colour. -/
def lighter (c : Color) : Color := ⟨c.r+(1-c.r)*0.6,c.g+(1-c.g)*0.6,c.b+(1-c.b)*0.6⟩
def darker (c : Color) : Color := ⟨c.r*0.6,c.g*0.6,c.b*0.6⟩

/-- The border of a border box at `(x,y)`, size `w` by `h`: top and bottom across the
whole width, left and right between them. `outset` is light at the top and left and
dark at the bottom and right; `inset` is the reverse. -/
def borderNodes (id : Nat) (s : Computed) (x y w h : Float) : Array Node := Id.run do
  let b := s.borderEdges
  if !s.visible || w <= 0 || h <= 0 || s.borderStyle == .none then return #[]
  let c := s.borderColor.getD s.color
  let (near,far) := match s.borderStyle with
    | .outset => (lighter c,darker c)
    | .inset => (darker c,lighter c)
    | _ => (c,c)
  let rect := fun (c : Color) (x y w h : Float) =>
    if w <= 0 || h <= 0 then #[] else #[Node.paint ⟨some id,{geometry := .rect x y w h,style := {fill := .solid c}}⟩]
  return rect near x y w b.top ++ rect far x (y+h-b.bottom) w b.bottom ++
    rect near x (y+b.top) b.left (h-b.top-b.bottom) ++ rect far (x+w-b.right) (y+b.top) b.right (h-b.top-b.bottom)

/-- Background, then border, of a border box. -/
private def decorations (id : Nat) (s : Computed) (x y w h : Float) : Array Node :=
  background id s x y w h ++ borderNodes id s x y w h

/-- The content of a replaced element that Lean decoded or drew: the image of an
`img`, and in time the poster or frame of a `video` or the bitmap of a `canvas`.
`id` names the bitmap in the paint table, so one bitmap used twice is stored once. -/
structure Picture where
  id : Nat
  bitmap : Bitmap
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
def replacedSize (s : Computed) (intrinsic : Option (Float × Float)) (available : Float) : Float × Float :=
  let horizontal := fun (l : CSS.Length) => match l with
    | .px n => some n
    | .percent p => if available <= 0 then none else some (available*p)
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

/-- The intrinsic size of a picture: its pixels, one CSS pixel each. -/
def Picture.size (p : Picture) : Float × Float :=
  (Float.ofNat p.bitmap.width,Float.ofNat p.bitmap.height)

/-- CSS Images 3 §5.5: the scale of content of `iw` by `ih` in a box of `w` by `h`. -/
def fitScale (fit : ObjectFit) (iw ih w h : Float) : Float × Float :=
  match fit with
  | .fill => (w/iw,h/ih)
  | .contain => let k := min (w/iw) (h/ih); (k,k)
  | .cover => let k := max (w/iw) (h/ih); (k,k)
  | .none => (1,1)
  | .scaleDown => let k := min 1 (min (w/iw) (h/ih)); (k,k)

/-- The paint of a picture in the content box `x`, `y`, `w`, `h`: one rectangle filled
with the image, centred (`object-position: 50% 50%`) and cut to the box by its own
geometry, as the SVG `image` with `slice` is. -/
def pictureNodes (id : Nat) (s : Computed) (picture : Picture) (x y w h : Float) : List Node :=
  let (iw,ih) := picture.size
  if !s.visible || w <= 0 || h <= 0 || iw <= 0 || ih <= 0 then [] else
  let (sx,sy) := fitScale s.objectFit iw ih w h
  let dx := x+(w-iw*sx)/2
  let dy := y+(h-ih*sy)/2
  let left := max x dx
  let top := max y dy
  let right := min (x+w) (dx+iw*sx)
  let bottom := min (y+h) (dy+ih*sy)
  if right <= left || bottom <= top then [] else
  let map : Transform := ⟨1/sx,0,0,1/sy,-dx/sx,-dy/sy⟩
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

/-- The width that margins, borders and padding add to a box. -/
private def horizontalEdges (s : Computed) : Float :=
  s.margin.left+s.margin.right+s.borderEdges.left+s.borderEdges.right+s.padding.left+s.padding.right

inductive Inline where
  | word (source : Nat) (style : Computed) (text : String) (start : Nat)
  | space (source : Nat) (style : Computed)
  | lineBreak (style : Computed)
  /-- A replaced element (`img`, inline `svg`): its margin box and paint at the origin. -/
  | replaced (source : Nat) (style : Computed) (width height : Float) (nodes : List Node)
  /-- An `inline-block` from `openAtomic` to `closeAtomic`, laid out (`atomize`): its
  margin box and its content at the origin. -/
  | atomic (source : Nat) (width height : Float) (inner : Result)
  /-- Bounds of an `inline-block` in the flat list that `inlineItems` gives. -/
  | openAtomic (source : Nat) (style : Computed)
  | closeAtomic
  /-- A bidi control character that an inline box with `unicode-bidi` adds (CSS
  Writing Modes 3 §2.4.2): no width, no paint. -/
  | bidiMark (c : Char)
  deriving Repr
instance : Inhabited Inline := ⟨.closeAtomic⟩

private def textItems (id : Nat) (style : Computed) (text : String) : List Inline := Id.run do
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
        result := .word id style word start :: result
        word := ""
      if style.preformatted then
        -- CSS Text 3 §4.1.1 `white-space: pre`: each space and tab stays, and each newline breaks.
        if c == '\n' then
          result := .lineBreak style :: result
          column := 0
        else if c != '\r' then
          let count := if c == '\t' then 8-column%8 else 1
          for _ in [0:count] do result := .space id style :: result
          column := column+count
      else
        if !spaced then result := .space id style :: result
      spaced := true
    else
      if word.isEmpty then start := index
      word := word.push c
      spaced := false
      column := column+1
    index := index+1
  if !word.isEmpty then result := .word id style word start :: result
  return result.reverse

/-- What an `img` with no picture shows: its `alt` text in brackets, nothing for
`alt=""` (an image that adds nothing), and `[image]` with no `alt`. -/
private def altItems (id : Nat) (s : Computed) (n : DOM.Node) : Array Inline :=
  if !CSS.hasAttribute n "alt" then (textItems id s "[image]").toArray
  else
    let alt := CSS.attrValue n "alt"
    if alt.isEmpty then #[] else (textItems id s s!"[{alt}]").toArray

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
    if n.type == .text then return (textItems id s n.data).toArray
    if n.type != .element then return #[]
    -- A replaced element with a picture: an `img`, and later a `video` or `canvas`.
    if let some picture := pictures id then
      let (w,h) := replacedSize s (some picture.size) available
      let (ow,oh,nodes) := replacedBox id s w h (fun x y => pictureNodes id s picture x y w h)
      return #[.replaced id s ow oh nodes]
    -- An image that is missing, broken or refused stands as its description, and stays a link.
    if n.lname == "img" then return altItems id s n
    if n.lname == "br" then return #[.lineBreak s]
    if n.ns == some DOM.svgNS then
      let (width,height) ← svgSize n s available
      if width <= 0 || height <= 0 then return #[]
      let inner ← embedding id s width height
      -- The SVG producer paints the root's background itself.
      let (ow,oh,nodes) := replacedBox id {s with background := none} width height
        (fun x y => [.group none ⟨1,0,0,1,x,y⟩ inner])
      return #[.replaced id s ow oh nodes]
    -- A block inside an inline (old pages often have one) breaks the line around it.
    -- An inline-block is one atomic box: `atomize` lays out what is between its bounds.
    -- An inline box with `unicode-bidi` is wrapped in its bidi control characters.
    let mut out : Array Inline := if s.display.isBlockLevel then #[.lineBreak s]
      else if s.display == .inlineBlock then #[.openAtomic id s]
      else (bidiOpen s).map .bidiMark
    for child in n.kids do out := out ++ (← inlineItems dom styles embedding pictures available fuel child)
    if s.display == .inline && s.background.isSome then out := out.map (withBackground s)
    return if s.display.isBlockLevel then out.push (.lineBreak s)
      else if s.display == .inlineBlock then out.push .closeAtomic else out ++ (bidiClose s).map .bidiMark

private def translate (x y : Float) : Transform := ⟨1,0,0,1,x,y⟩
private def glyphNodes (font : FontProfile) (run : GlyphRun) (s : Computed) : Array Node := Id.run do
  let mut out := #[]
  if !s.visible then return out
  let scale := run.fontSize/font.unitsPerEm
  for g in run.glyphs do
    for geometry in font.outline g.index do
      let primitive : Primitive := {geometry,style := {fill := .solid s.color}, transform := ⟨scale,0,0,scale,g.x,g.y⟩}
      out := out.push (.paint ⟨some run.source,primitive⟩)
  if s.underline && !run.glyphs.isEmpty then
    let left := (run.glyphs[0]?).map (·.x) |>.getD 0
    let top := (run.glyphs[0]?).map (·.y) |>.getD 0
    let width := run.glyphs.foldl (fun w g => w+g.advance) 0
    let thickness := max 1 (run.fontSize/14)
    let baseline := top+font.ascent*scale
    out := out.push (.paint ⟨some run.source,{geometry := .rect left (baseline+thickness) width thickness,style := {fill := .solid (s.decorationColor.getD s.color)}}⟩)
  return out

private def itemWidth (font : FontProfile) (rtl : Option Bool := none) : Inline → Except String Float
  | .word _ s text _ => do
    match ← font.word s text rtl with
    | none => return font.advance*s.fontSize/font.unitsPerEm*Float.ofNat text.length
    | some word => return word.advance*s.fontSize/font.unitsPerEm
  | .replaced _ _ w _ _ | .atomic _ w _ _ => pure w
  | _ => pure 0

private def shapedNodes (word : FontProvider.Word) (run : GlyphRun) (s : Computed)
    (left baseline width : Float) : Array Node := Id.run do
  if !s.visible then return #[]
  let scale := run.fontSize/word.unitsPerEm
  let mut out := #[]
  for (glyph,position) in word.glyphs.zip run.glyphs do
    for geometry in glyph.geometry do
      out := out.push (.paint ⟨some run.source,{geometry,style := {fill := .solid s.color}, transform := ⟨scale,0,0,scale,position.x,position.y⟩}⟩)
  if s.underline && width > 0 then
    let thickness := max 1 (run.fontSize/14)
    out := out.push (.paint ⟨some run.source,{geometry := .rect left (baseline+thickness) width thickness, style := {fill := .solid (s.decorationColor.getD s.color)}}⟩)
  return out

/-- A laid-out box moved by `(dx,dy)`: its paint in a translated group, its boxes and
its glyph positions moved by the same amount. -/
private def shiftResult (dx dy : Float) (r : Result) : Result :=
  let boxes := r.boxes.map fun b => {b with x := b.x+dx, y := b.y+dy}
  let runs := r.runs.map fun run => {run with glyphs := run.glyphs.map fun g => {g with x := g.x+dx, y := g.y+dy}}
  {r with nodes := #[.group none (translate dx dy) r.nodes.toList], boxes, runs}

/-- CSS 2.1 §10.6.1: the background of inline text covers its content area, the
font's ascent and descent, from `top`. -/
private def textBackground (font : FontProfile) (source : Nat) (s : Computed) (x top width : Float) : Array Node :=
  match s.background with
  | some c =>
    if !s.visible || width <= 0 then #[] else
    #[.paint ⟨some source,{geometry := .rect x top width ((font.ascent+font.descent)*s.fontSize/font.unitsPerEm),style := {fill := .solid c}}⟩]
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
    ascent := font.ascent*style.fontSize/font.unitsPerEm+leading
    descent := font.descent*style.fontSize/font.unitsPerEm+leading
  for (_,item) in items do
    match item with
    | .word _ s _ _ | .space _ s | .lineBreak s =>
      let leading := lineLeading font s
      ascent := max ascent (font.ascent*s.fontSize/font.unitsPerEm+leading)
      descent := max descent (font.descent*s.fontSize/font.unitsPerEm+leading)
    | .replaced _ s _ h _ => match s.verticalAlign with
      | .baseline => ascent := max ascent h
      -- CSS 2.1 §10.8.1: the middle on the baseline plus half the x-height, here half an em.
      | .middle =>
        ascent := max ascent (h/2+s.fontSize/4)
        descent := max descent (h/2-s.fontSize/4)
      | .top => tallTop := max tallTop h
      | .bottom => tallBottom := max tallBottom h
    | .atomic _ _ h _ => ascent := max ascent h
    | .openAtomic _ _ | .closeAtomic | .bidiMark _ => pure ()
  -- A box aligned to the top or bottom of the line makes the line tall enough for it.
  if tallBottom > ascent+descent then ascent := tallBottom-descent
  if tallTop > ascent+descent then descent := tallTop-ascent
  let mut out : Result := {height := ascent+descent}
  for k in [0:items.size] do
    let (offset,item) := items[k]!
    let rtl := dirs[k]?.getD none
    match item with
    | .word source s text start =>
      let top := y+ascent-font.ascent*s.fontSize/font.unitsPerEm
      let leading := lineLeading font s
      if s.background.isSome then
        out := {out with nodes := out.nodes ++ textBackground font source s (x+offset) top (← itemWidth font rtl item)}
      match ← font.word s text rtl with
      | none =>
        -- A character this font has no glyph for shows as a question mark.
        let chars := text.toList.map fun c => if font.admits c.toNat then c else '?'
        let advance := font.advance*s.fontSize/font.unitsPerEm
        let glyphs := chars.toArray.mapIdx fun i c =>
          ({index := c.toNat, x := x+offset+Float.ofNat i*advance, y := top, advance, clusterStart := start+i, clusterEnd := start+i+1} : Glyph)
        let run : GlyphRun := ⟨source,font.family,s.fontSize,text,glyphs⟩
        out := {out with nodes := out.nodes ++ glyphNodes font run s, runs := out.runs.push run, boxes := out.boxes.push ⟨source,x+offset,top-leading,advance*Float.ofNat chars.length,s.lineHeight⟩}
      | some word =>
        let scale := s.fontSize/word.unitsPerEm
        let width := word.advance*s.fontSize/font.unitsPerEm
        let glyphs := word.glyphs.map fun glyph =>
          ({index := glyph.index,x := x+offset+glyph.x*scale,y := top+glyph.y*scale, advance := glyph.advance*scale,clusterStart := start+glyph.clusterStart,clusterEnd := start+glyph.clusterEnd} : Glyph)
        let run : GlyphRun := ⟨source,font.family,s.fontSize,text,glyphs⟩
        out := {out with nodes := out.nodes ++ shapedNodes word run s (x+offset) (y+ascent) width, runs := out.runs.push run,boxes := out.boxes.push ⟨source,x+offset,top-leading,width,s.lineHeight⟩}
    | .space source s =>
      let advance ← spaceWidth font s
      let leading := lineLeading font s
      let top := y+ascent-font.ascent*s.fontSize/font.unitsPerEm-leading
      out := {out with nodes := out.nodes ++ textBackground font source s (x+offset) (top+leading) advance,
                       boxes := out.boxes.push ⟨source,x+offset,top,advance,s.lineHeight⟩}
      if s.underline && s.visible then
        let thickness := max 1 (s.fontSize/14)
        out := {out with nodes := out.nodes.push (.paint ⟨some source,{geometry := .rect (x+offset) (y+ascent+thickness) advance thickness,style := {fill := .solid (s.decorationColor.getD s.color)}}⟩)}
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
    | .atomic source width height inner =>
      let top := y+ascent-height
      let moved := shiftResult (x+offset) top inner
      -- `inner` holds the border box of the inline-block first, then its content boxes.
      let _ := width
      out := {out with nodes := out.nodes ++ moved.nodes, runs := out.runs ++ moved.runs, boxes := out.boxes ++ moved.boxes}
    | _ => pure ()
  return out

private def appendResult (a b : Result) : Result :=
  {nodes := a.nodes ++ b.nodes, boxes := a.boxes ++ b.boxes, runs := a.runs ++ b.runs, height := a.height+b.height}

/-- A word of preformatted text: it never wraps. -/
private def preformatted : Inline → Bool
  | .word _ s _ _ => s.preformatted
  | _ => false

/-- The characters an item stands for in its paragraph, for UAX #9: a forced line
break is a paragraph separator, a replaced or atomic box an object replacement
character (CSS Writing Modes 3 §2.4.1). -/
private def bidiChars : Inline → Array Char
  | .word _ _ text _ => text.toList.toArray
  | .space _ _ => #[' ']
  | .lineBreak _ => #[' ']
  | .replaced .. | .atomic .. => #['￼']
  | .bidiMark c => #[c]
  | .openAtomic _ _ | .closeAtomic => #[]

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
    | .space _ _ | .lineBreak _ | .bidiMark _ => ls := ls.set! j (paras[j]?.getD 0)
    | _ => break
  let order := Unicode.reorderByLevels (Array.range n) ls
  let width := fun (j : Nat) => (if j+1 < n then line[j+1]!.1 else lineEnd) - line[j]!.1
  let mut xs : Array Float := Array.replicate n 0
  let mut pen : Float := 0
  for j in order do
    xs := xs.set! j pen
    pen := pen+width j
  return ((Array.range n).map fun j => (xs[j]!, line[j]!.2), ls.map fun l => some (l % 2 == 1))

/-- Word wrapping constructs line participants first. The font profile and
positioned glyph runs are consumed to paint the actual word geometry. With bidi
(`needsBidi`), words are cut by level first, a word's pieces stay on one line, and
each line is reordered (`bidiLine`). -/
def inlineLayout (font : FontProfile) (items0 : Array Inline) (x y available : Float)
    (strut : Option Computed := none) : Except String Result := do
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
  let indent := fun (w : Float) => match (strut.map (·.textAlign)).getD .start with
    | .start => if rtlAlign then max 0 (available-w) else 0
    | .end_ => if rtlAlign then 0 else max 0 (available-w)
    | .left => 0
    | .right => max 0 (available-w)
    | .center => max 0 ((available-w)/2)
  -- A finished line: reordered when there is bidi.
  let place := fun (line : Array (Float × Inline)) (idx : Array Nat) (lineEnd : Float) =>
    if bidi then bidiLine line (idx.map fun k => bi.levels[k]?.getD 0) (idx.map fun k => bi.paraLevels[k]?.getD 0) lineEnd
    else (line, #[])
  let mut out : Result := {}
  let mut cursorX : Float := 0
  let mut pendingSpace : Option (Nat × Computed) := none
  let mut pendingK : Nat := 0
  let mut line : Array (Float × Inline) := #[]
  let mut lineIdx : Array Nat := #[]
  for k in [0:items.size] do
    let item := items[k]!
    match item with
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
      else
        pendingSpace := some (source,s)
        pendingK := k
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
    | .lineBreak _ =>
      let (row,dirs) := place (line.push (cursorX,item)) (lineIdx.push k) cursorX
      let row ← lineLayout font row (x+indent cursorX) (y+out.height) strut dirs
      out := appendResult out {row with height := if row.height > 0 then row.height else 19.2}
      line := #[]
      lineIdx := #[]
      cursorX := 0
      pendingSpace := none
    | _ =>
      let width ← itemWidth font (dirOf k) item
      -- The pieces of a word cut by bidi levels go on one line together.
      let mut whole := width
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
      if cursorX > 0 && cursorX+gap+whole > available && !preformatted item && !glued k then
        let (row,dirs) := place line lineIdx cursorX
        out := appendResult out (← lineLayout font row (x+indent cursorX) (y+out.height) strut dirs)
        line := #[]
        lineIdx := #[]
        cursorX := 0
      else
        if gap > 0 then
          if let some (source,s) := pendingSpace then
            line := line.push (cursorX,.space source s)
            lineIdx := lineIdx.push pendingK
        cursorX := cursorX+gap
      line := line.push (cursorX,item)
      lineIdx := lineIdx.push k
      cursorX := cursorX+width
      pendingSpace := none
  if !line.isEmpty then
    let (row,dirs) := place line lineIdx cursorX
    out := appendResult out (← lineLayout font row (x+indent cursorX) (y+out.height) strut dirs)
  return out

private def append (a b : Result) : Result :=
  {nodes := a.nodes ++ b.nodes,boxes := a.boxes ++ b.boxes,runs := a.runs ++ b.runs, height := a.height+b.height}
/-- CSS 2.2 §10.3.9 and §10.6.6: an inline-block with `width:auto` is as wide as its
widest line (at most the room); its content is laid out at the origin inside its
border and padding. Its bottom margin edge sits on the line's baseline, as a
replaced element does here. -/
private def atomicBox (font : FontProfile) (id : Nat) (s : Computed) (items : Array Inline)
    (available : Float) : Except String Inline := do
  let b := s.borderEdges
  let p := s.padding
  let m := s.margin
  let room := max 0 (available-m.left-m.right-b.left-b.right-p.left-p.right)
  let fixed := CSS.resolve available s.width
  let content ← inlineLayout font items 0 0 (fixed.getD room) (some {s with textAlign := .left})
  let used := fixed.getD (content.boxes.foldl (fun w box => max w (box.x+box.width)) 0)
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
  let box : Box := ⟨id,m.left,m.top,w,h⟩
  return .atomic id (m.left+w+m.right) (m.top+h+m.bottom)
    {inner with nodes := decorations id s m.left m.top w h ++ inner.nodes, boxes := #[box] ++ inner.boxes}

/-- Each outermost `openAtomic .. closeAtomic` becomes one `atomic` item. An
inline-block inside another is laid out inline in it (its bounds are dropped). One
pass over the items: a loop. -/
def atomize (font : FontProfile) (items : Array Inline) (available : Float) : Except String (Array Inline) := do
  let mut out : Array Inline := #[]
  let mut depth : Nat := 0
  let mut opened : Option (Nat × Computed) := none
  let mut inside : Array Inline := #[]
  for item in items do
    match item with
    | .openAtomic id s =>
      if depth == 0 then
        opened := some (id,s)
        inside := #[]
      depth := depth+1
    | .closeAtomic =>
      if depth == 1 then
        if let some (id,s) := opened then out := out.push (← atomicBox font id s inside available)
        opened := none
      depth := depth-1
    | other => if depth == 0 then out := out.push other else inside := inside.push other
  -- Bounds always pair in `inlineItems`; an unpaired open keeps its content inline.
  return if depth == 0 then out else out ++ inside

/-- What goes before a list item: its number in an ordered list, else a star. -/
private def listMarker (dom : Dom) (id : Nat) : String := Id.run do
  let some parent := (dom.get id).parent | return "* "
  if (dom.get parent).lname != "ol" then return "* "
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
  deriving Repr

/-- The right edge of what a line layout placed, from its left edge `0`. -/
private def lineExtent (r : Result) : Float := r.boxes.foldl (fun m b => max m (b.x+b.width)) 0

/-- A result moved down by `dy`: its paint in a translated group, its boxes and glyphs moved. -/
private def Result.shiftY (r : Result) (dy : Float) : Result :=
  if dy == 0 then r else
  {r with nodes := if r.nodes.isEmpty then #[] else #[.group none (translate 0 dy) r.nodes.toList],
          boxes := r.boxes.map fun b => {b with y := b.y+dy},
          runs := r.runs.map fun run => {run with glyphs := run.glyphs.map fun g => {g with y := g.y+dy}}}

/-- The style of the contents of a cell: the cell's own, or for an anonymous cell
its parent's, with no box edges (an anonymous box has none). -/
private def anonymousBox (base : Computed) : Computed :=
  {base with padding := {}, margin := {}, background := none, width := .auto, height := .auto,
             verticalAlign := .baseline, autoMarginLeft := false, autoMarginRight := false}
private def cellStyle (styles : Array Computed) : Table.Source → Computed
  | .element id => styles[id]!
  | .anonymous parent _ => anonymousBox styles[parent]!
private def cellContents (dom : Dom) : Table.Source → Nat × Array Nat
  | .element id => (id,(dom.get id).kids)
  | .anonymous parent kids => (parent,kids)

/-- The width a cell asks of its columns (CSS 2.1 §17.5.2.2): its min-content and
max-content widths with its padding, and its specified width. -/
private def cellMeasure (s : Computed) (widths : Float × Float) : Table.Measure :=
  let pad := s.padding.left+s.padding.right
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
  padding : Edges
  hs : Float
  vs : Float

private def tableFrame (styles : Array Computed) (element : Option Nat) (container : Nat) : TableFrame :=
  let s := match element with
    | some id => styles[id]!
    | none => {anonymousBox styles[container]! with display := .table, tableFixed := false}
  let edges := element.isSome
  {style := s, margin := if edges then s.margin else {}, padding := if edges then s.padding else {},
   hs := if s.borderCollapse then 0 else s.borderSpacingX,
   vs := if s.borderCollapse then 0 else s.borderSpacingY}

/-- Min-content and max-content widths (CSS Sizing 3 §5), margins included for a box.
Text is measured with `inlineLayout` itself: with no room, every break opportunity is
taken (min-content); with unbounded room, none is (max-content). A table's widths are
those of its columns (`Table.columns`). Fuel is shared with `layoutTask`: one level per
element or table. -/
def intrinsic (dom : Dom) (styles : Array Computed) (font : FontProfile) (embedding : Embedding) (pictures : Pictures) :
    Nat → Task → Except String (Float × Float)
  | 0, _ => throw "unsupported HTML nesting depth (maximum 64)"
  | fuel+1, task => do
    let inlineWidths (items : Array Inline) : Except String (Float × Float) := do
      if items.isEmpty then return (0,0)
      let narrow ← inlineLayout font (← atomize font items 0) 0 0 0
      let wide ← inlineLayout font (← atomize font items 1.0e9) 0 0 1.0e9
      return (lineExtent narrow,lineExtent wide)
    let flowWidths (container : Nat) (kids : Array Nat) (lead : Array Inline) : Except String (Float × Float) := do
      let mut widths : Float × Float := (0,0)
      let mut inline := lead
      for seg in Table.segments dom styles kids do
        match seg with
        | .run run =>
          let (a,b) ← inlineWidths inline
          inline := #[]
          let (c,d) ← intrinsic dom styles font embedding pictures fuel (.table none container run)
          widths := (max widths.1 (max a c),max widths.2 (max b d))
        | .node k =>
          if (styles[k]!).display.isBlockLevel then
            let (a,b) ← inlineWidths inline
            inline := #[]
            let (c,d) ← intrinsic dom styles font embedding pictures fuel (.box k)
            widths := (max widths.1 (max a c),max widths.2 (max b d))
          else
            inline := inline ++ (← inlineItems dom styles embedding pictures 0 fuel k)
      let (a,b) ← inlineWidths inline
      return (max widths.1 a,max widths.2 b)
    let tableWidths (element : Option Nat) (container : Nat) (kids : Array Nat) : Except String (Float × Float) := do
      let frame := tableFrame styles element container
      let grid := Table.build dom styles (element.getD container) kids
      let mut measures : Array Table.Measure := #[]
      for cell in grid.cells do
        let (c,ks) := cellContents dom cell.source
        measures := measures.push (cellMeasure (cellStyle styles cell.source) (← intrinsic dom styles font embedding pictures fuel (.contents c ks)))
      let cols := Table.columns grid.columns grid.cells measures (grid.columnElements.map (columnMeasure styles)) frame.hs
      let spacing := if grid.columns == 0 then 0 else frame.hs*Float.ofNat (grid.columns+1)
      let edges := frame.padding.left+frame.padding.right
      let low := Table.total (cols.map (·.min))+spacing+edges
      let high := max low (Table.total ((Table.guesses cols 0)[3]!)+spacing+edges)
      let margins := frame.margin.left+frame.margin.right
      match frame.style.width with
      | .px w => return (max w low+margins,max w low+margins)
      | _ => return (low+margins,high+margins)
    match task with
    | .contents container kids => flowWidths container kids #[]
    | .table element container kids => tableWidths element container kids
    | .box id =>
      let n := dom.get id
      let s := styles[id]!
      if s.display == .none then return (0,0)
      if s.display.isTable then return (← tableWidths (some id) (n.parent.getD 0) n.kids)
      if let some picture := pictures id then
        let w := (replacedSize s (some picture.size) 0).1+horizontalEdges s
        return (w,w)
      if n.ns == some DOM.svgNS then
        let w := (← svgSize n s 0).1+horizontalEdges s
        return (w,w)
      let edges := s.margin.left+s.margin.right+s.padding.left+s.padding.right
      match s.width with
      | .px w => return (w+edges,w+edges)
      | _ =>
        let lead := if n.lname == "li" then (textItems id s (listMarker dom id)).toArray
          else if n.lname == "img" then altItems id s n else #[]
        let (a,b) ← flowWidths id n.kids lead
        return (a+edges,b+edges)

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
    -- The flow of `kids` in a block container with style `s`: block-level children
    -- stack, inline children share line boxes, runs of internal table boxes are tables.
    let flow (s : Computed) (container : Nat) (kids : Array Nat) (lead : Array Inline)
        (innerX innerY width : Float) : Except String Result := do
      let mut content : Result := {}
      let mut inline : Array Inline := lead
      for seg in Table.segments dom styles kids do
        match seg with
        | .run run =>
          if !inline.isEmpty then
            content := append content (← inlineLayout font (← atomize font inline width) innerX (innerY+content.height) width (some s))
            inline := #[]
          content := append content (← layoutTask dom styles font embedding pictures fuel (.table none container run) innerX (innerY+content.height) width)
        | .node child =>
          let cs := styles[child]!
          if cs.display.isBlockLevel then
            if !inline.isEmpty then
              content := append content (← inlineLayout font (← atomize font inline width) innerX (innerY+content.height) width (some s))
              inline := #[]
            content := append content (← layoutTask dom styles font embedding pictures fuel (.box child) innerX (innerY+content.height) width)
          else
            inline := inline ++ (← inlineItems dom styles embedding pictures width fuel child)
      if !inline.isEmpty then content := append content (← inlineLayout font (← atomize font inline width) innerX (innerY+content.height) width (some s))
      return content
    -- A table box (CSS 2.1 §17): captions, then the grid, then bottom captions.
    let table (element : Option Nat) (container : Nat) (kids : Array Nat) : Except String Result := do
      let frame := tableFrame styles element container
      let ts := frame.style
      let grid := Table.build dom styles (element.getD container) kids
      let (hs,vs) := (frame.hs,frame.vs)
      -- Column widths from the cells' min-content and max-content widths.
      let mut measures : Array Table.Measure := #[]
      for cell in grid.cells do
        let (c,ks) := cellContents dom cell.source
        measures := measures.push (cellMeasure (cellStyle styles cell.source) (← intrinsic dom styles font embedding pictures fuel (.contents c ks)))
      let elements := grid.columnElements.map (columnMeasure styles)
      let cols := Table.columns grid.columns grid.cells measures elements hs
      let spacing := if grid.columns == 0 then 0 else hs*Float.ofNat (grid.columns+1)
      let padX := frame.padding.left+frame.padding.right
      let padY := frame.padding.top+frame.padding.bottom
      let lowest := Table.total (cols.map (·.min))+spacing
      -- `width` of a table is its border box (HTML §15.3.8 `table { box-sizing: border-box }`).
      let specified := (CSS.resolve available ts.width).map (·-padX)
      let room := available-frame.margin.left-frame.margin.right-padX
      let contentWidth := match specified with
        | some w => max w lowest
        | none => max lowest (min room (Table.total ((Table.guesses cols room)[3]!)+spacing))
      let target := max 0 (contentWidth-spacing)
      let widths := if ts.tableFixed && specified.isSome then
          let firstRow := (grid.cells.zip measures).filter (·.1.row == 0)
          Table.fixedWidths grid.columns firstRow elements target hs
        else Table.distribute cols target
      let contentWidth := max contentWidth (Table.extent widths hs)
      let borderWidth := contentWidth+padX
      let outerX := x+autoMarginShift ts available (frame.margin.left+borderWidth+frame.margin.right)+frame.margin.left
      let innerX := outerX+frame.padding.left
      let colX := Table.offsets widths hs
      -- Each cell laid out once, at its column and at the top; moved down when the rows are known.
      let mut laid : Array (Result × Float) := #[]
      for cell in grid.cells do
        let cs := cellStyle styles cell.source
        let (c,ks) := cellContents dom cell.source
        let w := Table.spanSize widths cell.col cell.colSpan hs
        let left := innerX+colX.getD cell.col 0+cs.padding.left
        let r ← layoutTask dom styles font embedding pictures fuel (.contents c ks) left cs.padding.top (max 0 (w-cs.padding.left-cs.padding.right))
        let own := (CSS.resolve 0 cs.height).getD 0
        let outer := max (r.height+cs.padding.top+cs.padding.bottom) (own+cs.padding.top+cs.padding.bottom)
        laid := laid.push (r,outer)
      let minimum := grid.rows.map fun row => match row.element with
        | some id => (CSS.resolve 0 (styles[id]!).height).getD 0
        | none => 0
      let rows := Table.rowHeights minimum grid.cells (laid.map (·.2)) vs
      let gridHeight := Table.extent rows vs
      let rows := match CSS.resolve 0 ts.height with
        | some h => Table.stretch rows (h-padY-gridHeight)
        | none => rows
      let gridHeight := Table.extent rows vs
      let borderHeight := max (gridHeight+padY) ((CSS.resolve 0 ts.height).getD 0)
      let rowY := Table.offsets rows vs
      -- Captions above and below, as wide as the table's border box.
      let mut out : Result := {}
      let mut top := y+frame.margin.top
      for caption in grid.captions do
        if !(styles[caption]!).captionBottom then
          let r ← layoutTask dom styles font embedding pictures fuel (.box caption) outerX top borderWidth
          out := append out r
          top := top+r.height
      let innerY := top+frame.padding.top
      let mut nodes : Array Node := background (element.getD container) ts outerX top borderWidth borderHeight
      let mut paints : Array Node := #[]
      let mut boxes : Array Box := #[]
      let mut runs : Array GlyphRun := #[]
      for (cell,(r,outer)) in grid.cells.zip laid do
        let cs := cellStyle styles cell.source
        let cx := innerX+colX.getD cell.col 0
        let cy := innerY+rowY.getD cell.row 0
        let w := Table.spanSize widths cell.col cell.colSpan hs
        let h := Table.spanSize rows cell.row cell.rowSpan vs
        -- Row group, row and cell backgrounds, each in the cell's area (CSS 2.1 §17.5.1).
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
      let tableBox : Array Box := match element with
        | some id => #[⟨id,outerX,top,borderWidth,borderHeight⟩]
        | none => #[]
      out := {out with nodes := out.nodes ++ nodes ++ paints, boxes := out.boxes ++ tableBox ++ boxes,
                       runs := out.runs ++ runs, height := out.height+borderHeight}
      top := top+borderHeight
      for caption in grid.captions do
        if (styles[caption]!).captionBottom then
          let r ← layoutTask dom styles font embedding pictures fuel (.box caption) outerX top borderWidth
          out := append out r
          top := top+r.height
      return {out with height := top-y+frame.margin.bottom}
    match task with
    | .contents container kids => flow (styles[container]!) container kids #[] x y available
    | .table element container kids => table element container kids
    | .box id =>
      let n := dom.get id
      let s := styles[id]!
      if s.display == .none then return {}
      if s.display.isTable then return (← table (some id) (n.parent.getD 0) n.kids)
      if n.lname == "hr" then
        return {nodes := #[.paint ⟨some id,{geometry := .rect x (y+8) available 1,style := {fill := .solid ⟨0.5,0.5,0.5⟩}}⟩],height := 17}
      let margin := s.margin
      let padding := s.padding
      let border := s.borderEdges
      let edgesX := border.left+border.right+padding.left+padding.right
      -- CSS 2.1 §10.4: the width, then `max-width`, then `min-width` (a minimum wins).
      let width := (CSS.resolve available s.width).getD (available-margin.left-margin.right-edgesX)
      let width := match CSS.resolve available s.maxWidth with
        | some m => min width m
        | none => width
      let width := max 0 (max ((CSS.resolve available s.minWidth).getD 0) width)
      -- §10.3.3: auto margins share the room the box leaves.
      let shift := autoMarginShift s available (margin.left+width+edgesX+margin.right)
      let outerX := x+shift+margin.left
      let outerY := y+margin.top
      let innerX := outerX+border.left+padding.left
      let innerY := outerY+border.top+padding.top
      -- A block-level replaced element: its margin box at the start of the line, or where
      -- its auto margins put it.
      let replaced := fun (w h : Float) (content : Float → Float → List Node) (s : Computed) =>
        let (ow,oh,nodes) := replacedBox id s w h content
        let dx := autoMarginShift s available ow
        ({nodes := #[.group none (translate (x+dx) y) nodes],
          boxes := #[⟨id,x+dx+margin.left,outerY,ow-margin.left-margin.right,oh-margin.top-margin.bottom⟩],height := oh} : Result)
      if let some picture := pictures id then
        let (w,h) := replacedSize s (some picture.size) available
        return replaced w h (fun cx cy => pictureNodes id s picture cx cy w h) s
      if n.ns == some DOM.svgNS then
        let (sw,sh) ← svgSize n s available
        let nodes ← embedding id s sw sh
        return replaced sw sh (fun cx cy => [.group none (translate cx cy) nodes]) {s with background := none}
      let lead := if n.lname == "li" then (textItems id s (listMarker dom id)).toArray
        else if n.lname == "img" then altItems id s n else #[]
      let content ← flow s id n.kids lead innerX innerY width
      let height := match s.height with
        | .percent _ => content.height
        | _ => max 0 ((CSS.resolve 0 s.height).getD content.height)
      let borderWidth := width+padding.left+padding.right+border.left+border.right
      let borderHeight := height+padding.top+padding.bottom+border.top+border.bottom
      let nodes := clipContent s.clipOverflow (decorations id s outerX outerY borderWidth borderHeight) content.nodes
        ⟨outerX+border.left,outerY+border.top,width+padding.left+padding.right,height+padding.top+padding.bottom,identity⟩
      let box : Box := ⟨id,outerX,outerY,borderWidth,borderHeight⟩
      return {content with nodes, boxes := #[box] ++ content.boxes, height := margin.top+borderHeight+margin.bottom}

/-- An element's block box: `layoutTask` of `.box id`. -/
def block (dom : Dom) (styles : Array Computed) (font : FontProfile) (embedding : Embedding)
    (pictures : Pictures) (fuel id : Nat) (x y available : Float) : Except String Result :=
  layoutTask dom styles font embedding pictures fuel (.box id) x y available

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

/-- Existing DOM input, explicit viewport and font data, immutable scene output.
`pictures` holds the decoded content of replaced elements. -/
def render (dom : Dom) (rules : List CSS.Rule) (font : FontProfile) (embedding : Embedding)
    (width height : Nat) (textScale : Float := 1) (state : CSS.ElementState := {})
    (pictures : Pictures := noPictures) : Except String (Scene × Array Box) := do
  if width == 0 || height == 0 || width > 4096 || height > 4096 then throw "unsupported viewport: require dimensions 1 to 4096"
  let vw := Float.ofNat width
  let vh := Float.ofNat height
  let styles := (← CSS.computeAll dom rules textScale state).map fun s =>
    {s with width := s.width.atViewport vw vh, height := s.height.atViewport vw vh,
            minWidth := s.minWidth.atViewport vw vh, maxWidth := s.maxWidth.atViewport vw vh,
            minHeight := s.minHeight.atViewport vw vh, maxHeight := s.maxHeight.atViewport vw vh}
  let canvas := canvasBackground dom styles
  let styles := match canvas with
    | some (id,_) => styles.modify id fun s => {s with background := none}
    | none => styles
  let result ← block dom styles font embedding pictures 64 0 0 0 vw
  let result : Result := match canvas with
    | some (id,c) => {result with nodes := #[Node.paint ⟨some id,{geometry := .rect 0 0 vw (max vh result.height),style := {fill := .solid c}}⟩] ++ result.nodes}
    | none => result
  if result.nodes.size > 1048576 then throw "HTML paint count exceeds 1048576"
  -- Links are kept down to the foot of the document, not the viewport: a host that scrolls
  -- a band of the page with no new layout (the Hub, issue 1268) hit-tests links below the
  -- first screen with this list.
  let links := linkRegions dom styles result.boxes (Float.ofNat width) (linkHeight vh result.height)
  if links.size > 49152 || links.any (fun link => link.href.utf8ByteSize > 2048) then
    throw "unsupported link region count or href exceeding 2048 UTF-8 bytes"
  return (⟨width,height,⟨1,1,0,0,0,0,Float.ofNat width,Float.ofNat height⟩, result.nodes.toList,result.runs,links⟩,result.boxes)

end L4Factoidal.Rendering.Layout
