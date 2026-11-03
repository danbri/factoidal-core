import L4Factoidal.Rendering.Style
import L4Factoidal.Rendering.FontFace

/-! Block flow and inline word wrapping over the existing DOM arena. This
profile excludes floats, positioning, bidi, flex/grid, margin collapse and
inline box decorations. Those features are refused rather than approximated. -/
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

def FontProfile.ofFace (face : FontProvider.Face) : FontProfile :=
  {family := face.family,unitsPerEm := face.unitsPerEm,advance := 0,
   ascent := face.ascent,descent := face.descent,outline := fun _ => [],admits := fun _ => false,
   cssFamilies := [face.family],fontSha256 := some face.fontSha256,faceIndex := face.faceIndex,
   shapedWord := some face.lookup}

private def FontProfile.checkFamily (font : FontProfile) (style : Computed) : Except String Unit := do
  if !font.cssFamilies.any (fun family => family.toLower == style.fontFamily.toLower) then
    throw s!"unsupported font family: {style.fontFamily} (matching font data required)"

private def FontProfile.word (font : FontProfile) (style : Computed) (text : String) : Except String (Option FontProvider.Word) := do
  font.checkFamily style
  match font.shapedWord with
  | none => return none
  | some shape =>
    let size := style.fontSize.toUInt32.toNat
    if Float.ofNat size != style.fontSize || size == 0 || size > 512 then
      throw "unsupported shaped font size: integer pixels 1 to 512 required"
    let word ← shape text size
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
  if s.margin.top != 0 || s.margin.right != 0 || s.margin.bottom != 0 || s.margin.left != 0 ||
      s.padding.top != 0 || s.padding.right != 0 || s.padding.bottom != 0 || s.padding.left != 0 then
    throw "unsupported embedded SVG margin or padding"
  if let .percent _ := s.height then
    throw "unsupported percentage SVG height without definite containing height"

inductive Inline where
  | word (source : Nat) (style : Computed) (text : String) (start : Nat)
  | space (source : Nat) (style : Computed)
  | lineBreak (style : Computed)
  | replaced (source : Nat) (width height : Float) (nodes : List Node)
  deriving Repr

private def textItems (id : Nat) (style : Computed) (text : String) : List Inline := Id.run do
  let mut result : List Inline := []
  let mut word := ""
  let mut start := 0
  let mut index := 0
  let mut spaced := false
  for c in text.toList do
    if [' ','\n','\r','\t'].contains c || c.toNat == 12 then
      if !word.isEmpty then
        result := .word id style word start :: result
        word := ""
      if !spaced then result := .space id style :: result
      spaced := true
    else
      if word.isEmpty then start := index
      word := word.push c
      spaced := false
    index := index+1
  if !word.isEmpty then result := .word id style word start :: result
  return result.reverse

/-- Inline descendants are flattened in DOM order; the nesting budget is a
profile error, never a silent truncation. Siblings use a fold. -/
def inlineItems (dom : Dom) (styles : Array Computed) (embedding : Embedding) (available : Float) :
    Nat → Nat → Except String (Array Inline)
  | 0, _ => throw "unsupported HTML nesting depth (maximum 64)"
  | fuel+1, id => do
    let n := dom.get id
    let s := styles[id]!
    if s.display == .none then return #[]
    if n.type == .text then return (textItems id s n.data).toArray
    if n.type != .element then return #[]
    if n.ns != some DOM.htmlNS && n.ns != some DOM.svgNS then
      throw "unsupported foreign namespace in HTML layout"
    if ["img","input","textarea","select","video","audio","canvas","iframe","object","embed","table","ruby","ul","ol","li"].contains n.lname then
      throw s!"unsupported HTML layout element: {n.lname}"
    if n.lname == "br" then return #[.lineBreak s]
    if s.display == .block then throw "unsupported block descendant inside inline context"
    if n.ns != some DOM.svgNS && (s.background.isSome ||
      s.margin.top != 0 || s.margin.right != 0 || s.margin.bottom != 0 || s.margin.left != 0 ||
      s.padding.top != 0 || s.padding.right != 0 || s.padding.bottom != 0 || s.padding.left != 0 || s.clipOverflow) then
      throw "unsupported inline box decoration or spacing"
    if n.ns == some DOM.svgNS then
      checkSVGBox s
      let attrLength := fun key fallback => do
        let v := CSS.attrValue n key
        if v.isEmpty then pure fallback else CSS.number v
      let width := (CSS.resolve available s.width).getD (← attrLength "width" 300)
      let height := (CSS.resolve 150 s.height).getD (← attrLength "height" 150)
      if width <= 0 || height <= 0 then return #[]
      return #[.replaced id width height (← embedding id s width height)]
    let mut out := #[]
    for child in n.kids do out := out ++ (← inlineItems dom styles embedding available fuel child)
    return out

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

private def itemWidth (font : FontProfile) : Inline → Except String Float
  | .word _ s text _ => do
    match ← font.word s text with
    | none => return font.advance*s.fontSize/font.unitsPerEm*Float.ofNat text.length
    | some word => return word.advance*s.fontSize/font.unitsPerEm
  | .replaced _ w _ _ => pure w
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

/-- All inline participants share the line baseline, computed before any glyph
position or replaced-element position is emitted. -/
private def lineLayout (font : FontProfile) (items : Array (Float × Inline))
    (x y : Float) (strut : Option Computed) : Except String Result := do
  let mut ascent : Float := 0
  let mut descent : Float := 0
  if let some style := strut then
    font.checkFamily style
    let leading := lineLeading font style
    ascent := font.ascent*style.fontSize/font.unitsPerEm+leading
    descent := font.descent*style.fontSize/font.unitsPerEm+leading
  for (_,item) in items do
    match item with
    | .word _ s _ _ | .space _ s | .lineBreak s =>
      font.checkFamily s
      let leading := lineLeading font s
      ascent := max ascent (font.ascent*s.fontSize/font.unitsPerEm+leading)
      descent := max descent (font.descent*s.fontSize/font.unitsPerEm+leading)
    | .replaced _ _ h _ => ascent := max ascent h
  let mut out : Result := {height := ascent+descent}
  for (offset,item) in items do
    match item with
    | .word source s text start =>
      let top := y+ascent-font.ascent*s.fontSize/font.unitsPerEm
      let leading := lineLeading font s
      match ← font.word s text with
      | none =>
        let chars := text.toList
        if !chars.all (fun c => font.admits c.toNat) then
          throw "unsupported text: ASCII bitmap font admits U+0020 to U+007E only"
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
      out := {out with boxes := out.boxes.push ⟨source,x+offset,top,advance,s.lineHeight⟩}
      if s.underline && s.visible then
        let thickness := max 1 (s.fontSize/14)
        out := {out with nodes := out.nodes.push (.paint ⟨some source,{geometry := .rect (x+offset) (y+ascent+thickness) advance thickness,style := {fill := .solid (s.decorationColor.getD s.color)}}⟩)}
    | .replaced source width height nodes =>
      let top := y+ascent-height
      out := {out with nodes := out.nodes.push (.group none (translate (x+offset) top) nodes), boxes := out.boxes.push ⟨source,x+offset,top,width,height⟩}
    | _ => pure ()
  return out

private def appendResult (a b : Result) : Result :=
  {nodes := a.nodes ++ b.nodes, boxes := a.boxes ++ b.boxes, runs := a.runs ++ b.runs, height := a.height+b.height}

/-- Word wrapping constructs line participants first. The font profile and
positioned glyph runs are consumed to paint the actual word geometry. -/
def inlineLayout (font : FontProfile) (items : Array Inline) (x y available : Float)
    (strut : Option Computed := none) : Except String Result := do
  let mut out : Result := {}
  let mut cursorX : Float := 0
  let mut pendingSpace : Option (Nat × Computed) := none
  let mut line : Array (Float × Inline) := #[]
  for item in items do
    match item with
    | .space source s => pendingSpace := some (source,s)
    | .lineBreak _ =>
      let row ← lineLayout font (line.push (cursorX,item)) x (y+out.height) strut
      out := appendResult out {row with height := if row.height > 0 then row.height else 19.2}
      line := #[]
      cursorX := 0
      pendingSpace := none
    | _ =>
      let width ← itemWidth font item
      let gap ← if cursorX > 0 then match pendingSpace with
        | some (_,s) => spaceWidth font s
        | none => pure 0
        else pure 0
      if cursorX > 0 && cursorX+gap+width > available then
        out := appendResult out (← lineLayout font line x (y+out.height) strut)
        line := #[]
        cursorX := 0
      else
        if gap > 0 then
          if let some (source,s) := pendingSpace then line := line.push (cursorX,.space source s)
        cursorX := cursorX+gap
      line := line.push (cursorX,item)
      cursorX := cursorX+width
      pendingSpace := none
  if !line.isEmpty then out := appendResult out (← lineLayout font line x (y+out.height) strut)
  return out

private def append (a b : Result) : Result :=
  {nodes := a.nodes ++ b.nodes,boxes := a.boxes ++ b.boxes,runs := a.runs ++ b.runs, height := a.height+b.height}
private def background (id : Nat) (s : Computed) (x y w h : Float) : Array Node :=
  match s.background with
  | none => #[]
  | some c => if !s.visible || w <= 0 || h <= 0 then #[] else
    #[.paint ⟨some id,{geometry := .rect x y w h,style := {fill := .solid c}}⟩]

/-- Block children stack vertically, and adjacent inline children share an
anonymous inline formatting context. Width/height use the CSS content box. -/
def block (dom : Dom) (styles : Array Computed) (font : FontProfile) (embedding : Embedding) :
    Nat → Nat → Float → Float → Float → Except String Result
  | 0, _, _, _, _ => throw "unsupported HTML nesting depth (maximum 64)"
  | fuel+1, id, x, y, available => do
    let n := dom.get id
    let s := styles[id]!
    if s.display == .none then return {}
    if n.type == .element && n.ns != some DOM.htmlNS && n.ns != some DOM.svgNS then
      throw "unsupported foreign namespace in HTML layout"
    if ["table","ul","ol","li"].contains n.lname then throw s!"unsupported HTML layout element: {n.lname}"
    let margin := s.margin
    if n.lname != "body" && (margin.top != 0 || margin.bottom != 0) then
      throw "unsupported collapsing vertical block margins"
    let padding := s.padding
    let outerX := x+margin.left
    let outerY := y+margin.top
    let width := max 0 ((CSS.resolve available s.width).getD
      (available-margin.left-margin.right-padding.left-padding.right))
    let innerX := outerX+padding.left
    let innerY := outerY+padding.top
    if n.ns == some DOM.svgNS then
      checkSVGBox s
      let v := CSS.attrValue n "width"
      let intrinsicWidth ← if v.isEmpty then pure 300 else CSS.number v
      let v := CSS.attrValue n "height"
      let intrinsicHeight ← if v.isEmpty then pure 150 else CSS.number v
      let sw := max 0 ((CSS.resolve available s.width).getD intrinsicWidth)
      let sh := max 0 ((CSS.resolve 0 s.height).getD intrinsicHeight)
      let nodes ← embedding id s sw sh
      return {nodes := #[.group none (translate outerX outerY) nodes], boxes := #[⟨id,outerX,outerY,sw,sh⟩],height := margin.top+sh+margin.bottom}
    let mut content : Result := {}
    let mut inline : Array Inline := #[]
    for child in n.kids do
      let cs := styles[child]!
      if cs.display == .block then
        if !inline.isEmpty then
          content := append content (← inlineLayout font inline innerX (innerY+content.height) width (some s))
          inline := #[]
        content := append content (← block dom styles font embedding fuel child innerX (innerY+content.height) width)
      else
        if cs.display == .inlineBlock then throw "unsupported CSS inline-block layout"
        inline := inline ++ (← inlineItems dom styles embedding width fuel child)
    if !inline.isEmpty then content := append content (← inlineLayout font inline innerX (innerY+content.height) width (some s))
    if let .percent _ := s.height then throw "unsupported percentage height without definite containing height"
    let height := max 0 ((CSS.resolve 0 s.height).getD content.height)
    let borderWidth := width+padding.left+padding.right
    let borderHeight := height+padding.top+padding.bottom
    let nodes := background id s outerX outerY borderWidth borderHeight ++ content.nodes
    let nodes := if s.clipOverflow then
      #[.clipped none identity ⟨outerX,outerY,borderWidth,borderHeight,identity⟩ nodes.toList]
      else nodes
    let box : Box := ⟨id,outerX,outerY,borderWidth,borderHeight⟩
    return {content with nodes, boxes := #[box] ++ content.boxes, height := margin.top+borderHeight+margin.bottom}

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

private def clipLinkBox (dom : Dom) (clips : Std.TreeMap Nat Box) : Nat → Nat → Box → Box
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

/-- Link fragments come from the same visible layout boxes as glyphs and
replaced elements. Collapsed spaces produce boxes only when retained on a line. -/
def linkRegions (dom : Dom) (styles : Array Computed) (boxes : Array Box)
    (width height : Float) : Array LinkRegion :=
  let clipBoxes := boxes.foldl (fun (out : Std.TreeMap Nat Box) box =>
    if (styles[box.source]!).clipOverflow && (dom.get box.source).type == .element then out.insert box.source box else out) {}
  boxes.foldl (fun (out : Array LinkRegion) (box : Box) =>
    match anchorAncestor dom (dom.size+1) box.source with
    | none => out
    | some (source,href) =>
      let box := clipLinkBox dom clipBoxes (dom.size+1) box.source box
      if (styles[box.source]!).visible && box.width > 0 && box.height > 0 then
        let left := max 0 box.x
        let top := max 0 box.y
        let right := min width (box.x+box.width)
        let bottom := min height (box.y+box.height)
        if right > left && bottom > top then out.push ⟨source,href,left,top,right-left,bottom-top⟩ else out
      else out) #[]

/-- Existing DOM input, explicit viewport and font data, immutable scene output. -/
def render (dom : Dom) (rules : List CSS.Rule) (font : FontProfile) (embedding : Embedding)
    (width height : Nat) : Except String (Scene × Array Box) := do
  if width == 0 || height == 0 || width > 4096 || height > 4096 then throw "unsupported viewport: require dimensions 1 to 4096"
  let styles ← CSS.computeAll dom rules
  let result ← block dom styles font embedding 64 0 0 0 (Float.ofNat width)
  if result.nodes.size > 12288 then throw "HTML paint count exceeds 12288"
  let links := linkRegions dom styles result.boxes (Float.ofNat width) (Float.ofNat height)
  if links.size > 12288 || links.any (fun link => link.href.utf8ByteSize > 2048) then
    throw "unsupported link region count or href exceeding 2048 UTF-8 bytes"
  return (⟨width,height,⟨1,1,0,0,0,0,Float.ofNat width,Float.ofNat height⟩, result.nodes.toList,result.runs,links⟩,result.boxes)

end L4Factoidal.Rendering.Layout
