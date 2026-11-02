import L4Factoidal.Rendering.Style

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
abbrev Embedding := Nat → Float → Float → Except String (List Node)

inductive Inline where
  | word (source : Nat) (style : Computed) (text : String) (start : Nat)
  | space (style : Computed)
  | lineBreak
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
      if !spaced then result := .space style :: result
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
def inlineItems (dom : Dom) (styles : Array Computed) (embedding : Embedding) :
    Nat → Nat → Except String (Array Inline)
  | 0, _ => throw "unsupported HTML nesting depth (maximum 64)"
  | fuel+1, id => do
    let n := dom.get id
    let s := styles[id]!
    if s.display == .none then return #[]
    if n.type == .text then return (textItems id s n.data).toArray
    if n.type != .element then return #[]
    if n.lname == "br" then return #[.lineBreak]
    if n.ns != some DOM.svgNS && (s.background.isSome ||
      s.margin.top != 0 || s.margin.right != 0 || s.margin.bottom != 0 || s.margin.left != 0 ||
      s.padding.top != 0 || s.padding.right != 0 || s.padding.bottom != 0 || s.padding.left != 0) then
      throw "unsupported inline box decoration or spacing"
    if n.ns == some DOM.svgNS then
      let attrLength := fun key fallback => do
        let v := CSS.attrValue n key
        if v.isEmpty then pure fallback else CSS.number v
      let width := (CSS.resolve 300 s.width).getD (← attrLength "width" 300)
      let height := (CSS.resolve 150 s.height).getD (← attrLength "height" 150)
      if width <= 0 || height <= 0 then return #[]
      return #[.replaced id width height (← embedding id width height)]
    let mut out := #[]
    for child in n.kids do out := out ++ (← inlineItems dom styles embedding fuel child)
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
  return out

private def itemWidth (font : FontProfile) : Inline → Float
  | .word _ s text _ => font.advance*s.fontSize/font.unitsPerEm*Float.ofNat text.length
  | .replaced _ w _ _ => w
  | _ => 0

/-- All inline participants share the line baseline, computed before any glyph
position or replaced-element position is emitted. -/
private def lineLayout (font : FontProfile) (items : Array (Float × Inline))
    (x y : Float) : Except String Result := do
  let mut ascent : Float := 0
  let mut descent : Float := 0
  for (_,item) in items do
    match item with
    | .word _ s _ _ =>
      let leading := (s.lineHeight-s.fontSize)/2
      ascent := max ascent (font.ascent*s.fontSize/font.unitsPerEm+leading)
      descent := max descent (font.descent*s.fontSize/font.unitsPerEm+leading)
    | .replaced _ _ h _ => ascent := max ascent h
    | _ => pure ()
  let mut out : Result := {height := ascent+descent}
  for (offset,item) in items do
    match item with
    | .word source s text start =>
      let chars := text.toList
      if !chars.all (fun c => font.admits c.toNat) then
        throw "unsupported text: ASCII bitmap font admits U+0020 to U+007E only"
      let advance := font.advance*s.fontSize/font.unitsPerEm
      let top := y+ascent-font.ascent*s.fontSize/font.unitsPerEm
      let glyphs := chars.toArray.mapIdx fun i c =>
        ({index := c.toNat, x := x+offset+Float.ofNat i*advance, y := top, advance, clusterStart := start+i, clusterEnd := start+i+1} : Glyph)
      let run : GlyphRun := ⟨source,font.family,s.fontSize,text,glyphs⟩
      out := {out with nodes := out.nodes ++ glyphNodes font run s, runs := out.runs.push run}
    | .replaced source width height nodes =>
      let top := y+ascent-height
      out := {out with nodes := out.nodes.push (.group none (translate (x+offset) top) nodes), boxes := out.boxes.push ⟨source,x+offset,top,width,height⟩}
    | _ => pure ()
  return out

private def appendResult (a b : Result) : Result :=
  {nodes := a.nodes ++ b.nodes, boxes := a.boxes ++ b.boxes, runs := a.runs ++ b.runs, height := a.height+b.height}

/-- Word wrapping constructs line participants first. The font profile and
positioned glyph runs are consumed to paint the actual word geometry. -/
def inlineLayout (font : FontProfile) (items : Array Inline) (x y available : Float) : Except String Result := do
  let mut out : Result := {}
  let mut cursorX : Float := 0
  let mut pendingSpace : Float := 0
  let mut line : Array (Float × Inline) := #[]
  for item in items do
    match item with
    | .space s => pendingSpace := font.advance*s.fontSize/font.unitsPerEm
    | .lineBreak =>
      let row ← lineLayout font line x (y+out.height)
      out := appendResult out {row with height := max row.height 19.2}
      line := #[]
      cursorX := 0
      pendingSpace := 0
    | _ =>
      let width := itemWidth font item
      let gap := if cursorX > 0 then pendingSpace else 0
      if cursorX > 0 && cursorX+gap+width > available then
        out := appendResult out (← lineLayout font line x (y+out.height))
        line := #[]
        cursorX := 0
      else cursorX := cursorX+gap
      line := line.push (cursorX,item)
      cursorX := cursorX+width
      pendingSpace := 0
  if !line.isEmpty then out := appendResult out (← lineLayout font line x (y+out.height))
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
      let v := CSS.attrValue n "width"
      let intrinsicWidth ← if v.isEmpty then pure 300 else CSS.number v
      let v := CSS.attrValue n "height"
      let intrinsicHeight ← if v.isEmpty then pure 150 else CSS.number v
      let sw := max 0 ((CSS.resolve available s.width).getD intrinsicWidth)
      let sh := max 0 ((CSS.resolve 0 s.height).getD intrinsicHeight)
      let nodes ← embedding id sw sh
      return {nodes := #[.group none (translate outerX outerY) nodes], boxes := #[⟨id,outerX,outerY,sw,sh⟩],height := margin.top+sh+margin.bottom}
    let mut content : Result := {}
    let mut inline : Array Inline := #[]
    for child in n.kids do
      let cs := styles[child]!
      if cs.display == .block then
        if !inline.isEmpty then
          content := append content (← inlineLayout font inline innerX (innerY+content.height) width)
          inline := #[]
        content := append content (← block dom styles font embedding fuel child innerX (innerY+content.height) width)
      else
        if cs.display == .inlineBlock then throw "unsupported CSS inline-block layout"
        inline := inline ++ (← inlineItems dom styles embedding fuel child)
    if !inline.isEmpty then content := append content (← inlineLayout font inline innerX (innerY+content.height) width)
    if let .percent _ := s.height then throw "unsupported percentage height without definite containing height"
    let height := max 0 ((CSS.resolve 0 s.height).getD content.height)
    let borderWidth := width+padding.left+padding.right
    let borderHeight := height+padding.top+padding.bottom
    let nodes := background id s outerX outerY borderWidth borderHeight ++ content.nodes
    let box : Box := ⟨id,outerX,outerY,borderWidth,borderHeight⟩
    return {content with nodes, boxes := #[box] ++ content.boxes, height := margin.top+borderHeight+margin.bottom}

/-- Existing DOM input, explicit viewport and font data, immutable scene output. -/
def render (dom : Dom) (rules : List CSS.Rule) (font : FontProfile) (embedding : Embedding)
    (width height : Nat) : Except String (Scene × Array Box) := do
  if width == 0 || height == 0 || width > 4096 || height > 4096 then throw "unsupported viewport: require dimensions 1 to 4096"
  let styles ← CSS.computeAll dom rules
  let result ← block dom styles font embedding 64 0 0 0 (Float.ofNat width)
  if result.nodes.size > 12288 then throw "HTML paint count exceeds 12288"
  return (⟨width,height,⟨1,1,0,0,0,0,Float.ofNat width,Float.ofNat height⟩, result.nodes.toList,result.runs⟩,result.boxes)

end L4Factoidal.Rendering.Layout
