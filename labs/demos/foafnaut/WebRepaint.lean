import L4Factoidal.Rendering.Layout

/-! # Hover and `:active` with no layout (issues 1268 and 1292)

A pointer state (the hover and active nodes of `CSS.ElementState`) is not in the layout
key (`WebDocument.LayoutKey.pointer` is empty for it). The page is laid out once with
no pointer state; a frame with one re-runs the cascade with it and compares the
computed styles. When every style that changed changes colours only (`sameShape`),
the boxes, lines and glyph places are those of the layout without it, and the paints
are the same paints with other colours: `recolor` gives them the new colours. When a
style changes anything else (a padding, a border width, an underline that comes or
goes), `restyle` answers `none` and the host's frame lays out with the pointer state in
the key (`FrameCost.hover_geometry_layouts` is that case).

`WebDocumentTests.lean` checks, for pages with colour-only and with geometry hover and
active styles, that a frame through `restyle` is the frame that a layout with the
pointer state gives (`run` against `runUncached`).

A paint of the HTML layout takes its colour from the style of its source node
(`Layout.glyphNodes`, `shapedNodes`, `background`, `borderNodes`, the underline), from
the background of an inline ancestor (`Layout.withBackground`), or is the grey rule of
`hr`. `recolor` maps each colour of a source through the colour pairs of that node and
its ancestors, and gives up (answers `none`) when one old colour would map to two new
ones, or when a colour is not one of them. A node whose paints come from elsewhere (SVG,
a replaced element, a table) gives up as well. -/
namespace WebRepaint
open L4Factoidal L4Factoidal.Rendering
open L4Factoidal.Rendering.CSS (Computed Edges)

private def colorEq (a b : Color) : Bool := a.r == b.r && a.g == b.g && a.b == b.b
private def lengthEq : CSS.Length → CSS.Length → Bool
  | .auto, .auto => true
  | .px a, .px b => a == b
  | .percent a, .percent b => a == b
  | .vw a, .vw b => a == b
  | .vh a, .vh b => a == b
  | .calc a c, .calc b d => a == b && c == d
  | .minContent, .minContent => true
  | .maxContent, .maxContent => true
  | .fitContent, .fitContent => true
  | .stretch, .stretch => true
  | _, _ => false
private def edgesEq (a b : Edges) : Bool :=
  a.top == b.top && a.right == b.right && a.bottom == b.bottom && a.left == b.left
private def optEq {α : Type} (eq : α → α → Bool) : Option α → Option α → Bool
  | some a, some b => eq a b
  | none, none => true
  | _, _ => false
/-- Two side colours that are the same colour, or both `currentColor`, or both transparent. -/
private def sideColorEq : CSS.SideColor → CSS.SideColor → Bool
  | .current, .current => true
  | .transparent, .transparent => true
  | .color a, .color b => colorEq a b
  | .alpha a x, .alpha b y => colorEq a b && x == y
  | _, _ => false
private def sideColorsEq (a b : CSS.Sides CSS.SideColor) : Bool :=
  sideColorEq a.top b.top && sideColorEq a.right b.right && sideColorEq a.bottom b.bottom && sideColorEq a.left b.left
/-- The sides that are transparent: a side that is, or stops being, transparent paints a
different number of shapes. -/
private def transparentSides (a : CSS.Sides CSS.SideColor) : List Bool :=
  [a.top,a.right,a.bottom,a.left].map fun | .transparent => true | _ => false

/-- Every field of `Computed` but the colours is equal, and a background, a border and
an underline are there in both or in neither: the two styles lay out the same and make
the same paints. The anonymous constructor names every field in order, so a field added
to `Computed` stops this from compiling until it is sorted here. The custom properties
(`vars`) are not compared: they act only through the other fields of this element and of
its descendants, each of which is compared itself. -/
def sameShape (a b : Computed) : Bool :=
  match a with
  | ⟨display,width,height,margin,padding,_color,background,backgroundGradient,columnCount,columnWidth,fontSize,fontFamily,lineHeight,
    lineHeightFactor,visible,clipOverflow,underline,decorationColor,preformatted,borderWidth,borderStyle,
    borderColor,borderSpacingX,borderSpacingY,borderCollapse,captionBottom,verticalAlign,tableFixed,
    minWidth,maxWidth,minHeight,maxHeight,objectFit,textAlign,direction,unicodeBidi,autoMarginLeft,autoMarginRight,
    autoMarginTop,autoMarginBottom,align,flex,pos,_vars,grid,fontWeight,inheritedWeight,oblique,
    colorAlpha,backgroundAlpha,opacity,paintOpacity⟩ =>
  display == b.display && lengthEq width b.width && lengthEq height b.height &&
  edgesEq margin b.margin && edgesEq padding b.padding &&
  background.isSome == b.background.isSome && fontSize == b.fontSize && fontFamily == b.fontFamily &&
  -- a gradient background is painted from its stops: a style with one is never the same shape
  backgroundGradient.isNone && b.backgroundGradient.isNone &&
  columnCount == b.columnCount && optEq (· == ·) columnWidth b.columnWidth &&
  lineHeight == b.lineHeight && optEq (· == ·) lineHeightFactor b.lineHeightFactor &&
  visible == b.visible && clipOverflow == b.clipOverflow && underline == b.underline &&
  decorationColor.isSome == b.decorationColor.isSome && preformatted == b.preformatted &&
  edgesEq borderWidth b.borderWidth && borderStyle == b.borderStyle &&
  transparentSides borderColor == transparentSides b.borderColor &&
  borderSpacingX == b.borderSpacingX && borderSpacingY == b.borderSpacingY &&
  borderCollapse == b.borderCollapse && captionBottom == b.captionBottom &&
  verticalAlign == b.verticalAlign && tableFixed == b.tableFixed &&
  lengthEq minWidth b.minWidth && lengthEq maxWidth b.maxWidth &&
  lengthEq minHeight b.minHeight && lengthEq maxHeight b.maxHeight && objectFit == b.objectFit &&
  textAlign == b.textAlign && direction == b.direction && unicodeBidi == b.unicodeBidi &&
  autoMarginLeft == b.autoMarginLeft && autoMarginRight == b.autoMarginRight &&
  autoMarginTop == b.autoMarginTop && autoMarginBottom == b.autoMarginBottom &&
  align.same b.align && flex.same b.flex && pos.same b.pos && grid.same b.grid &&
  -- the bold and the oblique face change the paints of the glyphs, not only their colour
  fontWeight == b.fontWeight && inheritedWeight == b.inheritedWeight && oblique == b.oblique &&
  -- an alpha or an opacity changes how a paint is made, not only its colour
  colorAlpha == b.colorAlpha && backgroundAlpha == b.backgroundAlpha && opacity == b.opacity &&
  paintOpacity == b.paintOpacity

/-- The same style, colours included. -/
def same (a b : Computed) : Bool :=
  sameShape a b && colorEq a.color b.color && optEq colorEq a.background b.background &&
  sideColorsEq a.borderColor b.borderColor && optEq colorEq a.decorationColor b.decorationColor &&
  a.borderStyle == b.borderStyle

/-- The colours of a side's border, as `Layout.borderNodes` makes them: the side's colour
and its tones (`Layout.sideTones`, for the near and the far sides). -/
private def sideColours (s : Computed) (c : CSS.SideColor) (st : CSS.BorderStyle) : List Color :=
  match Layout.sidePaint s c with
  | none => []
  | some x =>
    let (a,b) := Layout.sideTones st true x
    let (c',d) := Layout.sideTones st false x
    [x,a,b,c',d,Layout.lighter x,Layout.darker x]
/-- The colour pairs (before, after) of the paints that a node's own style makes. -/
def ownPairs (a b : Computed) : List (Color × Color) :=
  [(a.color,b.color)] ++
  (match a.background,b.background with | some x,some y => [(x,y)] | _,_ => []) ++
  (if a.underline then [(a.decorationColor.getD a.color,b.decorationColor.getD b.color)] else []) ++
  (if !a.hasBorder then [] else
    (["top","right","bottom","left"].flatMap fun side =>
      (sideColours a (a.borderColor.get side) (a.borderStyle.get side)).zip
        (sideColours b (b.borderColor.get side) (b.borderStyle.get side))))

/-- The background pair of a node, for the text of its inline descendants. -/
private def backgroundPairs (a b : Computed) : List (Color × Color) :=
  match a.background,b.background with | some x,some y => [(x,y)] | _,_ => []

/-- The grey of `hr` (`Layout`), which no style changes. -/
private def rule : Color := ⟨0.5,0.5,0.5⟩

/-- The new colour of `c` under `pairs`: none when `c` is in no pair, or when two pairs
with old colour `c` disagree. -/
def mapColor (pairs : List (Color × Color)) (c : Color) : Option Color :=
  match pairs.filter (colorEq ·.1 c) with
  | [] => none
  | (_,n) :: rest => if rest.all (colorEq ·.2 n) then some n else none

/-- Elements whose paints do not all come from their computed style. -/
private def foreign (n : DOM.Node) : Bool :=
  n.ns == some DOM.svgNS || n.ns == some DOM.mathmlNS ||
  ["svg","img","video","canvas","object","embed","iframe","math","picture","input","select","textarea"].contains n.lname

/-- For each node: `none` when its paints keep their colours; `some pairs` when they
are to be mapped through `pairs`. Fails when a node that changed changes geometry, or
when a node with paints to map makes paints from elsewhere. Nodes come parents first
(`dom.treeOrder 0`). -/
def plan (dom : DOM.Dom) (old new : Array Computed) : Option (Array (Option (List (Color × Color)))) := Id.run do
  if old.size != dom.size || new.size != dom.size then return none
  -- `inherited[id]`: the background pairs of the ancestors of `id`, and whether one of
  -- them changed.
  let mut inherited : Array (List (Color × Color) × Bool) := Array.replicate dom.size ([],false)
  let mut out : Array (Option (List (Color × Color))) := Array.replicate dom.size none
  for id in dom.treeOrder 0 do
    let n := dom.get id
    let a := old[id]!
    let b := new[id]!
    let changed := !same a b
    if changed && !sameShape a b then return none
    let (above,aboveChanged) := inherited[id]!
    let dirty := changed || aboveChanged
    if dirty then
      if foreign n || a.display.isTable || a.display.isTableInternal || a.borderCollapse then return none
      let fixed := if n.type == .element && n.lname == "hr" then [(rule,rule)] else []
      out := out.set! id (some (ownPairs a b ++ above ++ fixed))
    let below := (backgroundPairs a b ++ above,dirty)
    for kid in n.kids do
      if kid < inherited.size then inherited := inherited.set! kid below
  return some out

/-- A paint with its colour mapped, or none. Only solid fills come from styles. -/
private def recolorItem (plan : Array (Option (List (Color × Color)))) (item : PaintItem) : Option PaintItem :=
  match item.source.bind (plan[·]?) |>.join with
  | none => some item
  | some pairs =>
    match item.primitive.style.fill,item.primitive.style.stroke with
    | .solid c,.none => (mapColor pairs c).map fun n =>
        {item with primitive := {item.primitive with style := {item.primitive.style with fill := .solid n}}}
    | .solid c,.solid outline =>
      -- text in the bold face the engine makes (`Layout.glyphStyle`): the outline is filled
      -- and stroked with the one colour
      if colorEq c outline then (mapColor pairs c).map fun n =>
        {item with primitive := {item.primitive with style := {item.primitive.style with fill := .solid n, stroke := .solid n}}}
      else none
    | _,_ => none

mutual
  def recolorNode (plan : Array (Option (List (Color × Color)))) : Node → Option Node
    | .paint item => (recolorItem plan item).map .paint
    | .group id transform children => (recolorList plan children).map (.group id transform)
    | .clipped id content clip children => (recolorList plan children).map (.clipped id content clip)
  termination_by node => sizeOf node
  def recolorList (plan : Array (Option (List (Color × Color)))) : List Node → Option (List Node)
    | [] => some []
    | node :: rest => do
      let head ← recolorNode plan node
      let tail ← recolorList plan rest
      return head :: tail
  termination_by nodes => sizeOf nodes
end

/-- The scene of a layout with no pointer state, given the styles of that layout (`old`)
and the styles with the pointer state (`new`): the same scene with the new colours, or
none when a style changed more than colours. -/
def recolor (dom : DOM.Dom) (old new : Array Computed) (scene : Scene) : Option Scene := do
  let plan ← plan dom old new
  if plan.all Option.isNone then return scene
  let tree ← recolorList plan scene.tree
  return {scene with tree}

end WebRepaint
