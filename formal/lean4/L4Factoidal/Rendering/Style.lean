import L4Factoidal.Rendering.Scene
import L4Factoidal.DOM.OfHtml
import L4Factoidal.Unicode.Bidi
import L4Factoidal.Rendering.MediaQuery
import L4Factoidal.Rendering.CssValues.Properties
import L4Factoidal.Rendering.FlexStyle
import L4Factoidal.Rendering.GridStyle
import L4Factoidal.Rendering.CssValues.Logical
import L4Factoidal.Rendering.SheetReader
import L4Factoidal.Rendering.CssVars
import L4Factoidal.Rendering.FontSynthesis
import L4Factoidal.DOM.Selectors
import L4Factoidal.HTML.Dimension
import Std.Data.TreeMap
import Std.Data.HashMap

/-! Computed styles for an explicitly bounded CSS block/inline profile.
Selectors: universal, type, id and class compound selectors, selector lists and
descendants, and the pseudo-classes `:link`, `:visited`, `:any-link`, `:hover`
and `:active` (Selectors Level 4 §8 and §9) over an `ElementState` that the
host supplies. CSS error handling applies: what this profile does not understand
is dropped, and the rest of the sheet still applies. A page is never refused
for its style sheet. -/
namespace L4Factoidal.Rendering.CSS
open DOM
private def trim (s : String) := s.trimAscii.toString
-- `Length` is in `Rendering/BoxAlign.lean`, which the flex and alignment values also use.
structure Edges where
  top : Float := 0
  right : Float := 0
  bottom : Float := 0
  left : Float := 0
  deriving Repr
/-- CSS Display 3 outer and inner display types that this profile lays out.
The table values are those of CSS 2.1 §17.2 (CSS Tables 3 §2). -/
inductive Display where
  | none | block | inline | inlineBlock
  | table | inlineTable | tableRowGroup | tableHeaderGroup | tableFooterGroup
  | tableRow | tableCell | tableCaption | tableColumn | tableColumnGroup
  /-- Flex and grid containers (CSS Display 3 §2.2): block-level, or inline-level. -/
  | flex | inlineFlex | grid | inlineGrid
  deriving Repr, BEq

/-- Boxes that are laid out by the table layout. `inline-table` is laid out as a
block-level table: this profile has no atomic inline boxes
(https://github.com/danbri/factoidal/issues/1272). -/
def Display.isTable : Display → Bool
  | .table | .inlineTable => true | _ => false
/-- Internal table boxes (CSS 2.1 §17.2): outside a table they get an anonymous table. -/
def Display.isTableInternal : Display → Bool
  | .tableRowGroup | .tableHeaderGroup | .tableFooterGroup | .tableRow | .tableCell
  | .tableCaption | .tableColumn | .tableColumnGroup => true
  | _ => false
/-- Boxes that stack in block flow: blocks and tables. -/
def Display.isBlockLevel (d : Display) : Bool := d == .block || d.isTable || d == .flex || d == .grid
/-- A flex container (CSS Flexbox 1 §3): its children are flex items. -/
def Display.isFlex (d : Display) : Bool := d == .flex || d == .inlineFlex
/-- A grid container (CSS Grid 2 §5.1). -/
def Display.isGrid (d : Display) : Bool := d == .grid || d == .inlineGrid
/-- CSS Display 3 §2.7: the display of a flex or grid item is blockified. -/
def Display.blockified : Display → Display
  | .inline | .inlineBlock => .block
  | .inlineTable => .table
  | .inlineFlex => .flex
  | .inlineGrid => .grid
  | .tableRowGroup | .tableHeaderGroup | .tableFooterGroup | .tableRow | .tableCell
  | .tableCaption | .tableColumn | .tableColumnGroup => .block
  | d => d
/-- An inline-level flex or grid container: one atomic box on a line. -/
def Display.isInlineContainer (d : Display) : Bool := d == .inlineFlex || d == .inlineGrid
/-- Boxes whose contents are one block formatting context (the strut of their lines). -/
def Display.isBlockContainer (d : Display) : Bool :=
  d == .block || d == .tableCell || d == .tableCaption

/-- `vertical-align` as it applies to table cells (CSS 2.1 §17.5.3). -/
inductive VerticalAlign where | baseline | top | middle | bottom
  deriving Repr, BEq
/-- CSS Images 3 §5.5 `object-fit`: how a replaced element's content fills its box. -/
inductive ObjectFit where | fill | contain | cover | none | scaleDown
  deriving Repr, BEq
/-- CSS Text 3 §6.1 `text-align` of this profile. `start` and `end_` (`end`)
follow `direction`; `left` and `right` do not. -/
inductive TextAlign where | start | right | center | left | end_
  deriving Repr, BEq
/-- CSS Writing Modes 3 §2.1 `direction` (inherited). -/
inductive Direction where | ltr | rtl
  deriving Repr, BEq
/-- CSS Writing Modes 3 §2.2 `unicode-bidi` (not inherited): how an inline box
takes part in the Unicode Bidirectional Algorithm (§2.4.2 gives the bidi
control characters of each value). -/
inductive UnicodeBidi where | normal | embed | isolate | bidiOverride | isolateOverride | plaintext
  deriving Repr, BEq
/-- CSS Backgrounds 3 §4.2 line styles (`hidden` is `none` here: no table conflict
resolution reads it). -/
inductive BorderStyle where | none | solid | inset | outset | dotted | dashed | double | groove | ridge
  deriving Repr, BEq
/-- One value for each side of a box: top, right, bottom, left. -/
structure Sides (α : Type) where
  top : α
  right : α
  bottom : α
  left : α
  deriving Repr
def Sides.all (a : α) : Sides α := ⟨a,a,a,a⟩
/-- The sides in the order of CSS's one-to-four-value shorthands (CSS Backgrounds 3 §4). -/
def Sides.ofList : List α → Option (Sides α)
  | [a] => some ⟨a,a,a,a⟩
  | [a,b] => some ⟨a,b,a,b⟩
  | [a,b,c] => some ⟨a,b,c,b⟩
  | [a,b,c,d] => some ⟨a,b,c,d⟩
  | _ => none
/-- The side named `top`, `right`, `bottom` or `left` set to `a`. -/
def Sides.set (x : Sides α) (side : String) (a : α) : Sides α :=
  match side with
  | "top" => {x with top := a} | "right" => {x with right := a}
  | "bottom" => {x with bottom := a} | _ => {x with left := a}
def Sides.toList (x : Sides α) : List α := [x.top, x.right, x.bottom, x.left]
/-- The border paint is independent of whether its widths take up space. -/
inductive BorderColor where
  | current
  | transparent
  | solid (color : Color)
  deriving Repr

/-- Substitute the element's computed text colour when the border uses currentcolor. -/
def BorderColor.resolve (paint : BorderColor) (currentColor : Color) : Option Color :=
  match paint with
  | .current => some currentColor
  | .transparent => none
  | .solid c => some c

/-- A `linear-gradient()` background image (CSS Images 3 §3.1): the direction as an angle in
degrees (0 is up, 90 is right; `to bottom`, the default, is 180), or a corner (`to top
right`: x and y each -1, 0 or 1), whose angle depends on the box; and the colour stops, each
a colour, its opacity and its position when it has one (px, or a fraction of the line when
`percent`). -/
structure BackgroundGradient where
  angle : Float := 180
  corner : Option (Int × Int) := none
  stops : List (Color × Float × Option (Float × Bool)) := []
  deriving Repr

/-- Size of the first raster background layer (CSS Backgrounds 3 §2.9). -/
inductive BackgroundSize where
  | dimensions (width height : Length)
  | cover
  | contain
  deriving Repr

/-- An offset from the start of a background's physical positioning axis. -/
inductive BackgroundOffset where
  | length (value : Length)
  | calculation (expression : CssValues.Calc) (units : CssValues.Ctx)

instance : Repr BackgroundOffset where
  reprPrec
    | .length value, prec => reprPrec value prec
    | .calculation expr _, prec => reprPrec (CssValues.Calc.text expr) prec

structure Computed where
  display : Display := .inline
  width : Length := .auto
  height : Length := .auto
  margin : Edges := {}
  padding : Edges := {}
  color : Color := ⟨0,0,0⟩
  background : Option Color := none
  /-- `background-image: linear-gradient(...)`, painted over the colour; other images are
  not drawn. -/
  backgroundGradient : Option BackgroundGradient := none
  /-- `column-count` and `column-width` (px) of a multi-column container (CSS Multi-column
  Layout 1 §3); none is `auto`. With both `auto` the box is not a multi-column container. -/
  columnCount : Option Nat := none
  columnWidth : Option Float := none
  fontSize : Float := 16
  /-- CSS Fonts 4 §2.1: the initial value is the user agent's; as in browsers, `serif`
  (`FontFaceRule.genericOf`: drawn with the serif face when the engine holds one, else with
  its first font, as before). -/
  fontFamily : String := "serif"
  lineHeight : Float := 19.2
  lineHeightFactor : Option Float := some 1.2
  visible : Bool := true
  clipOverflow : Bool := false
  underline : Bool := false
  decorationColor : Option Color := none
  /-- Source spaces, tabs and line feeds are preserved. -/
  preformatted : Bool := false
  /-- Source line feeds are preserved while spaces and tabs collapse. -/
  preserveSegmentBreaks : Bool := false
  /-- Border widths as specified; `Computed.borderEdges` is the used width (0 with no style). -/
  borderWidth : Edges := ⟨3,3,3,3⟩
  /-- `border-*-style`, one for each side. -/
  borderStyles : Sides BorderStyle := .all .none
  /-- `border-*-color`, one for each side. -/
  borderColors : Sides BorderColor := .all .current
  /-- `border-spacing`, horizontal and vertical (inherited). -/
  borderSpacingX : Float := 0
  borderSpacingY : Float := 0
  /-- `border-collapse: collapse` (inherited). -/
  borderCollapse : Bool := false
  /-- `caption-side: bottom` (inherited). -/
  captionBottom : Bool := false
  verticalAlign : VerticalAlign := .baseline
  /-- `table-layout: fixed`. -/
  tableFixed : Bool := false
  /-- CSS 2.1 §10.4 and §10.7: `auto` is 0 for a minimum and `none` for a maximum. -/
  minWidth : Length := .auto
  maxWidth : Length := .auto
  minHeight : Length := .auto
  maxHeight : Length := .auto
  objectFit : ObjectFit := .fill
  objectPosition : Option (Length × Length) := none
  /-- `text-align` (inherited): where the lines of a block container sit. -/
  textAlign : TextAlign := .start
  /-- `letter-spacing` and `word-spacing` (inherited, CSS Text 3 §8.1, §8.2): added after each
  character, and to each word separator. `normal` is 0. A percentage is of the font size of the
  element that uses it, so it inherits as a percentage (`letterSpacingPx`). -/
  letterSpacing : Length := .px 0
  wordSpacing : Length := .px 0
  /-- `text-indent` (inherited, CSS Text 3 §8.3): the indent of the first line of a block
  container; a percentage is of the container's width. -/
  textIndent : Length := .px 0
  /-- `direction` (inherited), from CSS or the HTML `dir` attribute. -/
  direction : Direction := .ltr
  /-- `unicode-bidi` (not inherited). -/
  unicodeBidi : UnicodeBidi := .normal
  /-- `margin-left: auto` and `margin-right: auto` (CSS 2.1 §10.3.3): the used margin
  takes the room a block-level box leaves; `margin` holds 0 on such a side. -/
  autoMarginLeft : Bool := false
  autoMarginRight : Bool := false
  /-- `margin-top: auto` and `margin-bottom: auto`: read by flex and grid layout (in block
  flow they are 0, CSS 2.1 §10.6.3). -/
  autoMarginTop : Bool := false
  autoMarginBottom : Bool := false
  /-- Box alignment, gaps and `order` (`Rendering/BoxAlign.lean`): read by flex and grid. -/
  align : AlignStyle := {}
  /-- The flex container and flex item values (`Rendering/FlexStyle.lean`). -/
  flex : FlexStyle := {}
  /-- Positioning, floats and box sizing (`Rendering/BoxPosition.lean`). -/
  pos : PositionStyle := {}
  /-- The custom properties of the element (CSS Variables 1 §2; inherited): name to
  computed value. Empty on a page that declares none; an element that declares none
  shares its parent's map. -/
  vars : CssVars.Vars := {}
  /-- The grid container and grid item values (`Rendering/GridStyle.lean`). -/
  grid : GridStyle := {}
  /-- `font-weight` (inherited): 1 to 1000, 400 is `normal`. Text of 600 and up is drawn with
  the bold face the engine makes (`Rendering/FontSynthesis.lean`: one regular face is held). -/
  fontWeight : Nat := 400
  /-- The parent's `font-weight`: what `bolder` and `lighter` are relative to (CSS Fonts 4
  §2.2.1), kept beside the element's own weight, which a user agent default may have set. -/
  inheritedWeight : Nat := 400
  /-- `font-style: italic` or `oblique` (inherited): drawn with the oblique face the engine
  makes. -/
  oblique : Bool := false
  /-- The element has a `mask-image` whose image this engine does not draw (a `url()` other
  than a reference into the document; not inherited). CSS Masking 1 §7.1 counts an image
  that is not shown as a transparent black layer, which hides the element. Pages use such
  masks on empty elements whose background colour is the shape of an icon; drawn unmasked,
  that background is a filled square. So the element's own background and border are not
  painted (`Layout.decorations`); its content still is, unmasked, and its boxes stay in the
  layout. -/
  masked : Bool := false
  /-- `vertical-align: super` (1), `sub` (-1) or neither (0) of this element (not
  inherited); `rise` is the baseline shift it and its ancestors give its text. -/
  shift : Int := 0
  /-- How far the baseline of this element's text is raised, in px (inherited, summed down
  the tree: CSS 2.1 §10.8.1 `super` and `sub`, a third and a fifth of the parent's font
  size, as other browsers draw them). Only the glyphs move; the line box is not grown. -/
  rise : Float := 0
  /-- HTML §15.3.3: an element with `align=center` (and `center`) centres its block-level
  descendants, as `text-align: -webkit-center` does in other engines. Inherited as
  `text-align` is; any other `text-align` clears it. -/
  centerBlocks : Bool := false
  /-- `clip: rect(...)` with no area (CSS 2.1 §11.1.2; it applies to absolutely positioned
  boxes) and `clip-path: inset(50%)` or more: what pages write to hide text visually and keep
  it for screen readers (skip links, labels). Not inherited; `clipHidden` is. -/
  clipRectEmpty : Bool := false
  clipPathEmpty : Bool := false
  /-- The element or an ancestor is clipped to nothing: none of it is painted (`visible`
  false), and its boxes stay in the layout. Inherited, never cleared by a descendant. -/
  clipHidden : Bool := false
  /-- `background-image: url(...)` (CSS Backgrounds 3 §3.3), the first layer's URL as the page
  wrote it after the engine resolved it against its sheet (`WebDocument`); none for `none` or a
  gradient. Not inherited. -/
  backgroundImage : Option String := none
  /-- The decoded image of `backgroundImage` and its paint-table id, when the host gave its
  bytes and they decoded (`WebDocument` sets it after the cascade); `Layout.background` tiles
  it. None: only the colour (and a gradient) is painted, as before. -/
  backgroundBitmap : Option (Nat × Bitmap) := none
  /-- The natural width, height and ratio (width over height) of the background image, any of
  them missing (CSS Images 3 §5.1): an SVG image may have none. None: those of
  `backgroundBitmap`. -/
  backgroundNatural : Option (Option Float × Option Float × Option Float) := none
  backgroundSize : BackgroundSize := .dimensions .auto .auto
  backgroundRepeat : Bool × Bool := (true, true)
  backgroundPositionX : BackgroundOffset := .length (.percent 0)
  backgroundPositionY : BackgroundOffset := .length (.percent 0)
  /-- `background-clip` (CSS Backgrounds 3 §3.7): the box each layer is painted in, as
  0 border box, 1 padding box, 2 content box; one item per comma-separated value. -/
  backgroundClip : List Nat := [0]
  /-- The number of background layers: the comma-separated items of `background-image`
  (CSS Backgrounds 3 §3.1). -/
  backgroundLayers : Nat := 1
  deriving Repr
instance : Inhabited Computed := ⟨{}⟩
/-- The clip of the final layer, which the background colour uses (CSS Backgrounds 3 §3.7):
the `background-clip` list repeats to the number of layers. -/
def Computed.colorClip (s : Computed) : Nat :=
  s.backgroundClip.getD ((s.backgroundLayers - 1) % max 1 s.backgroundClip.length) 0

/-- Properties consumed by HTML style/layout, including an embedded SVG root.
The DOM-to-SVG adapter uses this same list to avoid a second interpretation. -/
def htmlProperties : List String :=
  ["display","width","height","margin","padding",
   "margin-top","margin-right","margin-bottom","margin-left",
   "padding-top","padding-right","padding-bottom","padding-left",
   "color","background","background-color","font-size","font-family",
   "line-height","visibility","overflow","text-decoration","text-decoration-line",
   "border","border-width","border-style","border-color",
   "border-spacing","border-collapse","caption-side","vertical-align","table-layout",
   "min-width","max-width","min-height","max-height","object-fit","object-position","text-align",
   "direction","unicode-bidi","background-size","background-repeat",
   "background-position","background-position-x","background-position-y","background-clip"]

/-- CSS Backgrounds 3 §4.3: the computed border width is 0 when the style is none. -/
def Computed.borderEdges (s : Computed) : Edges :=
  let w := s.borderWidth
  let b := s.borderStyles
  ⟨if b.top == .none then 0 else w.top, if b.right == .none then 0 else w.right,
   if b.bottom == .none then 0 else w.bottom, if b.left == .none then 0 else w.left⟩

/-- The style of the first side, of top, right, bottom and left, that has one; `none` when
no side has a border. -/
def Computed.borderStyle (s : Computed) : BorderStyle :=
  (s.borderStyles.toList.find? (· != .none)).getD .none
/-- Whether some side has a border style (it may still be 0 wide). -/
def Computed.hasBorder (s : Computed) : Bool := s.borderStyle != .none
/-- All four sides with the one style `st`. -/
def Computed.withBorderStyle (s : Computed) (st : BorderStyle) : Computed := {s with borderStyles := .all st}

structure Declaration where
  property : String
  value : String
  important : Bool := false
  deriving Repr
/-- Selectors Level 4 location (§8) and user action (§9) pseudo-classes. -/
inductive PseudoClass where | link | visited | anyLink | hover | active
  deriving Repr, BEq
structure Compound where
  tag : Option String := none
  id : Option String := none
  classes : List String := []
  pseudo : List PseudoClass := []
  /-- `:host` or `:host(compound)` (CSS Scoping 1 §3.2.1): it matches only the shadow host
  of the rule's shadow tree, and the other fields test that host. -/
  host : Bool := false
  deriving Repr
structure Selector where
  /-- Rightmost compound first; ancestors follow. -/
  parts : List Compound
  specificity : Nat × Nat × Nat
  /-- `::slotted(compound)` after the rightmost compound (CSS Scoping 1 §3.2.2): the
  selector matches an element assigned to a slot that `parts` matches. -/
  slotted : Option Compound := none
  /-- A selector beyond compounds and descendant combinators (child and sibling
  combinators, attribute selectors, `:not()`, `:nth-child()` and the rest of Selectors 4
  that `DOM.Selectors` reads): the whole selector, matched by `DOM.Selectors.matchComplex`.
  `parts` then holds one compound with the id, classes and type of the selector's rightmost
  compound: a necessary condition, which puts the rule in a bucket. -/
  complex : Option DOM.Selectors.Complex := none
instance : Repr Selector := ⟨fun s _ =>
  "{ parts := " ++ repr s.parts ++ ", specificity := " ++ repr s.specificity ++ ", slotted := " ++ repr s.slotted ++
    (if s.complex.isSome then ", complex" else "") ++ " }"⟩
/-- A selector that names `:visited` anywhere. Such a rule sets only colours. -/
def Selector.visitedDependent (sel : Selector) : Bool :=
  sel.parts.any (·.pseudo.contains .visited) || (sel.slotted.any (·.pseudo.contains .visited))

/-- The element state the host says (Selectors Level 4 §9.1-§9.2, HTML §4.16.3):
the element the pointer designates, the element being activated (each with its
ancestors), and the hyperlinks whose target is in the session history. -/
structure ElementState where
  hover : Option Nat := none
  active : Option Nat := none
  visited : List Nat := []
  /-- The values of running animations and transitions (`Rendering.Animation`): node,
  longhand, computed value text, and whether a transition gives it. They enter the cascade
  as declarations of their own origins (`animatedIndex`). Empty on a page that animates
  nothing. -/
  animated : List (Nat × String × String × Bool) := []
  deriving Repr, BEq, Inhabited
structure Rule where
  selectors : List Selector
  declarations : List Declaration
  /-- The shadow root whose style sheet the rule is from (CSS Scoping 1 §3.1); none for
  the document's. -/
  scope : Option Nat := none
  /-- The place of the rule's cascade layer in the layer order of its sheet (CSS Cascade 5
  §6.4, `SheetReader.rankOf`): 0 for a rule in no layer, 1 for the first layer declared. -/
  layer : Nat := 0
  /-- A declaration of the rule is a custom property or mentions `var()`: an element that
  no such rule matches (and whose `style` attribute has none) skips the substitution step
  of `computedFrom`. -/
  usesVars : Bool := false
  /-- A declaration of the rule may be for a flow-relative property (`margin-inline-start`,
  `inline-size`; `CssValues.Logical.mentions`): an element that no such rule matches
  skips the mapping to physical properties in `computedFrom`. -/
  usesLogical : Bool := false
  /-- The selectors of the rule that end in `::before` (CSS Pseudo-Elements 4 §4.1), each
  without the pseudo-element: a selector of the originating element. `selectors` has none
  of them, so the rule matches no element by them; `Generated` gives the pseudo-element
  its box and these rules. -/
  before : List Selector := []
  /-- The same for `::after`. -/
  after : List Selector := []
  /-- The same for `::first-letter` (CSS Pseudo-Elements 4 §2.3); `Generated.firstLetters`
  wraps the first letter of the originating element in an element that has these rules. -/
  firstLetter : List Selector := []
  deriving Repr

def attrValue (n : DOM.Node) (key : String) : String :=
  ((n.attrs.find? fun a => a.ns.isNone && a.lname == key).map (·.value)).getD ""
def hasAttribute (n : DOM.Node) (key : String) : Bool :=
  n.attrs.any (fun a => a.ns.isNone && a.lname == key)

private def words (s : String) : List String :=
  (s.replace "\n" " " |>.replace "\t" " " |>.replace "\r" " ").splitOn " " |>.filter (· != "")
/-- Splits `source` at white space outside quotes and parentheses, so that `rgb(0, 0, 255)`
is one value. One pass, no recursion. -/
def topWords (source : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut item := ""
  let mut depth := 0
  let mut quote : Option Char := none
  for c in source.toList do
    if let some q := quote then
      item := item.push c
      if c == q then quote := none
    else if c == '"' || c == '\'' then
      quote := some c
      item := item.push c
    else if c == '(' then
      depth := depth+1
      item := item.push c
    else if c == ')' then
      depth := depth-1
      item := item.push c
    else if (c == ' ' || c == '\t' || c == '\n' || c == '\r') && depth == 0 then
      if !item.isEmpty then out := out.push item
      item := ""
    else item := item.push c
  if !item.isEmpty then out := out.push item
  return out.toList
#guard topWords "1px  solid rgb(0, 0, 255)" == ["1px","solid","rgb(0, 0, 255)"]
private def ident (s : String) : Bool := !s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '-' || c == '_')
/-- Splits `source` at the commas outside quotes and parentheses (CSS Syntax 3 §5.3.11,
for a comma-separated list of component values). One pass, no recursion. -/
def splitTopCommas (source : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut item := ""
  let mut depth := 0
  let mut quote : Option Char := none
  for c in source.toList do
    if let some q := quote then
      item := item.push c
      if c == q then quote := none
    else if c == '"' || c == '\'' then
      quote := some c
      item := item.push c
    else if c == '(' then
      depth := depth+1
      item := item.push c
    else if c == ')' then
      depth := depth-1
      item := item.push c
    else if c == ',' && depth == 0 then
      out := out.push item
      item := ""
    else item := item.push c
  return (out.push item).toList

/-- The generic family keywords of CSS Fonts 4 §2.1 and the CSS-wide keywords, lower case: an
unquoted item spelled so is a keyword, a quoted one a family name (`familyNames`). -/
def genericFamilyKeywords : List String :=
  ["serif","sans-serif","monospace","cursive","fantasy","system-ui","ui-serif","ui-sans-serif",
    "ui-monospace","ui-rounded","math","emoji","fangsong","generic","default","initial","inherit",
    "unset","revert","revert-layer"]

/-- CSS Fonts 4 §2.1 `<family-name>#`: a quoted string, or identifiers separated by
white space (joined by one space). Generic family keywords stay as they are. A quoted
string spelled like a generic or CSS-wide keyword is a family name, not the keyword
(CSS Fonts 4 §5.1: `"monospace"` names a font called monospace), so it keeps its double
quotes and no generic-family test matches it. `none` for a list this profile can not read:
an empty item, a backslash escape, an unclosed quote, or an unquoted item that is not
identifiers. -/
def familyNames (value : String) : Option (List String) := do
  let items ← (splitTopCommas value).mapM fun item => do
    let raw := trim item
    if raw.isEmpty || raw.contains '\\' then none
    if raw.startsWith "\"" || raw.startsWith "'" then
      let q := raw.front
      if raw.length < 2 || !raw.endsWith q.toString then none
      let inner := ((raw.drop 1).dropEnd 1).toString
      if inner.contains q || inner.isEmpty then none
      if genericFamilyKeywords.contains inner.toLower then pure ("\"" ++ inner ++ "\"") else pure inner
    else
      let parts := words raw
      if parts.isEmpty || !parts.all ident then none
      pure (" ".intercalate parts)
  if items.isEmpty then none else some items

/-- The list of `familyNames` as `Computed.fontFamily` holds it: the names joined by
", ". One family stays the name itself, as before. -/
def familyValue (names : List String) : String := ", ".intercalate names

/-- The names of a `Computed.fontFamily` value. -/
def familyList (value : String) : List String :=
  ((value.splitOn ", ").map trim).filter (!·.isEmpty)

private def pseudoClass : String → Option PseudoClass
  | "link" => some .link | "visited" => some .visited | "any-link" => some .anyLink
  | "hover" => some .hover | "active" => some .active | _ => none
private def compoundBody (s : String) : Except String Compound := do
  let chunks := s.toList.foldl (fun (acc : List String) c =>
    if c == '#' || c == '.' || c == ':' then String.singleton c :: acc
    else match acc with | [] => [String.singleton c] | a::rest => (a.push c)::rest) []
  let mut out : Compound := {}
  for chunk in chunks.reverse do
    if chunk.startsWith "#" then
      let value := (chunk.drop 1).toString
      if !ident value || out.id.isSome then throw "unsupported CSS id selector"
      out := {out with id := some value}
    else if chunk.startsWith "." then
      let value := (chunk.drop 1).toString
      if !ident value then throw "unsupported CSS class selector"
      out := {out with classes := value :: out.classes}
    else if chunk.startsWith ":" then
      let some value := pseudoClass ((chunk.drop 1).toString.toLower) | throw s!"unsupported CSS pseudo-class: {chunk}"
      out := {out with pseudo := value :: out.pseudo}
    else if chunk == "*" then pure ()
    else if ident chunk then out := {out with tag := some chunk.toLower}
    else throw s!"unsupported CSS selector: {s}"
  return out
/-- A compound, or `:host` and `:host(compound)` (CSS Scoping 1 §3.2.1). -/
private def compound (s : String) : Except String Compound := do
  if s == ":host" then return {host := true}
  if s.startsWith ":host(" && s.endsWith ")" then
    let inner ← compoundBody ((s.drop 6).dropEnd 1).toString
    return {inner with host := true}
  compoundBody s
private def compoundSpecificity (n : Nat × Nat × Nat) (p : Compound) : Nat × Nat × Nat :=
  (n.1 + (if p.id.isSome then 1 else 0), n.2.1 + p.classes.length + p.pseudo.length + (if p.host then 1 else 0),
    n.2.2 + (if p.tag.isSome then 1 else 0))
/-- The specificity of a selector of `DOM.Selectors` (Selectors 4 §17): ids; classes,
attributes and pseudo-classes; types and pseudo-elements. `:is()`, `:not()`, `:has()` and the `of`
list of `:nth-child()` count as their most specific argument. The recursion is on the
nesting of the selector (at most `DOM.Selectors.maxNesting`). -/
def complexSpecificity : Nat → DOM.Selectors.Complex → Nat × Nat × Nat
  | 0, _ => (0, 0, 0)
  | fuel + 1, .mk parts =>
    let add := fun (a b : Nat × Nat × Nat) => (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
    let most := fun (l : List DOM.Selectors.Complex) =>
      (l.map (complexSpecificity fuel)).foldl (fun m x =>
        if m.1 < x.1 || (m.1 == x.1 && (m.2.1 < x.2.1 || (m.2.1 == x.2.1 && m.2.2 < x.2.2))) then x else m) (0, 0, 0)
    parts.foldl (fun acc (_, simples) =>
      simples.foldl (fun acc simple => add acc (match simple with
        | .type _ (some _) => (0, 0, 1)
        | .type _ none => (0, 0, 0)
        | .id _ => (1, 0, 0)
        | .cls _ => (0, 1, 0)
        | .attr _ _ _ _ _ _ => (0, 1, 0)
        -- a pseudo-element by name (`::before`) counts once, as its `.never` does
        | .pseudo n => if n.startsWith "::" then (0, 0, 0) else (0, 1, 0)
        | .lang _ => (0, 1, 0)
        | .nth _ _ _ of => add (0, 1, 0) (most (of.getD []))
        | .not l => most l
        | .is l => most l
        | .has l => most l
        -- only made after the specificity is taken (`resolveHas`)
        | .anchors _ => (0, 0, 0)
        | .never => (0, 0, 1))) acc) (0, 0, 0)

/-- The id, classes and type that the rightmost compound of a selector of `DOM.Selectors`
names: an element the selector matches has them (`DOM.Selectors.matchSimple`: the same
attribute, the same white space split, and a lower-case type name is the local name of an
HTML or other element alike). -/
def complexPrefilter : DOM.Selectors.Complex → Compound
  | .mk parts =>
    match parts.getLast? with
    | none => {}
    | some (_, simples) =>
      { id := simples.findSome? fun simple => match simple with
          | .id v => some v
          | _ => none
        classes := simples.filterMap fun simple => match simple with
          | .cls v => some v
          | _ => none
        tag := simples.findSome? fun simple => match simple with
          | .type .default (some n) => if n == n.toLower then some n else none
          | _ => none }

/-- A selector that the compound grammar below does not read, through `DOM.Selectors`. -/
private def complexSelector (s : String) : Except String Selector :=
  match DOM.Selectors.parse s with
  | some [c] =>
    .ok { parts := [complexPrefilter c], specificity := complexSpecificity DOM.Selectors.maxNesting c, complex := some c }
  | _ => .error s!"unsupported CSS selector: {s}"

private def compoundSelector (s : String) : Except String Selector := do
  let ws := words (trim s)
  -- `::slotted(compound)` ends the last compound (CSS Scoping 1 §3.2.2).
  let (ws, slotted) ← match ws.getLast? with
    | some w =>
      match w.splitOn "::slotted(" with
      | [before, inner] => do
        if !inner.endsWith ")" then throw "unsupported ::slotted() selector"
        let c ← compoundBody (inner.dropEnd 1).toString
        pure (ws.dropLast ++ [if before.isEmpty then "*" else before], some c)
      | _ => pure (ws, none)
    | none => pure (ws, none)
  let parts ← ws.mapM compound
  if parts.isEmpty || parts.length > 16 then throw "CSS selector exceeds supported depth"
  let specificity := (parts ++ slotted.toList).foldl compoundSpecificity (0,0,0)
  -- `::slotted` is a pseudo-element: one more in the last count.
  let specificity := if slotted.isSome then (specificity.1, specificity.2.1, specificity.2.2 + 1) else specificity
  return {parts := parts.reverse, specificity, slotted}

/-- One selector of a rule: the compound grammar of this profile (which has the dynamic
pseudo-classes and the shadow tree selectors), else all of what `DOM.Selectors` reads. -/
private def selector (s : String) : Except String Selector :=
  match compoundSelector s with
  | .ok sel => .ok sel
  | .error _ => complexSelector s

/-- A selector that ends in the pseudo-element `::before` or `::after` (`:before` and
`:after` too: CSS 2.1 §5.12.3), split: the selector of the originating element, and
whether the pseudo-element is `::before`. A pseudo-element alone, or after a combinator,
stands on `*`. `none` for any other selector. -/
def generatedSelector (s : String) : Option (String × Bool) :=
  let t := trim s
  let low := t.toLower
  let split := fun (n : Nat) (before : Bool) =>
    let base := (t.dropEnd n).toString
    let bare := match base.toList.getLast? with
      | none => true
      | some c => c == ' ' || c == '>' || c == '+' || c == '~' || c == '\t' || c == '\n'
    some ((if bare then base ++ "*" else base), before)
  if low.endsWith "::before" then split 8 true
  else if low.endsWith "::after" then split 7 false
  else if low.endsWith ":before" then split 7 true
  else if low.endsWith ":after" then split 6 false
  else none

/-- A selector that ends in `::first-letter` (or CSS 2's `:first-letter`): the selector of
its originating element. -/
def firstLetterSelector (s : String) : Option String :=
  let t := trim s
  let low := t.toLower
  let split := fun (n : Nat) =>
    let base := (t.dropEnd n).toString
    let bare := match base.toList.getLast? with
      | none => true
      | some c => c == ' ' || c == '>' || c == '+' || c == '~' || c == '\t' || c == '\n'
    some (if bare then base ++ "*" else base)
  if low.endsWith "::first-letter" then split 14
  else if low.endsWith ":first-letter" then split 13
  else none

#guard firstLetterSelector "p::first-letter" == some "p"
#guard firstLetterSelector "div:first-letter" == some "div"
#guard firstLetterSelector "::first-letter" == some "*"
#guard firstLetterSelector "p::before" == none

/-- The longhands that a side shorthand read by this profile sets, in the order of its
values: the four sides of `margin`, `padding` and `inset`, the two sides of a
flow-relative shorthand of one axis (`margin-block`, `padding-inline`, `inset-block`;
`CssValues.Logical.pair`), or the two axes of `background-position`. -/
def sidesOf (property : String) : List String :=
  if property == "margin" || property == "padding" then ["top","right","bottom","left"].map (property ++ "-" ++ ·)
  else if property == "inset" then ["top","right","bottom","left"]
  else if property == "background-position" then ["background-position-x","background-position-y"]
  else match CssValues.Logical.pair property with
    | some (a, b) => [a, b]
    | none => []

/-- The longhand declarations of a side shorthand: one to four values for four sides (CSS
Box 4 §3.2), one or two for the two sides of an axis (CSS Logical 1 §4.2). The values are
the component values: `calc(1px + 2px)` and `var(--a, 1px 2px)` are one each.
`background-position` uses the shared property grammar. -/
def expandSides (property value : String) (important : Bool) : List Declaration :=
  if property == "background-position" then
    ((CssValues.expand property value).getD []).filterMap fun (name, v) =>
      if name == property then none else some ⟨name,v,important⟩
  else
    let names := sidesOf property
    let each := match names.length, SheetReader.splitWords value with
      | 4, [a] => [a,a,a,a]
      | 4, [a,b] => [a,b,a,b]
      | 4, [a,b,c] => [a,b,c,b]
      | 4, [a,b,c,d] => [a,b,c,d]
      | 2, [a] => [a,a]
      | 2, [a,b] => [a,b]
      | _, _ => []
    (names.zip each).map fun (name, v) => ⟨name,v,important⟩

/-- The longhands of a `font` shorthand that this profile has (size, family, line height),
each with its canonical specified value; none when the value is not a `font` value or is a
system font. -/
def fontLonghands (value : String) (important : Bool) : List Declaration :=
  match CssValues.expand "font" value with
  | some ls => ["font-size", "font-family", "line-height", "font-weight", "font-style"].filterMap fun n =>
      (ls.lookup n).map fun v => (⟨n, v, important⟩ : Declaration)
  | none => []

/-- The URL of the first `url(...)` of a value (CSS Values 4 §4.5: unquoted, or a quoted
string), as written; none when the value has none or it is not closed. Case is kept. -/
def firstUrl? (value : String) : Option String := do
  let parts := value.toLower.splitOn "url("
  if parts.length < 2 then none
  let at_ := parts.head!.length
  let rest := ((value.toList.drop (at_+4)).dropWhile Char.isWhitespace)
  match rest with
  | [] => none
  | q :: more =>
    if q == '"' || q == '\'' then
      let inner := more.takeWhile (· != q)
      if inner.length == more.length then none
      some (String.ofList inner)
    else
      let inner := rest.takeWhile (· != ')')
      if inner.length == rest.length then none
      let url := String.ofList (inner.reverse.dropWhile Char.isWhitespace).reverse
      if url.isEmpty then none else some url

/-- The text inside the first `linear-gradient(` ... `)` of a value, to its matching
parenthesis; none when the value has none. -/
def gradientArgs (value : String) : Option String := do
  let lower := value.toLower
  let parts := lower.splitOn "linear-gradient("
  -- `repeating-linear-gradient` is not read: its stops repeat
  if parts.length < 2 || (parts.head!.endsWith "repeating-") then none
  let rest := (parts.drop 1).foldl (fun acc p => if acc.isEmpty then p else acc ++ "linear-gradient(" ++ p) ""
  let mut depth := 1
  let mut out := ""
  for c in rest.toList do
    if c == '(' then depth := depth+1
    if c == ')' then
      depth := depth-1
      if depth == 0 then return out
    out := out.push c
  none

/-- The declarations of this profile for declarations as written (`SheetReader.Decl`):
side shorthands as their longhands (`expandSides`), `background` as the colour, the layout
shorthands (`flex`, `flex-flow`, `gap`, `place-*`) as their longhands, so the cascade
orders them. -/
def declarationsOf (ds : List SheetReader.Decl) : List Declaration :=
  ds.foldr (fun d acc =>
    let key := d.name
    let whole : Declaration := ⟨key,d.value,d.important⟩
    -- `background` is also its colour, `background-color`, which this profile reads (`apply`,
    -- `tableDeclaration`); the shorthand stays for getComputedStyle's other longhands
    -- and its image, `none` unless it is a `linear-gradient()` (the one image drawn)
    if key == "background" then
      let image := if (gradientArgs d.value).isSome || (firstUrl? d.value).isSome then d.value else "none"
      let expanded := CssValues.expand key d.value
      let rasterPlacement : List Declaration := ["background-size", "background-repeat", "background-clip",
        "background-position-x", "background-position-y"].filterMap fun name =>
        (expanded.bind (·.lookup name)).map fun value => ⟨name,value,d.important⟩
      (⟨"background-color",d.value,d.important⟩ : Declaration) :: ⟨"background-image",image,d.important⟩ ::
        rasterPlacement ++ (whole :: acc) else
    if key == "background-position" && !CssVars.mentions d.value then
      expandSides key d.value d.important ++ acc else
    -- a side's border shorthand as that side's width, style and colour (CSS Backgrounds 3 §4.4)
    if ["border-top", "border-right", "border-bottom", "border-left"].contains key && !CssVars.mentions d.value then
      match CssValues.expand key d.value with
      | some ls =>
        -- CSS Backgrounds 3 §4.3: with style `none` or `hidden` the side's computed width is 0,
        -- whatever width the shorthand gives (its initial `medium`, 3 px, since border widths
        -- are read in every unit: `borderWidthPx`).
        let hidden := ls.any fun (n, v) => n.endsWith "-style" && ["none","hidden"].contains (trim v).toLower
        let ls := if hidden then ls.map (fun (n, v) => if n.endsWith "-width" then (n, "0") else (n, v)) else ls
        (ls.map fun (n, v) => (⟨n, v, d.important⟩ : Declaration)) ++ acc
      | none => acc
    else
    -- a side shorthand that mentions `var()` is kept whole: its sides are known only
    -- after substitution (`computedFrom`)
    if (key == "margin" || key == "padding" || key == "inset" || CssValues.Logical.mentions key) &&
        !CssVars.mentions d.value then
      match expandSides key d.value d.important with
      | [] => if key == "margin" || key == "padding" then acc else whole :: acc
      | sides => sides ++ acc
    else if key == "font" && d.value.utf8ByteSize ≤ 14 &&
        ["inherit","initial","unset","revert","revert-layer"].contains (trim d.value).toLower then
      -- a CSS-wide keyword on the shorthand is that keyword on each longhand the profile has
      ["font-size","font-family","line-height","font-weight","font-style"].map (fun name => (⟨name,d.value,d.important⟩ : Declaration)) ++ acc
    else if key == "font" && !CssVars.mentions d.value then
      -- the `font` shorthand (CSS Fonts 4 §2.8) as the longhands this profile has, and
      -- whole for getComputedStyle's other longhands (`font-weight` ...); a system font
      -- (`caption` ...) is kept whole and not read
      match fontLonghands d.value d.important with
      | [] => whole :: acc
      | ls => whole :: ls ++ acc
    else match layoutShorthand key d.value with
      | some longhands => longhands.map (fun (k,v) => (⟨k,v,d.important⟩ : Declaration)) ++ acc
      | none =>
        -- `grid`, `grid-template`, `grid-area`, `grid-row`, `grid-column`: their longhands
        -- (one that mentions `var()` is kept whole)
        match (if CssVars.mentions d.value then none else gridShorthand key d.value) with
        | some longhands => longhands.map (fun (k,v) => (⟨k,v,d.important⟩ : Declaration)) ++ acc
        | none => whole :: acc) []

/-- A declaration that is a custom property or mentions `var()`. -/
def Declaration.usesVars (d : Declaration) : Bool :=
  d.property.startsWith "--" || CssVars.mentions d.value

/-- A winning declaration with its `var()` references replaced by the element's custom
properties, as the declaration of longhand `key`: a side shorthand kept whole (`sidesOf`)
gives its side `key` after substitution. `none`: invalid at computed-value time (CSS Variables 1
§3.1), so the property is as if not declared. -/
def substituted (vars : CssVars.Vars) (key : String) (d : Declaration) : Option Declaration :=
  if !CssVars.mentions d.value then (if d.property == key then some d else none)
  else match vars.apply d.value with
    | none => none
    | some value =>
      if d.property == key then some {d with value}
      else (expandSides d.property value d.important).find? (·.property == key)

/-- A declaration with no `var()` is not changed by substitution. -/
theorem substituted_plain (vars : CssVars.Vars) (d : Declaration) (h : CssVars.mentions d.value = false) :
    substituted vars d.property d = some d := by
  simp [substituted, h]

/-- The declarations of a declaration list (a `style` attribute), split as CSS Syntax 3
says (`SheetReader.splitDecls`: a `;` in a string, a `url()` or a block ends nothing).
A declaration this profile can not read is dropped later (`applyOrKeep`); the others
stand. -/
def declarations (s : String) : Except String (List Declaration) :=
  .ok (declarationsOf (SheetReader.splitDecls s))

/-- A media query list of `@media` (Media Queries Level 4 §2) holds for the media
type `medium` when one of its queries is that type or `all`, with an optional
`only`. A query with a media feature, `not`, or `and` is not read by this profile,
and so does not hold. -/
def mediaMatches (medium queries : String) : Bool :=
  (queries.splitOn ",").any fun query =>
    let words := ((trim query).toLower.splitOn " ").filter (· != "")
    let words := if words.head? == some "only" then words.drop 1 else words
    match words with
    | [kind] => kind == medium || kind == "all"
    | _ => false

/-- The most bytes of a sheet text that are read: 8 MiB. The text of all the sheets of a
document is read as one (`WebDocument.sheetSource`), and a large site's sheets are a few
hundred kilobytes to a few megabytes. The bound keeps the cost of a hostile page's sheet
finite; what is past it is not read. -/
def maxSheetBytes : Nat := 8388608

/-- The leaves of a sheet text (`SheetReader.read`), with `@supports` conditions answered
by the property table (`CssSupports.ruleHolds`). -/
def sheetLeaves (source : String) : Array SheetReader.Leaf :=
  SheetReader.read CssSupports.ruleHolds
    (if source.utf8ByteSize ≤ maxSheetBytes then source else (source.take maxSheetBytes).toString)

/-- A style rule of a sheet with the query lists of the `@media` rules around it, innermost
first (none outside one): the rule applies when every list holds. -/
abbrev RawRule := List String × Rule

/-- The style rule of a leaf of a sheet. A rule with a selector this profile can not read
is dropped whole, as CSS drops an invalid selector list. -/
def ruleOfLeaf (leaf : SheetReader.Leaf) : Option Rule :=
  if !leaf.kind.isEmpty then none
  else
    -- each selector with the pseudo-element it ends in: `none`, `::before`, `::after`
    let texts := (splitTopCommas leaf.prelude).map fun s => match generatedSelector s with
      | some (base,before) => (base,some (if before then 0 else 1))
      | none => match firstLetterSelector s with
        | some base => (base,some 2)
        | none => (s,none)
    match texts.mapM (fun t => selector t.1) with
    | .ok all =>
      let tagged := all.zip (texts.map (·.2))
      let pick := fun (which : Option Nat) => tagged.filterMap fun (sel,w) => if w == which then some sel else none
      let declarations := declarationsOf leaf.decls
      let usesVars := declarations.any (·.usesVars)
      let usesLogical := declarations.any fun d => CssValues.Logical.mentions d.property
      some {selectors := pick none, before := pick (some 0), after := pick (some 1), firstLetter := pick (some 2),
            declarations, layer := leaf.rank, usesVars, usesLogical}
    | .error _ => none

/-- The rules of a sheet, each with the query lists of the `@media` rules it is in, before
any media environment is read: what `parseInRaw` filters. Read by `SheetReader`: rules in
`@media` (nested too), in `@supports` when the condition holds, in `@layer` (with the
layer's place in the layer order), and nested style rules; `@container`, `@scope` and
`@starting-style` blocks are skipped. -/
def parseRaw (source : String) : Except String (List RawRule) :=
  .ok ((sheetLeaves source).toList.filterMap fun leaf => (ruleOfLeaf leaf).map fun rule => (leaf.media,rule))

/-- The rules of `parseRaw` that hold in the media environment `env`: those outside an
`@media` block or in blocks whose query lists all hold. A relayout at another width needs
only this step; a host may keep what `parseRaw` read (realperf: reading Wikipedia's sheets
again was 30 ms of each relayout). -/
def parseInRaw (env : MediaQuery.Env) (raw : List RawRule) : List Rule :=
  raw.filterMap fun (queries,rule) => if queries.all (MediaQuery.applies env) then some rule else none

/-- Rules of a sheet in the media environment `env` (`MediaQuery.Env`: the media type,
and the viewport and colour scheme when the host gives them), with the media conditions
tested before a rule's selectors are read. A list that `MediaQuery` can not read does not
hold. Agrees with `parseIn` (`parseInBlocks_eq`). -/
def parseInBlocks (env : MediaQuery.Env) (source : String) : Except String (List Rule) :=
  .ok ((sheetLeaves source).toList.filterMap fun leaf =>
    if leaf.media.all (MediaQuery.applies env) then ruleOfLeaf leaf else none)

/-- Rules of a sheet in the media environment `env`: `parseRaw`, then `parseInRaw`. -/
def parseIn (env : MediaQuery.Env) (source : String) : Except String (List Rule) := do
  return parseInRaw env (← parseRaw source)

/-- Reading the rules and then filtering by the media conditions (`parseIn`, what a host
that keeps the read sheet does) gives the rules of filtering first (`parseInBlocks`). -/
theorem parseInBlocks_eq (env : MediaQuery.Env) (source : String) :
    parseIn env source = parseInBlocks env source := by
  simp only [parseIn, parseRaw, parseInRaw, parseInBlocks, bind, Except.bind, pure, Except.pure]
  congr 1
  rw [List.filterMap_filterMap]
  congr 1
  funext leaf
  cases h : ruleOfLeaf leaf <;> simp [Option.bind]

/-- Rules of a sheet for the media type `medium` ("screen" or "print") with no viewport:
an `@media` query with a width or colour-scheme feature does not hold. -/
def parseFor (medium source : String) : Except String (List Rule) := parseIn {medium} source

/-- The descriptor blocks of the `@font-face` rules of a sheet (CSS Fonts 4 §4.1), in
order: those outside `@media`, and those in `@media` blocks whose query lists hold in `env`
(by default the media type `medium` with no viewport). -/
def fontFaceBlocks (medium source : String) (env : MediaQuery.Env := {medium}) : List String :=
  (sheetLeaves source).toList.filterMap fun leaf =>
    if leaf.kind == "font-face" && leaf.media.all (MediaQuery.applies env) then some leaf.body else none

/-- `id` is `target` or one of its ancestors. The walk is bounded by the arena size. -/
def inclusiveAncestor (dom : Dom) (id : Nat) : Nat → Option Nat → Bool
  | 0, _ => false
  | _+1, none => false
  | f+1, some at_ => at_ == id || inclusiveAncestor dom id f (dom.get at_).parent

/-- HTML §4.16.3: an `a` or `area` element with an `href` attribute is a hyperlink. -/
def isHyperlink (n : DOM.Node) : Bool :=
  (n.lname == "a" || n.lname == "area") && hasAttribute n "href"

private def pseudoMatches (dom : Dom) (state : ElementState) (id : Nat) (n : DOM.Node) : PseudoClass → Bool
  | .anyLink => isHyperlink n
  | .link => isHyperlink n && !state.visited.contains id
  | .visited => isHyperlink n && state.visited.contains id
  | .hover => inclusiveAncestor dom id (dom.size+1) state.hover
  | .active => inclusiveAncestor dom id (dom.size+1) state.active

/-- The rules of a sheet on a screen. -/
def parse (source : String) : Except String (List Rule) := parseFor "screen" source

/-- What the matcher reads of an element besides its tag and pseudo-classes: its class
words and its `id` attribute. `ElemKey.read` reads them from the node; a cascade reads
them once per element (`ElemKeys`), not once per element and rule (realperf, record
docs/designissues/2026-11-09-real-site-layout-speed.md: splitting `class` for every
element and rule was 95% of a Wikipedia layout). -/
structure ElemKey where
  classes : List String := []
  id : String := ""
  deriving Inhabited
def ElemKey.read (n : DOM.Node) : ElemKey := ⟨words (attrValue n "class"), attrValue n "id"⟩
/-- The keys of each node, read from the arena when asked: the reference. -/
def readKeys (dom : Dom) : Nat → ElemKey := fun i => ElemKey.read (dom.get i)

/-- The fields of a compound on element `id`, the test of `:host` apart. -/
private def compoundFieldsK (keys : Nat → ElemKey) (dom : Dom) (state : ElementState) (id : Nat) (s : Compound) : Bool :=
  let n := dom.get id
  n.type == .element && (s.tag.map (· == n.lname)).getD true &&
    (s.id.map (· == (keys id).id)).getD true &&
    s.classes.all ((keys id).classes.contains ·) &&
    s.pseudo.all (pseudoMatches dom state id n)
/-- A compound on element `id` of a tree with no shadow scope: `:host` matches nothing. -/
private def compoundMatchesK (keys : Nat → ElemKey) (dom : Dom) (state : ElementState) (id : Nat) (s : Compound) : Bool :=
  !s.host && compoundFieldsK keys dom state id s
private def matchAncestorsK (keys : Nat → ElemKey) (dom : Dom) (state : ElementState) : Nat → Option Nat → Compound → Option Nat
  | 0, _, _ => none
  | _+1, none, _ => none
  | f+1, some id, sel =>
    if compoundMatchesK keys dom state id sel then some id else matchAncestorsK keys dom state f (dom.get id).parent sel
private def partsMatchK (keys : Nat → ElemKey) (dom : Dom) (state : ElementState) : List Compound → Option Nat → Bool
  | [], _ => true
  | sel::rest, ancestor => match matchAncestorsK keys dom state (dom.size+1) ancestor sel with
    | none => false
    | some id => partsMatchK keys dom state rest (dom.get id).parent

/-- The compounds of a selector on element `id` (keys from `keys`): the whole selector of
the compound grammar, the necessary condition of a selector with `complex`. -/
def selectorPartsMatchK (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (sel : Selector) (state : ElementState := {}) : Bool :=
  match sel.parts with
  | [] => false
  | head::rest => sel.slotted.isNone && compoundMatchesK keys dom state id head && partsMatchK keys dom state rest (dom.get id).parent

/-- The rest of a selector with `complex`: `DOM.Selectors` matches it on the tree. -/
def complexMatches (dom : Dom) (id : Nat) (sel : Selector) : Bool :=
  match sel.complex with
  | none => true
  | some c => DOM.Selectors.matchComplex dom none DOM.Selectors.matchFuel id c

/-- `selectorMatches` with the element keys `keys` (`readKeys dom` or a table of them). -/
def selectorMatchesK (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (sel : Selector) (state : ElementState := {}) : Bool :=
  selectorPartsMatchK keys dom id sel state && complexMatches dom id sel

def selectorMatches (dom : Dom) (id : Nat) (sel : Selector) (state : ElementState := {}) : Bool :=
  selectorMatchesK (readKeys dom) dom id sel state

/-- The keys of every node of an arena, read once. -/
def ElemKeys := Array ElemKey
def ElemKeys.of (dom : Dom) : ElemKeys := dom.nodes.map ElemKey.read
/-- The keys of node `i`: from the table, or read (a node outside the table). -/
def ElemKeys.get (ks : ElemKeys) (dom : Dom) (i : Nat) : ElemKey :=
  match (show Array ElemKey from ks)[i]? with
  | some k => k
  | none => ElemKey.read (dom.get i)

/-- The table gives the keys that the arena gives. -/
theorem ElemKeys.get_of (dom : Dom) : (ElemKeys.of dom).get dom = readKeys dom := by
  funext i
  unfold ElemKeys.get ElemKeys.of readKeys Dom.get
  rw [Array.getElem?_map]
  cases h : dom.nodes[i]? with
  | none => simp [Array.getD]
  | some n =>
    have hi := (Array.getElem?_eq_some_iff.mp h)
    simp [Array.getD, hi.1, hi.2]

/-- The matcher over a key table is the matcher of the arena. -/
theorem selectorMatchesK_of (dom : Dom) (id : Nat) (sel : Selector) (state : ElementState) :
    selectorMatchesK ((ElemKeys.of dom).get dom) dom id sel state = selectorMatches dom id sel state := by
  rw [ElemKeys.get_of]; rfl

/-! ### Selectors of shadow trees (CSS Scoping 1 §3)

A page with a shadow tree is laid out on its flat tree (`DOM.Dom.flat`); its selectors
match on the node tree, each rule in its own tree: a rule of the document's style sheets
matches elements of the document tree, a rule of a shadow tree's `style` elements matches
elements of that shadow tree, its `:host` the shadow host, and its `::slotted()` the
elements assigned to its slots. A page with no shadow tree never takes this path. -/

/-- The node tree of a flat-tree layout and each node's shadow root (none in the document
tree). -/
structure TreeScope where
  tree : Dom
  scopes : Array (Option Nat)
  deriving Inhabited

def TreeScope.of (tree : Dom) : TreeScope := Id.run do
  let mut scopes := Array.replicate tree.size (none : Option Nat)
  for i in [0:tree.size] do
    if tree.isShadowRoot i then
      for k in tree.treeOrder i do scopes := scopes.set! k (some i)
  return {tree, scopes}

/-- The shadow root of node `id`'s tree; none in the document tree. -/
def TreeScope.scopeOf (ts : TreeScope) (id : Nat) : Option Nat := ts.scopes.getD id none

def hostOfScope (ts : TreeScope) (scope : Option Nat) : Option Nat :=
  scope.bind fun r => (ts.tree.get r).host

/-- A compound of a rule of tree `scope`: a `:host` compound matches only the host of that
tree, and no other compound matches it (the host is featureless there). -/
private def compoundInK (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState) (scope : Option Nat) (id : Nat) (s : Compound) : Bool :=
  s.host == (hostOfScope ts scope == some id) && compoundFieldsK keys ts.tree state id s

/-- The next node up for a selector of tree `scope`: the parent, and from that tree's
shadow root its host. -/
private def upIn (ts : TreeScope) (scope : Option Nat) (n : Nat) : Option Nat :=
  match (ts.tree.get n).parent with
  | some p => some p
  | none => if scope == some n then (ts.tree.get n).host else none

private def matchAncestorsInK (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState) (scope : Option Nat) : Nat → Option Nat → Compound → Option Nat
  | 0, _, _ => none
  | _+1, none, _ => none
  | f+1, some id, sel =>
    if compoundInK keys ts state scope id sel then some id else matchAncestorsInK keys ts state scope f (upIn ts scope id) sel
private def partsInK (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState) (scope : Option Nat) : List Compound → Option Nat → Bool
  | [], _ => true
  | sel::rest, ancestor => match matchAncestorsInK keys ts state scope (ts.tree.size+1) ancestor sel with
    | none => false
    | some id => partsInK keys ts state scope rest (upIn ts scope id)

/-- The compounds of `sel`, of a rule of tree `scope`, on element `id` (keys from `keys`). -/
def selectorPartsMatchInK (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState) (scope : Option Nat) (id : Nat) (sel : Selector) : Bool :=
  match sel.parts with
  | [] => false
  | head::rest =>
    match sel.slotted with
    | none =>
      (head.host || ts.scopeOf id == scope) &&
        compoundInK keys ts state scope id head && partsInK keys ts state scope rest (upIn ts scope id)
    | some c =>
      scope.isSome && compoundFieldsK keys ts.tree state id c &&
      match ts.tree.findSlot id with
      | some sl => ts.scopeOf sl == scope && compoundInK keys ts state scope sl head &&
          partsInK keys ts state scope rest (upIn ts scope sl)
      | none => false

/-- `sel`, of a rule of tree `scope`, matches element `id` (keys from `keys`). -/
def selectorMatchesInK (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState) (scope : Option Nat) (id : Nat) (sel : Selector) : Bool :=
  selectorPartsMatchInK keys ts state scope id sel && complexMatches ts.tree id sel

/-- `selectorMatchesInK` with the arena's keys: the reference. -/
def selectorMatchesIn (ts : TreeScope) (state : ElementState) (scope : Option Nat) (id : Nat) (sel : Selector) : Bool :=
  selectorMatchesInK (readKeys ts.tree) ts state scope id sel

/-- Strict finite decimal conversion for CSS lengths; exponent syntax is outside
this first profile, and malformed declarations are refused. -/
def number (source : String) : Except String Float := do
  let s := trim source
  let negative := s.startsWith "-"
  let s := if negative || s.startsWith "+" then (s.drop 1).toString else s
  if s.length > 24 || s.isEmpty then throw "unsupported CSS number"
  let parts := s.splitOn "."
  if parts.length > 2 || parts.any (fun p => !p.toList.all Char.isDigit) || parts.all String.isEmpty then throw "invalid CSS number"
  let whole := (parts.headD "").toNat?.getD 0
  let fraction := parts[1]?.getD ""
  let scale := fraction.toList.foldl (fun (n : Float) _ => n*10) 1
  let value := Float.ofNat whole + Float.ofNat (fraction.toNat?.getD 0)/scale
  let value := if negative then -value else value
  if !value.isFinite || value.abs > 1000000 then throw "CSS number exceeds finite range"
  return value

def length (s : String) : Except String Length := do
  let s := trim s
  if s == "auto" then return .auto
  -- the sizing keywords of `width`, `height` and their limits (CSS Sizing 3 §3.2)
  if let some keyword := sizeKeyword? s.toLower then return keyword
  if s.endsWith "px" then return .px (← number ((s.dropEnd 2).toString))
  if s.endsWith "%" then return .percent ((← number ((s.dropEnd 1).toString))/100)
  if s.endsWith "vw" then return .vw ((← number ((s.dropEnd 2).toString))/100)
  if s.endsWith "vh" then return .vh ((← number ((s.dropEnd 2).toString))/100)
  if s == "0" then return .px 0
  if s.startsWith "calc(" then
    if let some l := calcLengthOfText s then return l
  throw s!"unsupported CSS length unit: {s}"
def resolve (basis : Float) : Length → Option Float
  | .auto | .vw _ | .vh _ => none | .px n => some n | .percent n => some (basis*n)
  | .calc p n => some (basis*p+n)
  | .minContent | .maxContent | .fitContent | .stretch => none
/-- The used `letter-spacing` and `word-spacing` in px: a percentage is of this element's font
size (CSS Text 4 §8.1, §8.2). -/
def Computed.letterSpacingPx (s : Computed) : Float := (resolve s.fontSize s.letterSpacing).getD 0
def Computed.wordSpacingPx (s : Computed) : Float := (resolve s.fontSize s.wordSpacing).getD 0
/-- CSS Values 4 §6.2: viewport units, computed once the viewport is known. -/
def Length.atViewport (width height : Float) : Length → Length
  | .vw n => .px (n*width).floor
  | .vh n => .px (n*height).floor
  | other => other

def BackgroundOffset.atViewport (vw vh : Float) : BackgroundOffset → BackgroundOffset
  | .length value => .length (value.atViewport vw vh)
  | .calculation expr units =>
    .calculation expr {units with viewportW := tableRat vw, viewportH := tableRat vh}

-- Percentages use the space left by the sized tile, which can be negative.
def BackgroundOffset.resolve (basis : Float) : BackgroundOffset → Option Float
  | .length value => L4Factoidal.Rendering.CSS.resolve basis value
  | .calculation expr units =>
    let reference := if basis < 0 then -(tableRat (-basis)) else tableRat basis
    let units := {units with percentageBasis := some reference}
    match CssValues.Calc.simp (some units) (CssValues.Calc.depth 64 expr + 4) expr with
    | .val result "px" => some (ratToFloat result)
    | _ => none

def BackgroundSize.atViewport (vw vh : Float) : BackgroundSize → BackgroundSize
  | .dimensions w h => .dimensions (w.atViewport vw vh) (h.atViewport vw vh)
  | .cover => .cover
  | .contain => .contain

/-- Read one axis of a position validated by the CSS property grammar. -/
private def objectPositionAxis (s : String) : Option Length :=
  match s with
  | "left" | "top" => some (.percent 0)
  | "center" => some (.percent 0.5)
  | "right" | "bottom" => some (.percent 1)
  | _ =>
    let edge := (s.splitOn " ").headD ""
    if edge == "left" || edge == "top" then
      (length (s.drop (edge.length + 1)).toString).toOption
    else if edge == "right" || edge == "bottom" then
      match (length (s.drop (edge.length + 1)).toString).toOption with
      | some (.px n) => some (.calc 1 (-n))
      | some (.percent p) => some (.percent (1-p))
      | some (.calc p n) => some (.calc (1-p) (-n))
      | _ => none
    else (length s).toOption

private def pixels (s : String) : Except String Float := do
  match ← length s with | .px n => return n | _ => throw "box edges require px in this CSS profile"
private def color (source : String) : Except String Color := do
  let s := (trim source).toLower
  let named : List (String × Color) := [("black",⟨0,0,0⟩),("white",⟨1,1,1⟩),("red",⟨1,0,0⟩),("green",⟨0,0.5019607843137255,0⟩),("lime",⟨0,1,0⟩),("blue",⟨0,0,1⟩),("yellow",⟨1,1,0⟩),("gray",⟨0.5019607843137255,0.5019607843137255,0.5019607843137255⟩),("navy",⟨0,0,0.5019607843137255⟩)]
  if let some (_,c) := named.find? (fun p => p.1 == s) then return c
  let hex := fun c => if c >= '0' && c <= '9' then some (c.toNat-48) else if c >= 'a' && c <= 'f' then some (c.toNat-87) else none
  if s.startsWith "#" then
    let some ds := ((s.drop 1).toString.toList.mapM hex) | throw "invalid CSS hex color"
    let rgb (r g b : Nat) : Color := ⟨Float.ofNat r/255,Float.ofNat g/255,Float.ofNat b/255⟩
    match ds with
    | [a,b,c] => return rgb (a*17) (b*17) (c*17)
    | [a,b,c,d,e,f] => return rgb (a*16+b) (c*16+d) (e*16+f)
    | _ => throw "unsupported CSS hex color length"
  -- CSS Color 4 §4.1: rgb() with commas or spaces, numbers or percentages.
  if s.startsWith "rgb(" && s.endsWith ")" then
    let inner := ((s.drop 4).toString.dropEnd 1).toString
    let channels := (inner.splitOn ",").flatMap (·.splitOn " ") |>.filter (· != "")
    let channel := fun (c : String) => do
      let value ← if c.endsWith "%" then (fun n => n/100) <$> number (c.dropEnd 1).toString
        else (fun n => n/255) <$> number c
      pure (max 0 (min 1 value))
    match channels with
    | [r,g,b] => return ⟨← channel r,← channel g,← channel b⟩
    | _ => throw s!"unsupported CSS color: {source}"
  throw s!"unsupported CSS color: {source}"
/-- A font size or other positive float as a rational, to a thousandth. -/
def ratOfFloat (x : Float) : Rat :=
  if x.isFinite && x > 0 then ((x * 1000).round.toUInt64.toNat : Rat) / 1000 else 0

/-- The computed value of `value` for `property` by the property table, with lengths in px
against font size `fontSize`; `none` when it is not a value of the property. -/
def tableComputed (fontSize : Float) (property value : String) : Option String :=
  (CssValues.specified property value).map fun s =>
    CssValues.computed { num := { fontSize := ratOfFloat fontSize } } property s

private def borderPaint (source : String) : Except String BorderColor :=
  match (trim source).toLower with
  | "transparent" => .ok .transparent
  | "currentcolor" => .ok .current
  | _ => .solid <$> color source

private def edgeValues (s : String) : Except String Edges := do
  let vals ← (words s).mapM pixels
  if vals.any (· < 0) then throw "negative edges outside first CSS profile"
  match vals with
  | [a] => return ⟨a,a,a,a⟩
  | [a,b] => return ⟨a,b,a,b⟩
  | [a,b,c] => return ⟨a,b,c,b⟩
  | [a,b,c,d] => return ⟨a,b,c,d⟩
  | _ => throw "CSS edge shorthand requires one to four values"
private def edgePixel (source : String) : Except String Float := do
  let value ← pixels source
  if value < 0 then throw "negative edges outside first CSS profile"
  return value
/-- One border width (CSS Backgrounds 3 §4.3 `<line-width>`): `thin`, `medium` and `thick`
are 1, 3 and 5 px; a length in any unit is read by the property table, `em` against font
size `fontSize`. Before 2026-11-22 only `px` was read, and a width such as `1in`, `6pt` or
`1em` gave the initial 3 px (846 WPT reftests set a border width so, mostly in css/CSS2). -/
def borderWidthPx (fontSize : Float) (source : String) : Except String Float :=
  snapBorderWidth <$> borderWidthRaw fontSize source
where
  /-- CSS Values 4 §"snap as a border width", at one device pixel per px: a width above 1 is
  rounded down to whole pixels, a width between 0 and 1 is rounded up to 1. -/
  snapBorderWidth (w : Float) : Float := if w <= 0 then 0 else if w < 1 then 1 else w.floor
  borderWidthRaw (fontSize : Float) (source : String) : Except String Float := do
    match edgePixel source with
    | .ok v => return v
    | .error e =>
      match (trim source).toLower with
      | "thin" => return 1
      | "medium" => return 3
      | "thick" => return 5
      | _ =>
        match tableComputed fontSize "border-top-width" source with
        | some t => if t == source then throw e else edgePixel t
        | none => throw e

/-- The `border-width` shorthand: one to four `borderWidthPx` values. -/
private def borderEdges (fontSize : Float) (s : String) : Except String Edges := do
  match ← (words s).mapM (borderWidthPx fontSize) with
  | [a] => return ⟨a,a,a,a⟩
  | [a,b] => return ⟨a,b,a,b⟩
  | [a,b,c] => return ⟨a,b,c,b⟩
  | [a,b,c,d] => return ⟨a,b,c,d⟩
  | _ => throw "CSS edge shorthand requires one to four values"
/-- One margin: its length and its percentage part, a fraction of the containing block's
width that the layout resolves (`Layout.percentEdges`). A margin may be negative. -/
private def marginParts (source : String) : Except String (Float × Float) := do
  match ← length source with
  | .px n => return (n,0)
  | .percent p => return (0,p)
  | .calc p v => return (v,p)
  | _ => throw "box edges require a length or a percentage"
/-- One padding, as `marginParts`; never negative. -/
private def paddingParts (source : String) : Except String (Float × Float) := do
  let (px,of) ← marginParts source
  if px < 0 || of < 0 then throw "negative edges outside first CSS profile"
  return (px,of)
/-- The four margins of a `margin` shorthand: a margin may be negative (CSS 2.1 §8.3). -/
private def marginValues (s : String) : Except String Edges := do
  match ← (words s).mapM pixels with
  | [a] => return ⟨a,a,a,a⟩
  | [a,b] => return ⟨a,b,a,b⟩
  | [a,b,c] => return ⟨a,b,c,b⟩
  | [a,b,c,d] => return ⟨a,b,c,d⟩
  | _ => throw "CSS edge shorthand requires one to four values"
private def borderStyle (source : String) : Except String BorderStyle :=
  match (trim source).toLower with
  | "none" | "hidden" => pure .none
  | "solid" => pure .solid
  | "inset" => pure .inset
  | "outset" => pure .outset
  | "dotted" => pure .dotted
  | "dashed" => pure .dashed
  | "double" => pure .double
  | "groove" => pure .groove
  | "ridge" => pure .ridge
  | _ => throw "unsupported CSS border style"
/-- A `min-*` or `max-*` value: `none` and `auto` are `auto` here; a negative length is
invalid (CSS 2.1 §10.4). -/
private def limit (source : String) : Except String Length := do
  let v := (trim source).toLower
  if v == "none" || v == "auto" then return .auto
  match ← length v with
  | .px n => if n < 0 then throw "negative CSS size limit" else return .px n
  | .percent n => if n < 0 then throw "negative CSS size limit" else return .percent n
  | other => return other
/-- Text split at `sep` outside parentheses, each piece trimmed, empty pieces kept. -/
private def topLevelSplit (sep : Char) (inner : String) : List String := Id.run do
  let mut depth := 0
  let mut cur := ""
  let mut out : Array String := #[]
  for c in inner.toList do
    if c == '(' then depth := depth+1
    if c == ')' then depth := depth-1
    if c == sep && depth == 0 then
      out := out.push (trim cur)
      cur := ""
    else cur := cur.push c
  return (out.push (trim cur)).toList
/-- The arguments of a function at its top level, split at commas outside parentheses. -/
private def topLevelArgs (inner : String) : List String := topLevelSplit ',' inner

/-- A colour stop's position: a percentage of the gradient line, or px. -/
private def stopPosition (p : String) : Except String (Float × Bool) :=
  if p.endsWith "%" then do pure ((← number (p.dropEnd 1).toString)/100,true)
  else do pure (← pixels p,false)

/-- CSS Images 3 §3.1.1: a `linear-gradient()` from its arguments. The direction is an
angle (`deg`, `grad`, `rad`, `turn`) or `to` a side or corner; each stop a colour with
at most two positions (px or %). Two stops at least. -/
def parseLinearGradient (args : String) : Except String BackgroundGradient := do
  let parts := topLevelArgs args
  let some first := parts.head? | throw "linear-gradient has no arguments"
  let words := (first.splitOn " ").filter (· != "")
  let angleOf := fun (w : String) => do
    let unit := fun (u : String) (k : Float) => if w.endsWith u then some ((number (w.dropEnd u.length).toString).toOption.map (·*k)) else none
    match unit "deg" 1 <|> unit "grad" 0.9 <|> unit "turn" 360 <|> unit "rad" (180/3.141592653589793) with
    | some (some a) => some a
    | _ => if w == "0" then some 0 else none
  let dir : Float × Option (Int × Int) × List String ←
    if words.head? == some "to" then
      let x : Int := if words.contains "left" then -1 else if words.contains "right" then 1 else 0
      let y : Int := if words.contains "top" then -1 else if words.contains "bottom" then 1 else 0
      if words.length < 2 || words.length > 3 || (x == 0 && y == 0) then throw "linear-gradient direction is not valid"
      if x != 0 && y != 0 then pure (180,some (x,y),parts.drop 1)
      else pure (if y == -1 then 0 else if x == 1 then 90 else if y == 1 then 180 else 270,none,parts.drop 1)
    else match words with
      | [w] => match angleOf w with
        | some a => pure (a,none,parts.drop 1)
        | none => pure (180,none,parts)
      | _ => pure (180,none,parts)
  let (angle,corner,stopParts) := dir
  let mut stops : List (Color × Float × Option (Float × Bool)) := []
  for part in stopParts do
    -- the colour is the part before its positions (a colour function keeps its spaces)
    let pieces := (topLevelSplit ' ' part).filter (· != "")
    let colourText := pieces.head?.getD ""
    let positions := pieces.drop 1
    let co : Color × Float ← if colourText.toLower == "transparent" then pure (⟨0,0,0⟩,0)
      else match color colourText with
        | .ok c => pure (c,1)
        | .error _ => throw s!"linear-gradient stop is not a colour: {colourText}"
    let (c,opacity) := co
    match positions with
    | [] => stops := stops ++ [(c,opacity,none)]
    | [p] => stops := stops ++ [(c,opacity,some (← stopPosition p))]
    | [p,q] => stops := stops ++ [(c,opacity,some (← stopPosition p)),(c,opacity,some (← stopPosition q))]
    | _ => throw "linear-gradient stop has more than two positions"
  if stops.length < 2 then throw "linear-gradient needs two colour stops"
  return {angle,corner,stops}

/-- Whether a `mask-image` or `mask` value has a layer whose image is a `url()` that is not
a reference into the document (`url(#mask)`): an image this engine does not draw. -/
def maskHides (value : String) : Bool :=
  match value.toLower.splitOn "url(" with
  | [] | [_] => false
  | _ :: rest => rest.any fun p => (p.toList.dropWhile (fun c => c == ' ' || c == '"' || c == '\'')).head? != some '#'

/-- CSS 2.1 §11.1.2: whether `clip: rect(top, right, bottom, left)` (commas or spaces; `auto`
is the box's edge) has no area: its bottom at or above its top, or its right at or left of
its left. Any other value clips nothing here. -/
def clipRectEmpty (value : String) : Bool :=
  let v := (trim value).toLower
  if !(v.startsWith "rect(" && v.endsWith ")") then false else
  let inner := String.ofList ((v.toList.drop 5).dropLast)
  let parts := ((inner.replace "," " ").splitOn " ").filter (· != "")
  match parts.map (fun p => if p == "auto" then none else (pixels p).toOption) with
  | [t, r, b, l] =>
    (match t, b with | some t, some b => b <= t | _, _ => false) ||
    (match r, l with | some r, some l => r <= l | _, _ => false)
  | _ => false

/-- CSS Masking 1 §6.1: whether `clip-path: inset(...)` with every inset at 50% or more
leaves no area. Other shapes and references clip nothing here. -/
def clipPathEmpty (value : String) : Bool :=
  let v := (trim value).toLower
  if !(v.startsWith "inset(" && v.endsWith ")") then false else
  let parts := ((String.ofList ((v.toList.drop 6).dropLast)).splitOn " ").filter (· != "")
  !parts.isEmpty && parts.all fun p => p.endsWith "%" && ((String.ofList p.toList.dropLast).toNat?.getD 0) ≥ 50

#guard clipRectEmpty "rect(0 0 0 0)"
#guard clipRectEmpty "rect(0, 0, 0, 0)"
#guard clipRectEmpty "rect(1px, 1px, 1px, 1px)"
#guard clipRectEmpty "RECT(1px 1px 1px 1px)"
#guard !clipRectEmpty "rect(0, 10px, 10px, 0)"
#guard !clipRectEmpty "rect(auto, auto, auto, auto)"
#guard !clipRectEmpty "auto"
#guard clipPathEmpty "inset(50%)"
#guard clipPathEmpty "inset(100%)"
#guard !clipPathEmpty "inset(10%)"
#guard !clipPathEmpty "circle(40%)"

#guard maskHides "url(https://example.org/icon.svg)"
#guard maskHides "url(\"data:image/svg+xml,%3Csvg%3E\") no-repeat center / 20px"
#guard maskHides "linear-gradient(red, blue), url(a.svg)"
#guard !maskHides "none"
#guard !maskHides "linear-gradient(to bottom, black, transparent)"
#guard !maskHides "url(#fade)"
#guard !maskHides "url( '#fade' )"

private def apply (s : Computed) (d : Declaration) : Except String Computed := do
  match d.property with
  | "display" =>
    -- `flow-root` is a block that is the root of a block formatting context (`pos.flowRoot`)
    -- `contents`: no box of its own (`pos.contents`; `Generated.flattenContents`); what is
    -- left of it is an inline box that is never laid out
    let s := {s with pos := {s.pos with flowRoot := d.value == "flow-root", contents := d.value == "contents"}}
    match (if d.value == "flow-root" then "block" else if d.value == "contents" then "inline" else d.value) with
    | "none" => return {s with display := .none}
    | "block" => return {s with display := .block}
    | "inline" => return {s with display := .inline}
    | "inline-block" => return {s with display := .inlineBlock}
    | "table" => return {s with display := .table}
    | "inline-table" => return {s with display := .inlineTable}
    | "table-row-group" => return {s with display := .tableRowGroup}
    | "table-header-group" => return {s with display := .tableHeaderGroup}
    | "table-footer-group" => return {s with display := .tableFooterGroup}
    | "table-row" => return {s with display := .tableRow}
    | "table-cell" => return {s with display := .tableCell}
    | "table-caption" => return {s with display := .tableCaption}
    | "table-column" => return {s with display := .tableColumn}
    | "table-column-group" => return {s with display := .tableColumnGroup}
    | "flex" => return {s with display := .flex}
    | "inline-flex" => return {s with display := .inlineFlex}
    | "grid" => return {s with display := .grid}
    | "inline-grid" => return {s with display := .inlineGrid}
    | _ => throw "unsupported CSS display"
  | "width" => return {s with width := ← length d.value}
  | "height" => return {s with height := ← length d.value}
  | "margin" => return {s with margin := ← marginValues d.value}
  | "padding" => return {s with padding := ← edgeValues d.value}
  | "margin-top" =>
    if (trim d.value).toLower == "auto" then
      return {s with margin := {s.margin with top := 0}, autoMarginTop := true, pos := s.pos.withMarginOf 0 0}
    let (px,of) ← marginParts d.value
    return {s with margin := {s.margin with top := px}, autoMarginTop := false, pos := s.pos.withMarginOf 0 of}
  | "margin-right" =>
    if (trim d.value).toLower == "auto" then
      return {s with margin := {s.margin with right := 0}, autoMarginRight := true, pos := s.pos.withMarginOf 1 0}
    let (px,of) ← marginParts d.value
    return {s with margin := {s.margin with right := px}, autoMarginRight := false, pos := s.pos.withMarginOf 1 of}
  | "margin-bottom" =>
    if (trim d.value).toLower == "auto" then
      return {s with margin := {s.margin with bottom := 0}, autoMarginBottom := true, pos := s.pos.withMarginOf 2 0}
    let (px,of) ← marginParts d.value
    return {s with margin := {s.margin with bottom := px}, autoMarginBottom := false, pos := s.pos.withMarginOf 2 of}
  | "margin-left" =>
    if (trim d.value).toLower == "auto" then
      return {s with margin := {s.margin with left := 0}, autoMarginLeft := true, pos := s.pos.withMarginOf 3 0}
    let (px,of) ← marginParts d.value
    return {s with margin := {s.margin with left := px}, autoMarginLeft := false, pos := s.pos.withMarginOf 3 of}
  | "letter-spacing" | "word-spacing" =>
    let v := (trim d.value).toLower
    -- a percentage is of the font size (CSS Text 4 §8.1, §8.2)
    -- em values become px here (`tableComputed`); a percentage stays relative
    let parsed := match length v with
      | .ok l => some l
      | .error _ => (tableComputed s.fontSize d.property v).bind fun t => (length t).toOption
    let n ← if v == "normal" then pure (Length.px 0) else match parsed with
      | some (.px n) => pure (Length.px n)
      | some (.percent f) => pure (Length.percent f)
      | some (.calc p n) => pure (Length.calc p n)
      | _ => throw "letter-spacing and word-spacing require a length"
    return if d.property == "letter-spacing" then {s with letterSpacing := n} else {s with wordSpacing := n}
  | "text-indent" =>
    match ← length d.value with
    | .px n => return {s with textIndent := .px n}
    | .percent n => return {s with textIndent := .percent n}
    | .calc p n => return {s with textIndent := .calc p n}
    | _ => throw "text-indent requires a length or a percentage"
  | "text-align" => match (trim d.value).toLower with
    | "start" => return {s with textAlign := .start, centerBlocks := false}
    | "left" => return {s with textAlign := .left, centerBlocks := false}
    | "right" => return {s with textAlign := .right, centerBlocks := false}
    | "end" => return {s with textAlign := .end_, centerBlocks := false}
    | "center" => return {s with textAlign := .center, centerBlocks := false}
    -- the value of other engines for HTML's `align=center` (HTML §15.3.3): text centred,
    -- and block-level descendants too
    | "-webkit-center" => return {s with textAlign := .center, centerBlocks := true}
    | _ => throw "unsupported CSS text-align"
  -- CSS Masking 1 §7.1: a mask layer whose image is not drawn here (a `url()` that is not a
  -- reference into the document) is a transparent black image: the element is not painted.
  -- `none` and the generated images (gradients) leave it painted, as before.
  | "mask-image" | "-webkit-mask-image" | "mask" | "-webkit-mask" =>
    return {s with masked := maskHides d.value}
  -- the visually hidden pattern (`clipHidden`, `finishEffects`)
  | "clip" => return {s with clipRectEmpty := clipRectEmpty d.value}
  | "clip-path" | "-webkit-clip-path" => return {s with clipPathEmpty := clipPathEmpty d.value}
  | "direction" => match (trim d.value).toLower with
    | "ltr" => return {s with direction := .ltr}
    | "rtl" => return {s with direction := .rtl}
    | _ => throw "unsupported CSS direction"
  | "unicode-bidi" => match (trim d.value).toLower with
    | "normal" => return {s with unicodeBidi := .normal}
    | "embed" => return {s with unicodeBidi := .embed}
    | "isolate" => return {s with unicodeBidi := .isolate}
    | "bidi-override" => return {s with unicodeBidi := .bidiOverride}
    | "isolate-override" => return {s with unicodeBidi := .isolateOverride}
    | "plaintext" => return {s with unicodeBidi := .plaintext}
    | _ => throw "unsupported CSS unicode-bidi"
  | "padding-top" =>
    let (px,of) ← paddingParts d.value
    return {s with padding := {s.padding with top := px}, pos := s.pos.withPaddingOf 0 of}
  | "padding-right" =>
    let (px,of) ← paddingParts d.value
    return {s with padding := {s.padding with right := px}, pos := s.pos.withPaddingOf 1 of}
  | "padding-bottom" =>
    let (px,of) ← paddingParts d.value
    return {s with padding := {s.padding with bottom := px}, pos := s.pos.withPaddingOf 2 of}
  | "padding-left" =>
    let (px,of) ← paddingParts d.value
    return {s with padding := {s.padding with left := px}, pos := s.pos.withPaddingOf 3 of}
  | "color" => return {s with color := ← color d.value}
  | "background" | "background-color" =>
    let bg ← if d.value == "transparent" then pure none else some <$> color d.value
    return {s with background := bg}
  | "column-count" =>
    let v := (trim d.value).toLower
    if v == "auto" then return {s with columnCount := none}
    let some n := v.toNat? | throw "column-count must be auto or a whole number"
    if n == 0 then throw "column-count must be at least 1"
    return {s with columnCount := some (min n 1000)}
  | "column-width" =>
    let v := (trim d.value).toLower
    if v == "auto" then return {s with columnWidth := none}
    match tableLength s.fontSize "column-width" v with
    | some (.px w) => if w < 0 then throw "column-width must not be negative" else return {s with columnWidth := some w}
    | _ => throw "column-width must be auto or a length"
  | "columns" =>
    -- CSS Multi-column Layout 1 §3.3: a width and a count, in either order, `auto` for either
    let words := ((trim d.value).toLower.splitOn " ").filter (· != "")
    if words.isEmpty || words.length > 2 then throw "columns takes one or two values"
    let mut count : Option Nat := none
    let mut width : Option Float := none
    for w in words do
      if w == "auto" then continue
      match w.toNat? with
      | some n => if n == 0 then throw "column-count must be at least 1" else count := some (min n 1000)
      | none => match tableLength s.fontSize "column-width" w with
        | some (.px x) => width := some (max 0 x)
        | _ => throw "columns: not a count or a length"
    return {s with columnCount := count, columnWidth := width}
  | "background-size" =>
    let parts := (CssValues.commaItems d.value).headD []
    let word := CssValues.serialize parts
    if word == "cover" then return {s with backgroundSize := .cover}
    if word == "contain" then return {s with backgroundSize := .contain}
    let read := fun cv =>
      let value := CssValues.serialize [cv]
      (length value).toOption.orElse fun _ => tableLength s.fontSize "width" value
    let size := match parts with
      | [a] => (read a).map fun x => BackgroundSize.dimensions x .auto
      | [a,b] => (read a).bind fun x => (read b).map fun y => BackgroundSize.dimensions x y
      | _ => none
    match size with
    | some v => return {s with backgroundSize := v}
    | none => throw "unsupported background size"
  | "background-clip" =>
    let clip : String → Except String Nat := fun v => match (trim v).toLower with
      | "border-box" => pure 0
      | "padding-box" => pure 1
      | "content-box" => pure 2
      | _ => throw "unsupported background clip"
    return {s with backgroundClip := ← ((trim d.value).splitOn ",").mapM clip}
  | "background-repeat" =>
    let parts := (CssValues.commaItems d.value).headD []
    let value := String.intercalate " " (parts.map fun cv => CssValues.serialize [cv])
    let axes ← match value with
      | "repeat" | "repeat repeat" => pure (true,true)
      | "repeat-x" | "repeat no-repeat" => pure (true,false)
      | "repeat-y" | "no-repeat repeat" => pure (false,true)
      | "no-repeat" | "no-repeat no-repeat" => pure (false,false)
      | _ => throw "unsupported background repeat mode"
    return {s with backgroundRepeat := axes}
  | "background-position-x" | "background-position-y" =>
    let parts := (CssValues.commaItems d.value).headD []
    let value := String.intercalate " " (parts.map fun cv => CssValues.serialize [cv])
    let some canonical := CssValues.specified d.property value | throw "invalid background position"
    let components := CssValues.stripWs (CssValues.CV.parse (CssValues.computedForm d.property canonical))
    let offset : BackgroundOffset ← match components with
      | [cv@(.fn _ _)] =>
        let some expr := CssValues.Calc.parse cv | throw "unsupported background position calculation"
        pure (.calculation expr {fontSize := tableRat s.fontSize})
      | _ =>
        let some length := tableLength s.fontSize d.property value | throw "unsupported background position"
        pure (.length length)
    if d.property == "background-position-x" then return {s with backgroundPositionX := offset}
    return {s with backgroundPositionY := offset}
  | "background-image" =>
    let s := {s with backgroundLayers := max 1 (CssValues.commaItems d.value).length}
    if ((trim d.value).toLower.splitOn ",").all (fun v => trim v == "none") then
      return {s with backgroundGradient := none, backgroundImage := none}
    -- The first layer: an image URL (`url(...)`) or a linear gradient, whichever comes first.
    let urlFirst := match firstUrl? d.value, (d.value.toLower.splitOn "url(").head?, (d.value.toLower.splitOn "gradient(").head? with
      | some _, some a, some g => decide (a.length < g.length)
      | some _, _, _ => true
      | none, _, _ => false
    if urlFirst then
      let some u := firstUrl? d.value | throw "background-image: url() not read"
      return {s with backgroundImage := some u, backgroundGradient := none}
    let some args := gradientArgs d.value | throw "background-image: only linear-gradient() and url() are drawn"
    return {s with backgroundGradient := some (← parseLinearGradient args), backgroundImage := none}
  | "font-size" =>
    let v ← pixels d.value
    if v <= 0 then throw "font-size must be positive"
    return {s with fontSize := v, lineHeight := s.lineHeightFactor.map (v*·) |>.getD s.lineHeight}
  | "line-height" =>
    if d.value == "0px" then
      return {s with lineHeight := 0, lineHeightFactor := none}
    let factor ← if d.value.endsWith "px" then pure none
      else some <$> (if d.value == "normal" then pure 1.2 else number d.value)
    let v ← match factor with | none => pixels d.value | some n => pure (n*s.fontSize)
    if v < 0 then throw "line-height must be non-negative"
    return {s with lineHeight := v, lineHeightFactor := factor}
  | "white-space" | "white-space-collapse" =>
    let nowrap := d.property != "white-space" && s.pos.nowrap
    match (trim d.value).toLower with
    | "pre-line" | "preserve-breaks" =>
      return {s with preformatted := false, preserveSegmentBreaks := true, pos := {s.pos with nowrap}}
    | "pre" | "pre-wrap" | "break-spaces" | "preserve" | "preserve-spaces" =>
      return {s with preformatted := true, preserveSegmentBreaks := false, pos := {s.pos with nowrap}}
    | "nowrap" =>
      return {s with preformatted := false, preserveSegmentBreaks := false, pos := {s.pos with nowrap := true}}
    | "normal" | "collapse" =>
      return {s with preformatted := false, preserveSegmentBreaks := false, pos := {s.pos with nowrap}}
    | _ => throw "unsupported CSS white-space"
  | "visibility" => match d.value with
    | "visible" => return {s with visible := true}
    | "hidden" | "collapse" => return {s with visible := false}
    | _ => throw "unsupported CSS visibility"
  | "overflow" =>
    if d.value == "visible" then return {s with clipOverflow := false, pos := {s.pos with scrolls := false}}
    if d.value == "hidden" || d.value == "clip" then return {s with clipOverflow := true, pos := {s.pos with scrolls := false}}
    -- A scroll container (`pos.scrolls`): nothing scrolls yet, so nothing is clipped away,
    -- but the box holds its floats and its children's margins.
    if d.value == "auto" || d.value == "scroll" || d.value == "overlay" then
      return {s with clipOverflow := false, pos := {s.pos with scrolls := true}}
    throw "unsupported CSS overflow mode"
  | "text-decoration" | "text-decoration-line" =>
    if d.value == "underline" then return {s with underline := true}
    if d.value == "none" then return {s with underline := false}
    throw "unsupported CSS text decoration"
  | "border-style" =>
    match Sides.ofList (← (topWords d.value).mapM borderStyle) with
    | some st => return {s with borderStyles := st}
    | none => throw "border-style requires one to four styles"
  | "border-top-width" => return {s with borderWidth := {s.borderWidth with top := ← borderWidthPx s.fontSize d.value}}
  | "border-right-width" => return {s with borderWidth := {s.borderWidth with right := ← borderWidthPx s.fontSize d.value}}
  | "border-bottom-width" => return {s with borderWidth := {s.borderWidth with bottom := ← borderWidthPx s.fontSize d.value}}
  | "border-left-width" => return {s with borderWidth := {s.borderWidth with left := ← borderWidthPx s.fontSize d.value}}
  | "border-top-style" | "border-right-style" | "border-bottom-style" | "border-left-style" =>
    let side := ((d.property.drop 7).takeWhile (· != '-')).toString
    return {s with borderStyles := s.borderStyles.set side (← borderStyle d.value)}
  | "border-top-color" | "border-right-color" | "border-bottom-color" | "border-left-color" =>
    let side := ((d.property.drop 7).takeWhile (· != '-')).toString
    return {s with borderColors := s.borderColors.set side (← borderPaint d.value)}
  | "border-width" => return {s with borderWidth := ← borderEdges s.fontSize d.value}
  | "border-color" =>
    match Sides.ofList (← (topWords d.value).mapM borderPaint) with
    | some c => return {s with borderColors := c}
    | none => throw "border-color requires one to four colours"
  | "border" =>
    -- CSS Backgrounds 3 §4.4: width, style and colour in any order; each omitted one is reset.
    let mut out := {s with borderWidth := ⟨3,3,3,3⟩, borderStyles := .all .none, borderColors := .all .current}
    for part in topWords d.value do
      if let .ok style := borderStyle part then out := {out with borderStyles := .all style}
      else if let .ok w := borderWidthPx s.fontSize part then out := {out with borderWidth := ⟨w,w,w,w⟩}
      else out := {out with borderColors := .all (← borderPaint part)}
    return out
  | "border-spacing" =>
    match ← (words d.value).mapM pixels with
    | [a] => if a < 0 then throw "negative border-spacing" else return {s with borderSpacingX := a, borderSpacingY := a}
    | [a,b] => if a < 0 || b < 0 then throw "negative border-spacing" else return {s with borderSpacingX := a, borderSpacingY := b}
    | _ => throw "border-spacing requires one or two lengths"
  | "border-collapse" => match d.value with
    | "collapse" => return {s with borderCollapse := true}
    | "separate" => return {s with borderCollapse := false}
    | _ => throw "unsupported CSS border-collapse"
  | "caption-side" => match d.value with
    | "top" => return {s with captionBottom := false}
    | "bottom" => return {s with captionBottom := true}
    | _ => throw "unsupported CSS caption-side"
  | "table-layout" => match d.value with
    | "fixed" => return {s with tableFixed := true}
    | "auto" => return {s with tableFixed := false}
    | _ => throw "unsupported CSS table-layout"
  | "vertical-align" => match d.value with
    | "top" | "text-top" => return {s with verticalAlign := .top, shift := 0}
    | "middle" => return {s with verticalAlign := .middle, shift := 0}
    | "bottom" | "text-bottom" => return {s with verticalAlign := .bottom, shift := 0}
    | "baseline" => return {s with verticalAlign := .baseline, shift := 0}
    | "super" => return {s with verticalAlign := .baseline, shift := 1}
    | "sub" => return {s with verticalAlign := .baseline, shift := -1}
    | _ => throw "unsupported CSS vertical-align"
  | "min-width" => return {s with minWidth := ← limit d.value}
  | "max-width" => return {s with maxWidth := ← limit d.value}
  | "min-height" => return {s with minHeight := ← limit d.value}
  | "max-height" => return {s with maxHeight := ← limit d.value}
  | "object-position" =>
    let some value := tableComputed s.fontSize d.property d.value | throw "invalid CSS object-position"
    let some (x,y) := CssValues.positionXY value | throw "unsupported CSS object-position"
    let some x := objectPositionAxis x | throw "unsupported horizontal object-position"
    let some y := objectPositionAxis y | throw "unsupported vertical object-position"
    return {s with objectPosition := some (x,y)}
  | "object-fit" => match (trim d.value).toLower with
    | "fill" => return {s with objectFit := .fill}
    | "contain" => return {s with objectFit := .contain}
    | "cover" => return {s with objectFit := .cover}
    | "none" => return {s with objectFit := .none}
    | "scale-down" => return {s with objectFit := .scaleDown}
    | _ => throw "unsupported CSS object-fit"
  | "font-weight" =>
    -- CSS Fonts 4 §2.2: a keyword or a number; `bolder` and `lighter` under the parent's weight.
    match FontSynthesis.weight? s.inheritedWeight d.value with
    | some weight => return {s with fontWeight := weight}
    | none => throw "unsupported CSS font-weight"
  | "font-style" =>
    match FontSynthesis.oblique? d.value with
    | some oblique => return {s with oblique}
    | none => throw "unsupported CSS font-style"
  | "font-family" =>
    -- CSS Fonts 4 §2.1: a list of families, tried in order (`familyNames`).
    let some names := familyNames d.value | throw s!"unsupported font family syntax: {d.value}"
    if names.any (·.contains ',') then throw s!"unsupported font family syntax: {d.value}"
    return {s with fontFamily := familyValue names}
  | property =>
    -- The values of flex and grid layout: each reader checks the property name first.
    if let some flex := s.flex.set s.fontSize property d.value then return {s with flex}
    if let some align := s.align.set s.fontSize property d.value then return {s with align}
    if let some pos := s.pos.set s.fontSize property d.value then return {s with pos}
    if let some grid := s.grid.set s.fontSize property d.value then return {s with grid}
    throw s!"unsupported CSS property: {d.property}"

/-! ### Values this profile's parsers do not read, through the property table

The parsers above read a small set of forms (`px`, `%`, nine colour names, hex and `rgb()`,
a few keywords). A declaration they refuse is given a second reading: the property table
(`CssValues`) reads the value in full CSS (every unit, `calc()` and the other math
functions, every colour syntax, keywords in any case), computes it against the element's
font size, and writes it in a form the parsers above do read. A declaration the parsers
read is never changed, so nothing that was laid out before is laid out differently; a
declaration neither reading understands is dropped as before. -/

/-- A colour as `#rrggbb` (the alpha is not kept: this profile has opaque colours), or
`transparent` when the alpha is 0; `none` when the value is not a colour with sRGB
coordinates (`currentcolor`, `lab()` ...). -/
def colorHex (value : String) : Option String :=
  match CssValues.specified "color" value with
  | none => none
  | some s =>
    let hex2 := fun (v : Rat) =>
      let n := min 255 (v.floor.toNat)
      String.ofList ((Nat.toDigits 16 (n / 16)) ++ (Nat.toDigits 16 (n % 16)))
    match CssValues.stripWs (CssValues.CV.parse (CssValues.computed {} "color" s)) with
    | [.fn name args] =>
      let nums := (CssValues.stripWs args).filterMap fun cv => match cv with
        | .tok (.num v _) => some v
        | _ => none
      match name, nums with
      | "rgb", [r, g, b] => some ("#" ++ hex2 r ++ hex2 g ++ hex2 b)
      | "rgba", [r, g, b, a] => if a == 0 then some "transparent" else some ("#" ++ hex2 r ++ hex2 g ++ hex2 b)
      | _, _ => none
    | _ => none

/-- The absolute font size keywords (CSS Fonts 4 §3.5, medium 16px) in px. -/
def fontSizeKeyword : String → Option Float
  | "xx-small" => some 9 | "x-small" => some 10 | "small" => some 13 | "medium" => some 16
  | "large" => some 18 | "x-large" => some 24 | "xx-large" => some 32 | "xxx-large" => some 48
  | _ => none

/-- A percentage text as a fraction. -/
def percentOf (text : String) : Option Float :=
  if text.endsWith "%" then (number (text.dropEnd 1).toString).toOption.map (· / 100) else none

/-- A declaration this profile's parsers refused, written as they read it, when the
property table reads it: lengths in px, colours as hex, `display` as the nearest box this
profile lays out, border styles it does not draw as `solid`. `s` is the style so far (its
font size is the element's, or the parent's for `font-size` itself). -/
def tableValue (s : Computed) (d : Declaration) : Option String :=
  let value := fun (v : String) => some v
  let px := fun (x : Float) => CssValues.fmtRat (ratOfFloat x) ++ "px"
  match d.property with
  | "color" | "border-color" => (colorHex d.value).bind fun h => if h == "transparent" then none else value h
  | "background-color" | "background" =>
    -- also the colour of a `background` shorthand (`declarations` reads it as the colour)
    match colorHex d.value with
    | some h => value h
    | none =>
      let parts := (CssValues.stripWs (CssValues.CV.parse d.value)).map fun cv => CssValues.serialize [cv]
      match parts.findSome? colorHex with
      | some h => value h
      | none =>
        -- a `background` with no colour sets the colour to its initial value (CSS
        -- Backgrounds 3 §3.10), when it is a background value at all
        -- (the colour that `declarationsOf` takes from a `background` is a `background-color`
        -- declaration with the shorthand's value)
        if (d.property == "background" || d.property == "background-color") &&
            (CssValues.specified "background-color" d.value).isNone && (CssValues.specified "background" d.value).isSome then
          value "transparent"
        else none
  | "font-size" =>
    match (tableComputed s.fontSize "font-size" d.value).map (·.toLower) with
    | none => none
    | some t =>
      match fontSizeKeyword t, percentOf t with
      | some size, _ => value (px size)
      | _, some fraction => value (px (fraction * s.fontSize))
      | _, _ =>
        if t == "larger" then value (px (s.fontSize * 1.2))
        else if t == "smaller" then value (px (s.fontSize / 1.2))
        else value t
  | "line-height" =>
    match tableComputed s.fontSize "line-height" d.value with
    | none => none
    | some t =>
      match percentOf t with
      | some fraction => value (px (fraction * s.fontSize))
      | none => value t
  | "border" =>
    match CssValues.expand "border" d.value with
    | none => none
    | some ds =>
      let width := ((ds.lookup "border-top-width").bind (tableComputed s.fontSize "border-top-width")).getD "3px"
      let style := (ds.lookup "border-top-style").getD "none"
      let style := if ["none", "hidden", "solid", "inset", "outset"].contains style then style else "solid"
      let colour := ((ds.lookup "border-top-color").bind colorHex).filter (· != "transparent")
      value (" ".intercalate ([width, style] ++ colour.toList))
  | "border-top-style" | "border-right-style" | "border-bottom-style" | "border-left-style" =>
    match (CssValues.specified d.property d.value) with
    | some w => value (if ["none", "hidden", "inset", "outset", "dotted", "dashed", "double", "groove", "ridge"].contains w then w else "solid")
    | none => none
  | "border-top-color" | "border-right-color" | "border-bottom-color" | "border-left-color" =>
    (colorHex d.value).bind fun h => if h == "transparent" then none else value h
  | "border-style" =>
    match (words d.value.toLower).head? with
    | some w => if (CssValues.specified "border-top-style" w).isSome then value (if ["none", "hidden", "inset", "outset", "dotted", "dashed", "double", "groove", "ridge"].contains w then w else "solid") else none
    | none => none
  | "border-width" =>
    (tableComputed s.fontSize "border-width" d.value).map fun t =>
      " ".intercalate ((words t).map fun w => (CssValues.lineWidthKeyword w).getD w)
  | "display" =>
    match (CssValues.specified "display" d.value) with
    | none => none
    | some t =>
      if ["flex", "grid", "flow-root", "list-item", "grid-lanes", "block ruby", "math", "block math"].contains t then value "block"
      else if ["inline-flex", "inline-grid", "inline-grid-lanes", "ruby", "inline list-item"].contains t then value "inline-block"
      else if t == "run-in" then value "inline"
      -- the legacy flexible boxes (CSS Display 3 §2.6 note: -webkit-box) as flex containers
      else if t == "-webkit-box" then value "flex"
      else if t == "-webkit-inline-box" then value "inline-flex"
      else value t
  | "text-align" =>
    match (CssValues.specified "text-align" d.value) with
    | some "justify" => value "start"
    | some "-webkit-center" => value "center"
    | some "-webkit-left" => value "left"
    | some "-webkit-right" => value "right"
    | some t => value t
    | none => none
  | "text-decoration" | "text-decoration-line" =>
    if (CssValues.specified "text-decoration" d.value).isSome then
      value (if (words d.value.toLower).contains "underline" then "underline" else "none")
    else none
  | "width" | "height" | "min-width" | "max-width" | "min-height" | "max-height"
  | "margin-top" | "margin-right" | "margin-bottom" | "margin-left"
  | "padding-top" | "padding-right" | "padding-bottom" | "padding-left" | "border-spacing"
  | "letter-spacing" | "word-spacing" | "text-indent" =>
    (tableComputed s.fontSize d.property d.value).bind value
  | _ =>
    -- a keyword property: the table's canonical form (lower case)
    (CssValues.specified d.property d.value).bind fun t => if t == d.value then none else value t

/-- The declaration with the value the table gives (`tableValue`): the same property. -/
def tableDeclaration (s : Computed) (d : Declaration) : Option Declaration :=
  (tableValue s d).map fun v => { d with value := v }

theorem tableDeclaration_property (s : Computed) (d d' : Declaration) (h : tableDeclaration s d = some d') :
    d'.property = d.property := by
  unfold tableDeclaration at h
  cases hv : tableValue s d with
  | none => simp [hv] at h
  | some v => simp only [hv, Option.map_some, Option.some.injEq] at h; rw [← h]

/-- The properties `apply` names in its own arms. -/
def ownProperties : List String :=
  ["display","width","height","margin","padding","margin-top","margin-right","margin-bottom","margin-left",
   "text-align","direction","unicode-bidi","padding-top","padding-right","padding-bottom","padding-left",
   "color","background","background-color","font-size","line-height","white-space","white-space-collapse",
   "visibility","overflow","text-decoration","text-decoration-line","border-style",
   "border-top-width","border-right-width","border-bottom-width","border-left-width",
   "border-top-style","border-right-style","border-bottom-style","border-left-style",
   "border-top-color","border-right-color","border-bottom-color","border-left-color",
   "border-width","border-color","border","border-spacing","border-collapse","caption-side","table-layout",
   "vertical-align","min-width","max-width","min-height","max-height","object-fit","object-position","font-weight","font-style",
   "font-family","letter-spacing","word-spacing","text-indent","background-image","background-clip","background-size","background-repeat",
   "background-position-x","background-position-y","column-count","column-width","columns","mask-image","mask","-webkit-mask-image","-webkit-mask","clip","clip-path","-webkit-clip-path"]

/-- A property `apply` may read: its own arms (`ownProperties`), the names the flex,
alignment, position and grid readers take, `content`, and the prefixed names those readers
map to a standard one (`-webkit-`, `-moz-`, `grid-`). For any other property `apply`
refuses every value (`apply_other`). -/
def appliedName (p : String) : Bool :=
  p.startsWith "-webkit-" || p.startsWith "-moz-" || p.startsWith "grid-" || p == "content" ||
    p == "counter-reset" || p == "counter-increment" || p == "counter-set" ||
    ownProperties.contains p || flexProperties.contains p || alignProperties.contains p ||
    positionProperties.contains p || gridProperties.contains p

/-- Kind: equivalence (the guard of a fast path). Says: `apply` refuses a declaration of a
property that `appliedName` does not name, whatever its value and the style. -/
theorem apply_other (s : Computed) (d : Declaration) (h : appliedName d.property = false) :
    ∃ e, apply s d = .error e := by
  simp only [appliedName, Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, hm⟩, hg⟩, hc⟩, hcr⟩, hci⟩, hcs⟩, hown⟩, hflex⟩, halign⟩, hpos⟩, hgrid⟩ := h
  have h1 : FlexStyle.set s.fontSize s.flex d.property d.value = none := by
    unfold FlexStyle.set
    simp only [hw, Bool.false_eq_true, if_false]
    rw [if_pos (by simpa using hflex)]
  have h2 : AlignStyle.set s.fontSize s.align d.property d.value = none := by
    unfold AlignStyle.set
    simp only [hw, hg, Bool.or_false, Bool.false_eq_true, if_false]
    rw [if_pos (by simpa using halign)]
  have h3 : PositionStyle.set s.fontSize s.pos d.property d.value = none := by
    unfold PositionStyle.set
    simp only [hw, hm, Bool.or_false, Bool.false_eq_true, if_false, hc, hcr, hci, hcs]
    rw [if_pos (by simpa using hpos)]
  have h4 : GridStyle.set s.fontSize s.grid d.property d.value = none := by
    unfold GridStyle.set
    rw [if_pos (by simpa using hgrid)]
  unfold apply
  split
  all_goals first
    | (rename_i heq; simp [heq, ownProperties] at hown; done)
    | (simp only [h1, h2, h3, h4]; exact ⟨_, rfl⟩)

/-- A value or property this profile can not use leaves the style as it was: after the
second reading through the property table (`tableDeclaration`). -/
private def applyOrKeepSlow (s : Computed) (d : Declaration) : Computed :=
  match apply s d with
  | .ok r => r
  | .error _ =>
    match tableDeclaration s d with
    | some d' => (apply s d').toOption.getD s
    | none => s

/-- `applyOrKeepSlow` with no reading at all for a property that `apply` never reads
(`appliedName`): on a documentation page with modern sheets the table's reading of such
declarations was a fifth of each layout. The same style (`applyOrKeep_eq`). -/
private def applyOrKeep (s : Computed) (d : Declaration) : Computed :=
  if appliedName d.property then applyOrKeepSlow s d else s

/-- Kind: equivalence (the fast path changes no style). -/
private theorem applyOrKeep_eq (s : Computed) (d : Declaration) : applyOrKeep s d = applyOrKeepSlow s d := by
  unfold applyOrKeep
  split
  · rfl
  · rename_i h
    have h : appliedName d.property = false := by simpa using h
    obtain ⟨e, he⟩ := apply_other s d h
    unfold applyOrKeepSlow
    rw [he]
    cases ht : tableDeclaration s d with
    | none => rfl
    | some d' =>
      have hp := tableDeclaration_property s d d' ht
      obtain ⟨e', he'⟩ := apply_other s d' (by rw [hp]; exact h)
      simp only [he']
      rfl

/-! ### CSS-wide keywords (CSS Cascade 4 §7.3) -/

/-- Style `s` with property `property` of this profile as `source` has it; none for a
property the profile does not have. The font size carries the line height with it, as a
declared font size does; `font` is the size, the family and the line height; `border` the
widths, the style and the colour. -/
def copyProperty (property : String) (source s : Computed) : Option Computed :=
  let lineHeightOf := fun (size : Float) (factor : Option Float) (height : Float) => (factor.map (size * ·)).getD height
  match property with
  | "display" => some {s with display := source.display}
  | "width" => some {s with width := source.width}
  | "height" => some {s with height := source.height}
  | "margin-top" => some {s with margin := {s.margin with top := source.margin.top}}
  | "margin-right" => some {s with margin := {s.margin with right := source.margin.right}, autoMarginRight := source.autoMarginRight}
  | "margin-bottom" => some {s with margin := {s.margin with bottom := source.margin.bottom}}
  | "margin-left" => some {s with margin := {s.margin with left := source.margin.left}, autoMarginLeft := source.autoMarginLeft}
  | "padding-top" => some {s with padding := {s.padding with top := source.padding.top}}
  | "padding-right" => some {s with padding := {s.padding with right := source.padding.right}}
  | "padding-bottom" => some {s with padding := {s.padding with bottom := source.padding.bottom}}
  | "padding-left" => some {s with padding := {s.padding with left := source.padding.left}}
  | "color" => some {s with color := source.color}
  | "background" | "background-color" => some {s with background := source.background}
  | "background-image" => some {s with backgroundGradient := source.backgroundGradient, backgroundImage := source.backgroundImage}
  | "background-size" => some {s with backgroundSize := source.backgroundSize}
  | "background-repeat" => some {s with backgroundRepeat := source.backgroundRepeat}
  | "background-clip" => some {s with backgroundClip := source.backgroundClip}
  | "background-position-x" => some {s with backgroundPositionX := source.backgroundPositionX}
  | "background-position-y" => some {s with backgroundPositionY := source.backgroundPositionY}
  | "column-count" => some {s with columnCount := source.columnCount}
  | "column-width" => some {s with columnWidth := source.columnWidth}
  | "font-size" =>
    some {s with fontSize := source.fontSize, lineHeight := lineHeightOf source.fontSize s.lineHeightFactor s.lineHeight}
  | "font-family" => some {s with fontFamily := source.fontFamily}
  | "font-weight" => some {s with fontWeight := source.fontWeight}
  | "font-style" => some {s with oblique := source.oblique}
  | "line-height" =>
    some {s with lineHeightFactor := source.lineHeightFactor,
                 lineHeight := lineHeightOf s.fontSize source.lineHeightFactor source.lineHeight}
  | "font" =>
    some {s with fontSize := source.fontSize, fontFamily := source.fontFamily, lineHeightFactor := source.lineHeightFactor,
                 lineHeight := lineHeightOf source.fontSize source.lineHeightFactor source.lineHeight,
                 fontWeight := source.fontWeight, oblique := source.oblique}
  | "visibility" => some {s with visible := source.visible}
  | "white-space" | "white-space-collapse" =>
    let nowrap := if property == "white-space" then source.pos.nowrap else s.pos.nowrap
    some {s with preformatted := source.preformatted, preserveSegmentBreaks := source.preserveSegmentBreaks,
                 pos := {s.pos with nowrap}}
  | "overflow" => some {s with clipOverflow := source.clipOverflow}
  | "text-decoration" | "text-decoration-line" => some {s with underline := source.underline}
  | "border-width" => some {s with borderWidth := source.borderWidth}
  | "border-style" => some {s with borderStyles := source.borderStyles}
  | "border-color" => some {s with borderColors := source.borderColors}
  | "border" => some {s with borderWidth := source.borderWidth, borderStyles := source.borderStyles, borderColors := source.borderColors}
  | "border-spacing" => some {s with borderSpacingX := source.borderSpacingX, borderSpacingY := source.borderSpacingY}
  | "border-collapse" => some {s with borderCollapse := source.borderCollapse}
  | "caption-side" => some {s with captionBottom := source.captionBottom}
  | "table-layout" => some {s with tableFixed := source.tableFixed}
  | "vertical-align" => some {s with verticalAlign := source.verticalAlign}
  | "min-width" => some {s with minWidth := source.minWidth}
  | "max-width" => some {s with maxWidth := source.maxWidth}
  | "min-height" => some {s with minHeight := source.minHeight}
  | "max-height" => some {s with maxHeight := source.maxHeight}
  | "object-fit" => some {s with objectFit := source.objectFit}
  | "object-position" => some {s with objectPosition := source.objectPosition}
  | "text-align" => some {s with textAlign := source.textAlign}
  | "letter-spacing" => some {s with letterSpacing := source.letterSpacing}
  | "word-spacing" => some {s with wordSpacing := source.wordSpacing}
  | "text-indent" => some {s with textIndent := source.textIndent}
  | "direction" => some {s with direction := source.direction}
  | "unicode-bidi" => some {s with unicodeBidi := source.unicodeBidi}
  | _ => none

/-- The properties of this profile that are inherited (CSS 2 and the modules that define
them). -/
def inheritedProperties : List String :=
  ["color","font","font-size","font-family","font-weight","font-style","line-height","visibility","border-spacing","border-collapse",
   "caption-side","text-align","direction","white-space","white-space-collapse"]

/-- The style a CSS-wide keyword takes the property from (CSS Cascade 4 §7.3): `inherit`
the parent's; `initial` the initial values (the fields of an empty `Computed`); `unset`
one or the other as the property is inherited or not; `revert` and `revert-layer` the
element's start, `start`: what the user agent gives the element before author rules
(this profile holds those as the start of `computedFrom`, not as declarations, and has no
user origin). None for any other value. -/
def wideSource (parent start : Computed) (d : Declaration) : Option Computed :=
  if d.value.utf8ByteSize > 14 then none
  else match (trim d.value).toLower with
    | "inherit" => some parent
    | "initial" => some {}
    | "unset" => some (if inheritedProperties.contains d.property then parent else {})
    | "revert" | "revert-layer" => some start
    | _ => none

/-- A winning declaration applied to the style so far: a CSS-wide keyword copies the
property from the style it names (`wideSource`); any other value is read by the profile
(`applyOrKeep`). A keyword on a property the profile does not have changes nothing. -/
private def applyWinner (parent start s : Computed) (d : Declaration) : Computed :=
  match wideSource parent start d with
  | some source => (copyProperty d.property source s).getD s
  | none => applyOrKeep s d

/-- The ordinary winning-declaration path sets a zero pixel line height and
clears the inherited unitless factor, preserving the remaining style fields. -/
theorem applyWinner_lineHeight_zeroPx (parent start s : Computed) :
    applyWinner parent start s ⟨"line-height", "0px", false⟩ =
      {s with lineHeight := 0, lineHeightFactor := none} := by
  have wide : wideSource parent start ⟨"line-height", "0px", false⟩ = none := by
    have spelling : (trim "0px").toLower = "0px" := by cbv
    simp [wideSource, spelling]
  have supported : appliedName "line-height" = true := by simp [appliedName, ownProperties]
  have value : apply s ⟨"line-height", "0px", false⟩ =
      .ok {s with lineHeight := 0, lineHeightFactor := none} := rfl
  simp only [applyWinner, wide, applyOrKeep, supported, if_true, applyOrKeepSlow, value]

#print axioms applyWinner_lineHeight_zeroPx

/-- `inherit` gives the parent's value. -/
theorem copyProperty_color (source s : Computed) :
    (copyProperty "color" source s).map (·.color) = some source.color := rfl

theorem copyProperty_width (source s : Computed) :
    (copyProperty "width" source s).map (·.width) = some source.width := rfl

/-- A value longer than every CSS-wide keyword is read by the profile, not copied. -/
theorem wideSource_long (parent start : Computed) (d : Declaration) (h : d.value.utf8ByteSize > 14) :
    wideSource parent start d = none := by
  simp [wideSource, h]

/-- The declarations of `rules` and of `style` attributes that this profile can not
read, each once, in source order, as "property: value (reason)". Such a declaration is
dropped (`applyOrKeep`), as CSS error handling drops it; this list says which, so that
a page that renders wrong can be grouped by the feature it lacks. It reads each
declaration alone, with no cascade: a declaration that an overriding one hides is
listed too. -/
def droppedDeclarations (dom : Dom) (rules : List Rule) : Array String := Id.run do
  let mut seen : Std.TreeMap String Unit := {}
  let mut out : Array String := #[]
  let mut all : Array Declaration := #[]
  for rule in rules do all := all ++ rule.declarations.toArray
  for n in dom.nodes do
    if n.type == .element && hasAttribute n "style" then
      if let .ok ds := declarations (attrValue n "style") then all := all ++ ds.toArray
  for d in all do
    -- custom properties and declarations with `var()` are read by the cascade, not here
    if d.usesVars then continue
    match apply {} d with
    | .ok _ => pure ()
    | .error reason =>
      let line := s!"{d.property}: {d.value} ({reason})"
      if !seen.contains line && out.size < 1024 then
        seen := seen.insert line ()
        out := out.push line
  return out

/-- Whether an ancestor of `id` is a list (`dir`, `dl`, `menu`, `ol`, `ul`): HTML §15.3.8's
`:is(dir, dl, menu, ol, ul) :is(dir, dl, menu, ol, ul) { margin-block: 0 }`. The walk takes
at most as many steps as the arena has nodes. -/
def insideList (dom : Dom) (id : Nat) : Bool := Id.run do
  let mut cur := (dom.get id).parent
  for _ in [0:dom.size] do
    match cur with
    | none => return false
    | some k =>
      let a := dom.get k
      if ["dir","dl","menu","ol","ul"].contains a.lname then return true
      cur := a.parent
  return false

/-- The user agent's margins of an element whose font size is `size` (HTML §15.3.3, §15.3.6,
§15.3.7, §15.3.8): `margin-block: 1em` on `p`, `pre`, `listing`, `xmp`, `plaintext`,
`blockquote`, `figure`, `dl` and the lists (0 for a list or `dl` in a list: `nested`);
`blockquote` and `figure` 40 px inline; headings 0.67em to 2.33em; `dd` 40 px at the start;
`body` 8 px. These margins collapse (`Layout.collapsePx`). Before 2026-11-23 each was half
of this, from the time when margins here did not collapse: a `p` and a block after it stood
8 px apart, where browsers have 16 px. -/
def startMargin (tag : String) (size : Float) (nested : Bool := false) : Edges :=
  let em := size
  if tag == "body" then ⟨8,8,8,8⟩
  else if ["p","pre","listing","xmp","plaintext"].contains tag then ⟨em,0,em,0⟩
  else if tag == "dl" then (if nested then {} else ⟨em,0,em,0⟩)
  else if ["ul","ol","dir","menu"].contains tag then (if nested then ⟨0,0,0,40⟩ else ⟨em,0,em,40⟩)
  else if tag == "blockquote" || tag == "figure" then ⟨em,40,em,40⟩
  else if tag == "dd" then ⟨0,0,0,40⟩
  else match tag with
    | "h1" => ⟨0.67*em,0,0.67*em,0⟩ | "h2" => ⟨0.83*em,0,0.83*em,0⟩ | "h3" => ⟨em,0,em,0⟩
    | "h4" => ⟨1.33*em,0,1.33*em,0⟩ | "h5" => ⟨1.67*em,0,1.67*em,0⟩ | "h6" => ⟨2.33*em,0,2.33*em,0⟩
    | _ => {}

/-- HTML §15.3.4 (the user agent's rules `pre, listing, xmp, plaintext, code, kbd, samp, tt
{ font-family: monospace }`): elements that start in the monospace family, so that with
`serif` the initial family their text keeps the face it had. Author CSS wins. -/
def monospaceTags : List String := ["pre","listing","xmp","plaintext","code","kbd","samp","tt"]

private def headingScale : String → Float
  | "h1" => 2 | "h2" => 1.5 | "h3" => 1.17 | "h5" => 0.83 | "h6" => 0.67 | _ => 1

/-- HTML §3.2.6.4 `dir=auto`: the direction of the first character of bidi class
L, R or AL in the element's text, skipping `bdi`, `script`, `style` and
`textarea` elements and elements with their own `dir`; left to right if there is
none. One pass over a work list, at most the size of the arena. -/
def autoDirection (dom : Dom) (id : Nat) : Direction := Id.run do
  let mut pending : List Nat := (dom.get id).kids.toList
  for _ in [:dom.size+1] do
    match pending with
    | [] => return .ltr
    | k::rest =>
      let n := dom.get k
      pending := rest
      if n.type == .text then
        for c in n.data.toList do
          match Unicode.bidiClassOf c with
          | .L => return .ltr
          | .R | .AL => return .rtl
          | _ => pure ()
      else if n.type == .element && !["bdi","script","style","textarea"].contains n.lname &&
          !hasAttribute n "dir" then
        pending := n.kids.toList ++ pending
  return .ltr

/-- The HTML rendering section's display for table elements (HTML §15.3.8). -/
private def tableDisplay : String → Display
  | "table" => .table | "caption" => .tableCaption | "thead" => .tableHeaderGroup
  | "tbody" => .tableRowGroup | "tfoot" => .tableFooterGroup | "tr" => .tableRow
  | "td" | "th" => .tableCell | "col" => .tableColumn | "colgroup" => .tableColumnGroup
  | _ => .inline

/-- A dimension value (`HTML.Dimension`) as a length of this profile: px, or a percentage
as a fraction. -/
def dimLength (d : HTML.Dimension.Dim) : Length :=
  match d.kind with
  | .percentage => .percent (d.toFloat / 100)
  | .length => .px d.toFloat

/-- An attribute that "maps to the dimension property" (HTML §15.2): the rules for parsing
dimension values (§2.3.4.4), in this profile's lengths. -/
def dimensionAttribute (value : String) : Option Length := (HTML.Dimension.parse value).map dimLength

/-- An attribute that "maps to the dimension property (ignoring zero)": zero is no hint. -/
def nonzeroDimensionAttribute (value : String) : Option Length :=
  (HTML.Dimension.parseNonzero value).map dimLength

/-- An attribute that "maps to the pixel length property": a non-negative integer, in px. -/
def pixelLengthAttribute (value : String) : Option Float :=
  (HTML.Dimension.parseNonNegative value).map Float.ofNat

/-- The nearest table element above a cell, within three levels (row, row group). -/
private def tableAncestor (dom : Dom) (id : Nat) : Option DOM.Node := Id.run do
  let mut cursor := (dom.get id).parent
  for _ in [0:3] do
    match cursor with
    | none => return none
    | some p =>
      if (dom.get p).lname == "table" then return some (dom.get p)
      cursor := (dom.get p).parent
  return none

/-- Presentational hints and the user agent table rules of HTML §15.3.8 and §15.3.10:
`table { border-spacing: 2px }`, `td, th { padding: 1px }`, the `cellspacing`,
`cellpadding`, `width`, `height`, `bgcolor` and `valign` attributes, and the
`vertical-align: middle` of rows and row groups that cells inherit. Author CSS
overrides them all, as it does presentation attributes. -/
private def tableHints (dom : Dom) (id : Nat) (s parent : Computed) : Computed := Id.run do
  let n := dom.get id
  let mut s := s
  let tag := n.lname
  if !["table","caption","thead","tbody","tfoot","tr","td","th","col","colgroup"].contains tag then return s
  if tag == "table" then
    let spacing := (dimensionAttribute (attrValue n "cellspacing")).bind (resolve 0)
    let v := spacing.getD 2
    s := { s with
      borderSpacingX := v, borderSpacingY := v, borderCollapse := false, captionBottom := false
      pos := {s.pos with borderBox := true} }
  if ["thead","tbody","tfoot","tr"].contains tag then s := {s with verticalAlign := .middle}
  if tag == "td" || tag == "th" then
    let pad := ((tableAncestor dom id).bind fun t => (dimensionAttribute (attrValue t "cellpadding")).bind (resolve 0)).getD 1
    s := {s with padding := ⟨pad,pad,pad,pad⟩, verticalAlign := parent.verticalAlign}
  -- HTML §15.3.10: `table` width, `td`/`th` width and height ignore zero; `col` width,
  -- `table` and `tr` height map as they are.
  let widthHint := if ["table","td","th"].contains tag then nonzeroDimensionAttribute (attrValue n "width")
    else if tag == "col" then dimensionAttribute (attrValue n "width") else none
  if let some w := widthHint then s := {s with width := w}
  let heightHint := if ["td","th"].contains tag then nonzeroDimensionAttribute (attrValue n "height")
    else if ["table","tr"].contains tag then dimensionAttribute (attrValue n "height") else none
  if let some h := heightHint then s := {s with height := h}
  if ["table","thead","tbody","tfoot","tr","td","th"].contains tag then
    let bg := attrValue n "bgcolor"
    if !bg.isEmpty then if let .ok c := color bg then s := {s with background := some c}
  -- HTML §15.3.10: a `table`'s `bordercolor` maps to the four `border-*-color` properties
  if tag == "table" then
    let bc := attrValue n "bordercolor"
    if !bc.isEmpty then if let .ok c := color bc then s := {s with borderColors := .all (.solid c)}
  if ["tr","td","th","thead","tbody","tfoot"].contains tag then
    match (attrValue n "valign").toLower with
    | "top" => s := {s with verticalAlign := .top}
    | "middle" => s := {s with verticalAlign := .middle}
    | "bottom" => s := {s with verticalAlign := .bottom}
    | "baseline" => s := {s with verticalAlign := .baseline}
    | _ => pure ()
  return s

/-- A margin hint as its pixels and its percentage part (`marginParts`'s form). -/
def hintEdge : Option Length → Option (Float × Float)
  | some (.px v) => some (v, 0)
  | some (.percent p) => some (0, p)
  | _ => none

/-- HTML §15.4.3 and §15.3.13, §15.5.15: the `width` and `height` attributes of `img`,
`video`, `canvas`, `iframe`, `embed`, `object`, `marquee` and an image button map to the
`width` and `height` properties; `hr` width too. `hspace` and `vspace` of `img`, `embed`,
`object`, `marquee` and an image button map to the horizontal and vertical margins; the
`border` of `img`, `object` and an image button to the border widths, with a solid border.
All below author CSS. A percentage height resolves against a definite containing height
(`Fragment.percentHeights`) and is read as `auto` otherwise. -/
def replacedHints (n : DOM.Node) (s : Computed) : Computed := Id.run do
  let tag := n.lname
  let imageInput := tag == "input" && (attrValue n "type").toLower == "image"
  let sized := imageInput || ["img","video","canvas","iframe","embed","object","marquee"].contains tag
  if !sized && tag != "hr" then return s
  -- HTML §15.4.1: the video box contains its poster at its intrinsic ratio.
  let mut s := if tag == "video" then {s with objectFit := .contain} else s
  if let some w := dimensionAttribute (attrValue n "width") then s := {s with width := w}
  if sized then
    if let some h := dimensionAttribute (attrValue n "height") then s := {s with height := h}
  if imageInput || ["img","embed","object","marquee"].contains tag then
    -- a dimension: pixels, or a percentage of the containing block's width (`marginOf`)
    if let some (h, ho) := hintEdge (dimensionAttribute (attrValue n "hspace")) then
      s := {s with margin := {s.margin with left := h, right := h}, pos := (s.pos.withMarginOf 1 ho).withMarginOf 3 ho}
    if let some (v, vo) := hintEdge (dimensionAttribute (attrValue n "vspace")) then
      s := {s with margin := {s.margin with top := v, bottom := v}, pos := (s.pos.withMarginOf 0 vo).withMarginOf 2 vo}
  if imageInput || tag == "img" || tag == "object" then
    if let some b := pixelLengthAttribute (attrValue n "border") then
      s := {s with borderWidth := ⟨b,b,b,b⟩, borderStyles := .all .solid}
  return s

/-- HTML §15.4.3: an `img` in a `picture` takes its `width` and `height` hints from the
`source` element its image comes from (here: the first earlier `source` sibling with a
`srcset` and no `media` or `type`), when that source has them. -/
def sourceDimensionHints (dom : Dom) (id : Nat) (s : Computed) : Computed := Id.run do
  let n := dom.get id
  if n.lname != "img" then return s
  let some p := n.parent | return s
  if (dom.get p).lname != "picture" then return s
  let before := (dom.get p).kids.toList.takeWhile (· != id)
  match before.find? (fun k => let c := dom.get k
      c.type == .element && c.lname == "source" && hasAttribute c "srcset" && !hasAttribute c "media" && !hasAttribute c "type") with
  | none => return s
  | some k =>
    let src := dom.get k
    let mut s := s
    if let some w := dimensionAttribute (attrValue src "width") then s := {s with width := w}
    if let some h := dimensionAttribute (attrValue src "height") then s := {s with height := h}
    return s

/-- HTML §15.3.3: the margins of `body` from its `marginheight`, `topmargin`, `marginwidth`
and `leftmargin` attributes (pixel lengths; `marginheight` before `topmargin`, `marginwidth`
before `leftmargin`); `rightmargin` and `bottommargin` are not read in standards mode. -/
def bodyMarginHints (n : DOM.Node) (s : Computed) : Computed := Id.run do
  if n.lname != "body" then return s
  let first := fun (names : List String) => names.findSome? fun a => pixelLengthAttribute (attrValue n a)
  let mut m := s.margin
  if let some v := first ["marginheight", "topmargin"] then m := {m with top := v}
  if let some v := first ["marginheight"] then m := {m with bottom := v}
  if let some v := first ["marginwidth", "leftmargin"] then m := {m with left := v}
  if let some v := first ["marginwidth"] then m := {m with right := v}
  return {s with margin := m}

/-- The `align` attribute value `a` (trimmed, lower case) of an HTML element named `tag`
(HTML §15.3.3, §15.3.10): `div`, `caption`, `thead`, `tbody`, `tfoot`, `tr`, `td` and `th`
align their text and, for `center` and `middle`, centre their block-level descendants
(`centerBlocks`, the `-webkit-center` of other engines); `p` and `h1` to `h6` align their
text only; a `table` with `align=center` has auto inline margins. -/
def alignOf (tag a : String) (s : Computed) : Computed :=
  if a == "" then s
  else if ["div","caption","thead","tbody","tfoot","tr","td","th"].contains tag then
    if a == "left" then {s with textAlign := .left, centerBlocks := false}
    else if a == "right" then {s with textAlign := .right, centerBlocks := false}
    else if a == "center" || a == "middle" then {s with textAlign := .center, centerBlocks := true}
    else if a == "justify" then {s with textAlign := .start, centerBlocks := false}
    else s
  else if ["p","h1","h2","h3","h4","h5","h6"].contains tag then
    if a == "left" then {s with textAlign := .left, centerBlocks := false}
    else if a == "right" then {s with textAlign := .right, centerBlocks := false}
    else if a == "center" then {s with textAlign := .center, centerBlocks := false}
    else if a == "justify" then {s with textAlign := .start, centerBlocks := false}
    else s
  else if tag == "table" && a == "center" then {s with autoMarginLeft := true, autoMarginRight := true}
  else s

/-- The `align` attribute of `n`, trimmed and in lower case. -/
def alignValue (n : DOM.Node) : String := (attrValue n "align").trimAscii.toString.toLower

/-- Presentational hints of alignment, below author CSS (an author `text-align` or margin
wins): a block-level child of a parent that centres its blocks starts with auto inline
margins; the `center` element centres its text and its blocks (the user agent's
`center { text-align: -webkit-center }` of other engines); then the `align` attribute
(`alignOf`). A `table` under such a parent is centred and starts its own text at the
start: the legacy markup that centres blocks is that of pages in quirks mode, where other
engines reset `text-align` on tables (their quirks sheet's `table { text-align: start }`),
and this engine does not know the document's mode. An element outside the HTML namespace,
and any other node, is unchanged. -/
def alignHints (n : DOM.Node) (s parent : Computed) : Computed :=
  if n.type != .element || !(n.ns == some DOM.htmlNS || n.ns.isNone) then s else
  let s := if parent.centerBlocks && s.display != .inline && s.display != .none then
    {s with autoMarginLeft := true, autoMarginRight := true} else s
  let s := if parent.centerBlocks && n.lname == "table" then {s with textAlign := .start, centerBlocks := false} else s
  if n.lname == "center" then {s with textAlign := .center, centerBlocks := true}
  -- a `th` with no `align` is centred (the user agent's `th { text-align: -internal-center }`)
  else if n.lname == "th" && !hasAttribute n "align" then {s with textAlign := .center}
  else alignOf n.lname (alignValue n) s

/-- Kind: property. Says: an empty `align` value changes no style. -/
theorem alignOf_empty (tag : String) (s : Computed) : alignOf tag "" s = s := by
  simp [alignOf]

/-- Kind: property. Says: with no `align` attribute (or an empty one), a parent that does
not centre its blocks, and an element other than `center` and `th`, the hints change nothing. Does
not say: what an author rule does after them. -/
theorem alignHints_plain (n : DOM.Node) (s parent : Computed) (hp : parent.centerBlocks = false)
    (hc : n.lname ≠ "center") (ht : n.lname ≠ "th") (ha : alignValue n = "") :
    alignHints n s parent = s := by
  simp [alignHints, hp, hc, ht, ha, alignOf_empty]

/-- Whether the element itself is clipped to nothing: `clip` with no area on an absolutely
positioned box (CSS 2.1 §11.1.2 applies `clip` to those only), or `clip-path` with no area. -/
def Computed.clippedAway (s : Computed) : Bool := (s.clipRectEmpty && s.pos.isAbsolute) || s.clipPathEmpty

/-- After the cascade of an element: its text is raised by its own `super` (a third of the
parent's font size, CSS 2.1 §10.8.1, as other engines draw it) or lowered by its own `sub`
(a fifth), over what its ancestors raise; and when it or an ancestor is clipped to nothing
(`clippedAway`, the visually hidden pattern of skip links and screen reader text) it is
`clipHidden` and not painted, whatever its own `visibility`. -/
def finishEffects (parent s : Computed) : Computed :=
  -- Absolute and fixed boxes are out of flow. Their own vertical-align does not
  -- move their text relative to the box (CSS 2.2 §10.8.1).
  let own : Float := if s.pos.isAbsolute then 0
    else if s.shift == 1 then parent.fontSize/3 else if s.shift == -1 then -(parent.fontSize/5) else 0
  let hidden := parent.clipHidden || s.clippedAway
  {s with rise := parent.rise + own, clipHidden := hidden, visible := s.visible && !hidden}

/-- Kind: property (pages that hide nothing pay nothing). Says: with no clip to nothing on
the element or above it, its visibility is its own. -/
theorem finishEffects_visible (parent s : Computed) (hp : parent.clipHidden = false) (hs : s.clippedAway = false) :
    (finishEffects parent s).visible = s.visible := by
  simp [finishEffects, hp, hs]

/-- Kind: property. Says: everything under an element clipped to nothing is not painted,
whatever its own declarations (the text of a skip link stays hidden). Does not say:
anything about layout, which is unchanged. -/
theorem finishEffects_hidden_parent (parent s : Computed) (hp : parent.clipHidden = true) :
    (finishEffects parent s).clipHidden = true ∧ (finishEffects parent s).visible = false := by
  simp [finishEffects, hp]

/-- Kind: property. Says: an element that is neither `sub` nor `super` raises its text as
much as its parent does. Does not say: where the line box is (it is not grown). -/
theorem finishEffects_rise_plain (parent s : Computed) (h : s.shift = 0) :
    (finishEffects parent s).rise = parent.rise + 0 := by
  simp [finishEffects, h]

/-- A positioned element's own vertical alignment does not add to its baseline shift. -/
theorem finishEffects_rise_positioned (parent s : Computed) (h : s.pos.isAbsolute = true) :
    (finishEffects parent s).rise = parent.rise + 0 := by
  simp [finishEffects, h]

/-- Kind: property. Says: `finishEffects` keeps the display and the box sizes of the
cascade: it changes no layout. -/
theorem finishEffects_layout (parent s : Computed) :
    (finishEffects parent s).display = s.display ∧ (finishEffects parent s).width = s.width ∧
      (finishEffects parent s).height = s.height ∧ (finishEffects parent s).margin = s.margin := by
  simp [finishEffects]

/-- The properties that presentational hints changed from `before` to `after`: those the
cascade takes from no UA rule. -/
def hintedProperties (before after : Computed) : List String :=
  (if after.width.same before.width then [] else ["width"]) ++
  (if after.height.same before.height then [] else ["height"]) ++
  (if after.margin.top == before.margin.top then [] else ["margin-top"]) ++
  (if after.margin.right == before.margin.right then [] else ["margin-right"]) ++
  (if after.margin.bottom == before.margin.bottom then [] else ["margin-bottom"]) ++
  (if after.margin.left == before.margin.left then [] else ["margin-left"]) ++
  (if after.pos.marginOf == before.pos.marginOf then [] else ["margin-top","margin-right","margin-bottom","margin-left"]) ++
  -- the `border` of an image button, `img` or `object` (HTML §15.4.3): the widths and the
  -- solid style it sets are above the user agent's `input` border
  (if after.borderStyle == before.borderStyle && after.borderWidth.top == before.borderWidth.top then [] else
    ["border","border-width","border-style","border-top-width","border-right-width","border-bottom-width",
     "border-left-width","border-top-style","border-right-style","border-bottom-style","border-left-style"])

/-- A hint that sets no width leaves the UA's `width` rules in force. -/
theorem hintedProperties_width (before after : Computed) (h : after.width.same before.width = true) :
    "width" ∉ hintedProperties before after := by
  simp [hintedProperties, h]

/-- HTML §15.3.3: the `body` of a document whose navigable's container is a `frame` or an
`iframe` takes its margins from the container's `marginheight` and `marginwidth` attributes
(pixel lengths), which win over the body's own attributes. -/
def containerMarginHints (marginwidth marginheight : String) (s : Computed) : Computed :=
  let m := s.margin
  let m := match pixelLengthAttribute marginheight with
    | some v => {m with top := v, bottom := v}
    | none => m
  let m := match pixelLengthAttribute marginwidth with
    | some v => {m with left := v, right := v}
    | none => m
  {s with margin := m}

/-- A container with neither attribute changes nothing. -/
theorem containerMarginHints_blank (s : Computed) : containerMarginHints "" "" s = s := by
  have h : HTML.Dimension.parseNonNegative "" = none := by decide
  simp [containerMarginHints, pixelLengthAttribute, h]

/-- A valid `marginwidth` sets both horizontal margins. -/
theorem containerMarginHints_width (mw mh : String) (s : Computed) (v : Float)
    (h : pixelLengthAttribute mw = some v) :
    (containerMarginHints mw mh s).margin.left = v ∧ (containerMarginHints mw mh s).margin.right = v := by
  simp [containerMarginHints, h]

/-- The order of cascade keys: lists of numbers, lexicographically; a list is not above
one it starts. -/
def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _::_, [] => false
  | a::as, b::bs => if a == b then lexLE as bs else a < b

theorem lexLE_refl (a : List Nat) : lexLE a a = true := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [lexLE, ih]

/-- Any two keys are comparable: the cascade always has a winner. -/
theorem lexLE_total (a b : List Nat) : lexLE a b = true ∨ lexLE b a = true := by
  induction a generalizing b with
  | nil => exact .inl rfl
  | cons x xs ih =>
    cases b with
    | nil => exact .inr rfl
    | cons y ys =>
      simp only [lexLE]
      by_cases hxy : x = y
      · subst hxy
        simpa using ih ys
      · have hyx : ¬ y = x := fun h => hxy h.symm
        simp only [beq_iff_eq, hxy, hyx, if_false, decide_eq_true_eq]
        omega

theorem lexLE_trans (a b c : List Nat) : lexLE a b = true → lexLE b c = true → lexLE a c = true := by
  induction a generalizing b c with
  | nil => intros; rfl
  | cons x xs ih =>
    cases b with
    | nil => simp [lexLE]
    | cons y ys =>
      cases c with
      | nil => simp [lexLE]
      | cons z zs =>
        simp only [lexLE]
        by_cases hxy : x = y
        · subst hxy
          by_cases hxz : x = z
          · subst hxz
            simpa using ih ys zs
          · simp [hxz]
        · by_cases hyz : y = z
          · subst hyz
            simp only [beq_iff_eq, hxy, if_false, beq_self_eq_true, if_true, decide_eq_true_eq]
            intro h _
            exact h
          · by_cases hxz : x = z
            · subst hxz
              simp only [beq_iff_eq, hxy, hyz, if_false, decide_eq_true_eq]
              omega
            · simp only [beq_iff_eq, hxy, hyz, hxz, if_false, decide_eq_true_eq]
              omega

/-- Two keys that are each at most the other are one key: with the source order in every
key (`ruleKey`, `inlineKey`), two declarations never tie, so the winner does not depend on
the order in which they are met. -/
theorem lexLE_antisymm (a b : List Nat) : lexLE a b = true → lexLE b a = true → a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [lexLE]
  | cons x xs ih =>
    cases b with
    | nil => simp [lexLE]
    | cons y ys =>
      simp only [lexLE]
      by_cases hxy : x = y
      · subst hxy
        simp only [beq_self_eq_true, if_true]
        intro h1 h2
        rw [ih ys h1 h2]
      · have hyx : ¬ y = x := fun h => hxy h.symm
        simp only [beq_iff_eq, hxy, hyx, if_false, decide_eq_true_eq]
        omega

/-- The position of unlayered declarations among layer places: above every layer for
normal declarations (`SheetReader` keeps at most 4096 layers). -/
def unlayered : Nat := 1000000

/-- Where a declaration of a rule in layer place `layer` (0: no layer) stands among the
declarations of one origin and context (CSS Cascade 5 §6.4.3): for normal declarations a
later layer wins and unlayered declarations win over every layer; for important ones the
order is the reverse. -/
def layerPosition (important : Bool) (layer : Nat) : Nat :=
  if layer == 0 then (if important then 0 else unlayered)
  else if important then unlayered - layer else layer

theorem layerPosition_normal_unlayered (l : Nat) (h0 : 0 < l) (h : l < unlayered) :
    layerPosition false l < layerPosition false 0 := by
  have : l ≠ 0 := by omega
  simp [layerPosition, this, h]

theorem layerPosition_important_unlayered (l : Nat) (h0 : 0 < l) (h : l < unlayered) :
    layerPosition true 0 < layerPosition true l := by
  have : l ≠ 0 := by omega
  simp only [layerPosition, this, beq_self_eq_true, if_true, beq_iff_eq, if_false]
  omega

theorem layerPosition_normal_later (a b : Nat) (h0 : 0 < a) (h : a < b) :
    layerPosition false a < layerPosition false b := by
  have ha : a ≠ 0 := by omega
  have hb : b ≠ 0 := by omega
  simp [layerPosition, ha, hb, h]

theorem layerPosition_important_later (a b : Nat) (h0 : 0 < a) (h : a < b) (hb : b < unlayered) :
    layerPosition true b < layerPosition true a := by
  have ha : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  simp only [layerPosition, ha, hb', beq_iff_eq, if_false, if_true]
  omega

/-- The cascade key of a declaration of a style rule (CSS Cascade 5 §6.1, most significant
first): importance; origin (0 user agent, 1 author) and context (a shadow tree's normal
declarations lose to the document's, its important ones win); 0 for "not attached to the
element"; the layer (`layerPosition`); the specificity of the selector that matched; the
order of appearance. The greatest key wins (`lexLE`). -/
def ruleKey (important : Bool) (origin : Nat) (inShadow : Bool) (layer : Nat)
    (specificity : Nat × Nat × Nat) (order : Nat) : List Nat :=
  let context := if (origin == 1 && inShadow) == important then 1 else 0
  [if important then 1 else 0, origin*2+context, 0, layerPosition important layer,
   specificity.1, specificity.2.1, specificity.2.2, order]

/-- The cascade key of a declaration of a `style` attribute: an author declaration of the
document, attached to the element (above every style rule of its importance, layered or
not: CSS Cascade 5 §6.1 "element-attached styles"). -/
def inlineKey (important : Bool) (order : Nat) : List Nat :=
  [if important then 1 else 0, 2+(if important then 0 else 1), 1, 0, 0, 0, 0, order]

/-- Declarations met at different places in the order of appearance have different keys:
no two declarations of an element tie. -/
theorem ruleKey_order (i i' : Bool) (o o' : Nat) (s s' : Bool) (l l' : Nat) (sp sp' : Nat × Nat × Nat)
    (n n' : Nat) (h : n ≠ n') : ruleKey i o s l sp n ≠ ruleKey i' o' s' l' sp' n' := by
  simp only [ruleKey, ne_eq, List.cons.injEq, and_true, not_and]
  intros
  exact h

/-- A normal declaration of a `style` attribute wins over a normal declaration of any
author rule of the document, and an important one over any important one. -/
theorem inlineKey_wins (important : Bool) (layer : Nat) (sp : Nat × Nat × Nat) (n n' : Nat) :
    lexLE (ruleKey important 1 false layer sp n) (inlineKey important n') = true := by
  cases important <;> simp [ruleKey, inlineKey, lexLE]

/-- The winning declarations of an element with those of flow-relative properties under
the physical names they stand for in `flow` (CSS Logical 1 §4.1): of the two declarations
for one physical property, the one with the greater cascade key stands. A list with no
flow-relative name is not changed. -/
def physicalWinners (flow : CssValues.Logical.Flow) (chosen : List (String × List Nat × Declaration)) :
    List (String × List Nat × Declaration) :=
  let logicals := chosen.filter fun e => (CssValues.Logical.physical flow e.1).isSome
  if logicals.isEmpty then chosen else
  let others : Std.TreeMap String (List Nat × Declaration) :=
    chosen.foldl (fun m (k, v) => if (CssValues.Logical.physical flow k).isSome then m else m.insert k v) {}
  (logicals.foldl (fun m (key, priority, d) =>
    match CssValues.Logical.physical flow key with
    | none => m
    | some name =>
      if (m.get? name).all (fun old => lexLE old.1 priority) then m.insert name (priority, {d with property := name})
      else m) others).toList

/-- Winners with no flow-relative name are what they were. -/
theorem physicalWinners_plain (flow : CssValues.Logical.Flow) (chosen : List (String × List Nat × Declaration))
    (h : ∀ e ∈ chosen, CssValues.Logical.physical flow e.1 = none) : physicalWinners flow chosen = chosen := by
  have : (chosen.filter fun e => (CssValues.Logical.physical flow e.1).isSome) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp [h e he]
  simp [physicalWinners, this]

/-- The user agent style sheet of this profile: HTML §15.3.4 (phrasing content:
hyperlink colours and underline) and §15.5.4 (the `button` element as an
inline-block with a raised border, sunken while it is `:active`), and the form controls
(`input`, `textarea`, `select`) as inline-blocks of a fixed size. The colours are
the ones that HTML gives (`#0000EE`, `#551A8B`, `#FF0000`); the button colours are
this profile's choice, since HTML leaves a button's look to the platform. -/
def userAgentSheet : String :=
  ":link{color:#0000ee}" ++
  ":visited{color:#551a8b}" ++
  -- `:link,:visited` in HTML; one `:any-link` rule, so that the `:visited` colour rule stays colour only.
  ":any-link{text-decoration:underline}" ++
  ":link:active,:visited:active{color:#ff0000}" ++
  "button{display:inline-block;padding:1px 6px;border:2px outset #767676;background-color:#efefef;color:#000000}" ++
  "button:hover{background-color:#e5e5e5}" ++
  "button:active{border-style:inset;background-color:#c8c8c8}" ++
  -- form controls (HTML §15.5.x): inline-block widgets of a fixed size, as a text field of
  -- `size=20`, a `textarea` of 20 columns by 2 rows, a checkbox; the sizes are this
  -- profile's choice, near the platform's
  "input{display:inline-block;padding:1px 2px;border:2px inset #767676;width:147px;height:15px;background-color:#ffffff}" ++
  "input[type=hidden]{display:none}" ++
  -- a check box or radio button: a box with an edge, filled with the accent colour of other
  -- engines while it is checked (the mark itself is not drawn)
  "input[type=checkbox],input[type=radio]{width:13px;height:13px;margin:3px 3px 3px 4px;padding:0;border:1px solid #767676;box-sizing:border-box;background-color:#ffffff}" ++
  "input[type=checkbox]:checked,input[type=radio]:checked{background-color:#0075ff;border-color:#0075ff}" ++
  -- a push button made with `input` (HTML §4.10.5.1.18-20): sized by its label, as `button` is
  "input[type=submit],input[type=reset],input[type=button]{width:auto;height:auto;padding:1px 6px;border:2px outset #767676;background-color:#efefef;color:#000000;text-align:center}" ++
  "input[type=file]{width:auto;height:auto;padding:0;border-width:0;background-color:transparent}" ++
  -- form controls draw their text at the size of other engines' controls (13.33px)
  "input,select,textarea,button{font-size:13.333px}" ++
  "textarea{display:inline-block;padding:2px;border:1px solid #767676;width:176px;height:30px;background-color:#ffffff;white-space:pre-wrap}" ++
  -- a drop-down list shows its selected option (`Layout.controlItems`), with room for its arrow
  "select{display:inline-block;padding:1px 4px;border:1px solid #767676;background-color:#ffffff;white-space:nowrap}" ++
  "select>*{display:none}" ++
  -- HTML §15.3.6
  "sub,sup{font-size:smaller}" ++
  -- HTML §15.4.1: `iframe { border: 2px inset; }`
  "iframe{border:2px inset}"

def userAgentRules : List Rule := (parse userAgentSheet).toOption.getD []

/-- The text of an `option` as a drop-down list shows it (HTML §4.10.10): its `label`
attribute when that is not empty, else its text with the white space collapsed. -/
def optionLabel (dom : Dom) (o : Nat) : String :=
  let n := dom.get o
  let label := attrValue n "label"
  if !label.isEmpty then label else " ".intercalate (words ((dom.textContent o).getD ""))

/-- The `option` elements of a `select` (HTML §4.10.7, the list of options): its `option`
children and those of its `optgroup` children, in tree order; 256 children read at each
level. -/
def selectOptions (dom : Dom) (sel : Nat) : List Nat :=
  let isEl := fun (k : Nat) (name : String) => (dom.get k).type == .element && (dom.get k).lname == name
  ((dom.get sel).kids.toList.take 256).flatMap fun k =>
    if isEl k "option" then [k]
    else if isEl k "optgroup" then ((dom.get k).kids.toList.take 256).filter (isEl · "option")
    else []

/-- The option a drop-down list shows (HTML §4.10.7, the selectedness setting algorithm):
the last option that is selected (its `selected` attribute, or what a script set,
`Node.checkedness`), else the first option. -/
def shownOption (dom : Dom) (sel : Nat) : Option Nat :=
  let opts := selectOptions dom sel
  (opts.reverse.find? fun o => (dom.get o).checkedness.getD (hasAttribute (dom.get o) "selected")).orElse fun _ => opts.head?

/-- `input` types whose box shows a line of text (HTML §4.10.5): the textual states, and an
unknown or absent type (the Text state). -/
def textualInputTypes : List String := ["", "text", "search", "email", "url", "tel", "password", "number"]
/-- The known `input` types (HTML §4.10.5); any other value is the Text state. -/
def knownInputTypes : List String :=
  ["hidden", "text", "search", "tel", "url", "email", "password", "date", "month", "week",
   "time", "datetime-local", "number", "range", "color", "checkbox", "radio", "file",
   "submit", "image", "reset", "button"]

/-- What a form control shows inside its box, and whether it is a placeholder (HTML §4.10):
a text field its `value` (a password field a bullet for each character), else its
`placeholder`; a push button made with `input` its `value`, else the label of its type
(`Submit`, `Reset`); a file chooser its button and state; a drop-down list the label of the
option it shows (`shownOption`); a `textarea` with no text its `placeholder`. Line breaks in
a one-line control become spaces. `none` for every other node, and when there is nothing to
show. The value a person types is the host's and is not shown here. -/
def controlText (dom : Dom) (id : Nat) : Option (String × Bool) :=
  let n := dom.get id
  let oneLine := fun (t : String) => String.ofList (t.toList.map fun c => if c == '\n' || c == '\r' || c == '\t' then ' ' else c)
  if n.type != .element || !(n.ns == some DOM.htmlNS || n.ns.isNone) then none
  else if n.lname == "input" then
    let t0 := (attrValue n "type").trimAscii.toString.toLower
    let t := if knownInputTypes.contains t0 then t0 else ""
    let value := oneLine (attrValue n "value")
    if t == "submit" || t == "reset" || t == "button" then
      if hasAttribute n "value" then (if value.isEmpty then none else some (value, false))
      else if t == "submit" then some ("Submit", false)
      else if t == "reset" then some ("Reset", false)
      else none
    else if t == "file" then some ("Choose File", false)
    else if textualInputTypes.contains t then
      if !value.isEmpty then some ((if t == "password" then String.ofList (value.toList.map fun _ => '•') else value), false)
      else
        let p := oneLine (attrValue n "placeholder")
        if p.isEmpty then none else some (p, true)
    else none
  else if n.lname == "select" then
    if hasAttribute n "multiple" then none
    else (shownOption dom id).bind fun o => let l := optionLabel dom o; if l.isEmpty then none else some (l, false)
  else if n.lname == "textarea" then
    if n.kids.any (fun k => !(dom.get k).data.isEmpty) then none
    else
      let p := attrValue n "placeholder"
      if p.isEmpty then none else some (p, true)
  else none

/-- Kind: property (a page with no form controls pays one name test an element). Says: an
element that is not `input`, `select` or `textarea` shows no control text. -/
theorem controlText_other (dom : Dom) (id : Nat) (hi : (dom.get id).lname ≠ "input")
    (hs : (dom.get id).lname ≠ "select") (ht : (dom.get id).lname ≠ "textarea") :
    controlText dom id = none := by
  simp [controlText, hi, hs, ht]

/-- The control text of the first element named `tag` of `source` (a test helper). -/
private def controlTextOf (source tag : String) : Option (String × Bool) :=
  let dom := DOM.parseHtmlDocument source
  ((dom.treeOrder 0).find? fun k => (dom.get k).lname == tag).bind (controlText dom)

#guard controlTextOf "<input placeholder='Search'>" "input" == some ("Search", true)
#guard controlTextOf "<input value='hello' placeholder='Search'>" "input" == some ("hello", false)
#guard controlTextOf "<input type=password value='abc'>" "input" == some ("•••", false)
#guard controlTextOf "<input type=submit>" "input" == some ("Submit", false)
#guard controlTextOf "<input type=submit value=Go>" "input" == some ("Go", false)
#guard controlTextOf "<input type=checkbox>" "input" == none
#guard controlTextOf "<input type=wibble placeholder=x>" "input" == some ("x", true)
#guard controlTextOf "<select><option>One<option selected>Two<option>Three</select>" "select" == some ("Two", false)
#guard controlTextOf "<select><optgroup label=g><option>  First   one </option></optgroup></select>" "select" == some ("First one", false)
#guard controlTextOf "<textarea placeholder='Write'></textarea>" "textarea" == some ("Write", true)
#guard controlTextOf "<textarea placeholder='Write'>x</textarea>" "textarea" == none
#guard controlTextOf "<p>text</p>" "p" == none

/-- A rule that matches only through `:visited` sets only colours (Selectors 4 §8.2,
the privacy restriction that browsers apply to visited links). -/
def visitedProperties : List String := ["color","background","background-color","border-color"]

/-- A rule that matches an element: its origin (0 the user agent, 1 the author), the rule,
and those of its selectors that match. -/
abbrev Match := Nat × Rule × List Selector

/-- Every rule with its origin, the user agent's first, in sheet order. -/
def ruleEntries (rules : List Rule) : List (Nat × Rule) := userAgentRules.map (0,·) ++ rules.map (1,·)

/-- The entry `e` as a match of element `id`, when one of its selectors matches. -/
def matchEntry (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (state : ElementState) (e : Nat × Rule) : Option Match :=
  let m := e.2.selectors.filter (selectorMatchesK keys dom id · state)
  if m.isEmpty then none else some (e.1,e.2,m)

/-- The reference: every rule tried, in order. -/
def matchedRules (dom : Dom) (id : Nat) (rules : List Rule) (state : ElementState := {}) : List Match :=
  (ruleEntries rules).filterMap (matchEntry (readKeys dom) dom id state)

/-! ### Rule buckets

As browsers do, each selector goes in one bucket by its rightmost compound: its id, else
its first class, else its tag, else the bucket of every element. An element tries only
the rules of the buckets it is in (`RuleIndex.candidates`), in sheet order. A selector
outside those buckets can not match (`selectorMatchesK_admits`), so the rules matched
are those of the plain loop (`matchedRules`); `RuleIndex.matched_eq` checks this on
the test pages (`CascadeTests.lean`) and `computeAll_eq_linear` lifts it to the styles. -/
inductive Bucket where
  | id (s : String) | cls (s : String) | tag (s : String) | any
  /-- A selector no element of a tree without shadow scope matches: `:host` and `::slotted()`. -/
  | never
/-- The bucket of a compound by its fields alone. -/
def Compound.fieldBucket (c : Compound) : Bucket :=
  match c.id with
  | some i => .id i
  | none => match c.classes with
    | k :: _ => .cls k
    | [] => match c.tag with
      | some t => .tag t
      | none => .any
def Compound.bucket (c : Compound) : Bucket :=
  if c.host then .never else c.fieldBucket
def Selector.bucket (sel : Selector) : Bucket :=
  if sel.slotted.isSome then .never else
  match sel.parts with
  | [] => .any
  | c :: _ => c.bucket
/-- An element with keys `k` and local name `lname` is in bucket `b`. -/
def Bucket.admits (k : ElemKey) (lname : String) : Bucket → Bool
  | .id i => i == k.id
  | .cls c => k.classes.contains c
  | .tag t => t == lname
  | .any => true
  | .never => false

/-- A compound's fields that match an element have the element in the compound's bucket. -/
private theorem compoundFieldsK_admits (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (c : Compound)
    (state : ElementState) (hc : compoundFieldsK keys dom state id c = true) :
    c.fieldBucket.admits (keys id) (dom.get id).lname = true := by
  unfold compoundFieldsK at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, htag⟩, hid⟩, hcls⟩, _⟩ := hc
  cases hi : c.id with
  | some i =>
    rw [hi] at hid
    simpa [Compound.fieldBucket, hi, Bucket.admits] using hid
  | none =>
    cases hk : c.classes with
    | cons k ks =>
      rw [hk] at hcls
      simp only [List.all_cons, Bool.and_eq_true] at hcls
      simpa [Compound.fieldBucket, hi, hk, Bucket.admits] using hcls.1
    | nil =>
      cases ht : c.tag with
      | some t =>
        rw [ht] at htag
        simpa [Compound.fieldBucket, hi, hk, ht, Bucket.admits] using htag
      | none => simp [Compound.fieldBucket, hi, hk, ht, Bucket.admits]

/-- A selector whose compounds match an element has the element in its bucket. -/
theorem selectorPartsMatchK_admits (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (sel : Selector)
    (state : ElementState) (h : selectorPartsMatchK keys dom id sel state = true) :
    sel.bucket.admits (keys id) (dom.get id).lname = true := by
  unfold selectorPartsMatchK at h
  cases hp : sel.parts with
  | nil => simp [hp] at h
  | cons c rest =>
    rw [hp] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hs, hc⟩, _⟩ := h
    unfold compoundMatchesK at hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hsome : sel.slotted.isSome = false := by
      cases hsl : sel.slotted with
      | none => rfl
      | some _ => rw [hsl] at hs; simp at hs
    have := compoundFieldsK_admits keys dom id c state hc.2
    simpa [Selector.bucket, hsome, hp, Compound.bucket, hc.1] using this

/-- A selector of tree `scope` that matches element `id` has it where the scoped index
(`ScopedIndex`) looks: under `::slotted(c)`, in the bucket of `c` with a slot of that tree
assigned; under a `:host` compound, as that tree's host; otherwise, in the bucket of the
rightmost compound and in that tree. -/
theorem selectorPartsMatchInK_admits (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState)
    (scope : Option Nat) (id : Nat) (sel : Selector)
    (h : selectorPartsMatchInK keys ts state scope id sel = true) :
    match sel.slotted, sel.parts with
    | some c, _ => c.fieldBucket.admits (keys id) (ts.tree.get id).lname = true ∧
        ∃ sl, ts.tree.findSlot id = some sl ∧ ts.scopeOf sl = scope
    | none, c :: _ =>
      if c.host then hostOfScope ts scope = some id
      else c.fieldBucket.admits (keys id) (ts.tree.get id).lname = true ∧ ts.scopeOf id = scope
    | none, [] => False := by
  unfold selectorPartsMatchInK at h
  cases hp : sel.parts with
  | nil => simp [hp] at h
  | cons c rest =>
    rw [hp] at h
    simp only at h
    cases hs : sel.slotted with
    | none =>
      simp only [hs, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hscope, hc⟩, _⟩ := h
      unfold compoundInK at hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hhost, hfields⟩ := hc
      cases hh : c.host with
      | true =>
        simp only [hh, if_true]
        rw [hh] at hhost
        have : (hostOfScope ts scope == some id) = true := by simpa using hhost
        exact beq_iff_eq.mp this
      | false =>
        simp only [hh, Bool.false_eq_true, if_false]
        refine ⟨compoundFieldsK_admits keys ts.tree id c state hfields, ?_⟩
        rcases hscope with hb | hsc
        · rw [hh] at hb; cases hb
        · exact hsc
    | some cc =>
      simp only [hs, Bool.and_eq_true] at h
      obtain ⟨⟨_, hfields⟩, hslot⟩ := h
      refine ⟨compoundFieldsK_admits keys ts.tree id cc state hfields, ?_⟩
      cases hfs : ts.tree.findSlot id with
      | none => rw [hfs] at hslot; cases hslot
      | some sl =>
        rw [hfs] at hslot
        simp only [Bool.and_eq_true, beq_iff_eq] at hslot
        exact ⟨sl, rfl, hslot.1.1⟩

/-- A selector that matches an element has the element in its bucket: a selector with
`complex` matches only where its compounds do. -/
theorem selectorMatchesK_admits (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (sel : Selector)
    (state : ElementState) (h : selectorMatchesK keys dom id sel state = true) :
    sel.bucket.admits (keys id) (dom.get id).lname = true := by
  unfold selectorMatchesK at h
  simp only [Bool.and_eq_true] at h
  exact selectorPartsMatchK_admits keys dom id sel state h.1

/-- The scoped form of `selectorMatchesK_admits`. -/
theorem selectorMatchesInK_admits (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState)
    (scope : Option Nat) (id : Nat) (sel : Selector)
    (h : selectorMatchesInK keys ts state scope id sel = true) :
    match sel.slotted, sel.parts with
    | some c, _ => c.fieldBucket.admits (keys id) (ts.tree.get id).lname = true ∧
        ∃ sl, ts.tree.findSlot id = some sl ∧ ts.scopeOf sl = scope
    | none, c :: _ =>
      if c.host then hostOfScope ts scope = some id
      else c.fieldBucket.admits (keys id) (ts.tree.get id).lname = true ∧ ts.scopeOf id = scope
    | none, [] => False := by
  unfold selectorMatchesInK at h
  simp only [Bool.and_eq_true] at h
  exact selectorPartsMatchInK_admits keys ts state scope id sel h.1

/-- The rules in buckets: `entries` is `ruleEntries`, and each bucket lists the entries
(by index, ascending, each once) with a selector in that bucket. -/
structure RuleIndex where
  entries : Array (Nat × Rule)
  byId : Std.HashMap String (Array Nat) := {}
  byClass : Std.HashMap String (Array Nat) := {}
  byTag : Std.HashMap String (Array Nat) := {}
  universal : Array Nat := #[]

private def bucketAdd (m : Std.HashMap String (List Nat)) (k : String) (i : Nat) : Std.HashMap String (List Nat) :=
  match m.get? k with
  | some (j :: rest) => if j == i then m else m.insert k (i :: j :: rest)
  | _ => m.insert k [i]
private def bucketArrays (m : Std.HashMap String (List Nat)) : Std.HashMap String (Array Nat) :=
  m.map fun _ l => l.reverse.toArray

/-- Buckets being filled, descending by entry. -/
structure RuleIndexB where
  byId : Std.HashMap String (List Nat) := {}
  byClass : Std.HashMap String (List Nat) := {}
  byTag : Std.HashMap String (List Nat) := {}
  universal : List Nat := []
  deriving Inhabited

def RuleIndexB.add (b : RuleIndexB) (bk : Bucket) (i : Nat) : RuleIndexB :=
  match bk with
  | .id k => {b with byId := bucketAdd b.byId k i}
  | .cls k => {b with byClass := bucketAdd b.byClass k i}
  | .tag k => {b with byTag := bucketAdd b.byTag k i}
  | .any => if b.universal.head? != some i then {b with universal := i :: b.universal} else b
  | .never => b

def RuleIndexB.finish (b : RuleIndexB) (entries : Array (Nat × Rule)) : RuleIndex :=
  ⟨entries, bucketArrays b.byId, bucketArrays b.byClass, bucketArrays b.byTag, b.universal.reverse.toArray⟩

/-- The buckets of `rules` (and the user agent's): one pass over the selectors. -/
def RuleIndex.build (rules : List Rule) : RuleIndex := Id.run do
  let entries := (ruleEntries rules).toArray
  let mut b : RuleIndexB := {}
  for h : i in [:entries.size] do
    for sel in entries[i].2.selectors do
      b := b.add sel.bucket i
  return b.finish entries

/-- The union of two ascending arrays, ascending, each value once: one pass, no recursion. -/
def RuleIndex.mergeAsc (a b : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty (a.size+b.size)
  let mut i := 0
  let mut j := 0
  for _ in [:a.size+b.size] do
    match a[i]?, b[j]? with
    | some x, some y =>
      if x < y then
        out := out.push x
        i := i+1
      else if y < x then
        out := out.push y
        j := j+1
      else
        out := out.push x
        i := i+1
        j := j+1
    | some x, none =>
      out := out.push x
      i := i+1
    | none, some y =>
      out := out.push y
      j := j+1
    | none, none => break
  return out

/-- The union of ascending arrays: pairs merged in passes, so that an element with many
classes costs its candidates times the logarithm of its classes. Loops only: a sort here
recursed as deep as its input. -/
def RuleIndex.mergeRuns (runs : Array (Array Nat)) : Array Nat := Id.run do
  let mut current := runs
  for _ in [:runs.size] do
    if current.size ≤ 1 then break
    let mut next : Array (Array Nat) := Array.mkEmpty (current.size/2+1)
    let mut k := 0
    for _ in [:current.size] do
      if k+1 < current.size then
        next := next.push (RuleIndex.mergeAsc (current.getD k #[]) (current.getD (k+1) #[]))
        k := k+2
      else if k < current.size then
        next := next.push (current.getD k #[])
        k := k+2
      else break
    current := next
  return current.getD 0 #[]

/-- The entries that element (keys `k`, local name `lname`) may match: those of its
buckets, ascending, each once. -/
def RuleIndex.candidates (ix : RuleIndex) (k : ElemKey) (lname : String) : Array Nat := Id.run do
  let mut runs : Array (Array Nat) := #[ix.universal]
  if let some a := ix.byTag[lname]? then runs := runs.push a
  if !k.id.isEmpty then
    if let some a := ix.byId[k.id]? then runs := runs.push a
  for cl in k.classes do
    if let some a := ix.byClass[cl]? then runs := runs.push a
  return RuleIndex.mergeRuns runs

/-- The rules that match element `id`, from its buckets. -/
def RuleIndex.matched (ix : RuleIndex) (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (state : ElementState := {}) : List Match :=
  (ix.candidates (keys id) (dom.get id).lname).toList.filterMap fun i =>
    match ix.entries[i]? with
    | some e => matchEntry keys dom id state e
    | none => none

/-! ### Rule buckets on a page with shadow trees

The same buckets, one set per tree: an element tries the user agent's rules, the rules
of its own tree, the `:host` rules of the tree it hosts, and the `::slotted()` rules of the
tree its parent hosts (the shadow root its slot is in). Numbers index the one entry
array of `ruleEntries`, so the union stays in sheet order as in `RuleIndex.matched`.
Nothing here runs on a page with no shadow host (`computeFor`, `computeAll`). -/

/-- The buckets of the rules of one tree. -/
structure TreeRules where
  normal : RuleIndex
  /-- Rules with a `:host` compound rightmost: tried only on that tree's host. -/
  hostRules : Array Nat := #[]
  slotted : RuleIndex

/-- A tree's rules while being filled. -/
structure TreeRulesB where
  normal : RuleIndexB := {}
  hostRules : List Nat := []
  slotted : RuleIndexB := {}
  deriving Inhabited

/-- The rules of each tree, in buckets: `doc` the document's, `shadow` by shadow root. -/
structure ScopedIndex where
  entries : Array (Nat × Rule)
  ua : RuleIndex
  doc : TreeRules
  shadow : Std.HashMap Nat TreeRules := {}
  empty : TreeRules

private def TreeRulesB.add (b : TreeRulesB) (sel : Selector) (i : Nat) : TreeRulesB :=
  match sel.slotted with
  | some c => {b with slotted := b.slotted.add c.fieldBucket i}
  | none => match sel.parts with
    | [] => b
    | c :: _ => if c.host then
        (if b.hostRules.head? != some i then {b with hostRules := i :: b.hostRules} else b)
      else {b with normal := b.normal.add c.fieldBucket i}

private def TreeRulesB.finish (b : TreeRulesB) (entries : Array (Nat × Rule)) : TreeRules :=
  {normal := b.normal.finish entries, hostRules := b.hostRules.reverse.toArray, slotted := b.slotted.finish entries}

/-- The scoped buckets of `rules` (and the user agent's): one pass over the selectors. -/
def ScopedIndex.build (rules : List Rule) : ScopedIndex := Id.run do
  let entries := (ruleEntries rules).toArray
  let mut ua : RuleIndexB := {}
  let mut doc : TreeRulesB := {}
  let mut shadow : Std.HashMap Nat TreeRulesB := {}
  for h : i in [:entries.size] do
    let (origin,rule) := entries[i]
    for sel in rule.selectors do
      if origin == 0 then
        ua := ua.add sel.bucket i
      else match rule.scope with
        | none => doc := doc.add sel i
        | some r => shadow := shadow.insert r ((shadow.getD r {}).add sel i)
  let none_ : TreeRulesB := {}
  return {entries, ua := ua.finish entries, doc := doc.finish entries,
          shadow := shadow.map fun _ b => b.finish entries, empty := none_.finish entries}

/-- The rules of tree `scope`. -/
def ScopedIndex.treeOf (ix : ScopedIndex) (scope : Option Nat) : TreeRules :=
  match scope with
  | none => ix.doc
  | some r => ix.shadow.getD r ix.empty

/-- The entries that element `id` (keys `k`) may match: those of the buckets above,
ascending, each once. -/
def ScopedIndex.candidates (ix : ScopedIndex) (ts : TreeScope) (k : ElemKey) (id : Nat) : Array Nat := Id.run do
  let n := ts.tree.get id
  let scope := ts.scopeOf id
  let own := ix.treeOf scope
  let mut runs : Array (Array Nat) := #[ix.ua.candidates k n.lname, own.normal.candidates k n.lname]
  if let some r := n.shadow then
    runs := runs.push (ix.treeOf (some r)).hostRules
  if let some p := n.parent then
    if let some r := (ts.tree.get p).shadow then
      runs := runs.push ((ix.treeOf (some r)).slotted.candidates k n.lname)
  return RuleIndex.mergeRuns runs

/-- The entry `e` as a match of element `id` in its tree: the user agent's rules match in
the element's tree, an author rule in the tree of its sheet. -/
def matchEntryIn (keys : Nat → ElemKey) (ts : TreeScope) (id : Nat) (state : ElementState) (e : Nat × Rule) : Option Match :=
  let scope := if e.1 == 0 then ts.scopeOf id else e.2.scope
  let m := e.2.selectors.filter (selectorMatchesInK keys ts state scope id ·)
  if m.isEmpty then none else some (e.1,e.2,m)

/-- The reference on a page with shadow trees: every rule tried, in order. -/
def matchedRulesIn (ts : TreeScope) (id : Nat) (rules : List Rule) (state : ElementState := {}) : List Match :=
  (ruleEntries rules).filterMap (matchEntryIn (readKeys ts.tree) ts id state)

/-- The rules that match element `id`, from its buckets. -/
def ScopedIndex.matched (ix : ScopedIndex) (keys : Nat → ElemKey) (ts : TreeScope) (id : Nat) (state : ElementState := {}) : List Match :=
  (ix.candidates ts (keys id) id).toList.filterMap fun i =>
    match ix.entries[i]? with
    | some e => matchEntryIn keys ts id state e
    | none => none

/-- Most children of a `details` among which its `summary` is looked for. The bound makes the
work for each child of a `details` constant: without it a page with one `details` of n
children, half of them `summary` elements after the other half, cost n squared steps. -/
def summarySearch : Nat := 64

/-- The first `summary` child of a `details` with children `kids`, among the first
`summarySearch` of them; none when there is none there. -/
def firstSummary (dom : Dom) (kids : Array Nat) : Option Nat :=
  (kids.extract 0 summarySearch).toList.find? fun k => (dom.get k).type == .element && (dom.get k).lname == "summary"

/-- Kind: resource bound. Says: the search for a `details` element's summary reads at most
`summarySearch` children, however many the page gives the element. Does not say: that a
`summary` after the first `summarySearch` children is found (it is not: it is content). -/
theorem firstSummary_work (kids : Array Nat) : (kids.extract 0 summarySearch).toList.length ≤ summarySearch := by
  simp [summarySearch]
  omega

/-- The content of a `details` element that is not open, all but its first `summary` child
(HTML §15.5.4): not rendered. -/
def closedDetailsContent (dom : Dom) (id : Nat) : Bool :=
  match (dom.get id).parent with
  | some p =>
    let d := dom.get p
    d.ns == some DOM.htmlNS && d.lname == "details" && !(d.attrs.any fun a => a.ns.isNone && a.lname == "open") &&
      !((dom.get id).lname == "summary" && firstSummary dom d.kids == some id)
  | none => false

/-- Kind: property. Says: a node with no parent (the root) is never the content of a closed
`details`. -/
theorem closedDetailsContent_root (dom : Dom) (id : Nat) (h : (dom.get id).parent = none) :
    closedDetailsContent dom id = false := by
  simp [closedDetailsContent, h]

/-- Kind: property. Says: the content of a `details` with the `open` attribute is rendered,
whatever it is. Does not say: anything of author rules (they are applied after). -/
theorem closedDetailsContent_open (dom : Dom) (id p : Nat) (hp : (dom.get id).parent = some p)
    (ho : ((dom.get p).attrs.any fun a => a.ns.isNone && a.lname == "open") = true) :
    closedDetailsContent dom id = false := by
  simp [closedDetailsContent, hp, ho]

/-- Kind: property. Says: a child of an element that is not a `details` is never hidden by
this rule. -/
theorem closedDetailsContent_other (dom : Dom) (id p : Nat) (hp : (dom.get id).parent = some p)
    (hn : ((dom.get p).lname == "details") = false) : closedDetailsContent dom id = false := by
  simp [closedDetailsContent, hp, hn]

/-- The elements the user agent sheet isolates (HTML §15.3.5, "Bidirectional text"). -/
def isolatedTags : List String :=
  ["address","blockquote","center","div","figure","figcaption","footer","form","header","hr",
   "legend","listing","main","p","plaintext","pre","summary","xmp","article","aside","h1","h2",
   "h3","h4","h5","h6","hgroup","nav","section","search","table","caption","colgroup","col",
   "thead","tbody","tfoot","tr","td","th","dir","dd","dl","dt","menu","ol","ul","li","bdi","output"]

/-- The `unicode-bidi` of the user agent sheet (HTML §15.3.5) for an HTML element `tag` with the
`dir` attribute `dir` (ASCII lower case, "" when absent) and, for an `input`, the `type`
attribute `type` (lower case): `bdo` is `isolate-override`; an `input` of type search, tel,
url or email, a `textarea` and a `pre` with `dir=auto` are `plaintext`; the listed elements and
an element with a valid `dir` are `isolate`; else none (the initial `normal`). -/
def uaUnicodeBidi (tag dir type : String) : Option UnicodeBidi :=
  if tag == "bdo" then some .isolateOverride
  else if dir == "auto" && (tag == "textarea" || tag == "pre" ||
      (tag == "input" && ["search","tel","url","email"].contains type)) then some .plaintext
  else if ["rtl","ltr","auto"].contains dir || isolatedTags.contains tag then some .isolate
  else none

/-- Kind: property. Says: `bdo` is `isolate-override`, whatever its `dir`. -/
theorem uaUnicodeBidi_bdo (dir type : String) : uaUnicodeBidi "bdo" dir type = some .isolateOverride := by
  simp [uaUnicodeBidi]

/-- Kind: property. Says: an element with `dir=ltr` or `dir=rtl` is isolated, unless it is a `bdo`
(which overrides as well). -/
theorem uaUnicodeBidi_dir (tag dir type : String) (hd : dir = "ltr" ∨ dir = "rtl") (ht : tag ≠ "bdo") :
    uaUnicodeBidi tag dir type = some .isolate := by
  rcases hd with rfl | rfl <;> simp [uaUnicodeBidi, ht]

#guard uaUnicodeBidi "div" "" "" == some .isolate
#guard uaUnicodeBidi "span" "" "" == none
#guard uaUnicodeBidi "span" "invalid" "" == none
#guard uaUnicodeBidi "input" "auto" "email" == some .plaintext
#guard uaUnicodeBidi "input" "auto" "text" == some .isolate
#guard uaUnicodeBidi "input" "" "email" == none
#guard uaUnicodeBidi "textarea" "auto" "" == some .plaintext
#guard uaUnicodeBidi "pre" "" "" == some .isolate

/-- Winning declarations are keyed by property, with importance, origin, specificity
and source order compared lexicographically (CSS Cascade 4 §6.1). The user agent
origin (`userAgentRules`) is below the author origin. Inheritance is applied first.
`matched` are the rules that match the element, in sheet order (`matchedRules`). In one
list position with the origin, a shadow tree's normal declarations lose to the document's
and its important ones win (CSS Cascade 4 §6.1 "context"), above the style attribute. -/
def computedFrom (dom : Dom) (id : Nat) (matched : List Match) (parent : Computed) : Except String Computed := do
  let n := dom.get id
  let block := ["html","body","div","p","section","main","article","header","footer","nav","aside",
    "h1","h2","h3","h4","h5","h6","ul","ol","li","dir","menu","dl","dt","dd","pre","listing","xmp","plaintext",
    "blockquote","address","center","hr","form","fieldset","legend","figure","figcaption",
    "details","summary","hgroup","search"].contains n.lname
  -- HTML §15.3.1 and §6.12 (the user agent's `dialog:not([open])` and
  -- `[popover]:not(:popover-open)` rules, `display: none`): a dialog that is not open and a
  -- popover that is not showing (`Node.states` bit 1) start as not rendered, as the elements
  -- of `head` do; an author rule for `display` still wins.
  let hasAttr := fun (name : String) => n.attrs.any fun a => a.ns.isNone && a.lname == name
  -- `noscript`: scripts run in this engine, so what it holds is not rendered (HTML §15.3.1,
  -- `noscript { display: none }` with scripting enabled; `SfntProfile.unrenderedText` already
  -- shapes none of its text). It was laid out: lean-lang.org began with its noscript notice.
  let hidden := ["head","style","script","title","meta","link","template","base","area","param","noscript"].contains n.lname ||
    -- the `hidden` attribute (HTML §15.3.1, the user agent's `[hidden] { display: none }`; an
    -- author rule for `display` wins, as over any user agent rule). It was not read: gov.uk's
    -- cookie notice showed the paragraphs of both of its answers.
    -- (`dialog:popover-open { display: block }`: a dialog showing as a popover is rendered)
    (n.ns == some DOM.htmlNS && ((n.lname == "dialog" && !hasAttr "open" && !(hasAttr "popover" && n.states % 2 == 1)) || (hasAttr "popover" && n.states % 2 == 0) ||
      hasAttr "hidden")) ||
    -- the content of a `details` that is not open (it was drawn open)
    closedDetailsContent dom id
  let svgViewport := n.ns == some DOM.svgNS && n.lname == "svg"
  let svgOverflow := attrValue n "overflow"
  let scale := headingScale n.lname
  let fontSize := if scale == 1 then parent.fontSize else (parent.fontSize*scale).round
  -- HTML §15.3.4 and §15.3.6: headings and `th` are bold, `b` and `strong` bolder than their
  -- parent, `i`, `em`, `cite`, `var`, `dfn` and `address` italic. Author CSS wins.
  let html := n.ns == some DOM.htmlNS || n.ns.isNone
  let fontWeight := if html && ["b","strong"].contains n.lname then FontSynthesis.bolder parent.fontWeight
    else if html && FontSynthesis.boldTags.contains n.lname then FontSynthesis.boldWeight
    else parent.fontWeight
  let mut initial : Computed := {
    fontWeight, inheritedWeight := parent.fontWeight,
    oblique := parent.oblique || (html && FontSynthesis.italicTags.contains n.lname),
    color := parent.color,
    clipOverflow := svgViewport && svgOverflow != "visible", fontSize,
    fontFamily := if html && monospaceTags.contains n.lname then "monospace" else parent.fontFamily,
    lineHeight := parent.lineHeightFactor.map (fontSize*·) |>.getD parent.lineHeight,
    lineHeightFactor := parent.lineHeightFactor, visible := parent.visible,
    rise := parent.rise, centerBlocks := parent.centerBlocks,
    -- HTML §15.3.6: `sub { vertical-align: sub }`, `sup { vertical-align: super }`
    shift := if html && n.lname == "sup" then 1 else if html && n.lname == "sub" then -1 else 0,
    preformatted := parent.preformatted || ["pre","listing","xmp","plaintext"].contains n.lname,
    preserveSegmentBreaks := parent.preserveSegmentBreaks,
    display := if hidden then .none else if block then .block else tableDisplay n.lname,
    margin := startMargin n.lname fontSize (insideList dom id),
    borderSpacingX := parent.borderSpacingX, borderSpacingY := parent.borderSpacingY,
    borderCollapse := parent.borderCollapse, captionBottom := parent.captionBottom,
    textAlign := parent.textAlign, direction := parent.direction, vars := parent.vars,
    letterSpacing := parent.letterSpacing, wordSpacing := parent.wordSpacing, textIndent := parent.textIndent,
    -- `writing-mode` and `list-style-type` are inherited (CSS Writing Modes 4 §3.2, CSS
    -- Lists 3 §3.1); the rest of `pos` is not
    pos := {writingMode := parent.pos.writingMode, listStyle := parent.pos.listStyle,
            listInside := parent.pos.listInside, nowrap := parent.pos.nowrap,
            textTransform := parent.pos.textTransform, lineBreak := parent.pos.lineBreak}}
  -- HTML §3.2.6.4 and §15.3.5: the `dir` attribute sets `direction` and isolates the
  -- element; `bdi` isolates, and `bdo` overrides with isolation. Author CSS wins.
  if n.ns == some DOM.htmlNS || n.ns.isNone then
    let dirAttr := (attrValue n "dir").toLower
    if dirAttr == "rtl" then initial := {initial with direction := .rtl}
    else if dirAttr == "ltr" then initial := {initial with direction := .ltr}
    else if dirAttr == "auto" || (n.lname == "bdi" && !hasAttribute n "dir") then
      initial := {initial with direction := autoDirection dom id}
    if let some b := uaUnicodeBidi n.lname dirAttr (attrValue n "type").toLower then
      initial := {initial with unicodeBidi := b}
  let preHint := initial
  -- MathML Core §2.1.2 and §2.1.3: on a MathML element `dir` is a presentational hint for
  -- `direction` (`ltr` or `rtl`, ASCII case-insensitive; any other value none), and
  -- `mathcolor`, `mathbackground` and `mathsize` for `color`, `background-color` and
  -- `font-size`. The deprecated MathML 3 attributes (`color`, `background`, `fontsize` ...)
  -- are not mapped.
  if n.ns == some DOM.mathmlNS then
    let dirAttr := (attrValue n "dir").toLower
    if dirAttr == "rtl" then initial := {initial with direction := .rtl}
    else if dirAttr == "ltr" then initial := {initial with direction := .ltr}
    for (attr, property) in [("mathcolor", "color"), ("mathbackground", "background-color"), ("mathsize", "font-size")] do
      let value := attrValue n attr
      if !value.isEmpty then initial := applyOrKeep initial ⟨property, value, false⟩
  if n.ns == some DOM.htmlNS || n.ns.isNone then
    initial := alignHints n (bodyMarginHints n (sourceDimensionHints dom id (replacedHints n (tableHints dom id initial parent)))) parent
  -- HTML §15.1: presentational hints sit above the user agent's rules (below the author's):
  -- a property a hint sets here takes no value from a rule of the UA sheet (`input` has
  -- `width: 147px` there; `<input type=image width=40>` is 40px wide)
  let hinted := hintedProperties preHint initial
  -- SVG presentation attributes have lower priority than author CSS.
  -- These properties affect HTML layout/inheritance, so compute them here.
  if svgViewport then
    for property in ["color","visibility","display"] do
      let value := attrValue n property
      if !value.isEmpty then initial := applyOrKeep initial ⟨property,value,false⟩
    for property in ["width","height"] do
      let value := trim (attrValue n property)
      if !value.isEmpty then
        -- `em` is the font size of the element (CSS Values 4 §6.1.1; BBC News draws its icons
        -- with width="1em"), `rem` that of the initial 16 px.
        let dimension ← if value == "auto" || value.endsWith "px" || value.endsWith "%" || value.endsWith "vw" || value.endsWith "vh" then length value
          else if value.endsWith "rem" then pure (.px ((← number (value.dropEnd 3).toString) * 16))
          else if value.endsWith "em" then pure (.px ((← number (value.dropEnd 2).toString) * initial.fontSize))
          else pure (.px (← number value))
        initial := if property == "width" then {initial with width := dimension}
          else {initial with height := dimension}
  let mut winners : Std.TreeMap String (List Nat × Declaration) := {}
  let mut order : Nat := 0
  -- a matched rule or the `style` attribute has a custom property or a `var()`
  let mut usesVars := false
  -- a matched rule or the `style` attribute may have a flow-relative property
  let mut usesLogical := false
  for (origin,rule,matched) in matched do
    let specificity := matched.foldl (fun m s => if lexLE [m.1,m.2.1,m.2.2] [s.specificity.1,s.specificity.2.1,s.specificity.2.2] then s.specificity else m) (0,0,0)
    let onlyVisited := matched.all (·.visitedDependent)
    if rule.usesVars then usesVars := true
    if rule.usesLogical then usesLogical := true
    for d in rule.declarations do
      if (!onlyVisited || visitedProperties.contains d.property) && !(origin == 0 && !d.important && hinted.contains d.property) then
        let key := ruleKey d.important origin rule.scope.isSome rule.layer specificity order
        -- a side shorthand kept whole (it mentions `var()`) stands for each of its sides
        let sides := if rule.usesVars && CssVars.mentions d.value then sidesOf d.property else []
        if sides.isEmpty then
          if (winners.get? d.property).all (fun old => lexLE old.1 key) then
            winners := winners.insert d.property (key,d)
        else
          for side in sides do
            if (winners.get? side).all (fun old => lexLE old.1 key) then winners := winners.insert side (key,d)
      order := order+1
  for d in ← declarations (attrValue n "style") do
    let key := inlineKey d.important order
    if d.usesVars then usesVars := true
    if CssValues.Logical.mentions d.property then usesLogical := true
    let sides := if CssVars.mentions d.value then sidesOf d.property else []
    if sides.isEmpty then
      if (winners.get? d.property).all (fun old => lexLE old.1 key) then winners := winners.insert d.property (key,d)
    else
      for side in sides do
        if (winners.get? side).all (fun old => lexLE old.1 key) then winners := winners.insert side (key,d)
    order := order+1
  let mut result := initial
  let mut chosen := winners.toList
  if usesVars then
    -- CSS Variables 1: the element's custom properties first (its own winning
    -- declarations over the inherited ones), then every other winner with its `var()`
    -- references replaced; one that is invalid at computed-value time is left out
    let own := chosen.filterMap fun (key,(_,d)) => if key.startsWith "--" then some (key,d.value) else none
    let vars := CssVars.resolve parent.vars own
    result := {result with vars}
    chosen := chosen.filterMap fun (key,(priority,d)) =>
      if key.startsWith "--" then none else (substituted vars key d).map fun d' => (key,(priority,d'))
  if usesLogical then
    -- CSS Logical 1 §4: a flow-relative property and the physical property it stands for
    -- in the element's flow are one property in the cascade. This profile lays out
    -- horizontal lines, so the flow is the element's direction: its own winning
    -- declaration, else the inherited one or the `dir` attribute.
    let rtl := match chosen.find? (·.1 == "direction") with
      | some (_,(_,d)) =>
        let v := (trim d.value).toLower
        if v == "rtl" then true else if v == "ltr" then false else initial.direction == .rtl
      | none => initial.direction == .rtl
    chosen := physicalWinners {rtl} chosen
  -- Font size precedes line-height and inheritance-sensitive dependent values.
  if let some (_,(_,d)) := chosen.find? (·.1 == "font-size") then
    -- `em`, `%`, `larger` and `smaller` in `font-size` are of the parent's font size (CSS
    -- Fonts 4 §2.5), not of the size the user agent gives the element: `h1 {font-size: 4em}`
    -- in a 16 px body is 64 px, not 4 × 32 px. A value that does not read keeps the user
    -- agent's size. (Until 2026-11-23 the base was the element's start, so every heading
    -- with an `em` or `%` size was twice as large, or as the user agent scales it.)
    let base := match wideSource parent initial d with
      | some _ => result
      | none => if (CssValues.specified "font-size" d.value).isSome || (apply result d).toOption.isSome
          then {result with fontSize := parent.fontSize} else result
    result := applyWinner parent initial base d
    -- the user agent's margins are in em of the element's own font size (`startMargin`); an
    -- author `margin` below still wins
    -- (only when the margins are still the user agent's: no presentational hint set them)
    let ua := startMargin n.lname initial.fontSize (insideList dom id)
    if html && result.fontSize != initial.fontSize && (let a := result.margin
        a.top == ua.top && a.right == ua.right && a.bottom == ua.bottom && a.left == ua.left) &&
        ua.top + ua.bottom > 0 then
      result := {result with margin := startMargin n.lname result.fontSize (insideList dom id)}
  for (key,(priority,d)) in chosen do
    if key != "font-size" then
      -- Inline SVG paint declarations stay with the existing SVG producer.
      -- External HTML paint rules are refused until that cascade is unified.
      if n.ns == some DOM.svgNS && priority[2]? == some 1 && !htmlProperties.contains key then pure ()
      else result := applyWinner parent initial result d
  -- A root or body never clips here: the window scrolls instead.
  if ["html","body"].contains n.lname then result := {result with clipOverflow := false}
  -- The children of a flex or grid container are its items: blockified.
  if parent.display.isFlex || parent.display.isGrid then result := {result with display := result.display.blockified}
  -- CSS 2.1 §9.7: an absolutely positioned or floated box is a block.
  if result.pos.isAbsolute || result.pos.float != .none then result := {result with display := result.display.blockified}
  let decoration := parent.decorationColor.orElse (fun _ => if result.underline then some result.color else none)
  return finishEffects parent {result with underline := decoration.isSome, decorationColor := decoration}

/-- The style of element `id` with every rule tried (`matchedRules`): the reference. -/
def computed (dom : Dom) (id : Nat) (rules : List Rule) (parent : Computed)
    (state : ElementState := {}) : Except String Computed :=
  computedFrom dom id (matchedRules dom id rules state) parent

/-- Reader text scaling is applied once after inheritance/cascade. Pixel sizes
are rounded to match the supplied-font raster contract; explicit line heights
scale too. Geometry, SVG viewports and DOM source are unchanged. -/
def Computed.scaleText (s : Computed) (scale : Float) : Computed :=
  if scale == 1 then s else
  let size := max 1 (s.fontSize*scale).round
  let height := (s.lineHeightFactor.map (size*·)).getD (s.lineHeight*scale)
  {s with fontSize := size, lineHeight := height}

/-- The style of node `id` under the style `parent` of its parent: an element's cascade
(`computedFrom`); any other node, and an SVG element inside SVG, takes what is inherited.
The step of `computeAllWith` and of `restyleWith`. -/
def styleOfNode (matchesOf : Nat → List Match) (dom : Dom) (id : Nat) (parent : Computed) : Except String Computed :=
  let n := dom.get id
  let svgDescendant := n.ns == some DOM.svgNS && (n.parent.map (fun p => (dom.get p).ns == some DOM.svgNS)).getD false
  if n.type == .element && !svgDescendant then computedFrom dom id (matchesOf id) parent else pure {parent with
    display := .inline, width := .auto, height := .auto,
    margin := {}, padding := {}, background := none, backgroundGradient := none, clipOverflow := false,
    columnCount := none, columnWidth := none,
    borderStyles := .all .none, borderWidth := ⟨3,3,3,3⟩, borderColors := .all .current,
    autoMarginLeft := false, autoMarginRight := false, unicodeBidi := .normal,
    autoMarginTop := false, autoMarginBottom := false, align := {}, flex := {},
        -- a text node keeps what its text is set by
        pos := {nowrap := parent.pos.nowrap, textTransform := parent.pos.textTransform,
                lineBreak := parent.pos.lineBreak}}

/-- Visit parents before children, using a work list and bounded arena size.
`matchesOf id` are the rules that match element `id`, in sheet order. `root` is the
document styled: the page's (node 0), or the document of a frame in the same arena. -/
def computeAllWith (matchesOf : Nat → List Match) (dom : Dom) (textScale : Float := 1) (root : Nat := 0) : Except String (Array Computed) := do
  if !textScale.isFinite || textScale < 0.5 then throw "text scale must be finite and at least 50%"
  let mut pending := [root]
  let mut styles := Array.replicate dom.size ({} : Computed)
  for _ in [:dom.size+1] do
    match pending with
    | [] => return styles.map (·.scaleText textScale)
    | id::rest =>
      let n := dom.get id
      let parent := (n.parent.bind (styles[·]?)).getD {}
      let style ← styleOfNode matchesOf dom id parent
      styles := styles.set! id style
      pending := n.kids.toList ++ rest
  throw "DOM style traversal exceeds arena bound"

/-! ### Styles again for part of the tree

A write of an element's `style` attribute, or a new animated value of an element,
changes the declarations of that element alone: the styles that can differ are its own
and those of its descendants (by inheritance). `restyleWith` gives the styles of the
whole tree from the styles before the change by styling those subtrees again, so a
script that writes one element's style and reads a computed value pays for one subtree,
not for the document. This holds only when no rule reads the `style` attribute
(`readsStyleAttribute`) and the text scale is 1 (`computeAllWith` scales at its end);
the caller (`WebDocument.measure`) checks both. -/

/-- The styles `base` with the subtrees of `roots` styled again, parents before children
(the step of `computeAllWith`). `base` must be the styles of the same tree with text
scale 1, or of that tree before nodes were added to its arena: a node `base` has no
style for takes the style of a node no cascade reaches (as `computeAllWith` leaves a node
that is in no document), until a root's subtree styles it. A root inside another root's
subtree is styled twice, last with its new parent. -/
def restyleWith (matchesOf : Nat → List Match) (dom : Dom) (base : Array Computed) (roots : List Nat) :
    Except String (Array Computed) :=
  if base.size > dom.size then .error "styles of another tree"
  else
  -- nodes made since `base` (the arena only grows)
  let base := if base.size < dom.size then base ++ Array.replicate (dom.size - base.size) ({} : Computed) else base
  if roots.isEmpty then .ok base
  else Id.run do
    let mut pending := roots
    let mut styles := base
    for _ in [:(dom.size + 1) * (roots.length + 1)] do
      match pending with
      | [] => return .ok styles
      | id::rest =>
        let n := dom.get id
        let parent := (n.parent.bind (styles[·]?)).getD {}
        match styleOfNode matchesOf dom id parent with
        | .ok style =>
          styles := styles.set! id style
          pending := n.kids.toList ++ rest
        | .error e => return .error e
    return .error "DOM style traversal exceeds arena bound"

/-- Kind: correctness (the empty case). Says: with no subtree to style again, the styles
are the ones given, for every tree and rule set. Does not say: that the styles of the
subtrees styled again are those of the whole cascade (`computeAllWith`) after the change;
that is tested on pages (`Animation.Computed`), not proved. -/
theorem restyleWith_nil (matchesOf : Nat → List Match) (dom : Dom) (base : Array Computed)
    (h : base.size = dom.size) : restyleWith matchesOf dom base [] = .ok base := by
  simp [restyleWith, h]

/-- Kind: totality of the answer. Says: with no subtree to style again, the styles of an
arena that grew are the styles before with one style for each new node, so the answer
has a style for every node. Does not say: more of the new nodes' styles than that they
are those of a node no cascade reached. -/
theorem restyleWith_nil_size (matchesOf : Nat → List Match) (dom : Dom) (base : Array Computed)
    (h : base.size ≤ dom.size) :
    (restyleWith matchesOf dom base []).toOption.map (·.size) = some dom.size := by
  have h1 : ¬ (base.size > dom.size) := by omega
  by_cases h2 : base.size < dom.size
  · have hs : (base ++ Array.replicate (dom.size - base.size) ({} : Computed)).size = dom.size := by
      rw [Array.size_append, Array.size_replicate]; omega
    simp [restyleWith, h1, h2, Except.toOption, hs]
  · have h3 : base.size = dom.size := by omega
    simp [restyleWith, h3, Except.toOption]

/-- A selector of `sels` tests the attribute `name`, also inside `:not()`, `:is()` and
`:nth-child(… of …)`. A work list, bounded: past the bound the answer is yes. -/
def selectorsReadAttr (name : String) (sels : List DOM.Selectors.Complex) : Bool := Id.run do
  let mut pending := sels
  for _ in [:4096] do
    match pending with
    | [] => return false
    | .mk parts :: rest =>
      let mut more := rest
      for (_, simples) in parts do
        for s in simples do
          match s with
          | .attr _ n _ _ _ _ => if n.toLower == name then return true
          | .nth _ _ _ (some inner) => more := inner ++ more
          | .not inner => more := inner ++ more
          | .is inner => more := inner ++ more
          | .has inner => more := inner ++ more
          | _ => pure ()
      pending := more
  return true

/-- A rule's selector tests the `style` attribute: a write of that attribute can then
change which rules match, and the styles are not those of `restyleWith`. -/
def readsStyleAttribute (rules : List Rule) : Bool :=
  rules.any fun r => r.selectors.any fun s =>
    match s.complex with
    | some c => selectorsReadAttr "style" [c]
    | none => false

/-- A selector of `sels` has `:has()`, also inside `:not()`, `:is()` and
`:nth-child(… of …)`. A work list, bounded: past the bound the answer is yes. -/
def selectorsUseHas (sels : List DOM.Selectors.Complex) : Bool := Id.run do
  let mut pending := sels
  for _ in [:4096] do
    match pending with
    | [] => return false
    | .mk parts :: rest =>
      let mut more := rest
      for (_, simples) in parts do
        for s in simples do
          match s with
          | .has _ => return true
          -- a `:has()` compound worked out against a document (`resolveHas`): as `:has()`
          | .anchors _ => return true
          | .nth _ _ _ (some inner) => more := inner ++ more
          | .not inner => more := inner ++ more
          | .is inner => more := inner ++ more
          | _ => pure ()
      pending := more
  return true

/-- No selector of the rules has `:has()`. The matching of an element then reads, of the
other elements, only its ancestors, the earlier siblings of itself and of its ancestors,
and (for `:nth-child(… of …)`) the siblings of those: an attribute of an element is read
only for the elements of its parent's subtree. A write of an element's `class` can then
change the rules that match in that subtree and nowhere else, so the styles after it are
those of `restyleWith` from the parent (`Hosts.Page.Reads.wrote`). -/
def attributesReachParentOnly (rules : List Rule) : Bool :=
  !rules.any fun r => r.selectors.any fun s =>
    match s.complex with
    | some c => selectorsUseHas [c]
    | none => false

/-! ### Animated values in the cascade

CSS Cascade 4 §6.1: animation declarations override the author's normal declarations
(also those of the `style` attribute) and are overridden by `!important` ones;
transition declarations override everything. The animated values of an element
(`ElementState.animated`) are one match of origin 2 for its animations and one of origin
3, marked important, for its transitions: the keys of `computedFrom` then order them as
the cascade says (an animation's key is `[0, 5, …]`, above the `style` attribute's
`[0, 3, …]` and below any `[1, …]`; a transition's is `[1, 6, …]`). -/

/-- The animated values as matches, by element. -/
def animatedIndex (animated : List (Nat × String × String × Bool)) : Std.HashMap Nat (List Match) :=
  let any : Selector := { parts := [], specificity := (0,0,0) }
  animated.foldl (fun m (id, property, value, transition) =>
    let old := m.getD id []
    let origin := if transition then 3 else 2
    -- as the declarations of a style sheet: a shorthand of the profile is its longhands
    -- (a custom property keeps its name as written)
    let ds : List Declaration :=
      if property.startsWith "--" then [⟨property, value, transition⟩]
      else match declarations (property ++ ":" ++ value) with
        | .ok ds => if ds.isEmpty then [⟨property, value, transition⟩] else ds.map fun d => { d with important := transition }
        | .error _ => [⟨property, value, transition⟩]
    let (mine, others) := old.partition (·.1 == origin)
    let rule : Rule := match mine with
      | (_, r, _) :: _ => { r with declarations := r.declarations ++ ds }
      | [] => { selectors := [any], declarations := ds }
    m.insert id (others ++ [(origin, rule, [any])])) {}

/-- `matchesOf` with the animated values of `state` after the rules of each element. A
state with none is `matchesOf` itself: no table is built. -/
def withAnimated (state : ElementState) (matchesOf : Nat → List Match) : Nat → List Match :=
  if state.animated.isEmpty then matchesOf else
  -- the values by element once; an element's are read as declarations when it is styled
  -- (a page with many animations pays that for the elements a cascade visits)
  let groups : Std.HashMap Nat (List (Nat × String × String × Bool)) :=
    state.animated.foldl (fun m item => m.insert item.1 (item :: m.getD item.1 [])) {}
  fun id => match groups[id]? with
    | some items => matchesOf id ++ (animatedIndex items.reverse).getD id []
    | none => matchesOf id

/-- With no animated value the cascade is that of the rules alone. -/
theorem withAnimated_none (state : ElementState) (matchesOf : Nat → List Match) (h : state.animated = []) :
    withAnimated state matchesOf = matchesOf := by
  simp [withAnimated, h]

/-- The styles of every node with every rule tried for every element: the reference. -/
def computeAllLinear (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  computeAllWith (withAnimated state fun id => matchedRules dom id rules state) dom textScale

/-- The styles of every node: the element keys read once, the rules in buckets. -/
def computeAll (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  let ix := RuleIndex.build rules
  let ks := ElemKeys.of dom
  computeAllWith (withAnimated state fun id => ix.matched (ks.get dom) dom id state) dom textScale

/-- The styles on a page with shadow trees, laid out on `dom` (its flat tree): the element
keys read once, the rules in buckets per tree. -/
def computeAllIn (ts : TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  let ix := ScopedIndex.build rules
  let ks := ElemKeys.of ts.tree
  computeAllWith (withAnimated state fun id => ix.matched (ks.get ts.tree) ts id state) dom textScale

/-- The reference for `computeAllIn`: every rule tried for every element. -/
def computeAllInLinear (ts : TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  computeAllWith (withAnimated state fun id => matchedRulesIn ts id rules state) dom textScale

/-- The `:has()` argument lists in the compounds of a complex selector (not inside other
functional pseudo-classes). -/
def hasLists : DOM.Selectors.Complex → List (List DOM.Selectors.Complex)
  | .mk parts => parts.flatMap fun (_, c) => c.filterMap fun s => match s with
    | .has l => some l
    | _ => none

/-- A selector with a `:has()` whose relative selectors no element of the document matches
even without their anchor can match nothing: such a `:has()` is false everywhere. -/
def hasNoMatch (dom : Dom) (l : List DOM.Selectors.Complex) : Bool :=
  !((List.range dom.size).any fun k =>
    (dom.get k).type == .element && l.any fun c => DOM.Selectors.matchComplex dom none DOM.Selectors.matchFuel k c)

/-- The rules without the selectors that a `:has()` false everywhere keeps from matching
(one pass over the document for each `:has()`), so that matching does not search a
large subtree once for each element (selectors/invalidation/has-complexity.html). Rules
with no `:has()` are as they were, and a page with none pays one test per selector. -/
def pruneHas (dom : Dom) (rules : List Rule) : List Rule :=
  if !(rules.any fun r => r.selectors.any fun sel => (sel.complex.map (fun c => !(hasLists c).isEmpty)).getD false) then rules
  else rules.filterMap fun r =>
    let sels := r.selectors.filter fun sel => match sel.complex with
      | some c => !((hasLists c).any (hasNoMatch dom))
      | none => true
    if sels.isEmpty then none else some { r with selectors := sels }

/-- A complex selector with each compound that has a `:has()` matched once against every
element of the document: the compound becomes its other simple selectors and the elements
where it held (`Simple.anchors`), so that matching an element does not search a subtree
again (selectors/invalidation/has-complexity.html: a `main:has(span) span` rule over many
spans). One pass over the document for each such compound. -/
def resolveHasIn (dom : Dom) : Nat → DOM.Selectors.Complex → DOM.Selectors.Complex
  | 0, c => c
  | fuel + 1, .mk parts => .mk (parts.map fun (comb, simples) =>
      -- the selector lists inside `:is()`, `:not()`, `:where()` and `:nth-child(of ...)`
      -- first: a `:has()` there is anchored at the element the inner compound is tried on
      let simples := simples.map fun (s : DOM.Selectors.Simple) => match s with
        | .is l => .is (l.map (resolveHasIn dom fuel))
        | .not l => .not (l.map (resolveHasIn dom fuel))
        | .nth k a b (some l) => .nth k a b (some (l.map (resolveHasIn dom fuel)))
        | s => s
      let isHas := fun (s : DOM.Selectors.Simple) => match s with
        | .has _ => true
        | _ => false
      if !(simples.any isHas) then (comb, simples)
      else
        let ids := ((List.range dom.size).filter fun k =>
          DOM.Selectors.matchCompound dom none DOM.Selectors.matchFuel k simples).toArray
        (comb, simples.filter (!isHas ·) ++ [.anchors ids]))

/-- Whether a selector has a `:has()`, at the top or inside `:is()`, `:not()`, `:where()` or
an `of` list (the nesting read to `fuel` levels). -/
def mentionsHas : Nat → DOM.Selectors.Complex → Bool
  | 0, _ => false
  | fuel + 1, .mk parts => parts.any fun (_, simples) => simples.any fun s => match s with
    | .has _ => true
    | .is l | .not l | .nth _ _ _ (some l) => l.any (mentionsHas fuel)
    | _ => false

/-- The rules with their `:has()` compounds resolved against the document (`resolveHasIn`);
rules with no `:has()` are as they were. -/
def resolveHas (dom : Dom) (rules : List Rule) : List Rule :=
  if !(rules.any fun r => r.selectors.any fun sel => (sel.complex.map (mentionsHas 16)).getD false) then rules
  else rules.map fun r =>
    { r with selectors := r.selectors.map fun sel => match sel.complex with
      | some c => if !mentionsHas 16 c then sel else { sel with complex := some (resolveHasIn dom 16 c) }
      | none => sel }

#guard (match DOM.Selectors.parse ":is(main:has(span)) .s" with
  | some [c] =>
    let d := DOM.parseHtmlDocument "<main><div><span></span></div><p class=s></p></main><p class=s></p>"
    let c' := resolveHasIn d 16 c
    ((List.range d.size).filter fun k => DOM.Selectors.matchComplex d none DOM.Selectors.matchFuel k c') ==
      ((List.range d.size).filter fun k => DOM.Selectors.matchComplex d none DOM.Selectors.matchFuel k c)
  | _ => false)
#guard (match DOM.Selectors.parse "main:has(span) .s" with
  | some [c] =>
    let d := DOM.parseHtmlDocument "<main><div><span></span></div><p class=s></p></main><p class=s></p>"
    let c' := resolveHasIn d 16 c
    ((List.range d.size).filter fun k => DOM.Selectors.matchComplex d none DOM.Selectors.matchFuel k c') ==
      ((List.range d.size).filter fun k => DOM.Selectors.matchComplex d none DOM.Selectors.matchFuel k c)
  | _ => false)

/-- A rule list with no `:has()` is left as it is. -/
theorem resolveHas_plain (dom : Dom) (rules : List Rule)
    (h : (rules.any fun r => r.selectors.any fun sel => (sel.complex.map (mentionsHas 16)).getD false) = false) :
    resolveHas dom rules = rules := by
  simp [resolveHas, h]

/-- Where each element is among its element siblings, for the whole document in one pass
over every child list: its place from the start and from the end, and among the siblings of
its type from the start and from the end (0 for a node that is no element or has no
parent). -/
structure SibPlaces where
  first : Array Nat
  last : Array Nat
  typeFirst : Array Nat
  typeLast : Array Nat

def SibPlaces.of (dom : Dom) : SibPlaces := Id.run do
  let n := dom.size
  let mut first := Array.replicate n 0
  let mut last := Array.replicate n 0
  let mut typeFirst := Array.replicate n 0
  let mut typeLast := Array.replicate n 0
  for p in [0:n] do
    let kids := ((dom.get p).kids.filter fun c => (dom.get c).type == .element)
    let m := kids.size
    let mut seen : Std.HashMap (String × Option String) Nat := {}
    for h : i in [0:m] do
      let c := kids[i]
      first := first.set! c (i + 1)
      last := last.set! c (m - i)
      let key := ((dom.get c).lname, (dom.get c).ns)
      let t := (seen.getD key 0) + 1
      seen := seen.insert key t
      typeFirst := typeFirst.set! c t
    -- the places among the siblings of each type from the end: the counts less the place
    for h : i in [0:m] do
      let c := kids[i]
      let key := ((dom.get c).lname, (dom.get c).ns)
      typeLast := typeLast.set! c ((seen.getD key 0) + 1 - typeFirst[c]!)
  return { first, last, typeFirst, typeLast }

/-- The elements, ascending, whose places satisfy `ok` (one pass over the nodes). -/
def SibPlaces.where_ (sp : SibPlaces) (ok : Nat → Bool) : Array Nat :=
  ((List.range sp.first.size).filter fun k => sp.first[k]! != 0 && ok k).toArray

/-- A structural pseudo-class (`:first-child` ... `:only-of-type`, `:nth-child(An+B)` and its
kin without `of`) as the elements where it holds, worked out from the sibling places;
`none` for any other simple selector. -/
def structuralAnchors (sp : SibPlaces) : DOM.Selectors.Simple → Option (Array Nat)
  | .pseudo "first-child" => some (sp.where_ fun k => sp.first[k]! == 1)
  | .pseudo "last-child" => some (sp.where_ fun k => sp.last[k]! == 1)
  | .pseudo "only-child" => some (sp.where_ fun k => sp.first[k]! == 1 && sp.last[k]! == 1)
  | .pseudo "first-of-type" => some (sp.where_ fun k => sp.typeFirst[k]! == 1)
  | .pseudo "last-of-type" => some (sp.where_ fun k => sp.typeLast[k]! == 1)
  | .pseudo "only-of-type" => some (sp.where_ fun k => sp.typeFirst[k]! == 1 && sp.typeLast[k]! == 1)
  | .nth kind a b none =>
    let pos := fun (k : Nat) => match kind with
      | .child => sp.first[k]! | .lastChild => sp.last[k]!
      | .ofType => sp.typeFirst[k]! | .lastOfType => sp.typeLast[k]!
    some (sp.where_ fun k => DOM.Selectors.nthOk a b (pos k))
  | _ => none

/-- A complex selector with its structural pseudo-classes, also inside `:is()`, `:not()`,
`:where()` and `of` lists, as the elements where they hold (`Simple.anchors`): matching
then looks an element up instead of reading its parent's child list each time. -/
def resolveStructuralIn (sp : Thunk SibPlaces) : Nat → DOM.Selectors.Complex → DOM.Selectors.Complex
  | 0, c => c
  | fuel + 1, .mk parts => .mk (parts.map fun (comb, simples) =>
      (comb, simples.map fun (s : DOM.Selectors.Simple) => match s with
        | .is l => .is (l.map (resolveStructuralIn sp fuel))
        | .not l => .not (l.map (resolveStructuralIn sp fuel))
        | .nth k a b (some l) => .nth k a b (some (l.map (resolveStructuralIn sp fuel)))
        | s => match structuralAnchors sp.get s with
          | some ids => .anchors ids
          | none => s))

/-- Whether a selector has a structural pseudo-class (the nesting read to `fuel` levels). -/
def mentionsStructural : Nat → DOM.Selectors.Complex → Bool
  | 0, _ => false
  | fuel + 1, .mk parts => parts.any fun (_, simples) => simples.any fun s => match s with
    | .pseudo n => ["first-child", "last-child", "only-child", "first-of-type", "last-of-type", "only-of-type"].contains n
    | .nth _ _ _ none => true
    | .is l | .not l | .nth _ _ _ (some l) => l.any (mentionsStructural fuel)
    | _ => false

/-- The rules with their structural pseudo-classes worked out for the document (one pass
over its child lists, made only when a rule has one); other rules are as they were. -/
def resolveStructural (dom : Dom) (rules : List Rule) : List Rule :=
  if !(rules.any fun r => r.selectors.any fun sel => (sel.complex.map (mentionsStructural 16)).getD false) then rules
  else
    let sp : Thunk SibPlaces := Thunk.mk fun _ => SibPlaces.of dom
    rules.map fun r =>
      { r with selectors := r.selectors.map fun sel => match sel.complex with
        | some c => if !mentionsStructural 16 c then sel else { sel with complex := some (resolveStructuralIn sp 16 c) }
        | none => sel }

/-- The rules as a document with no shadow tree matches them: a `:has()` nothing satisfies
dropped (`pruneHas`), each `:has()` compound and each structural pseudo-class worked out
once for the document (`resolveHas`, `resolveStructural`). -/
def forDocument (dom : Dom) (rules : List Rule) : List Rule :=
  resolveStructural dom (resolveHas dom (pruneHas dom rules))

#guard ["li:first-child", "li:last-child", "li:only-child", "p:first-of-type", "p:last-of-type", "span:only-of-type",
    "li:nth-child(2n+1)", "li:nth-last-child(2)", "p:nth-of-type(2)", "p:nth-last-of-type(1)", ":not(:first-child) > span",
    "ul > :is(li:last-child, p:first-of-type)"].all fun t =>
  match DOM.Selectors.parse t with
  | some [c] =>
    let d := DOM.parseHtmlDocument "<ul> <li>a</li> x <li>b</li><p>c</p> <li>d</li><p>e<span>s</span></p></ul><div><span>t</span><b>u</b></div>"
    let c' := resolveStructuralIn (Thunk.mk fun _ => SibPlaces.of d) 16 c
    ((List.range d.size).filter fun k => DOM.Selectors.matchComplex d none DOM.Selectors.matchFuel k c') ==
      ((List.range d.size).filter fun k => DOM.Selectors.matchComplex d none DOM.Selectors.matchFuel k c)
  | _ => false

/-- A rule list with no structural pseudo-class is left as it is. -/
theorem resolveStructural_plain (dom : Dom) (rules : List Rule)
    (h : (rules.any fun r => r.selectors.any fun sel => (sel.complex.map (mentionsStructural 16)).getD false) = false) :
    resolveStructural dom rules = rules := by
  simp [resolveStructural, h]

/-- `forDocument` for the tree the rules are matched on: the page's, or with shadow trees the
tree of the scope (`TreeScope.tree`, where complex selectors are matched with no scope
element, as `resolveHas` and `resolveStructural` match them); `:has()` that nothing in the
page satisfies is dropped against the page as before. -/
def forTree (treeScope : Option TreeScope) (dom : Dom) (rules : List Rule) : List Rule :=
  match treeScope with
  | none => forDocument dom rules
  | some ts => resolveStructural ts.tree (resolveHas ts.tree (pruneHas dom rules))

/-- `computeAll` for a page with no shadow tree; `computeAllIn` for one with shadow trees. -/
def computeFor (treeScope : Option TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  match treeScope with
  | none => computeAll dom (forDocument dom rules) textScale state
  | some ts => computeAllIn ts dom (forTree treeScope dom rules) textScale state

/-- The buckets give the styles of the plain loop wherever they give its matches. -/
theorem computeAll_eq_linear (dom : Dom) (rules : List Rule) (textScale : Float) (state : ElementState)
    (h : ∀ id, (RuleIndex.build rules).matched ((ElemKeys.of dom).get dom) dom id state = matchedRules dom id rules state) :
    computeAll dom rules textScale state = computeAllLinear dom rules textScale state := by
  unfold computeAll computeAllLinear
  simp only []
  rw [show (fun id => (RuleIndex.build rules).matched ((ElemKeys.of dom).get dom) dom id state) =
    (fun id => matchedRules dom id rules state) from funext h]

/-- Scoped buckets give the styles of the plain loop wherever they give its matches. -/
theorem computeAllIn_eq_linear (ts : TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float) (state : ElementState)
    (h : ∀ id, (ScopedIndex.build rules).matched ((ElemKeys.of ts.tree).get ts.tree) ts id state = matchedRulesIn ts id rules state) :
    computeAllIn ts dom rules textScale state = computeAllInLinear ts dom rules textScale state := by
  unfold computeAllIn computeAllInLinear
  simp only []
  rw [show (fun id => (ScopedIndex.build rules).matched ((ElemKeys.of ts.tree).get ts.tree) ts id state) =
    (fun id => matchedRulesIn ts id rules state) from funext h]

/-- With no shadow tree, nothing about the cascade differs (but for the selectors whose
`:has()` nothing satisfies, `pruneHas`, and the `:has()` compounds worked out once,
`resolveHas`). -/
theorem computeFor_none (dom : Dom) (rules : List Rule) (textScale : Float) (state : ElementState) :
    computeFor none dom rules textScale state = computeAll dom (forDocument dom rules) textScale state := rfl

/-- A page whose rules have no `:has()` is matched against its rules as they are. -/
theorem pruneHas_plain (dom : Dom) (rules : List Rule)
    (h : (rules.any fun r => r.selectors.any fun sel => (sel.complex.map (fun c => !(hasLists c).isEmpty)).getD false) = false) :
    pruneHas dom rules = rules := by
  simp [pruneHas, h]

end L4Factoidal.Rendering.CSS

namespace L4Factoidal.Rendering.CSS
/-- `CSS.supports(property, value)` (CSS Conditional 3 §8.1): the declaration parses under
the grammar of the property table (`CssValues.supports`, the function that the style
declaration block and computed values use). Until 2026-11-14 this answered for the layout
profile alone (`apply`); it now answers for the parser, as the standard says, so a
property that parses and is not yet laid out is supported here. -/
def supportsDeclaration (property value : String) : Bool :=
  CssValues.supports (property.trimAscii.toString) value

/-! ### Tests: a dialog that is not open and a popover that is not showing are not rendered -/

private def hiddenDoc : DOM.Dom :=
  DOM.parseHtmlDocument "<dialog>x</dialog><dialog open>y</dialog><div popover>z</div><div>w</div>"

/-- The initial `display` of the nodes named `lname`, in tree order: `true` for `none`. -/
private def displayNone (d : DOM.Dom) (lname : String) : List (Option Bool) :=
  (d.nodes.toList.zipIdx.filter fun (n, _) => n.lname == lname).map fun (_, i) =>
    (computedFrom d i [] {}).toOption.map (·.display == .none)

#guard displayNone hiddenDoc "dialog" == [some true, some false]
#guard displayNone hiddenDoc "div" == [some true, some false]
-- a showing popover (`Node.states` bit 1) is rendered
#guard displayNone ({ nodes := hiddenDoc.nodes.map fun n => if n.lname == "div" then { n with states := 1 } else n } : DOM.Dom) "div" ==
  [some false, some false]

/-- The computed style `s` with one more declaration applied, as the cascade applies it
(`apply`); none when the profile does not read the declaration. For the computed value
of a keyframe's specified value in an element's context (`Rendering.Animation`). -/
def applyDeclaration (s : Computed) (property value : String) : Option Computed :=
  match declarations (property ++ ":" ++ value) with
  | .ok ds => if ds.isEmpty then none else ds.foldlM (fun acc d => (apply acc d).toOption) s
  | .error _ => none

-- `background-image: url(...)` (issue 704): the first layer's URL, case kept, quoted or not.
#guard firstUrl? "url(a.png)" == some "a.png"
#guard firstUrl? "URL( 'Images/B.PNG' ) no-repeat" == some "Images/B.PNG"
#guard firstUrl? "url(\"x y.png\"), linear-gradient(red, blue)" == some "x y.png"
#guard firstUrl? "linear-gradient(red, blue)" == none
#guard firstUrl? "url(a.png" == none
#guard (applyDeclaration ({} : Computed) "background-image" "url(/i/a.png)").map (·.backgroundImage) == some (some "/i/a.png")
#guard (applyDeclaration ({} : Computed) "background-image" "none").map (·.backgroundImage) == some none
#guard match applyDeclaration ({} : Computed) "background-size" "50% auto" with
  | some style =>
    match style.backgroundSize with
    | BackgroundSize.dimensions (Length.percent value) Length.auto => value == 0.5
    | _ => false
  | none => false
#guard (applyDeclaration ({} : Computed) "background-repeat" "repeat-y").map (·.backgroundRepeat) == some (false,true)
#guard ((applyDeclaration ({} : Computed) "background-position" "right 10px bottom 5px").bind
  (fun s => s.backgroundPositionX.resolve 80)) == some 70
#guard ((applyDeclaration ({} : Computed) "background-position" "right 10px bottom 5px").bind
  (fun s => s.backgroundPositionY.resolve 30)) == some 25
#guard ((applyDeclaration ({} : Computed) "background-position-x" "center, left").bind
  (fun s => s.backgroundPositionX.resolve (-20))) == some (-10)
#guard ((applyDeclaration ({} : Computed) "background-position" "min(0%, 100%) max(0%, 100%)").map
  (fun s => (s.backgroundPositionX.resolve (-50),s.backgroundPositionY.resolve (-50)))) == some (some (-50),some 0)
#guard ((applyDeclaration ({} : Computed) "background-position-y" "max(5px, 50%)").bind
  (fun s => s.backgroundPositionY.resolve 40)) == some 20
#guard ((applyDeclaration ({} : Computed) "background-position-x" "calc(25% + 10vw)").bind
  (fun s => (s.backgroundPositionX.atViewport 200 100).resolve 40)) == some 30
#guard (applyDeclaration ({} : Computed) "background-image" "linear-gradient(red, blue), url(a.png)").map (·.backgroundImage) == some none

-- Border widths in every length unit and keyword (`borderWidthPx`; WPT css/CSS2/borders).
private def borderLeft (property value : String) : Option Float :=
  (applyDeclaration ({} : Computed) property value).map (·.borderWidth.left)
#guard borderLeft "border-left-width" "1in" == some 96
#guard borderLeft "border-left-width" "2.54cm" == some 96
#guard borderLeft "border-left-width" "25.4mm" == some 96
#guard borderLeft "border-left-width" "72pt" == some 96
#guard borderLeft "border-left-width" "+6pc" == some 96
#guard borderLeft "border-left-width" "1em" == some 16
#guard borderLeft "border-left-width" "-0pt" == some 0
#guard borderLeft "border-left-width" "thin" == some 1
#guard borderLeft "border-left-width" "thick" == some 5
#guard borderLeft "border-left-width" "7px" == some 7
#guard borderLeft "border-left-width" "-1pt" == none
#guard borderLeft "border" "1in solid red" == some 96
#guard borderLeft "border-width" "1pt 2pt 3pt 6pt" == some 8

end L4Factoidal.Rendering.CSS
