import L4Factoidal.Rendering.BoxAlign
import L4Factoidal.Rendering.Content
import L4Factoidal.Rendering.BoxTransform

/-! Computed values of positioning, floats and box sizing (CSS Positioned Layout 3, CSS 2.1
§9.5, CSS Sizing 3 §3.3): `Computed.pos`. Values are read through the property table, as
in `BoxAlign`. -/
namespace L4Factoidal.Rendering.CSS

/-- `position` (CSS Positioned Layout 3 §2). -/
inductive Position where
  | static | relative | absolute | fixed | sticky
  deriving Repr, BEq

/-- `float` (CSS 2.1 §9.5.1); the logical values follow the direction at layout. -/
inductive FloatSide where
  | none | left | right | inlineStart | inlineEnd
  deriving Repr, BEq

/-- `clear` (CSS 2.1 §9.5.2). -/
inductive Clear where
  | none | left | right | both | inlineStart | inlineEnd
  deriving Repr, BEq

/-- `writing-mode` (CSS Writing Modes 4 §3.2; inherited): the block axis is vertical, or
horizontal from the right (`vertical-rl`, `sideways-rl`) or from the left (`vertical-lr`,
`sideways-lr`). Block and inline layout are horizontal in this profile; flex containers
read it for their axes (`Layout.flexAxes`). -/
inductive WritingMode where
  | horizontalTb | verticalRl | verticalLr
  deriving Repr, BEq

/-- The side of an anchor box that an `anchor()` function names (CSS Anchor Positioning 1
§3.2 `<anchor-side>`): a physical side, a flow-relative one (of the containing block's
writing mode, or of the box's own with `self-`), `inside` or `outside` (the same side as the
inset, or the opposite one), `center`, or a fraction from the start side. -/
inductive AnchorSide where
  | top | right | bottom | left | start | end_ | selfStart | selfEnd | inside | outside | center
  | fraction (f : Float)
  deriving Repr, BEq

/-- An `anchor()` function in an inset (CSS Anchor Positioning 1 §3.2): the anchor name
(`none`: the box's default anchor, `position-anchor`), the side, and the fallback length
when no anchor is found (`none`: the inset is `auto`). -/
structure AnchorRef where
  name : Option String := none
  side : AnchorSide := .center
  fallback : Option Length := none
  deriving Repr

/-- The same anchor reference. -/
def AnchorRef.same (a b : AnchorRef) : Bool :=
  a.name == b.name && a.side == b.side &&
    (match a.fallback, b.fallback with
     | some x, some y => x.same y
     | none, none => true
     | _, _ => false)

def AnchorRef.sameOpt : Option AnchorRef → Option AnchorRef → Bool
  | some a, some b => a.same b
  | none, none => true
  | _, _ => false

/-- An `<anchor-side>` keyword. -/
def anchorSideOf : String → Option AnchorSide
  | "top" => some .top | "right" => some .right | "bottom" => some .bottom | "left" => some .left
  | "start" => some .start | "end" => some .end_ | "self-start" => some .selfStart
  | "self-end" => some .selfEnd | "inside" => some .inside | "outside" => some .outside
  | "center" => some .center
  | _ => none

/-- The `anchor()` of an inset's canonical value (CSS Anchor Positioning 1 §3.2): an
optional anchor name and a side, and an optional length-percentage fallback (read for
`property`); `none` for any other value. A fallback that is itself an `anchor()` is not
read: the inset is then `auto` when the anchor is missing. -/
def anchorOf (fontSize : Float) (property v : String) : Option AnchorRef :=
  match CssValues.stripWs (CssValues.CV.parse v) with
  | [.fn fname args] =>
    if CssValues.lower fname != "anchor" then none else
    match CssValues.splitCommas args with
    | g :: rest =>
      let parts := CssValues.stripWs g
      let name := parts.findSome? fun c => match c with
        | .tok (.ident k) => if k.startsWith "--" then some k else none
        | _ => none
      let side := parts.findSome? fun c => match c with
        | .tok (.ident k) => if k.startsWith "--" then none else anchorSideOf (CssValues.lower k)
        | .tok (.pct x) => some (.fraction (ratToFloat x / 100))
        | _ => none
      side.map fun side =>
        let fallback := match rest with
          | [f] => tableLength fontSize property (CssValues.serialize (CssValues.stripWs f))
          | _ => none
        { name, side, fallback }
    | [] => none
  | _ => none

/-- A `position-area` keyword (CSS Anchor Positioning 1 §3.1.1) as its axis (`some true`
horizontal, `some false` vertical, `none` either) and its tracks, in a horizontal-tb,
left-to-right containing block. -/
def areaKeyword (k : String) : Option (Option Bool × Nat × Nat) :=
  let x := fun (a b : Nat) => some (some true, a, b)
  let y := fun (a b : Nat) => some (some false, a, b)
  let e := fun (a b : Nat) => some (none, a, b)
  match k with
  | "left" | "x-start" | "self-x-start" | "inline-start" | "self-inline-start" => x 0 1
  | "right" | "x-end" | "self-x-end" | "inline-end" | "self-inline-end" => x 2 3
  | "span-left" | "span-x-start" | "span-self-x-start" | "span-inline-start" | "span-self-inline-start" => x 0 2
  | "span-right" | "span-x-end" | "span-self-x-end" | "span-inline-end" | "span-self-inline-end" => x 1 3
  | "top" | "y-start" | "self-y-start" | "block-start" | "self-block-start" => y 0 1
  | "bottom" | "y-end" | "self-y-end" | "block-end" | "self-block-end" => y 2 3
  | "span-top" | "span-y-start" | "span-self-y-start" | "span-block-start" | "span-self-block-start" => y 0 2
  | "span-bottom" | "span-y-end" | "span-self-y-end" | "span-block-end" | "span-self-block-end" => y 1 3
  | "start" | "self-start" => e 0 1
  | "end" | "self-end" => e 2 3
  | "span-start" | "span-self-start" => e 0 2
  | "span-end" | "span-self-end" => e 1 3
  | "center" => e 1 2
  | "span-all" => e 0 3
  | _ => none

/-- The tracks of a `position-area` value (horizontal, vertical): one keyword of an axis spans
all of the other; two keywords of no fixed axis are the block axis, then the inline one. -/
def areaOf (v : String) : Option ((Nat × Nat) × (Nat × Nat)) :=
  match (v.splitOn " ").filter (· != "") |>.mapM areaKeyword with
  | some [(ax, a0, a1)] =>
    match ax with
    | some true => some ((a0, a1), (0, 3))
    | some false => some ((0, 3), (a0, a1))
    | none => some ((a0, a1), (a0, a1))
  | some [(ax, a0, a1), (bx, b0, b1)] =>
    match ax, bx with
    | some true, _ => some ((a0, a1), (b0, b1))
    | some false, _ => some ((b0, b1), (a0, a1))
    | none, some true => some ((b0, b1), (a0, a1))
    | none, _ => some ((b0, b1), (a0, a1))
  | _ => none

#guard areaOf "top left" == some ((0, 1), (0, 1)) && areaOf "left top" == some ((0, 1), (0, 1))
#guard areaOf "end start" == some ((0, 1), (2, 3)) && areaOf "top" == some ((0, 3), (0, 1))
#guard areaOf "span-all" == some ((0, 3), (0, 3)) && areaOf "center right" == some ((2, 3), (1, 2))

/-- `text-transform` (CSS Text 3 §2.1): the case in which text is shown. -/
inductive TextTransform where | none | uppercase | lowercase | capitalize
  deriving Repr, BEq, DecidableEq

/-- `line-break` (CSS Text 3 §5.3; inherited): `auto` and `strict` break as UAX 14 does by
default; `normal` and `loose` also let a line start with a small kana, and `loose` with an
iteration mark (`Unicode.LineBreak.Mode`). `anywhere` is read as `loose` here. -/
inductive LineBreakStyle where | auto | strict | normal | loose
  deriving Repr, BEq, DecidableEq

/-- `list-style-type` (CSS Lists 3 §3.1; inherited), as this profile draws markers:
`auto` is by the kind of list (a number in `ol`, else the bullet of the list's nesting
depth), `none` no marker, a bullet, or a number (every numbering style is decimal here). -/
inductive ListStyle where
  | auto | none | disc | circle | square | number
  deriving Repr, BEq

structure PositionStyle where
  position : Position := .static
  /-- The inset properties; `auto` is no inset. -/
  top : Length := .auto
  right : Length := .auto
  bottom : Length := .auto
  left : Length := .auto
  /-- `z-index`; `none` is `auto`. -/
  zIndex : Option Int := none
  float : FloatSide := .none
  clear : Clear := .none
  /-- `box-sizing: border-box`: `width`, `height` and their limits name the border box. -/
  borderBox : Bool := false
  /-- `aspect-ratio` (CSS Sizing 4 §5.1): the preferred ratio, width to height, as two
  positive whole numbers; `none` is `auto` (and a degenerate ratio, which behaves as it). -/
  ratio : Option (Nat × Nat) := none
  /-- `aspect-ratio: auto <ratio>`: a replaced element with a natural ratio keeps its own. -/
  ratioAuto : Bool := false
  /-- `writing-mode`; the cascade copies it from the parent (it is inherited). -/
  writingMode : WritingMode := .horizontalTb
  /-- `list-style-type`; inherited, as `writingMode` is. -/
  listStyle : ListStyle := .auto
  /-- `display: flow-root` (CSS Display 3 §2.1): a block that is the root of a block
  formatting context: it holds its floats and its children's margins. Set by the cascade
  with `display`. -/
  flowRoot : Bool := false
  /-- `list-style-position: inside` (inherited): the marker is the first thing in the item's
  first line; else it is outside the item's box, beside that line. -/
  listInside : Bool := false
  /-- `content` of a `::before` or `::after` (`Content.read`): the text of a value that
  makes a box; `none` for `none` and `normal`, which make no box. -/
  content : Option String := none
  /-- `counter-reset`, `counter-increment` and `counter-set` (CSS 2.1 §12.4, CSS Lists 3 §4;
  not inherited): counter names with their integers (`Content.counterList`). -/
  counterReset : List (String × Int) := []
  counterIncrement : List (String × Int) := []
  counterSet : List (String × Int) := []
  /-- `white-space: nowrap` (CSS Text 3 §3; inherited): lines do not break at the spaces
  of this text. -/
  nowrap : Bool := false
  /-- `text-transform` (CSS Text 3 §2.1; inherited). -/
  textTransform : TextTransform := .none
  /-- `line-break` (CSS Text 3 §5.3; inherited). -/
  lineBreak : LineBreakStyle := .auto
  /-- `anchor-name` (CSS Anchor Positioning 1 §2.1): the names by which positioned boxes find
  this one. -/
  anchorNames : List String := []
  /-- `position-anchor` (§2.4): the name of the default anchor of an `anchor()` with none. -/
  positionAnchor : Option String := none
  /-- The insets that are `anchor()` functions (top, right, bottom, left); their `Length`
  fields hold the fallback, or `auto`. -/
  anchorTop : Option AnchorRef := none
  anchorRight : Option AnchorRef := none
  anchorBottom : Option AnchorRef := none
  anchorLeft : Option AnchorRef := none
  /-- `position-area` (CSS Anchor Positioning 1 §3.1): the tracks of the 3 × 3 grid around the
  default anchor that the box's containing block spans, horizontally and vertically, each as
  the first and the last-plus-one track (0 to 3); `none` for `none`. -/
  positionArea : Option ((Nat × Nat) × (Nat × Nat)) := none
  /-- `transform` (CSS Transforms 1): its functions in order (`BoxTransform.steps`); empty
  for `none`. -/
  transform : List TransformStep := []
  /-- `transform-origin`: `(x, ofWidth, y, ofHeight)`, lengths and fractions of the border
  box; its centre by default. -/
  transformOrigin : Float × Float × Float × Float := (0,0.5,0,0.5)
  /-- `display: contents` (CSS Display 3 §2.5): the element makes no box, and its children
  are laid out as children of its parent. Set by the cascade with `display`. -/
  contents : Bool := false
  /-- `overflow: auto` or `scroll` in an axis: a scroll container. Nothing scrolls yet, so
  nothing is clipped away; the box is still the root of a block formatting context (CSS 2.1
  §9.4.1): it holds its floats and its children's margins. -/
  scrolls : Bool := false
  /-- The percentage parts of the margins (top, right, bottom, left), as fractions of the
  containing block's width (CSS 2.1 §8.3), until `Layout.percentEdges` adds them to
  `Computed.margin`. -/
  marginOf : Float × Float × Float × Float := (0,0,0,0)
  /-- The same for the padding (§8.4). -/
  paddingOf : Float × Float × Float × Float := (0,0,0,0)
  deriving Repr

/-- Every field equal: the two lay out the same. -/
def PositionStyle.same (a b : PositionStyle) : Bool :=
  a.position == b.position && a.top.same b.top && a.right.same b.right && a.bottom.same b.bottom &&
  a.left.same b.left && a.zIndex == b.zIndex && a.float == b.float && a.clear == b.clear &&
  a.borderBox == b.borderBox && a.ratio == b.ratio && a.ratioAuto == b.ratioAuto &&
  a.writingMode == b.writingMode && a.listStyle == b.listStyle && a.listInside == b.listInside &&
  a.flowRoot == b.flowRoot && a.content == b.content && a.nowrap == b.nowrap && a.textTransform == b.textTransform &&
  a.lineBreak == b.lineBreak &&
  sameSteps a.transform b.transform && a.transformOrigin == b.transformOrigin &&
  a.marginOf == b.marginOf && a.paddingOf == b.paddingOf && a.scrolls == b.scrolls &&
  a.contents == b.contents && a.positionArea == b.positionArea && a.anchorNames == b.anchorNames && a.positionAnchor == b.positionAnchor &&
  AnchorRef.sameOpt a.anchorTop b.anchorTop && AnchorRef.sameOpt a.anchorRight b.anchorRight &&
  AnchorRef.sameOpt a.anchorBottom b.anchorBottom && AnchorRef.sameOpt a.anchorLeft b.anchorLeft

/-- Out of flow by positioning: `absolute` or `fixed`. -/
def PositionStyle.isAbsolute (p : PositionStyle) : Bool := p.position == .absolute || p.position == .fixed

/-- Establishes the containing block of its absolutely positioned descendants. -/
def PositionStyle.isPositioned (p : PositionStyle) : Bool := p.position != .static

/-- The box is the root of a block formatting context by `display: flow-root` or by being
a scroll container. -/
def PositionStyle.formattingRoot (p : PositionStyle) : Bool := p.flowRoot || p.scrolls

/-- One side of four (0 top, 1 right, 2 bottom, 3 left) set to `v`. -/
def setSide (t : Float × Float × Float × Float) (side : Nat) (v : Float) : Float × Float × Float × Float :=
  match side with
  | 0 => (v,t.2.1,t.2.2.1,t.2.2.2)
  | 1 => (t.1,v,t.2.2.1,t.2.2.2)
  | 2 => (t.1,t.2.1,v,t.2.2.2)
  | _ => (t.1,t.2.1,t.2.2.1,v)

/-- The percentage part of the margin of one side; the style itself when nothing changes. -/
def PositionStyle.withMarginOf (p : PositionStyle) (side : Nat) (v : Float) : PositionStyle :=
  if v == 0 && p.marginOf == (0,0,0,0) then p else {p with marginOf := setSide p.marginOf side v}

/-- The percentage part of the padding of one side. -/
def PositionStyle.withPaddingOf (p : PositionStyle) (side : Nat) (v : Float) : PositionStyle :=
  if v == 0 && p.paddingOf == (0,0,0,0) then p else {p with paddingOf := setSide p.paddingOf side v}

/-- A margin or padding of the box is a percentage (or has a percentage part). -/
def PositionStyle.percentEdges (p : PositionStyle) : Bool := p.marginOf != (0,0,0,0) || p.paddingOf != (0,0,0,0)

/-- A box that holds its absolutely positioned descendants: a positioned box, or a
transformed one (CSS Transforms 1 §3: it is their containing block, so they move with it). -/
def PositionStyle.containsAbsolutes (p : PositionStyle) : Bool := p.isPositioned || !p.transform.isEmpty

def positionProperties : List String :=
  ["position", "top", "right", "bottom", "left", "z-index", "anchor-name", "position-anchor", "position-area", "float", "clear", "box-sizing", "aspect-ratio",
   "writing-mode", "list-style-type", "list-style-position", "white-space", "text-transform", "line-break", "transform", "transform-origin", "overflow-x", "overflow-y"]

/-- The ratio `a / b` (width to height) as two whole numbers in lowest terms; `none` when
it is degenerate (a term that is zero or negative: CSS Sizing 4 §5.1, it behaves as `auto`). -/
def ratioOf (a b : Rat) : Option (Nat × Nat) :=
  if a.num > 0 && b.num > 0 then
    let n := a.num.toNat * b.den
    let d := a.den * b.num.toNat
    let g := Nat.gcd n d
    some (n / g, d / g)
  else none

/-- `p` with the declaration `property: value` applied, when `property` is one of
`positionProperties` and `value` is a value of it; else `none`. -/
def PositionStyle.set (fontSize : Float) (p : PositionStyle) (property value : String) : Option PositionStyle :=
  let name := if property.startsWith "-webkit-" || property.startsWith "-moz-" then CssValues.propertyName property else property
  -- `content`: kept as its text when it makes a box; a CSS-wide keyword is the initial
  -- value here (`normal`: no box), and any other text is not a value.
  if name == "content" then
    match Content.read value with
    | some (.parts _) => some {p with content := some value}
    | some .noBox => some {p with content := none}
    | none => if ["initial", "inherit", "unset", "revert", "revert-layer"].contains value.trimAscii.toString.toLower
        then some {p with content := none} else none
  else
  if name == "counter-reset" || name == "counter-increment" || name == "counter-set" then
    let dflt : Int := if name == "counter-increment" then 1 else 0
    let put := fun (l : List (String × Int)) =>
      if name == "counter-reset" then {p with counterReset := l}
      else if name == "counter-increment" then {p with counterIncrement := l} else {p with counterSet := l}
    match Content.counterList value dflt with
    | some l => some (put l)
    | none => if ["initial", "inherit", "unset", "revert", "revert-layer"].contains value.trimAscii.toString.toLower
        then some (put []) else none
  else
  if !positionProperties.contains name then none else
  match CssValues.specified name value with
  | none => none
  | some v =>
    let reset := resetsToInitial v
    -- an inset: a length, or an `anchor()` with its fallback as the length
    let inset := fun (put : Length → Option AnchorRef → PositionStyle) =>
      if reset then some (put .auto none) else
      match anchorOf fontSize name v with
      | some a => some (put (a.fallback.getD .auto) (some a))
      | none => (tableLength fontSize name value).map (put · none)
    match name with
    | "position" =>
      if reset then some {p with position := .static} else
      match v with
      | "static" => some {p with position := .static}
      | "relative" => some {p with position := .relative}
      | "absolute" => some {p with position := .absolute}
      | "fixed" => some {p with position := .fixed}
      | "sticky" => some {p with position := .sticky}
      | _ => none
    | "top" => inset fun l a => {p with top := l, anchorTop := a}
    | "right" => inset fun l a => {p with right := l, anchorRight := a}
    | "bottom" => inset fun l a => {p with bottom := l, anchorBottom := a}
    | "left" => inset fun l a => {p with left := l, anchorLeft := a}
    | "anchor-name" =>
      if reset || v == "none" then some {p with anchorNames := []}
      else some {p with anchorNames := (v.splitOn ",").map fun t => t.trimAscii.toString}
    | "position-area" =>
      if reset || v == "none" then some {p with positionArea := none} else
      (areaOf v).map fun a => {p with positionArea := some a}
    | "position-anchor" =>
      if reset || !v.startsWith "--" then some {p with positionAnchor := none}
      else some {p with positionAnchor := some v}
    | "z-index" =>
      if reset || v == "auto" then some {p with zIndex := none} else
      match tableComponents fontSize name value with
      | some [.tok (.num n _)] => some {p with zIndex := some n.floor}
      | _ => none
    | "float" =>
      if reset then some {p with float := .none} else
      match v with
      | "none" => some {p with float := .none}
      | "left" => some {p with float := .left}
      | "right" => some {p with float := .right}
      | "inline-start" => some {p with float := .inlineStart}
      | "inline-end" => some {p with float := .inlineEnd}
      | _ => none
    | "clear" =>
      if reset then some {p with clear := .none} else
      match v with
      | "none" => some {p with clear := .none}
      | "left" => some {p with clear := .left}
      | "right" => some {p with clear := .right}
      | "both" => some {p with clear := .both}
      | "inline-start" => some {p with clear := .inlineStart}
      | "inline-end" => some {p with clear := .inlineEnd}
      | _ => none
    | "box-sizing" =>
      if reset then some {p with borderBox := false} else
      match v with
      | "border-box" => some {p with borderBox := true}
      | "content-box" => some {p with borderBox := false}
      | _ => none
    | "list-style-type" =>
      if v == "inherit" || v == "unset" then some p
      else if reset then some {p with listStyle := .auto} else
      match v with
      | "none" => some {p with listStyle := .none}
      | "disc" | "disclosure-open" | "disclosure-closed" => some {p with listStyle := .disc}
      | "circle" => some {p with listStyle := .circle}
      | "square" => some {p with listStyle := .square}
      | "decimal" | "decimal-leading-zero" | "lower-alpha" | "upper-alpha" | "lower-latin" | "upper-latin"
      | "lower-roman" | "upper-roman" | "lower-greek" => some {p with listStyle := .number}
      -- another counter style or a string: the marker of the kind of list stands
      | _ => some {p with listStyle := .auto}
    | "overflow-x" | "overflow-y" =>
      -- one axis that scrolls makes the box a scroll container; the other values of the
      -- longhands are not read
      if v == "auto" || v == "scroll" then some {p with scrolls := true} else none
    | "transform" =>
      if reset then some {p with transform := []} else
      (BoxTransform.read (CssValues.computed { num := { fontSize := tableRat fontSize } } name v)).map fun steps =>
        {p with transform := steps}
    | "transform-origin" =>
      if reset then some {p with transformOrigin := (0,0.5,0,0.5)} else
      (BoxTransform.origin (CssValues.computed { num := { fontSize := tableRat fontSize } } name v)).map fun o =>
        {p with transformOrigin := o}
    | "white-space" =>
      -- inherited; `pre` and its relatives keep their spaces by another field, and wrap or not as they say
      if v == "inherit" || v == "unset" then some p
      else if reset then some {p with nowrap := false} else
      match v with
      | "nowrap" | "pre" => some {p with nowrap := true}
      | "normal" | "pre-wrap" | "pre-line" | "break-spaces" => some {p with nowrap := false}
      | _ => none
    | "line-break" =>
      if v == "inherit" || v == "unset" then some p
      else if reset then some {p with lineBreak := .auto} else
      match v with
      | "auto" => some {p with lineBreak := .auto}
      | "strict" => some {p with lineBreak := .strict}
      | "normal" => some {p with lineBreak := .normal}
      | "loose" | "anywhere" => some {p with lineBreak := .loose}
      | _ => none
    | "text-transform" =>
      if v == "inherit" || v == "unset" then some p
      else if reset then some {p with textTransform := .none} else
      match v with
      | "none" => some {p with textTransform := .none}
      | "uppercase" => some {p with textTransform := .uppercase}
      | "lowercase" => some {p with textTransform := .lowercase}
      | "capitalize" => some {p with textTransform := .capitalize}
      | _ => none
    | "list-style-position" =>
      if v == "inherit" || v == "unset" then some p
      else if reset then some {p with listInside := false} else
      match v with
      | "inside" => some {p with listInside := true}
      | "outside" => some {p with listInside := false}
      | _ => none
    | "writing-mode" =>
      -- inherited: `inherit` and `unset` keep the parent's, which the style already holds
      if v == "inherit" || v == "unset" then some p
      else if reset then some {p with writingMode := .horizontalTb} else
      match v with
      | "horizontal-tb" => some {p with writingMode := .horizontalTb}
      | "vertical-rl" | "sideways-rl" => some {p with writingMode := .verticalRl}
      | "vertical-lr" | "sideways-lr" => some {p with writingMode := .verticalLr}
      | _ => none
    | "aspect-ratio" =>
      -- `auto`, `<ratio>` or both (CSS Sizing 4 §5.1); a ratio is `a / b` or `a` (`a / 1`).
      if reset || v == "auto" then some {p with ratio := none, ratioAuto := false} else
      match tableComponents fontSize name value with
      | some parts =>
        let isAuto := fun (c : CssValues.CV) => match c with
          | .tok (.ident "auto") => true
          | _ => false
        match parts.filter (fun c => !isAuto c) with
        | [.tok (.num a _)] => some {p with ratio := ratioOf a 1, ratioAuto := parts.any isAuto}
        | [.tok (.num a _), .tok (.delim '/'), .tok (.num b _)] =>
          some {p with ratio := ratioOf a b, ratioAuto := parts.any isAuto}
        | _ => none
      | none => none
    | _ => none

/-- The longhands of `inset` (CSS Positioned Layout 3 §3.1), by the property table. -/
def positionShorthand (property value : String) : Option (List (String × String)) :=
  if property == "inset" then CssValues.expand property value else none

#guard ((PositionStyle.set 16 {} "position" "ABSOLUTE").map (·.position)) == some .absolute
#guard ((PositionStyle.set 16 {} "position" "bogus").map (·.position)) == none
#guard ((PositionStyle.set 10 {} "top" "-2em").map fun p => match p.top with | .px v => v | _ => 0) == some (-20)
#guard ((PositionStyle.set 10 {} "left" "50%").map fun p => match p.left with | .percent v => v | _ => 0) == some 0.5
#guard ((PositionStyle.set 10 {} "z-index" "-1").map (·.zIndex)) == some (some (-1))
#guard ((PositionStyle.set 10 {zIndex := some 3} "z-index" "auto").map (·.zIndex)) == some none
#guard ((PositionStyle.set 10 {} "box-sizing" "border-box").map (·.borderBox)) == some true
#guard ((PositionStyle.set 10 {} "float" "right").map (·.float)) == some .right
#guard (PositionStyle.set 10 {} "width" "3px").isNone
#guard ((PositionStyle.set 10 {} "aspect-ratio" "16 / 9").map (·.ratio)) == some (some (16, 9))
#guard ((PositionStyle.set 10 {} "aspect-ratio" "2").map (·.ratio)) == some (some (2, 1))
#guard ((PositionStyle.set 10 {} "aspect-ratio" "1.5").map (·.ratio)) == some (some (3, 2))
#guard ((PositionStyle.set 10 {} "aspect-ratio" "auto 4/3").map fun p => (p.ratio, p.ratioAuto)) == some (some (4, 3), true)
#guard ((PositionStyle.set 10 {ratio := some (2, 1)} "aspect-ratio" "auto").map (·.ratio)) == some none
#guard ((PositionStyle.set 10 {} "aspect-ratio" "0 / 1").map (·.ratio)) == some none
#guard (PositionStyle.set 10 {} "aspect-ratio" "bogus").isNone
#guard ((PositionStyle.set 10 {} "content" "\"a\" attr(x)").map (·.content)) == some (some "\"a\" attr(x)")
#guard ((PositionStyle.set 10 {content := some "''"} "content" "none").map (·.content)) == some none
#guard ((PositionStyle.set 10 {content := some "''"} "content" "unset").map (·.content)) == some none
#guard ((PositionStyle.set 10 {} "content" "12px").map (·.content)) == none
#guard ((PositionStyle.set 10 {} "counter-reset" "a 2 b").map (·.counterReset)) == some [("a", 2), ("b", 0)]
#guard ((PositionStyle.set 10 {} "counter-increment" "a").map (·.counterIncrement)) == some [("a", 1)]
#guard ((PositionStyle.set 10 {} "counter-increment" "12px").map (·.counterIncrement)) == none
#guard ((PositionStyle.set 10 {} "transform" "translate(1em, 50%) scale(2)").map (·.transform.length)) == some 2
#guard ((PositionStyle.set 10 {} "transform" "translate(1em, 50%)").map fun p => sameSteps p.transform [.translate 10 0 0 0.5]) == some true
#guard ((PositionStyle.set 10 {transform := [.translate 1 0 0 0]} "transform" "none").map (·.transform.length)) == some 0
#guard ((PositionStyle.set 10 {} "transform" "bogus").map (·.transform.length)) == none
#guard ((PositionStyle.set 10 {} "transform-origin" "left top").map (·.transformOrigin)) == some (0,0,0,0)
#guard ((PositionStyle.set 10 {} "overflow-x" "auto").map (·.scrolls)) == some true
#guard ((PositionStyle.set 10 {} "overflow-y" "hidden").map (·.scrolls)) == none
#guard (({scrolls := true} : PositionStyle).formattingRoot) == true
#guard (({flowRoot := true} : PositionStyle).formattingRoot) == true
#guard (({} : PositionStyle).formattingRoot) == false
#guard (({} : PositionStyle).containsAbsolutes) == false
#guard (({transform := [.matrix 1 0 0 1 0 0]} : PositionStyle).containsAbsolutes) == true
#guard ((PositionStyle.set 10 {} "white-space" "nowrap").map (·.nowrap)) == some true
#guard ((PositionStyle.set 10 {nowrap := true} "white-space" "normal").map (·.nowrap)) == some false
#guard ((PositionStyle.set 10 {nowrap := true} "white-space" "inherit").map (·.nowrap)) == some true
#guard ((PositionStyle.set 10 {} "white-space" "bogus").map (·.nowrap)) == none
#guard ((PositionStyle.set 10 {} "text-transform" "uppercase").map (·.textTransform)) == some .uppercase
#guard ((PositionStyle.set 10 {} "line-break" "loose").map (·.lineBreak)) == some .loose
#guard ((PositionStyle.set 10 {lineBreak := .normal} "line-break" "inherit").map (·.lineBreak)) == some .normal
-- anchor positioning (CSS Anchor Positioning 1)
#guard ((PositionStyle.set 10 {} "anchor-name" "--a1").map (·.anchorNames)) == some ["--a1"]
#guard ((PositionStyle.set 10 {} "position-anchor" "--b").map (·.positionAnchor)) == some (some "--b")
#guard ((PositionStyle.set 10 {} "left" "anchor(--a1 right)").map fun p => (p.anchorLeft.map (·.name), p.anchorLeft.map (·.side))) == some (some (some "--a1"), some .right)
#guard ((PositionStyle.set 10 {} "top" "anchor(bottom, 10px)").map fun p => ((p.anchorTop.bind (·.name)).isNone && (p.anchorTop.map (·.side)) == some .bottom && p.top.same (.px 10))) == some true
#guard ((PositionStyle.set 10 {anchorLeft := some {}} "left" "5px").map (·.anchorLeft.isNone)) == some true
#guard ((PositionStyle.set 10 {textTransform := .uppercase} "text-transform" "none").map (·.textTransform)) == some .none
#guard ((PositionStyle.set 10 {} "text-transform" "UPPERCASE").map (·.textTransform)) == some .uppercase
#guard ((PositionStyle.set 10 {} "list-style-type" "none").map (·.listStyle)) == some .none
#guard ((PositionStyle.set 10 {} "list-style-type" "square").map (·.listStyle)) == some .square
#guard ((PositionStyle.set 10 {} "list-style-position" "inside").map (·.listInside)) == some true
#guard ((PositionStyle.set 10 {listStyle := .none} "list-style-type" "decimal").map (·.listStyle)) == some .number
#guard ((PositionStyle.set 10 {listStyle := .none} "list-style-type" "inherit").map (·.listStyle)) == some .none
#guard ((PositionStyle.set 10 {} "writing-mode" "vertical-rl").map (·.writingMode)) == some .verticalRl
#guard ((PositionStyle.set 10 {writingMode := .verticalLr} "writing-mode" "inherit").map (·.writingMode)) == some .verticalLr
#guard ((PositionStyle.set 10 {writingMode := .verticalLr} "writing-mode" "initial").map (·.writingMode)) == some .horizontalTb
#guard positionShorthand "inset" "0 auto 3px" == some [("top", "0px"), ("right", "auto"), ("bottom", "3px"), ("left", "auto")]

end L4Factoidal.Rendering.CSS
