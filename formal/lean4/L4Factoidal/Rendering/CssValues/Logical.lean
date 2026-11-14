/-
L4Factoidal.Rendering.CssValues.Logical — flow-relative properties and the physical
properties they stand for (CSS Logical Properties and Values 1; CSS Writing Modes 4 §6).

A logical property group (`margin-inline-start` and `margin-left` ...) is one set of
values under two sets of names: which physical side `inline-start` is depends on the
element's `writing-mode` and `direction` (its flow). Both names take part in one cascade,
and a computed style answers for either.

`Flow.side` is the table of Writing Modes 4 §6.4 (abstract to physical). It is a bijection
between the four logical and the four physical sides for every flow (`side_logicalOf`,
`logicalOf_side`), so each physical longhand has exactly one logical name in a flow and
back. `physical` and `logical` apply it to property names: the box sides (`margin-`,
`padding-`, `inset-`, `border-` with `-width`, `-style`, `-color`, `scroll-margin-`,
`scroll-padding-`), the sizes (`inline-size`, `block-size`, with `min-`, `max-` and
`contain-intrinsic-`), the corners (`border-start-end-radius`) and the axes
(`overflow-inline`, `overscroll-behavior-block`).

Used by the layout cascade (`CSS.computedFrom`) and by `getComputedStyle`
(`ComputedGeneric`): one mapping, so they can not disagree.
-/

namespace L4Factoidal.Rendering.CssValues.Logical

/-- A physical side of a box. -/
inductive Side where
  | top | right | bottom | left
  deriving DecidableEq, Repr, Inhabited

def Side.name : Side → String
  | .top => "top" | .right => "right" | .bottom => "bottom" | .left => "left"

def Side.ofName : String → Option Side
  | "top" => some .top | "right" => some .right | "bottom" => some .bottom | "left" => some .left
  | _ => none

def Side.opposite : Side → Side
  | .top => .bottom | .bottom => .top | .left => .right | .right => .left

/-- A top or bottom side. -/
def Side.vertical : Side → Bool
  | .top | .bottom => true
  | _ => false

/-- A flow-relative side. -/
inductive LogicalSide where
  | blockStart | blockEnd | inlineStart | inlineEnd
  deriving DecidableEq, Repr, Inhabited

def LogicalSide.name : LogicalSide → String
  | .blockStart => "block-start" | .blockEnd => "block-end"
  | .inlineStart => "inline-start" | .inlineEnd => "inline-end"

def LogicalSide.ofName : String → Option LogicalSide
  | "block-start" => some .blockStart | "block-end" => some .blockEnd
  | "inline-start" => some .inlineStart | "inline-end" => some .inlineEnd
  | _ => none

inductive WritingMode where
  | horizontalTb | verticalRl | verticalLr | sidewaysRl | sidewaysLr
  deriving DecidableEq, Repr, Inhabited

/-- The flow of an element: its writing mode and whether its direction is right to left. -/
structure Flow where
  mode : WritingMode := .horizontalTb
  rtl : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The flow of the computed values of `writing-mode` and `direction`. -/
def Flow.of (writingMode direction : String) : Flow :=
  { mode := match writingMode with
      | "vertical-rl" => .verticalRl | "vertical-lr" => .verticalLr
      | "sideways-rl" => .sidewaysRl | "sideways-lr" => .sidewaysLr
      | _ => .horizontalTb
    rtl := direction == "rtl" }

/-- Lines are laid out top to bottom or bottom to top: the inline axis is vertical. -/
def Flow.vertical (f : Flow) : Bool := f.mode != .horizontalTb

/-- The physical side of the start of the block axis (Writing Modes 4 §6.4). -/
def Flow.blockStart (f : Flow) : Side :=
  match f.mode with
  | .horizontalTb => .top
  | .verticalRl | .sidewaysRl => .right
  | .verticalLr | .sidewaysLr => .left

/-- The physical side of the start of the inline axis (Writing Modes 4 §6.4): the line
left of a left-to-right line; in `sideways-lr` lines run bottom to top. -/
def Flow.inlineStart (f : Flow) : Side :=
  match f.mode with
  | .horizontalTb => if f.rtl then .right else .left
  | .verticalRl | .verticalLr | .sidewaysRl => if f.rtl then .bottom else .top
  | .sidewaysLr => if f.rtl then .top else .bottom

/-- The physical side of a flow-relative side. -/
def Flow.side (f : Flow) : LogicalSide → Side
  | .blockStart => f.blockStart
  | .blockEnd => f.blockStart.opposite
  | .inlineStart => f.inlineStart
  | .inlineEnd => f.inlineStart.opposite

/-- The flow-relative side that a physical side is. -/
def Flow.logicalOf (f : Flow) (s : Side) : LogicalSide :=
  if s == f.blockStart then .blockStart
  else if s == f.blockStart.opposite then .blockEnd
  else if s == f.inlineStart then .inlineStart
  else .inlineEnd

/-- Every physical side is the side of the flow-relative side it is named by. -/
theorem side_logicalOf (f : Flow) (s : Side) : f.side (f.logicalOf s) = s := by
  cases f with
  | mk mode rtl => cases mode <;> cases rtl <;> cases s <;> rfl

/-- Every flow-relative side is the name of its physical side: with `side_logicalOf`, the
four flow-relative sides and the four physical sides correspond one to one in every flow. -/
theorem logicalOf_side (f : Flow) (l : LogicalSide) : f.logicalOf (f.side l) = l := by
  cases f with
  | mk mode rtl => cases mode <;> cases rtl <;> cases l <;> rfl

/-- Two flow-relative sides with one physical side are one side. -/
theorem side_injective (f : Flow) (a b : LogicalSide) (h : f.side a = f.side b) : a = b := by
  have := congrArg f.logicalOf h
  rwa [logicalOf_side, logicalOf_side] at this

/-- The block axis and the inline axis are perpendicular. -/
theorem block_inline_perpendicular (f : Flow) : f.blockStart.vertical = !f.inlineStart.vertical := by
  cases f with
  | mk mode rtl => cases mode <;> cases rtl <;> rfl

/-- The block axis is vertical exactly in a horizontal writing mode. -/
theorem blockStart_vertical (f : Flow) : f.blockStart.vertical = !f.vertical := by
  cases f with
  | mk mode rtl => cases mode <;> rfl

/-- In the initial flow (`horizontal-tb`, `ltr`) the sides are those of CSS 2. -/
theorem side_initial : ([.blockStart, .blockEnd, .inlineStart, .inlineEnd].map ({} : Flow).side) =
    [.top, .bottom, .left, .right] := rfl

/-! ### Property names -/

/-- The box side families: the prefix of the flow-relative names and of the physical ones
(`inset-block-start` is `top`). -/
def sideFamilies : List (String × String) :=
  [("margin-", "margin-"), ("padding-", "padding-"), ("inset-", ""),
   ("scroll-margin-", "scroll-margin-"), ("scroll-padding-", "scroll-padding-")]

/-- What follows the side in a border property name; none for the side's own shorthand. -/
def borderParts : List String := ["-width", "-style", "-color", ""]

/-- The prefixes of the size properties. -/
def sizePrefixes : List String := ["", "min-", "max-", "contain-intrinsic-"]

/-- The properties with a value for each axis: flow-relative suffixes and physical ones. -/
def axisFamilies : List String := ["overflow-", "overscroll-behavior-"]

/-- A property name could be flow-relative: it has `inline` or `block` in it, or it is a
corner (`border-start-end-radius`). A cheap test before `physical`. -/
def mentions (name : String) : Bool :=
  name.utf8ByteSize ≥ 10 && ((name.splitOn "inline").length > 1 || (name.splitOn "block").length > 1 ||
    (name.endsWith "-radius" && ((name.splitOn "-start-").length > 1 || (name.splitOn "-end-").length > 1)))

private def dropPrefix (s pre : String) : Option String :=
  if s.startsWith pre then some (s.drop pre.length).toString else none

private def dropSuffix (s suf : String) : Option String :=
  if s.endsWith suf then some (s.dropEnd suf.length).toString else none

/-- The physical longhand (or side shorthand, for `border-block-start`) that a
flow-relative property is in flow `f`; none when the name is not flow-relative. -/
def physical (f : Flow) (name : String) : Option String :=
  if !mentions name then none else
  -- sizes
  (sizePrefixes.findSome? fun pre =>
    (dropPrefix name pre).bind fun rest =>
      if rest == "inline-size" then some (pre ++ (if f.vertical then "height" else "width"))
      else if rest == "block-size" then some (pre ++ (if f.vertical then "width" else "height"))
      else none)
  <|> (axisFamilies.findSome? fun pre =>
    (dropPrefix name pre).bind fun rest =>
      if rest == "inline" then some (pre ++ (if f.vertical then "y" else "x"))
      else if rest == "block" then some (pre ++ (if f.vertical then "x" else "y"))
      else none)
  -- box sides
  <|> (sideFamilies.findSome? fun (lp, pp) =>
    ((dropPrefix name lp).bind LogicalSide.ofName).map fun l => pp ++ (f.side l).name)
  -- borders
  <|> ((dropPrefix name "border-").bind fun rest =>
    borderParts.findSome? fun part =>
      ((dropSuffix rest part).bind LogicalSide.ofName).map fun l => "border-" ++ (f.side l).name ++ part)
  -- corners: `border-<block>-<inline>-radius`
  <|> (((dropPrefix name "border-").bind (dropSuffix · "-radius")).bind fun corner =>
    let side := fun (start : LogicalSide) (stop : LogicalSide) (w : String) =>
      if w == "start" then some (f.side start) else if w == "end" then some (f.side stop) else none
    match corner.splitOn "-" with
    | [b, i] =>
      match side .blockStart .blockEnd b, side .inlineStart .inlineEnd i with
      | some bs, some is =>
        let (v, h) := if bs.vertical then (bs, is) else (is, bs)
        some ("border-" ++ v.name ++ "-" ++ h.name ++ "-radius")
      | _, _ => none
    | _ => none)

/-- The flow-relative name of a physical longhand (or border side shorthand) in flow `f`;
none when the property is in no logical property group. -/
def logical (f : Flow) (name : String) : Option String :=
  -- sizes
  (sizePrefixes.findSome? fun pre =>
    (dropPrefix name pre).bind fun rest =>
      if rest == "width" then some (pre ++ (if f.vertical then "block-size" else "inline-size"))
      else if rest == "height" then some (pre ++ (if f.vertical then "inline-size" else "block-size"))
      else none)
  <|> (axisFamilies.findSome? fun pre =>
    (dropPrefix name pre).bind fun rest =>
      if rest == "x" then some (pre ++ (if f.vertical then "block" else "inline"))
      else if rest == "y" then some (pre ++ (if f.vertical then "inline" else "block"))
      else none)
  <|> (sideFamilies.findSome? fun (lp, pp) =>
    ((dropPrefix name pp).bind Side.ofName).map fun s => lp ++ (f.logicalOf s).name)
  <|> ((dropPrefix name "border-").bind fun rest =>
    borderParts.findSome? fun part =>
      ((dropSuffix rest part).bind Side.ofName).map fun s => "border-" ++ (f.logicalOf s).name ++ part)
  <|> (((dropPrefix name "border-").bind (dropSuffix · "-radius")).bind fun corner =>
    match (corner.splitOn "-").map Side.ofName with
    | [some v, some h] =>
      let word := fun (l : LogicalSide) => match l with
        | .blockStart | .inlineStart => "start"
        | _ => "end"
      let (b, i) := if f.blockStart.vertical then (f.logicalOf v, f.logicalOf h) else (f.logicalOf h, f.logicalOf v)
      some ("border-" ++ word b ++ "-" ++ word i ++ "-radius")
    | _ => none)

/-- The two longhands (start, end) of a flow-relative shorthand of one axis
(`margin-block`, `padding-inline`, `inset-block`, `border-inline-width` ...). -/
def pair (name : String) : Option (String × String) :=
  if !mentions name then none else
  (["margin-", "padding-", "inset-", "scroll-margin-", "scroll-padding-"].findSome? fun pre =>
    (dropPrefix name pre).bind fun axis =>
      if axis == "block" || axis == "inline" then some (name ++ "-start", name ++ "-end") else none)
  <|> ((dropPrefix name "border-").bind fun rest =>
    ["-width", "-style", "-color"].findSome? fun part =>
      (dropSuffix rest part).bind fun axis =>
        if axis == "block" || axis == "inline" then
          some ("border-" ++ axis ++ "-start" ++ part, "border-" ++ axis ++ "-end" ++ part)
        else none)

/-! ### Examples -/

def allFlows : List Flow :=
  [.horizontalTb, .verticalRl, .verticalLr, .sidewaysRl, .sidewaysLr].flatMap fun mode =>
    [{ mode, rtl := false }, { mode, rtl := true }]

private def logicalNames : List String :=
  (["margin-", "padding-", "inset-", "scroll-margin-", "scroll-padding-"].flatMap fun pre =>
    ["block-start", "block-end", "inline-start", "inline-end"].map (pre ++ ·)) ++
  (["block-start", "block-end", "inline-start", "inline-end"].flatMap fun side =>
    borderParts.map fun part => "border-" ++ side ++ part) ++
  (sizePrefixes.flatMap fun pre => [pre ++ "inline-size", pre ++ "block-size"]) ++
  ["border-start-start-radius", "border-start-end-radius", "border-end-start-radius", "border-end-end-radius",
   "overflow-inline", "overflow-block", "overscroll-behavior-inline", "overscroll-behavior-block"]

-- in every flow, each flow-relative name has a physical name whose flow-relative name it is
#guard allFlows.all fun f => logicalNames.all fun l => (physical f l).bind (logical f) == some l
-- and in every flow the physical names of the flow-relative names are all different
#guard allFlows.all fun f => ((logicalNames.filterMap (physical f)).eraseDups).length == logicalNames.length
#guard physical {} "margin-inline-start" == some "margin-left"
#guard physical { rtl := true } "margin-inline-start" == some "margin-right"
#guard physical { mode := .verticalRl } "margin-inline-start" == some "margin-top"
#guard physical { mode := .verticalRl } "margin-block-start" == some "margin-right"
#guard physical { mode := .sidewaysLr } "padding-inline-end" == some "padding-top"
#guard physical {} "inset-block-end" == some "bottom"
#guard physical {} "border-inline-end-width" == some "border-right-width"
#guard physical {} "border-block-start" == some "border-top"
#guard physical {} "inline-size" == some "width"
#guard physical { mode := .verticalLr } "max-inline-size" == some "max-height"
#guard physical {} "border-start-end-radius" == some "border-top-right-radius"
#guard physical { mode := .verticalRl } "border-start-end-radius" == some "border-bottom-right-radius"
#guard physical { mode := .verticalRl, rtl := true } "border-start-start-radius" == some "border-bottom-right-radius"
#guard physical {} "overflow-inline" == some "overflow-x"
#guard physical {} "margin-left" == none
#guard physical {} "display" == none
#guard logical {} "top" == some "inset-block-start"
#guard logical { rtl := true } "padding-left" == some "padding-inline-end"
#guard logical {} "height" == some "block-size"
#guard logical {} "color" == none
#guard pair "margin-block" == some ("margin-block-start", "margin-block-end")
#guard pair "border-inline-color" == some ("border-inline-start-color", "border-inline-end-color")
#guard pair "margin-block-start" == none
#guard pair "margin" == none

end L4Factoidal.Rendering.CssValues.Logical
