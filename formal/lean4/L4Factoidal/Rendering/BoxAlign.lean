import L4Factoidal.Rendering.CssValues.Properties

/-! Computed values that flex and grid layout share (CSS Box Alignment 3): content and
self alignment, gaps and `order`. `Computed.align` holds them. Every value is read through
the property table (`CssValues`): the table decides what is a value of a property and
gives its canonical text; this module only names the keywords the layout acts on. -/
namespace L4Factoidal.Rendering.CSS

/-- A length of the layout profile: px, a percentage (as a fraction), or viewport units
(fractions of the viewport, resolved when it is known: `Length.atViewport`). -/
inductive Length where
  | auto | px (value : Float) | percent (value : Float)
  | vw (value : Float) | vh (value : Float)
  /-- A percentage (as a fraction) plus px: `calc(50% - 8px)`, and what a `border-box`
  percentage is as a content-box size. -/
  | calc (percent : Float) (px : Float)
  /-- The sizing keywords (CSS Sizing 3 §3.2, 4 §6.1): a size taken from the contents, or
  `stretch`, the size that fills the containing block. They are not numbers: `resolve`
  answers `none` for them, and the layout gives them their sizes (`Layout.sizeKeyword`). -/
  | minContent | maxContent | fitContent | stretch
  deriving Repr

/-- The same length (a NaN is not the same as itself, as with `==` on floats). -/
def Length.same : Length → Length → Bool
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

/-- A sizing keyword: a size that the layout takes from the contents or the containing block. -/
def Length.isKeyword : Length → Bool
  | .minContent | .maxContent | .fitContent | .stretch => true
  | _ => false

/-- A sizing keyword by name (CSS Sizing 3 §3.2; `stretch` also under its older names). -/
def sizeKeyword? (name : String) : Option Length :=
  match name with
  | "min-content" => some .minContent
  | "max-content" => some .maxContent
  | "fit-content" => some .fitContent
  | "stretch" | "-webkit-fill-available" | "-moz-available" => some .stretch
  | _ => none

/-- An exact number of the property table as a float. -/
def ratToFloat (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

/-- A font size or other positive px value for the property table, to a thousandth. -/
def tableRat (x : Float) : Rat :=
  if x.isFinite && x > 0 then ((x * 1000).round.toUInt64.toNat : Rat) / 1000 else 0

/-- The components of the computed value of `value` for `property` by the property table,
with font-relative lengths in px against `fontSize`; `none` when it is not a value of the
property. -/
def tableComponents (fontSize : Float) (property value : String) : Option (List CssValues.CV) :=
  (CssValues.specified property value).map fun s =>
    CssValues.stripWs (CssValues.CV.parse
      (CssValues.computed { num := { fontSize := tableRat fontSize } } property s))

/-- One component as a length: px, a percentage, a viewport length kept for the layout
(the viewport is not known to the cascade), or `auto`. -/
def lengthOfComponent : CssValues.CV → Option Length
  | .tok (.dim v _ "px") => some (.px (ratToFloat v))
  | .tok (.pct v) => some (.percent (ratToFloat v / 100))
  | .tok (.num v _) => if v == 0 then some (.px 0) else none
  | .tok (.ident "auto") => some .auto
  | .fn "calc" args =>
    -- the computed form of a sum of a percentage and a length: `calc(P% + Npx)`, `calc(P% - Npx)`
    match CssValues.stripWs args with
    | [.tok (.pct p), .tok (.delim '+'), .tok (.dim v _ "px")] => some (.calc (ratToFloat p / 100) (ratToFloat v))
    | [.tok (.pct p), .tok (.delim '-'), .tok (.dim v _ "px")] => some (.calc (ratToFloat p / 100) (-(ratToFloat v)))
    | [.tok (.dim v _ "px"), .tok (.delim '+'), .tok (.pct p)] => some (.calc (ratToFloat p / 100) (ratToFloat v))
    | [.tok (.dim v _ "px"), .tok (.delim '-'), .tok (.pct p)] => some (.calc (-(ratToFloat p / 100)) (ratToFloat v))
    | _ => none
  | _ => none

/-- The text `calc(P% + Npx)` or `calc(P% - Npx)` as a length: the computed form of a sum
of a percentage and a length. -/
def calcLengthOfText (text : String) : Option Length :=
  match CssValues.stripWs (CssValues.CV.parse text) with
  | [.fn "calc" args] => lengthOfComponent (.fn "calc" args)
  | _ => none

/-- A length-valued property read through the property table. Viewport units are read
from the specified value, since the table computes them against a default viewport. -/
def tableLength (fontSize : Float) (property value : String) : Option Length :=
  match (CssValues.specified property value).map fun s => CssValues.stripWs (CssValues.CV.parse s) with
  | some [.tok (.dim v _ "vw")] => some (.vw (ratToFloat v / 100))
  | some [.tok (.dim v _ "vh")] => some (.vh (ratToFloat v / 100))
  | some _ =>
    match tableComponents fontSize property value with
    | some [c] => lengthOfComponent c
    | _ => none
  | none => none

/-- `justify-content` and `align-content` (CSS Box Alignment 3 §4). -/
inductive ContentAlign where
  | normal | start | end_ | flexStart | flexEnd | center | left | right
  | spaceBetween | spaceAround | spaceEvenly | stretch | baseline
  deriving Repr, BEq

/-- `align-items`, `align-self`, `justify-items` and `justify-self` (§5 and §6). -/
inductive ItemAlign where
  | auto | normal | stretch | start | end_ | flexStart | flexEnd | selfStart | selfEnd
  | center | left | right | baseline | lastBaseline
  deriving Repr, BEq

/-- The alignment and gap values of an element. -/
structure AlignStyle where
  justifyContent : ContentAlign := .normal
  alignContent : ContentAlign := .normal
  alignItems : ItemAlign := .normal
  alignSelf : ItemAlign := .auto
  justifyItems : ItemAlign := .normal
  justifySelf : ItemAlign := .auto
  /-- `row-gap` and `column-gap`; `auto` stands for `normal` (no gap in flex and grid). -/
  rowGap : Length := .auto
  columnGap : Length := .auto
  order : Int := 0
  /-- The overflow position `safe` (CSS Box Alignment 3 §4.4) of `align-items`,
  `align-self`, `justify-items`, `justify-self`: an item larger than its alignment
  container is aligned to its start. `unsafe` and no keyword are false. -/
  alignItemsSafe : Bool := false
  alignSelfSafe : Bool := false
  justifyItemsSafe : Bool := false
  justifySelfSafe : Bool := false
  deriving Repr

/-- Every field equal: the two lay out the same. -/
def AlignStyle.same (a b : AlignStyle) : Bool :=
  a.justifyContent == b.justifyContent && a.alignContent == b.alignContent &&
  a.alignItems == b.alignItems && a.alignSelf == b.alignSelf &&
  a.justifyItems == b.justifyItems && a.justifySelf == b.justifySelf &&
  a.rowGap.same b.rowGap && a.columnGap.same b.columnGap && a.order == b.order &&
  a.alignItemsSafe == b.alignItemsSafe && a.alignSelfSafe == b.alignSelfSafe &&
  a.justifyItemsSafe == b.justifyItemsSafe && a.justifySelfSafe == b.justifySelfSafe

/-- The words of a canonical keyword value, without the overflow position (`safe`,
`unsafe`: this layout aligns as `unsafe` does, except where the specification falls back). -/
def alignWords (canonical : String) : List String :=
  (canonical.splitOn " ").filter fun w => w != "" && w != "safe" && w != "unsafe"

/-- The value has the overflow position `safe`. -/
def alignSafe (canonical : String) : Bool := (canonical.splitOn " ").contains "safe"

#guard alignSafe "safe end" && !alignSafe "unsafe end" && !alignSafe "end"

def contentAlignOf (canonical : String) : Option ContentAlign :=
  match alignWords canonical with
  | ["normal"] => some .normal
  | ["start"] => some .start
  | ["end"] => some .end_
  | ["flex-start"] => some .flexStart
  | ["flex-end"] => some .flexEnd
  | ["center"] => some .center
  | ["left"] => some .left
  | ["right"] => some .right
  | ["space-between"] => some .spaceBetween
  | ["space-around"] => some .spaceAround
  | ["space-evenly"] => some .spaceEvenly
  | ["stretch"] => some .stretch
  | ["baseline"] | ["first", "baseline"] | ["last", "baseline"] => some .baseline
  | _ => none

def itemAlignOf (canonical : String) : Option ItemAlign :=
  match alignWords canonical with
  | ["auto"] => some .auto
  | ["normal"] => some .normal
  | ["stretch"] => some .stretch
  | ["start"] => some .start
  | ["end"] => some .end_
  | ["flex-start"] => some .flexStart
  | ["flex-end"] => some .flexEnd
  | ["self-start"] => some .selfStart
  | ["self-end"] => some .selfEnd
  | ["center"] | ["anchor-center"] => some .center
  | ["left"] => some .left
  | ["right"] => some .right
  | ["baseline"] | ["first", "baseline"] => some .baseline
  | ["last", "baseline"] => some .lastBaseline
  | ["legacy"] => some .normal
  | ["legacy", "left"] => some .left
  | ["legacy", "right"] => some .right
  | ["legacy", "center"] => some .center
  | _ => none

/-- The property names this module reads, as the table names them. -/
def alignProperties : List String :=
  ["justify-content", "align-content", "align-items", "align-self", "justify-items", "justify-self",
   "row-gap", "column-gap", "order"]

/-- The shorthands of those properties. -/
def alignShorthands : List String :=
  ["gap", "grid-gap", "place-content", "place-items", "place-self"]

/-- A CSS-wide keyword that resets to the initial value here (`initial`; and `unset`,
`revert`, `revert-layer`, since none of these properties is inherited or set by the user
agent sheet). `inherit` is not read. -/
def resetsToInitial (canonical : String) : Bool :=
  canonical == "initial" || canonical == "unset" || canonical == "revert" || canonical == "revert-layer"

/-- `a` with the declaration `property: value` applied, when `property` is one of
`alignProperties` (or its legacy alias) and `value` is a value of it; else `none`. The
check of the name comes first, so a declaration of any other property costs a few string
comparisons and no parse. -/
def AlignStyle.set (fontSize : Float) (a : AlignStyle) (property value : String) : Option AlignStyle :=
  let p := if property.startsWith "-webkit-" || property.startsWith "grid-" then CssValues.propertyName property else property
  if !alignProperties.contains p then none else
  match CssValues.specified p value with
  | none => none
  | some v =>
    let reset := resetsToInitial v
    match p with
    | "justify-content" => if reset then some {a with justifyContent := .normal} else (contentAlignOf v).map fun x => {a with justifyContent := x}
    | "align-content" => if reset then some {a with alignContent := .normal} else (contentAlignOf v).map fun x => {a with alignContent := x}
    | "align-items" => if reset then some {a with alignItems := .normal, alignItemsSafe := false}
        else (itemAlignOf v).map fun x => {a with alignItems := x, alignItemsSafe := alignSafe v}
    | "align-self" => if reset then some {a with alignSelf := .auto, alignSelfSafe := false}
        else (itemAlignOf v).map fun x => {a with alignSelf := x, alignSelfSafe := alignSafe v}
    | "justify-items" => if reset then some {a with justifyItems := .normal, justifyItemsSafe := false}
        else (itemAlignOf v).map fun x => {a with justifyItems := x, justifyItemsSafe := alignSafe v}
    | "justify-self" => if reset then some {a with justifySelf := .auto, justifySelfSafe := false}
        else (itemAlignOf v).map fun x => {a with justifySelf := x, justifySelfSafe := alignSafe v}
    | "row-gap" =>
      if reset || v == "normal" then some {a with rowGap := .auto} else (tableLength fontSize p value).map fun x => {a with rowGap := x}
    | "column-gap" =>
      if reset || v == "normal" then some {a with columnGap := .auto} else (tableLength fontSize p value).map fun x => {a with columnGap := x}
    | "order" =>
      if reset then some {a with order := 0} else
      match tableComponents fontSize p value with
      | some [.tok (.num n _)] => some {a with order := n.floor}
      | _ => none
    | _ => none

/-- The longhand declarations of an alignment shorthand, by the property table; `none`
for any other property or a value that is not one of the shorthand's. -/
def alignShorthand (property value : String) : Option (List (String × String)) :=
  if alignShorthands.contains property then CssValues.expand property value else none

#guard ((AlignStyle.set 16 {} "justify-content" "space-between").map (·.justifyContent)) == some .spaceBetween
#guard ((AlignStyle.set 16 {} "justify-content" "safe CENTER").map (·.justifyContent)) == some .center
#guard ((AlignStyle.set 16 {} "align-items" "last baseline").map (·.alignItems)) == some .lastBaseline
#guard ((AlignStyle.set 16 {} "justify-self" "safe end").map fun a => (a.justifySelf, a.justifySelfSafe)) == some (.end_, true)
#guard ((AlignStyle.set 16 {} "align-self" "unsafe end").map (·.alignSelfSafe)) == some false
#guard ((AlignStyle.set 16 {} "align-items" "bogus").map (·.alignItems)) == none
#guard ((AlignStyle.set 16 {} "-webkit-align-items" "center").map (·.alignItems)) == some .center
#guard ((AlignStyle.set 10 {} "column-gap" "1.5em").map fun a => match a.columnGap with | .px v => v | _ => -1) == some 15
#guard ((AlignStyle.set 10 {} "row-gap" "10%").map fun a => match a.rowGap with | .percent v => v | _ => -1) == some 0.1
#guard ((AlignStyle.set 16 {} "order" "-3").map (·.order)) == some (-3)
#guard (AlignStyle.set 16 {} "color" "red").isNone
#guard ((tableLength 10 "width" "calc(100% - 2em)").map fun l => match l with | .calc p x => (p, x) | _ => (0, 0)) == some (1, -20)
#guard ((tableLength 10 "width" "calc(1em + 50%)").map fun l => match l with | .calc p x => (p, x) | _ => (0, 0)) == some (0.5, 10)
#guard ((tableLength 10 "width" "calc(1em * 3)").map fun l => match l with | .px x => x | _ => 0) == some 30
#guard ((tableLength 10 "width" "12vw").map fun l => match l with | .vw x => x | _ => 0) == some 0.12
#guard alignShorthand "gap" "4px 8px" == some [("row-gap", "4px"), ("column-gap", "8px")]
#guard alignShorthand "gap" "4px" == some [("row-gap", "4px"), ("column-gap", "4px")]
#guard alignShorthand "place-items" "center" == some [("align-items", "center"), ("justify-items", "center")]

end L4Factoidal.Rendering.CSS
