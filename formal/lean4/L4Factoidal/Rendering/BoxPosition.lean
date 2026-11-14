import L4Factoidal.Rendering.BoxAlign

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
  deriving Repr

/-- Every field equal: the two lay out the same. -/
def PositionStyle.same (a b : PositionStyle) : Bool :=
  a.position == b.position && a.top.same b.top && a.right.same b.right && a.bottom.same b.bottom &&
  a.left.same b.left && a.zIndex == b.zIndex && a.float == b.float && a.clear == b.clear &&
  a.borderBox == b.borderBox && a.ratio == b.ratio && a.ratioAuto == b.ratioAuto

/-- Out of flow by positioning: `absolute` or `fixed`. -/
def PositionStyle.isAbsolute (p : PositionStyle) : Bool := p.position == .absolute || p.position == .fixed

/-- Establishes the containing block of its absolutely positioned descendants. -/
def PositionStyle.isPositioned (p : PositionStyle) : Bool := p.position != .static

def positionProperties : List String :=
  ["position", "top", "right", "bottom", "left", "z-index", "float", "clear", "box-sizing", "aspect-ratio"]

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
  if !positionProperties.contains name then none else
  match CssValues.specified name value with
  | none => none
  | some v =>
    let reset := resetsToInitial v
    let inset := fun (put : Length → PositionStyle) =>
      if reset then some (put .auto) else (tableLength fontSize name value).map put
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
    | "top" => inset fun l => {p with top := l}
    | "right" => inset fun l => {p with right := l}
    | "bottom" => inset fun l => {p with bottom := l}
    | "left" => inset fun l => {p with left := l}
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
#guard positionShorthand "inset" "0 auto 3px" == some [("top", "0px"), ("right", "auto"), ("bottom", "3px"), ("left", "auto")]

end L4Factoidal.Rendering.CSS
