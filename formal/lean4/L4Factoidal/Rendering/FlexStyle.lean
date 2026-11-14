import L4Factoidal.Rendering.BoxAlign

/-! Computed values of flex containers and flex items (CSS Flexible Box Layout 1 §5 and
§7): `Computed.flex`. Values are read through the property table, as in `BoxAlign`. -/
namespace L4Factoidal.Rendering.CSS

/-- `flex-basis` (§7.2.3): `auto` (the main size property), `content` (and the intrinsic
size keywords, read as `content`), or a length. -/
inductive FlexBasis where
  | auto | content | length (l : Length)
  deriving Repr

/-- `flex-wrap` (§5.2). -/
inductive FlexWrap where
  | nowrap | wrap | wrapReverse
  deriving Repr, BEq

structure FlexStyle where
  /-- `flex-direction`: the main axis is the block axis (`column`, `column-reverse`). -/
  column : Bool := false
  /-- `flex-direction`: `row-reverse` or `column-reverse`. -/
  reverse : Bool := false
  wrap : FlexWrap := .nowrap
  grow : Float := 0
  shrink : Float := 1
  basis : FlexBasis := .auto
  deriving Repr

def FlexBasis.same : FlexBasis → FlexBasis → Bool
  | .auto, .auto => true
  | .content, .content => true
  | .length a, .length b => a.same b
  | _, _ => false

/-- Every field equal: the two lay out the same. -/
def FlexStyle.same (a b : FlexStyle) : Bool :=
  a.column == b.column && a.reverse == b.reverse && a.wrap == b.wrap &&
  a.grow == b.grow && a.shrink == b.shrink && a.basis.same b.basis

def flexProperties : List String :=
  ["flex-direction", "flex-wrap", "flex-grow", "flex-shrink", "flex-basis"]

/-- A number-valued property read through the table (a `calc()` is computed). -/
def tableNumber (property value : String) : Option Float :=
  match tableComponents 16 property value with
  | some [.tok (.num n _)] => some (ratToFloat n)
  | _ => none

/-- `f` with the declaration `property: value` applied, when `property` is a flex
longhand (or its `-webkit-` alias) and `value` is a value of it; else `none`. -/
def FlexStyle.set (fontSize : Float) (f : FlexStyle) (property value : String) : Option FlexStyle :=
  let p := if property.startsWith "-webkit-" then CssValues.propertyName property else property
  if !flexProperties.contains p then none else
  match CssValues.specified p value with
  | none => none
  | some v =>
    let reset := resetsToInitial v
    match p with
    | "flex-direction" =>
      if reset then some {f with column := false, reverse := false} else
      match v with
      | "row" => some {f with column := false, reverse := false}
      | "row-reverse" => some {f with column := false, reverse := true}
      | "column" => some {f with column := true, reverse := false}
      | "column-reverse" => some {f with column := true, reverse := true}
      | _ => none
    | "flex-wrap" =>
      if reset then some {f with wrap := .nowrap} else
      let ws := v.splitOn " "
      if ws.contains "wrap-reverse" then some {f with wrap := .wrapReverse}
      else if ws.contains "wrap" then some {f with wrap := .wrap}
      else if ws.contains "nowrap" || ws.contains "balance" then some {f with wrap := .nowrap}
      else none
    | "flex-grow" => if reset then some {f with grow := 0} else (tableNumber p value).map fun x => {f with grow := x}
    | "flex-shrink" => if reset then some {f with shrink := 1} else (tableNumber p value).map fun x => {f with shrink := x}
    | "flex-basis" =>
      if reset || v == "auto" then some {f with basis := .auto}
      else match tableLength fontSize p value with
        | some l => some {f with basis := .length l}
        | none =>
          -- `content`, `min-content`, `max-content`, `fit-content` and the like
          some {f with basis := .content}
    | _ => none

/-- The longhands of the `flex` shorthand (§7.2): `none` is `0 0 auto`; a number alone
sets the grow factor with a basis of `0%`; a basis alone keeps `1 1`. -/
def flexShorthand (value : String) : Option (List (String × String)) :=
  match CssValues.specified "flex" value with
  | none => none
  | some v =>
    let triple := fun (g s b : String) => some [("flex-grow", g), ("flex-shrink", s), ("flex-basis", b)]
    if resetsToInitial v || v == "inherit" then triple v v v
    else if v == "none" then triple "0" "0" "auto"
    else
      let parts := (CssValues.stripWs (CssValues.CV.parse v)).map fun cv =>
        (CssValues.serialize [cv], match cv with | .tok (.num _ _) => true | _ => false)
      match parts with
      | [(a, true)] => triple a "1" "0%"
      | [(a, false)] => triple "1" "1" a
      | [(a, true), (b, true)] => triple a b "0%"
      | [(a, true), (b, false)] => triple a "1" b
      | [(b, false), (a, true)] => triple a "1" b
      | [(a, true), (b, true), (c, _)] => triple a b c
      | [(c, false), (a, true), (b, true)] => triple a b c
      | _ => none

/-- The longhand declarations of a shorthand that layout reads (`flex`, `flex-flow`, the
alignment shorthands), by the property table; `none` for any other property, or when the
value is not one of the shorthand's (the declaration is then dropped by its reader). -/
def layoutShorthand (property value : String) : Option (List (String × String)) :=
  let p := if property.startsWith "-webkit-" then CssValues.propertyName property else property
  if p == "flex" then flexShorthand value
  else if p == "flex-flow" then CssValues.expand p value
  else alignShorthand p value

#guard flexShorthand "1" == some [("flex-grow", "1"), ("flex-shrink", "1"), ("flex-basis", "0%")]
#guard flexShorthand "none" == some [("flex-grow", "0"), ("flex-shrink", "0"), ("flex-basis", "auto")]
#guard flexShorthand "auto" == some [("flex-grow", "1"), ("flex-shrink", "1"), ("flex-basis", "auto")]
#guard flexShorthand "2 3 10px" == some [("flex-grow", "2"), ("flex-shrink", "3"), ("flex-basis", "10px")]
#guard flexShorthand "0 0 50%" == some [("flex-grow", "0"), ("flex-shrink", "0"), ("flex-basis", "50%")]
#guard flexShorthand "10em" == some [("flex-grow", "1"), ("flex-shrink", "1"), ("flex-basis", "10em")]
#guard flexShorthand "1 1 0" == some [("flex-grow", "1"), ("flex-shrink", "1"), ("flex-basis", "0px")]
#guard flexShorthand "bogus" == none
#guard layoutShorthand "flex-flow" "column wrap" == some [("flex-direction", "column"), ("flex-wrap", "wrap")]
#guard layoutShorthand "color" "red" == none
#guard ((FlexStyle.set 16 {} "flex-direction" "column-reverse").map fun f => (f.column, f.reverse)) == some (true, true)
#guard ((FlexStyle.set 16 {} "flex-grow" "2.5").map (·.grow)) == some 2.5
#guard ((FlexStyle.set 20 {} "flex-basis" "2em").map fun f => match f.basis with | .length (.px v) => v | _ => -1) == some 40
#guard ((FlexStyle.set 16 {} "flex-basis" "0").map fun f => match f.basis with | .length (.px v) => v | _ => -1) == some 0
#guard ((FlexStyle.set 16 {} "flex-basis" "content").map fun f => match f.basis with | .content => true | _ => false) == some true
#guard (FlexStyle.set 16 {} "width" "10px").isNone

end L4Factoidal.Rendering.CSS
