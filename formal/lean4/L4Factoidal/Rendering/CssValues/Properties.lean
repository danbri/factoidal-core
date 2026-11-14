/-
L4Factoidal.Rendering.CssValues.Properties — the property table and the functions every
user of CSS values reads it through.

One table (`Data.properties`, generated from the grammars of the specifications) gives each
property its grammar, whether it is inherited, its initial value and, for a shorthand, its
longhands. From it:

- `specified p v`: the canonical specified value of `v` for property `p`, or `none` when
  `v` is not a value of `p`;
- `supports p v`: `(specified p v).isSome`, by definition: `CSS.supports`, the style
  declaration block and the parser can not disagree;
- `expand p v`: the longhand declarations a declaration stands for;
- `recombine p get`: the value of a shorthand from the values of its longhands;
- `computed ctx p v`: the computed value of a canonical specified value.
-/
import L4Factoidal.Rendering.CssValues.Grammar
import L4Factoidal.Rendering.CssValues.Color
import L4Factoidal.Rendering.CssValues.Data

namespace L4Factoidal.Rendering.CssValues

/-- A row of the property table. -/
structure Property where
  name : String
  grammar : String
  inherited : Bool
  initial : String
  longhands : List String
  deriving Repr, Inhabited

/-- The row of a property (the name in lower case). -/
def lookup (name : String) : Option Property :=
  (Data.properties.find? fun row => row.1 == name).map fun (n, g, inh, ini, ls) =>
    { name := n, grammar := g, inherited := inh, initial := ini,
      longhands := (ls.splitOn " ").filter (· != "") }

/-- The grammar of a non-terminal. -/
def syntaxOf (name : String) : Option String :=
  (Data.syntaxes.find? fun row => row.1 == name).map (·.2)

def isCustom (p : String) : Bool := p.length > 2 && p.toList.take 2 == ['-', '-']

/-- The name of a property as the table has it: lower case, a legacy alias replaced by its
target; a custom property as written. -/
def propertyName (p : String) : String :=
  if isCustom p then p
  else
    let l := lower p
    match Data.aliases.find? fun row => row.1 == l with
    | some (_, target) => target
    | none => l

/-- A text with CSS white space removed at both ends. -/
def trimText (s : String) : String :=
  String.ofList ((s.toList.dropWhile isCssSpace).reverse.dropWhile isCssSpace).reverse
where
  isCssSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\x0c'

/-- What computed values are computed against. -/
structure ComputeCtx where
  num : Ctx := {}
  /-- The computed value of `color` on the element, for `currentcolor`. -/
  currentColor : Option String := none
  deriving Inhabited

/-- A colour component read through `numeric`, so a `calc()` may stand for it. -/
def colorReader : Color.Reader := fun cv =>
  match Color.literalReader cv with
  | some c => some c
  | none =>
    match cv with
    | .fn _ _ =>
      match numeric (some {}) { kind := .number } cv with
      | some (.tok (.num v _)) => some (.num v)
      | _ =>
        match numeric (some {}) { kind := .percent } cv with
        | some (.tok (.pct v)) => some (.pct v)
        | _ =>
          match numeric (some {}) { kind := .angle } cv with
          | some (.tok (.dim v _ _)) => some (.angle v)
          | _ => none
    | _ => none

/-- The matcher's environment: specified values with `none`, computed values with a
context. -/
def env (ctx : Option ComputeCtx) : Env :=
  { syntaxOf := syntaxOf
    propSyntax := fun p => (lookup p).map (·.grammar)
    color := Color.parse { computed := ctx.isSome, current := ctx.bind (·.currentColor), read := colorReader }
    ctx := ctx.map (·.num) }

/-- The canonical text of `cvs` under a grammar text. -/
def matchText (ctx : Option ComputeCtx) (grammar : String) (cvs : List CV) : Option String :=
  (vds grammar).bind fun g => (matchAll (env ctx) g cvs).map fun o => serialize (untag 16 o)

/-- The single CSS-wide keyword that the values are, if they are one. -/
def wideKeyword (top : List CV) : Option String :=
  match top with
  | [.tok (.ident s)] => if cssWide.contains (lower s) then some (lower s) else none
  | _ => none

/-- Whether the value has a substitution function, so it is kept as written until computed
values are made (CSS Variables 1 §3). -/
def hasSubstitution (cvs : List CV) : Bool := hasFn "var" 32 cvs || hasFn "env" 32 cvs

/-- The short form of a `display` value (CSS Display 3 §2.5 and its serialisation: the
single-keyword legacy forms where they exist). The words arrive in the order of the
grammar: outside, inside, `list-item`. -/
def displayCanon (v : String) : String :=
  let ws := v.splitOn " "
  if ws.contains "list-item" then
    " ".intercalate (ws.filter fun w => w != "flow" && w != "block")
  else
    match ws with
    | ["flow"] => "block"
    | ["block", "flow"] => "block"
    | ["block", "flow-root"] => "flow-root"
    | ["block", "flex"] => "flex"
    | ["block", "grid"] => "grid"
    | ["block", "table"] => "table"
    | ["block", "grid-lanes"] => "grid-lanes"
    | ["inline", "flow"] => "inline"
    | ["inline", "flow-root"] => "inline-block"
    | ["inline", "flex"] => "inline-flex"
    | ["inline", "grid"] => "inline-grid"
    | ["inline", "table"] => "inline-table"
    | ["inline", "grid-lanes"] => "inline-grid-lanes"
    | ["inline", "ruby"] => "ruby"
    | ["inline", "math"] => "math"
    | ["run-in", "flow"] => "run-in"
    | _ => v

/-- The canonical forms that the order of the grammar alone does not give, by property. -/
def canonical (p v : String) : String :=
  match p with
  | "display" => displayCanon v
  | _ => v

/-- The canonical specified value of `value` for property `property`: `none` when the
property is not known or the value is not one of its values. -/
def specified (property value : String) : Option String :=
  let p := propertyName property
  let cvs := CV.parse value
  let top := stripWs cvs
  if hasBadToken 32 true top then none
  else if isCustom p then some (trimText value)
  else
    match lookup p with
    | none => none
    | some row =>
      if top.isEmpty then none
      else match wideKeyword top with
        | some k => some k
        | none =>
          if hasSubstitution cvs then some (rawText cvs)
          else if p == "all" then none
          else (matchText none row.grammar top).map (canonical p)

/-- `CSS.supports(property, value)` (CSS Conditional 3 §8.1): the value parses. -/
def supports (property value : String) : Bool := (specified property value).isSome

/-- Kind: structure. Says: `CSS.supports` and the parser are one function: a declaration is
supported exactly when the parser gives it a specified value. Does not say: that layout
reads the property; a supported declaration can be one the layout does not use yet. -/
theorem supports_iff_specified (p v : String) : supports p v = true ↔ ∃ s, specified p v = some s := by
  unfold supports
  cases specified p v <;> simp

/-! ### Shorthands -/

/-- How a shorthand is made of its longhands. -/
inductive Shape where
  /-- One to four values for the four sides (top, right, bottom, left). -/
  | sides
  /-- One or two values: the second defaults to the first. -/
  | pair
  /-- `a || b || c`: each part sets a group of longhands; a part left out is initial. -/
  | anyOrder (groups : List (List String))
  /-- `font` (CSS Fonts 4 §2.8): style, variant, weight and width in any order, then the
  size, an optional `/ line-height`, and the family; every other longhand is reset. -/
  | font
  deriving Repr, Inhabited

def sidesShorthands : List String :=
  ["margin", "padding", "border-width", "border-style", "border-color", "inset", "scroll-margin", "scroll-padding"]

def pairShorthands : List String :=
  ["gap", "place-content", "place-items", "place-self", "overflow", "overscroll-behavior",
   "inset-block", "inset-inline", "margin-block", "margin-inline", "padding-block", "padding-inline",
   "border-block-width", "border-block-style", "border-block-color",
   "border-inline-width", "border-inline-style", "border-inline-color",
   "scroll-margin-block", "scroll-margin-inline", "scroll-padding-block", "scroll-padding-inline",
   "contain-intrinsic-size", "grid-gap"]

def anyOrderShorthands : List String :=
  ["border-top", "border-right", "border-bottom", "border-left",
   "border-block-start", "border-block-end", "border-inline-start", "border-inline-end",
   "outline", "column-rule", "row-rule", "text-decoration", "list-style", "flex-flow", "text-emphasis", "columns"]

/-- A list as three runs of `n` (the widths, styles and colours of a border shorthand). -/
def thirds (n : Nat) (xs : List String) : List (List String) :=
  [xs.take n, (xs.drop n).take n, xs.drop (2 * n)]

/-- The shape of a shorthand that has a generic one. -/
def shapeOf (row : Property) : Option Shape :=
  let n := row.longhands.length
  if sidesShorthands.contains row.name && n == 4 then some .sides
  else if pairShorthands.contains row.name && n == 2 then some .pair
  else if anyOrderShorthands.contains row.name && n ≥ 2 then some (.anyOrder (row.longhands.map fun l => [l]))
  else if row.name == "font" then some .font
  else if (row.name == "border" || row.name == "border-block" || row.name == "border-inline") && n % 3 == 0 && n ≥ 3 then
    some (.anyOrder (thirds (n / 3) row.longhands))
  else none

/-- The values of the tagged matches, in order: property name and canonical text. -/
def tagged (out : List CV) : List (String × String) :=
  out.filterMap fun cv => match cv with
    | .fn name args => if isTag name then some ((name.drop 1).toString, serialize (untag 16 args)) else none
    | _ => none

/-- The canonical specified form of the initial value of a property ("" when not known). -/
def initialSpecified (p : String) : String :=
  match lookup p with
  | some row => (matchText none row.grammar (stripWs (CV.parse row.initial))).getD row.initial
  | none => ""

/-- The grammar of the `font` shorthand with its parts tagged by longhand. -/
def fontGrammar : G :=
  let kw := fun (ks : List String) => G.oneOf (ks.map G.kw)
  .seq [
    .rep (.anyOf [
      .prop "font-style",
      .tag "font-variant-caps" (kw ["normal", "small-caps"]),
      .prop "font-weight",
      .tag "font-stretch" (kw ["normal", "ultra-condensed", "extra-condensed", "condensed", "semi-condensed",
        "semi-expanded", "expanded", "extra-expanded", "ultra-expanded"])]) 0 (some 1) false,
    .prop "font-size",
    .rep (.seq [.lit '/', .prop "line-height"]) 0 (some 1) false,
    .prop "font-family"]

/-- The longhands of `font` that the shorthand writes; the others it resets. -/
def fontWritten : List String :=
  ["font-style", "font-variant-caps", "font-weight", "font-stretch", "font-size", "line-height", "font-family"]

/-- The longhand declarations that `property: value` stands for, each with its canonical
value: one for a longhand; for a shorthand its longhands, or the shorthand itself when it
has no generic shape here (it is then kept whole) or holds a substitution function. `none`:
not a valid declaration. -/
def expand (property value : String) : Option (List (String × String)) :=
  let p := propertyName property
  match specified p value with
  | none => none
  | some canonical =>
    match lookup p with
    | none => some [(p, canonical)]
    | some row =>
      if row.longhands.isEmpty then some [(p, canonical)]
      else
        let cvs := CV.parse value
        let top := stripWs cvs
        match wideKeyword top with
        | some k => some (row.longhands.map fun l => (l, k))
        | none =>
          if hasSubstitution cvs then some [(p, canonical)]
          else
            match shapeOf row with
            | none => some [(p, canonical)]
            | some .sides =>
              let first := row.longhands.headD p
              match (matchAll (env none) (.rep (.prop first) 1 (some 4) false) top).map tagged with
              | some [a] => some (row.longhands.map fun l => (l, a.2))
              | some [a, b] => some (row.longhands.zip [a.2, b.2, a.2, b.2])
              | some [a, b, c] => some (row.longhands.zip [a.2, b.2, c.2, b.2])
              | some [a, b, c, d] => some (row.longhands.zip [a.2, b.2, c.2, d.2])
              | _ => none
            | some .pair =>
              match row.longhands with
              | [l1, l2] =>
                match (matchAll (env none) (.seq [.prop l1, .rep (.prop l2) 0 (some 1) false]) top).map tagged with
                | some [a] => some [(l1, a.2), (l2, a.2)]
                | some [a, b] => some [(l1, a.2), (l2, b.2)]
                | _ => none
              | _ => none
            | some .font =>
              match (matchAll (env none) fontGrammar top).map tagged with
              | none =>
                -- a system font (`caption`, `menu` ...) is kept whole
                some [(p, canonical)]
              | some found =>
                some (row.longhands.map fun l => (l, (found.lookup l).getD (initialSpecified l)))
            | some (.anyOrder groups) =>
              let heads := groups.filterMap (·.head?)
              match (matchAll (env none) (.anyOf (heads.map G.prop)) top).map tagged with
              | none => none
              | some found =>
                some (groups.flatMap fun group =>
                  let head := group.headD ""
                  let v := match found.lookup head with
                    | some v => v
                    | none => (specified head ((lookup head).map (·.initial) |>.getD "")).getD ""
                  group.map fun l => (l, v))

/-- The value of a shorthand of a generic shape from the values of its longhands (`get`
answers "" for one that is not set): "" when it can not be written as one value. -/
def recombine (row : Property) (get : String → String) : String :=
  let vs := row.longhands.map get
  if vs.any (· == "") then ""
  else
    match vs with
    | [] => ""
    | v :: rest =>
      if cssWide.contains v then (if rest.all (· == v) then v else "")
      else if vs.any cssWide.contains then ""
      else
        match shapeOf row with
        | none => ""
        | some .sides =>
          match vs with
          | [t, r, b, l] =>
            if l == r then (if b == t then (if r == t then t else t ++ " " ++ r) else t ++ " " ++ r ++ " " ++ b)
            else t ++ " " ++ r ++ " " ++ b ++ " " ++ l
          | _ => ""
        | some .pair =>
          match vs with
          | [a, b] => if a == b then a else a ++ " " ++ b
          | _ => ""
        | some .font =>
          let resetOk := row.longhands.all fun l => fontWritten.contains l || get l == initialSpecified l
          let variant := get "font-variant-caps"
          let stretch := get "font-stretch"
          let keywordOnly := (variant == "normal" || variant == "small-caps") &&
            !(stretch.toList.any fun c => c.isDigit)
          if !resetOk || !keywordOnly then ""
          else
            let opt := fun (l : String) => let v := get l; if v == "normal" then [] else [v]
            let lineHeight := get "line-height"
            " ".intercalate (opt "font-style" ++ opt "font-variant-caps" ++ opt "font-weight" ++ opt "font-stretch" ++
              [get "font-size"] ++ (if lineHeight == "normal" then [] else ["/", lineHeight]) ++ [get "font-family"])
        | some (.anyOrder groups) =>
          let parts := groups.map fun group =>
            let head := group.headD ""
            let v := get head
            let uniform := group.all fun l => get l == v
            let initial := (specified head ((lookup head).map (·.initial) |>.getD "")).getD ""
            (v, uniform, v == initial)
          if parts.any (fun (_, uniform, _) => !uniform) then ""
          else
            match parts.filter (fun (_, _, isInitial) => !isInitial) with
            | [] => (parts.head?.map (·.1)).getD ""
            | shown => " ".intercalate (shown.map (·.1))

/-- The four values of a sides shorthand as the shorthand writes them. -/
def collapse4 (t r b l : String) : List String :=
  if l == r then (if b == t then (if r == t then [t] else [t, r]) else [t, r, b]) else [t, r, b, l]

/-- One to four values as the four sides (CSS Box 3 §3.2). -/
def expand4 : List String → Option (String × String × String × String)
  | [a] => some (a, a, a, a)
  | [a, b] => some (a, b, a, b)
  | [a, b, c] => some (a, b, c, b)
  | [a, b, c, d] => some (a, b, c, d)
  | _ => none

/-- Kind: round trip. Says: the shortest sides form of four values expands back to the same
four values, so writing a sides shorthand from its longhands loses nothing. Does not say:
that the parser gives those four values for a text (that is `expand`, tested by guards). -/
theorem expand4_collapse4 (t r b l : String) : expand4 (collapse4 t r b l) = some (t, r, b, l) := by
  unfold collapse4
  split
  · rename_i h1
    have e1 : l = r := by simpa using h1
    split
    · rename_i h2
      have e2 : b = t := by simpa using h2
      split
      · rename_i h3
        have e3 : r = t := by simpa using h3
        simp [expand4, e1, e2, e3]
      · simp [expand4, e1, e2]
    · simp [expand4, e1]
  · simp [expand4]

/-- Kind: idempotence. Says: collapsing the sides, expanding and collapsing again gives the
same shorthand text parts. Does not say: anything about values that differ only in
spelling (they are compared as canonical text). -/
theorem collapse4_expand4 (t r b l : String) :
    (expand4 (collapse4 t r b l)).map (fun (t', r', b', l') => collapse4 t' r' b' l') = some (collapse4 t r b l) := by
  simp [expand4_collapse4]

/-! ### Computed values -/

/-- Keywords of `<line-width>` as lengths (CSS Backgrounds 3 §4.3). -/
def lineWidthKeyword : String → Option String
  | "thin" => some "1px"
  | "medium" => some "3px"
  | "thick" => some "5px"
  | _ => none

def lineWidthProperties : List String :=
  ["border-top-width", "border-right-width", "border-bottom-width", "border-left-width",
   "border-block-start-width", "border-block-end-width", "border-inline-start-width", "border-inline-end-width",
   "outline-width", "column-rule-width", "row-rule-width"]

/-- The computed value of a canonical specified value (not a CSS-wide keyword: the cascade
resolves those): lengths absolute, colours resolved, `calc()` computed. A value the
grammar does not read in computed form stays as specified. -/
def computed (ctx : ComputeCtx) (property value : String) : String :=
  let p := propertyName property
  if isCustom p then value
  else
    match lookup p with
    | none => value
    | some row =>
      let cvs := CV.parse value
      if hasSubstitution cvs then value
      else
        let v := canonical p ((matchText (some ctx) row.grammar (stripWs cvs)).getD value)
        if lineWidthProperties.contains p then (lineWidthKeyword v).getD v
        else if p == "font-weight" then (if v == "normal" then "400" else if v == "bold" then "700" else v)
        else v

/-- The computed initial value of a property. -/
def initialComputed (ctx : ComputeCtx) (row : Property) : String :=
  match specified row.name row.initial with
  | some s => computed ctx row.name s
  | none => row.initial

/-! ### Tests -/

#guard specified "color" "RED" == some "red"
#guard specified "color" "#f00" == some "rgb(255, 0, 0)"
#guard specified "color" "1px" == none
#guard specified "COLOR" "inherit" == some "inherit"
#guard specified "width" "calc(1px + 2px)" == some "calc(3px)"
#guard specified "width" "-1px" == none
#guard specified "width" "var(--x)" == some "var(--x)"
#guard specified "--x" " a  b " == some "a  b"
#guard specified "-webkit-transform" "none" == some "none"
#guard propertyName "WORD-WRAP" == "overflow-wrap"
#guard specified "nonsense" "1px" == none
#guard specified "display" "GRID" == some "grid"
#guard specified "margin" "1px 2px" == some "1px 2px"
#guard specified "margin-top" "1px 2px" == none
#guard specified "color" "red;" == none
#guard specified "color" "red !important" == none
#guard specified "position-area" "none none" == none
#guard specified "z-index" "1.5" == none
#guard specified "opacity" "0.5" == some "0.5"
#guard specified "transform" "translate(10px, 20%) rotate(45deg)" == some "translate(10px, 20%) rotate(45deg)"
#guard specified "box-shadow" "1px 2px red" == some "red 1px 2px"
#guard supports "display" "flex"
#guard specified "display" "flow" == some "block"
#guard specified "display" "inline flow-root" == some "inline-block"
#guard specified "display" "list-item flow" == some "list-item"
#guard specified "display" "inline list-item" == some "inline list-item"
#guard specified "transform" "translatex(1px) TRANSLATE(1px)" == some "translateX(1px) translate(1px)"
#guard specified "background-image" "linear-gradient(to left bottom, red, blue)" == some "linear-gradient(to left bottom, red, blue)"
#guard specified "background-image" "linear-gradient(red, blue)" == some "linear-gradient(red, blue)"
#guard !supports "display" "flexx"
#guard expand "margin" "1px 2px" == some [("margin-top", "1px"), ("margin-right", "2px"), ("margin-bottom", "1px"), ("margin-left", "2px")]
#guard expand "margin" "1px 2px 3px 4px 5px" == none
#guard expand "border-top" "red solid" == some [("border-top-width", "medium"), ("border-top-style", "solid"), ("border-top-color", "red")]
#guard (expand "border" "1px solid").map (·.length) == some 12
#guard expand "gap" "1px" == some [("row-gap", "1px"), ("column-gap", "1px")]
#guard expand "overflow" "hidden auto" == some [("overflow-x", "hidden"), ("overflow-y", "auto")]
#guard expand "margin" "inherit" == some [("margin-top", "inherit"), ("margin-right", "inherit"), ("margin-bottom", "inherit"), ("margin-left", "inherit")]
#guard (lookup "margin").map (fun row => recombine row fun l => if l == "margin-top" then "1px" else "2px") == some "1px 2px 2px"
#guard (lookup "border-top").map (fun row => recombine row fun l =>
    if l == "border-top-width" then "medium" else if l == "border-top-style" then "solid" else "currentcolor") == some "solid"
#guard (lookup "border-top").map (fun row => recombine row fun l =>
    if l == "border-top-width" then "medium" else if l == "border-top-style" then "none" else "currentcolor") == some "medium"
#guard (expand "font" "italic bold 12px/2 FB Armada, serif").map (·.filter fun d => fontWritten.contains d.1) ==
  some [("font-style", "italic"), ("font-variant-caps", "normal"), ("font-weight", "bold"), ("font-stretch", "normal"),
        ("font-size", "12px"), ("line-height", "2"), ("font-family", "FB Armada, serif")]
#guard (expand "font" "12px").isNone
#guard (expand "font" "caption") == some [("font", "caption")]
#guard computed {} "width" "2em" == "32px"
#guard computed {} "color" "red" == "rgb(255, 0, 0)"
#guard computed { currentColor := some "rgb(0, 128, 0)" } "border-top-color" "currentcolor" == "rgb(0, 128, 0)"
#guard computed {} "border-top-width" "medium" == "3px"
#guard computed {} "margin-top" "calc(1em + 2px)" == "18px"

end L4Factoidal.Rendering.CssValues
