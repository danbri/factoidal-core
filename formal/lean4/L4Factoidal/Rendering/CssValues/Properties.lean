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
import L4Factoidal.Rendering.CssValues.Shapes
import Std.Data.HashMap

namespace L4Factoidal.Rendering.CssValues

/-- A row of the property table. -/
structure Property where
  name : String
  grammar : String
  inherited : Bool
  initial : String
  longhands : List String
  deriving Repr, Inhabited

/-! ### The table, indexed once

The rows are static data. The indexes below are lazy constants: each is built the first
time a script asks for a property value, and never for a page that does not. A grammar
text is read into a grammar at most once (the thunk of its row). -/

/-- The rows by property name. -/
def propertyMap : Thunk (Std.HashMap String Property) := Thunk.mk fun _ =>
  Data.properties.foldl (fun m (n, g, inh, ini, ls) =>
    m.insert n { name := n, grammar := g, inherited := inh, initial := ini,
                 longhands := (ls.splitOn " ").filter (· != "") }) {}

/-- The row of a property (the name in lower case). -/
def lookup (name : String) : Option Property := propertyMap.get[name]?

/-- The grammars of the properties, each read when first used. -/
def propertyGrammars : Thunk (Std.HashMap String (Thunk (Option G))) := Thunk.mk fun _ =>
  Data.properties.foldl (fun m (n, g, _, _, _) => m.insert n (Thunk.mk fun _ => vds g)) {}

/-- The grammars of the non-terminals, each read when first used. -/
def syntaxGrammars : Thunk (Std.HashMap String (Thunk (Option G))) := Thunk.mk fun _ =>
  Data.syntaxes.foldl (fun m (n, g) => m.insert n (Thunk.mk fun _ => vds g)) {}

/-- The grammar of a property. -/
def propG (name : String) : Option G := (propertyGrammars.get[name]?).bind (·.get)

/-- The grammar of a non-terminal. -/
def syntaxG (name : String) : Option G := (syntaxGrammars.get[name]?).bind (·.get)

/-- The legacy names and what they stand for. -/
def aliasMap : Thunk (Std.HashMap String String) := Thunk.mk fun _ =>
  Data.aliases.foldl (fun m (a, t) => m.insert a t) {}

def isCustom (p : String) : Bool := p.length > 2 && p.toList.take 2 == ['-', '-']

/-- The name of a property as the table has it: lower case, a legacy alias replaced by its
target; a custom property as written. -/
def propertyName (p : String) : String :=
  if isCustom p then p
  else
    let l := lower p
    (aliasMap.get[l]?).getD l

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

/-- The stand-in of an infinite colour channel: beyond every channel's range, and a multiple
of 360 (a hue of it is 0). -/
def infiniteChannel : Rat := 360 * 1000000000000

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
          | _ =>
            -- `calc(infinity)` is the channel's upper bound, `calc(-infinity)` and
            -- `calc(NaN)` its lower bound (CSS Values 4 §10.12): a number larger than any
            -- channel's range, and a multiple of 360 so that a hue of either is 0
            match (Calc.parse cv).map fun c => Calc.simp none (Calc.depth 64 c + 4) c with
            | some (.kw "infinity") => some (.num infiniteChannel)
            | some (.kw "-infinity") | some (.kw "nan") => some (.num (-infiniteChannel))
            | _ => none
    | _ => none

/-- The matcher's environment: specified values with `none`, computed values with a
context. -/
def env (ctx : Option ComputeCtx) : Env :=
  { syntaxG := syntaxG
    propG := propG
    color := Color.parse { computed := ctx.isSome, current := ctx.bind (·.currentColor), read := colorReader }
    ctx := ctx.map (·.num) }

/-- The canonical text of `cvs` as a value of property `p` (a name of the table). -/
def matchText (ctx : Option ComputeCtx) (p : String) (cvs : List CV) : Option String :=
  (propG p).bind fun g => (matchAll (env ctx) g cvs).map fun o => serialize (untag 16 o)

/-- The single CSS-wide keyword that the values are, if they are one. -/
def wideKeyword (top : List CV) : Option String :=
  match top with
  | [.tok (.ident s)] => if cssWide.contains (lower s) then some (lower s) else none
  | _ => none

/-- Whether the value has a substitution function, so it is kept as written until computed
values are made (CSS Variables 1 §3). -/
def hasSubstitution (cvs : List CV) : Bool :=
  hasFn "var" 32 cvs || hasFn "env" 32 cvs || hasFn "attr" 32 cvs || hasFn "if" 32 cvs

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

/-- The canonical form of a `scale` value (CSS Transforms 2 §5): percentages are numbers,
a third value of 1 is left out, and two equal values are one. -/
def scaleCanon (v : String) : String :=
  let nums := (stripWs (CV.parse v)).map fun cv => match cv with
    | .tok (.pct x) => CV.tok (.num (x / 100) false)
    | cv => cv
  let texts := nums.map fun cv => serialize [cv]
  match texts with
  | [x, y, z] => if z == "1" then (if x == y then x else x ++ " " ++ y) else x ++ " " ++ y ++ " " ++ z
  | [x, y] => if x == y then x else x ++ " " ++ y
  | _ => serialize nums

/-- A colour of a gradient written in a legacy form (named, hex, `rgb()`, `hsl()`, `hwb()`,
a system colour): its default interpolation space is sRGB (CSS Images 4 §3.1, CSS Color 4
§12.1); any other colour makes the default Oklab. -/
def modernColorFns : List String := ["lab", "lch", "oklab", "oklch", "color", "color-mix", "light-dark"]

/-- A gradient's arguments without its colour interpolation method when that is the default
one (`in oklab`, or `in srgb` when every colour is legacy) with no hue method: the
canonical form leaves it out. -/
def dropDefaultInterpolation (args : List CV) : List CV :=
  let groups := splitCommas args
  match groups with
  | first :: rest =>
    let ws := stripWs first
    let isIn := fun (cv : CV) => match cv with
      | .tok (.ident k) => lower k == "in"
      | _ => false
    match ws.reverse with
    | .tok (.ident sp) :: inTok :: before =>
      if !isIn inTok then args
      else
        let modern := rest.any fun g => g.any fun cv => match cv with
          | .fn f _ => modernColorFns.contains (lower f)
          | _ => false
        let default := if modern then "oklab" else "srgb"
        if lower sp != default then args
        else
          let first' := before.reverse
          let groups' := if first'.isEmpty then rest else first' :: rest
          (groups'.map stripWs).foldl (fun acc g => if acc.isEmpty then g else acc ++ [.tok .comma, .tok .ws] ++ g) []
    | _ => args
  | [] => args

/-- The value with the default interpolation method of each top-level gradient left out. -/
def gradientCanon (v : String) : String :=
  if (v.splitOn "gradient(").length ≤ 1 || (v.splitOn " in ").length ≤ 1 && (v.splitOn "(in ").length ≤ 1 then v
  else
    let cvs := CV.parse v
    let out := cvs.map fun cv => match cv with
      | .fn name args =>
        if (lower name).endsWith "gradient" then .fn name (dropDefaultInterpolation args) else cv
      | cv => cv
    serialize out

/-- The canonical forms that the order of the grammar alone does not give, by property. -/
def canonical (p v : String) : String :=
  match p with
  | "display" => displayCanon v
  | "scale" => if v == "none" then v else scaleCanon v
  | "rotate" => rotateCanon v
  | _ => gradientCanon v

/-- `canonical`, and for a shape property the shape's canonical form (`shapeValue`):
`none` when a `path()` in it is not path data, so the value is not one of the property's. -/
def canonicalValue (p v : String) : Option String :=
  if shapeProperties.contains p then shapeValue false p v else some (canonical p v)

/-- Whether the values can not be the value of a custom property (CSS Variables 1 §2): a
bad string or url, an unmatched closing token, or a top-level `;` or `!`. A `{}` block is
allowed. -/
def badCustomValue (top : List CV) : Bool :=
  hasBadToken 32 false top || top.any fun cv => match cv with
    | .tok .semicolon => true
    | .tok (.delim '!') => true
    | _ => false

/-- A `flex` value whose leading unitless zero the grammar reads as the basis: CSS Flexbox
1 §7.2 reads a unitless zero that is not after two flex factors as a flex factor, so
`flex: 0 1 1` is not a value (its last `1` is no basis). -/
def flexZeroMisread (top : List CV) : Bool :=
  match top with
  | .tok (.num n _) :: _ :: _ =>
    -- the grow factor read is not that zero
    n == 0 && ((propG "flex").bind fun g => matchAll (env none) g top).any fun out =>
      out.any fun cv => match cv with
        | .fn name args => isTag name && (name.drop 1).toString == "flex-grow" && serialize (untag 16 args) != "0"
        | _ => false
  | _ => false

/-- The canonical specified value of `value` for property `property`: `none` when the
property is not known or the value is not one of its values. -/
def specified (property value : String) : Option String :=
  let p := propertyName property
  let cvs := CV.parse value
  let top := stripWs cvs
  if isCustom p then (if badCustomValue top then none else some (trimText value))
  else if hasBadToken 32 true top then none
  else
    match lookup p with
    | none => none
    | some row =>
      if top.isEmpty then none
      else match wideKeyword top with
        | some k => some k
        | none =>
          if hasSubstitution cvs then some (rawText cvs)
          else if p == "all" || (p == "flex" && flexZeroMisread top) then none
          else (matchText none row.name top).bind (canonicalValue p)

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
  /-- One value for every longhand. -/
  | same
  /-- `a || b || c`: each part sets a group of longhands; a part left out is initial. -/
  | anyOrder (groups : List (List String))
  /-- `font` (CSS Fonts 4 §2.8): style, variant, weight and width in any order, then the
  size, an optional `/ line-height`, and the family; every other longhand is reset. -/
  | font
  /-- The shorthand's grammar names its parts as `<'property'>` (longhands, or shorthands of
  some of its longhands), each at most once: the parts are read off the match, and the value
  is written back by walking the grammar (`unparse`) and checked by expanding it again. -/
  | byGrammar (g : G)
  deriving Inhabited

def sidesShorthands : List String :=
  ["margin", "padding", "border-width", "border-style", "border-color", "inset", "scroll-margin", "scroll-padding",
   "corner-shape"]

def sameShorthands : List String :=
  ["column-rule-inset-start", "column-rule-inset-end", "row-rule-inset-start", "row-rule-inset-end"]

def pairShorthands : List String :=
  ["gap", "place-content", "place-items", "place-self", "overflow", "overscroll-behavior",
   "inset-block", "inset-inline", "margin-block", "margin-inline", "padding-block", "padding-inline",
   "border-block-width", "border-block-style", "border-block-color",
   "border-inline-width", "border-inline-style", "border-inline-color",
   "scroll-margin-block", "scroll-margin-inline", "scroll-padding-block", "scroll-padding-inline",
   "contain-intrinsic-size", "grid-gap", "size", "min-size", "max-size",
   "column-rule-inset-cap", "column-rule-inset-junction", "row-rule-inset-cap", "row-rule-inset-junction",
   "corner-top-shape", "corner-bottom-shape", "corner-left-shape", "corner-right-shape",
   "corner-block-start-shape", "corner-block-end-shape", "corner-inline-start-shape", "corner-inline-end-shape"]

def anyOrderShorthands : List String :=
  ["border-top", "border-right", "border-bottom", "border-left",
   "border-block-start", "border-block-end", "border-inline-start", "border-inline-end",
   "outline", "column-rule", "row-rule", "text-decoration", "list-style", "flex-flow", "text-emphasis", "columns"]

/-- A list as three runs of `n` (the widths, styles and colours of a border shorthand). -/
def thirds (n : Nat) (xs : List String) : List (List String) :=
  [xs.take n, (xs.drop n).take n, xs.drop (2 * n)]

/-- The properties a grammar names (`<'property'>` and tagged parts). The recursion is on
the nesting of the grammar (table data). -/
def propsOf : Nat → G → List String
  | 0, _ => []
  | fuel + 1, g =>
    match g with
    | .prop n => [n]
    | .tag n _ => [n]
    | .seq gs => gs.flatMap (propsOf fuel)
    | .oneOf gs => gs.flatMap (propsOf fuel)
    | .anyOf gs => gs.flatMap (propsOf fuel)
    | .allOf gs => gs.flatMap (propsOf fuel)
    | .rep g' _ _ _ => propsOf fuel g'
    | .req g' => propsOf fuel g'
    | .fn _ g' => propsOf fuel g'
    | .block _ g' => propsOf fuel g'
    | _ => []

/-- Whether every multiplier over a named property is `?`: each part occurs at most once. -/
def simpleRefs : Nat → G → Bool
  | 0, _ => false
  | fuel + 1, g =>
    match g with
    | .seq gs => gs.all (simpleRefs fuel)
    | .oneOf gs => gs.all (simpleRefs fuel)
    | .anyOf gs => gs.all (simpleRefs fuel)
    | .allOf gs => gs.all (simpleRefs fuel)
    | .rep g' lo hi comma => (propsOf fuel g').isEmpty || (lo == 0 && hi == some 1 && !comma && simpleRefs fuel g')
    | .req g' => simpleRefs fuel g'
    | .fn _ g' => (propsOf fuel g').isEmpty
    | .block _ g' => (propsOf fuel g').isEmpty
    | _ => true

/-- Whether a grammar has a part that carries a value outside a named property: a keyword,
a type, a function or a block that no `<'property'>` or tagged part holds. Such a part says
nothing of the longhands, so a reading by named parts would lose it. The recursion is on
the nesting of the grammar (table data). -/
def loose : Nat → G → Bool
  | 0, _ => true
  | fuel + 1, g =>
    match g with
    | .prop _ | .tag _ _ | .lit _ => false
    | .seq gs | .oneOf gs | .anyOf gs | .allOf gs => gs.any (loose fuel)
    | .rep g' _ _ _ | .req g' => loose fuel g'
    | _ => true

/-- The longhands of a keyword of a shorthand that is not one of its parts: the legacy
keywords of `white-space` (CSS Text 4 §3.1). -/
def keywordLonghands (shorthand keyword : String) : Option (List (String × String)) :=
  let ws := fun (c w : String) =>
    some [("white-space-collapse", c), ("text-wrap-mode", w), ("white-space-trim", "none")]
  match shorthand, keyword with
  | "white-space", "normal" => ws "collapse" "wrap"
  | "white-space", "pre" => ws "preserve" "nowrap"
  | "white-space", "pre-wrap" => ws "preserve" "wrap"
  | "white-space", "pre-line" => ws "preserve-breaks" "wrap"
  | _, _ => none

/-- A keyword alternative of a shorthand's grammar that the reading by parts keeps: the
shorthand's initial value (every longhand initial), `flex: none` (`missingDefault`), or a
keyword of `keywordLonghands`. -/
def bareKeyword (row : Property) (k : String) : Bool :=
  let k := (k.splitOn "=").headD k
  k == lower row.initial || (row.name == "flex" && k == "none") || (keywordLonghands row.name k).isSome

/-- The alternatives of a shorthand's grammar that the reading by parts holds: each names
its parts (`loose` is false) or is a keyword of `bareKeyword`. A value of another
alternative (`grid-template` areas, `grid: auto-flow ...`, `corner: round ...`) is kept
whole. -/
def tightAlternatives (row : Property) (g : G) : Option G :=
  let keep := fun (a : G) => match a with
    | .kw k => bareKeyword row k
    | a => !loose 24 a
  match g with
  | .oneOf alts => match alts.filter keep with
    | [] => none
    | kept => some (.oneOf kept)
  | g => if keep g then some g else none

/-- Kind: shape. Says: a legacy `white-space` keyword sets exactly the three longhands of
`white-space`, in their order, and `white-space-trim` to `none`. Does not say: that the
values are the ones CSS Text 4 gives (the guards of `Declaration` test that). -/
theorem keywordLonghands_whiteSpace (k : String) (ds : List (String × String))
    (h : keywordLonghands "white-space" k = some ds) :
    ds.map Prod.fst = ["white-space-collapse", "text-wrap-mode", "white-space-trim"] ∧
      ds.lookup "white-space-trim" = some "none" := by
  unfold keywordLonghands at h
  split at h <;> simp_all <;> subst h <;> decide

/-- Kind: subset. Says: the reading by parts keeps only alternatives of the table's grammar,
each one it can read (`loose` false, or a keyword of `bareKeyword`). -/
theorem tightAlternatives_oneOf (row : Property) (alts kept : List G)
    (h : tightAlternatives row (.oneOf alts) = some (.oneOf kept)) :
    ∀ a ∈ kept, a ∈ alts ∧ (match a with | .kw k => bareKeyword row k | a => !loose 24 a) = true := by
  intro a ha
  unfold tightAlternatives at h
  simp only at h
  cases hf : alts.filter (fun a => match a with | .kw k => bareKeyword row k | a => !loose 24 a) with
  | nil => rw [hf] at h; simp at h
  | cons x xs =>
    rw [hf] at h
    simp only [Option.some.injEq, G.oneOf.injEq] at h
    subst h
    rw [← hf] at ha
    exact List.mem_filter.mp ha

/-- The grammar of a shorthand with its parts named, where the table's grammar does not
name them: the grid placement shorthands (CSS Grid 2 §8.4). -/
def namedGrammar (name : String) : Option G :=
  let line := G.ref "grid-line" none none
  let slash := fun (l : String) => G.rep (.seq [.lit '/', .tag l line]) 0 (some 1) false
  match name with
  | "grid-row" => some (.seq [.tag "grid-row-start" line, slash "grid-row-end"])
  | "grid-column" => some (.seq [.tag "grid-column-start" line, slash "grid-column-end"])
  | "grid-area" => some (.seq [.tag "grid-row-start" line,
      .rep (.seq [.lit '/', .tag "grid-column-start" line,
        .rep (.seq [.lit '/', .tag "grid-row-end" line, slash "grid-column-end"]) 0 (some 1) false]) 0 (some 1) false])
  | _ => none

/-- The grammar by which a shorthand is read part by part, when it has one: every property
it names is a longhand of the shorthand or a shorthand of some of them, at most once. -/
def partsGrammar (row : Property) : Option G :=
  match ((namedGrammar row.name).orElse (fun _ => propG row.name)).bind (tightAlternatives row) with
  | none => none
  | some g =>
    let names := propsOf 24 g
    let ok := !names.isEmpty && simpleRefs 24 g && names.all fun n =>
      row.longhands.contains n ||
        (match lookup n with
          | some sub => !sub.longhands.isEmpty && sub.longhands.all row.longhands.contains
          | none => false)
    if ok then some g else none

/-- The shape of a shorthand that has a generic one. -/
def shapeOf (row : Property) : Option Shape :=
  let n := row.longhands.length
  if sidesShorthands.contains row.name && n == 4 then some .sides
  else if pairShorthands.contains row.name && n == 2 then some .pair
  else if sameShorthands.contains row.name && n ≥ 1 then some .same
  else if anyOrderShorthands.contains row.name && n ≥ 2 then some (.anyOrder (row.longhands.map fun l => [l]))
  else if row.name == "font" then some .font
  else if (row.name == "border" || row.name == "border-block" || row.name == "border-inline") && n % 3 == 0 && n ≥ 3 then
    some (.anyOrder (thirds (n / 3) row.longhands))
  else (partsGrammar row).map Shape.byGrammar

/-- The values of the tagged matches, in order: property name and canonical text. -/
def tagged (out : List CV) : List (String × String) :=
  out.filterMap fun cv => match cv with
    | .fn name args => if isTag name then some ((name.drop 1).toString, serialize (untag 16 args)) else none
    | _ => none

/-- The canonical specified form of the initial value of a property ("" when not known),
computed from the table. -/
def initialSpecifiedOf (p : String) : String :=
  match lookup p with
  | some row => (matchText none row.name (stripWs (CV.parse row.initial))).getD row.initial
  | none => ""

/-- The canonical initial values, each computed when first used. -/
def initialValues : Thunk (Std.HashMap String (Thunk String)) := Thunk.mk fun _ =>
  Data.properties.foldl (fun m (n, _, _, _, _) => m.insert n (Thunk.mk fun _ => initialSpecifiedOf n)) {}

/-- The canonical specified form of the initial value of a property ("" when not known). -/
def initialSpecified (p : String) : String := ((initialValues.get[p]?).map (·.get)).getD ""

/-- The percentage of a `font-width` keyword (CSS Fonts 4 §2.5). -/
def fontWidthName : String → String
  | "ultra-condensed" => "50%" | "extra-condensed" => "62.5%" | "condensed" => "75%"
  | "semi-condensed" => "87.5%" | "normal" => "100%" | "semi-expanded" => "112.5%"
  | "expanded" => "125%" | "extra-expanded" => "150%" | "ultra-expanded" => "200%"
  | k => k

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

/-- A longhand that a shorthand's value leaves out: its value. Initial, except where the
shorthand says otherwise: `flex` (CSS Flexbox 1 §7.1.1), the grid placement shorthands (CSS
Grid 2 §8.4: a missing end line repeats a custom identifier start line), and the `rule`
shorthands of CSS Gaps, which set the row and the column longhands alike. -/
def missingDefault (shorthand canonical : String) (found : List (String × String)) (l : String) : String :=
  let identLine := fun (v : String) =>
    match stripWs (CV.parse v) with
    | [.tok (.ident s)] => lower s != "auto" && lower s != "span"
    | _ => false
  let fromLine := fun (other : String) => match found.lookup other with
    | some v => if identLine v then v else "auto"
    | none => "auto"
  if shorthand == "flex" then
    if canonical == "none" then (if l == "flex-basis" then "auto" else "0")
    else if l == "flex-basis" then "0%" else "1"
  else if l == "grid-row-end" then fromLine "grid-row-start"
  else if l == "grid-column-start" && shorthand == "grid-area" then fromLine "grid-row-start"
  else if l == "grid-column-end" then
    (match found.lookup "grid-column-start" with
     | some v => if identLine v then v else "auto"
     | none => if shorthand == "grid-area" then fromLine "grid-row-start" else "auto")
  else if l.startsWith "row-rule" && (lookup shorthand).any (fun r => r.longhands.any (·.startsWith "column-rule")) then
    (found.lookup ("column-" ++ (l.drop 4).toString)).getD (initialSpecified l)
  else initialSpecified l

/-- The gap rule shorthands of CSS Gaps 1 §4.3 whose value may be a list of rules and
`repeat()`s: each longhand is then the list of that part of each rule. -/
def gapRuleShorthands : List String := ["column-rule", "row-rule", "-webkit-column-rule"]

/-- A value with a top-level comma or a `repeat()`. -/
def isRuleList (top : List CV) : Bool :=
  top.any fun cv => match cv with
    | .tok .comma => true
    | .fn n _ => lower n == "repeat"
    | _ => false

/-- The `repeat()` of a rule list item: its count and its rules. -/
def repeatParts (item : List CV) : Option (List CV × List (List CV)) :=
  match item with
  | [.fn n args] =>
    if lower n == "repeat" then
      match splitCommas args with
      | cnt :: rules => some (stripWs cnt, rules.map stripWs)
      | [] => none
    else none
  | _ => none

/-! ### `background` and `background-position` (CSS Backgrounds 3 §3.10, §3.6) -/

/-- The horizontal and vertical parts of one `<bg-position>` (in its canonical text): one
value is the horizontal one but for `top`/`bottom`; two values are horizontal then vertical
unless their keywords say otherwise; three or four values are a keyword with its offset for
each axis, in either order. -/
def positionXY (text : String) : Option (String × String) :=
  let ws := (stripWs (CV.parse text)).map fun cv => serialize [cv]
  let horiz := fun (w : String) => w == "left" || w == "right"
  let vert := fun (w : String) => w == "top" || w == "bottom"
  let kw := fun (w : String) => horiz w || vert w || w == "center"
  match ws with
  | [a] => if vert a then some ("center", a) else some (a, "center")
  | [a, b] => if vert a || horiz b then some (b, a) else some (a, b)
  | _ =>
    -- groups of a keyword and the offset after it
    let groups := ws.foldl (fun (acc : List (List String)) w =>
      if kw w then [w] :: acc else match acc with
        | g :: rest => (g ++ [w]) :: rest
        | [] => [[w]]) [] |>.reverse
    match groups with
    | [g1, g2] =>
      let t1 := " ".intercalate g1
      let t2 := " ".intercalate g2
      if vert (g1.headD "") || horiz (g2.headD "") then some (t2, t1) else some (t1, t2)
    | _ => none

/-- The text of one position from its horizontal and vertical parts. -/
def positionText (x y : String) : String := x ++ " " ++ y

/-- The items of a comma-separated list value, as texts. -/
def listItems (v : String) : List String :=
  (splitCommas (stripWs (CV.parse v))).map fun g => serialize (stripWs g)

/-- The grammar of one `background` layer with its parts tagged; the last layer has a colour. -/
def bgLayerGrammar (final : Bool) : G :=
  let r := fun (n : String) => G.ref n none none
  .anyOf ([.tag "image" (r "bg-image"),
    .seq [.tag "position" (r "bg-position"), .rep (.seq [.lit '/', .tag "size" (r "bg-size")]) 0 (some 1) false],
    .tag "repeat" (r "repeat-style"), .tag "attachment" (r "attachment"),
    .tag "box1" (r "visual-box"), .tag "box2" (r "bg-clip")] ++ (if final then [.tag "color" (.prop "background-color")] else []))

/-- The longhands of a `background` value: each layer read alone, a part left out at its
initial value, one box the origin and the clip, the colour from the last layer. -/
def backgroundExpand (top : List CV) : Option (List (String × String)) := do
  let layers := (splitCommas top).map stripWs
  let n := layers.length
  let parts ← (layers.zipIdx).mapM fun (layer, i) =>
    (matchAll (env none) (bgLayerGrammar (i + 1 == n)) layer).map tagged
  let get := fun (ps : List (String × String)) (k d : String) => (ps.lookup k).getD d
  let xy ← parts.mapM fun ps => positionXY (get ps "position" "0% 0%")
  let origin := parts.map fun ps => match ps.lookup "box1", ps.lookup "box2" with
    | some b, _ => b
    | none, some b => if ["border-box", "padding-box", "content-box"].contains b then b else "padding-box"
    | none, none => "padding-box"
  let clip := parts.map fun ps => match ps.lookup "box1", ps.lookup "box2" with
    | _, some b => b
    | some b, none => b
    | none, none => "border-box"
  let join := fun (xs : List String) => ", ".intercalate xs
  some [("background-image", join (parts.map (get · "image" "none"))),
    ("background-position-x", join (xy.map (·.1))), ("background-position-y", join (xy.map (·.2))),
    ("background-size", join (parts.map (get · "size" "auto"))),
    ("background-repeat", join (parts.map (get · "repeat" "repeat"))),
    ("background-attachment", join (parts.map (get · "attachment" "scroll"))),
    ("background-origin", join origin), ("background-clip", join clip),
    ("background-color", ((parts.getLast?).bind (·.lookup "color")).getD "transparent")]

/-- The `background` value of its longhands, when their lists agree in length. -/
def backgroundText (get : String → String) : String :=
  let ls := ["background-image", "background-position-x", "background-position-y", "background-size",
    "background-repeat", "background-attachment", "background-origin", "background-clip"].map fun l => listItems (get l)
  let color := get "background-color"
  match ls with
  | [imgs, xs, ys, sizes, reps, atts, origins, clips] =>
    let n := imgs.length
    if !([xs, ys, sizes, reps, atts, origins, clips].all (·.length == n)) || n == 0 || color == "" then ""
    else
      let layer := fun (i : Nat) =>
        let pick := fun (xs : List String) => xs.getD i ""
        let pos := positionText (pick xs) (pick ys)
        let size := pick sizes
        let posPart := if pos != "0% 0%" || size != "auto" then [pos ++ (if size != "auto" then " / " ++ size else "")] else []
        let boxes := if pick origins == "padding-box" && pick clips == "border-box" then []
          else if pick origins == pick clips then [pick origins] else [pick origins, pick clips]
        let colorPart := if i + 1 == n && color != "transparent" then [color] else []
        let ps := (if pick imgs != "none" then [pick imgs] else []) ++ posPart ++
          (if pick reps != "repeat" then [pick reps] else []) ++ (if pick atts != "scroll" then [pick atts] else []) ++ boxes ++ colorPart
        if ps.isEmpty then "none" else " ".intercalate ps
      ", ".intercalate ((List.range n).map layer)
  | _ => ""

/-- `expand`, with `fuel` for a shorthand whose parts are shorthands. -/
def expandF : Nat → String → String → Option (List (String × String))
  | 0, _, _ => none
  | fuel + 1, property, value =>
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
            else if p == "background" then (backgroundExpand top).orElse fun _ => some [(p, canonical)]
            else if p == "background-position" then
              match (listItems canonical).mapM positionXY with
              | some xys => some [("background-position-x", ", ".intercalate (xys.map (·.1))),
                  ("background-position-y", ", ".intercalate (xys.map (·.2)))]
              | none => some [(p, canonical)]
            else if gapRuleShorthands.contains p && isRuleList top then
              -- a list of rules (CSS Gaps 1 §4.3): each rule read alone, each longhand the
              -- list of its part, `repeat()` kept around the parts it repeats
              let one := fun (item : List CV) =>
                (expandF fuel p (serialize item)).bind fun ls =>
                  if ls.length == 3 && ls.all (fun (n, _) => row.longhands.contains n) then some (ls.map (·.2)) else none
              let parts : Option (List (List String)) := ((splitCommas top).map stripWs).mapM fun item =>
                match repeatParts item with
                | some (cnt, rules) => do
                  let ts ← rules.mapM one
                  some ((List.range 3).map fun k =>
                    "repeat(" ++ serialize cnt ++ ", " ++ ", ".intercalate (ts.map fun t => t.getD k "") ++ ")")
                | none => one item
              parts.map fun ps => row.longhands.zipIdx.map fun (l, k) => (l, ", ".intercalate (ps.map fun t => t.getD k ""))
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
              | some .same =>
                match (matchAll (env none) (.prop (row.longhands.headD p)) top).map tagged with
                | some [a] => some (row.longhands.map fun l => (l, a.2))
                | _ => none
              | some .pair =>
                match row.longhands with
                | [l1, l2] =>
                  match (matchAll (env none) (.seq [.prop l1, .rep (.prop l2) 0 (some 1) false]) top).map tagged with
                  | some [a] => some [(l1, a.2), (l2, a.2)]
                  | some [a, b] => some [(l1, a.2), (l2, b.2)]
                  | _ => none
                | _ => none
              | some (.byGrammar g) =>
                match keywordLonghands p (lower canonical) with
                | some ds => some ds
                | none =>
                  match (matchAll (env none) g top).map tagged with
                  -- a value of an alternative that does not name its parts is kept whole
                  | none => some [(p, canonical)]
                  | some found =>
                    -- a part that is a shorthand gives its own longhands
                    let parts := found.map fun (n, t) =>
                      if row.longhands.contains n then some [(n, t)] else expandF fuel n t
                    let direct := parts.flatMap (·.getD [])
                    if parts.any (·.isNone) || direct.any (fun (n, _) => !row.longhands.contains n) then
                      -- a part kept whole (`column-rule: repeat(...)` in `rule`): so is the shorthand
                      some [(p, canonical)]
                    else
                      some (row.longhands.map fun l => (l, (direct.lookup l).getD (missingDefault p canonical direct l)))
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
                      | none => initialSpecified head
                    group.map fun l => (l, v))

/-- The longhand declarations that `property: value` stands for, each with its canonical
value: one for a longhand; for a shorthand its longhands, or the shorthand itself when it
has no generic shape here (it is then kept whole) or holds a substitution function. `none`:
not a valid declaration. -/
def expand (property value : String) : Option (List (String × String)) := expandF 4 property value

/-- The ways to write a shorthand by walking its grammar, the first choices first: each
named part gives its value, an optional part whose properties all have the value they
would get if left out is left out (`leaveOut`), `||` shows the parts that are not at their
default (the first if none is), and each alternative of `|` is a way (a keyword
alternative too, when `keywords`). The caller keeps the first way that expands back to the
same longhands. At most `ways` are kept at each step. -/
def unparse (value : String → String) (isDefault : String → Bool) (leaveOut keywords : Bool) : Nat → G → List (List String)
  | 0, _ => []
  | fuel + 1, g =>
    let skip := fun (g' : G) => leaveOut && (let ps := propsOf fuel g'; !ps.isEmpty && ps.all isDefault)
    let product := fun (gs : List G) =>
      gs.foldl (fun (acc : List (List String)) g' =>
        (acc.flatMap fun pre => (unparse value isDefault leaveOut keywords fuel g').map fun p => pre ++ p).take 8) [[]]
    match g with
    | .prop n => let v := value n; if v == "" then [] else [[v]]
    | .tag n _ => let v := value n; if v == "" then [] else [[v]]
    | .kw k =>
      match k.splitOn "=" with
      | [a] => [[a]]
      | [_, b] => [if b == "" then [] else [b]]
      | _ => []
    | .lit c => [[String.singleton c]]
    | .seq gs => product gs
    | .rep g' lo _ _ => if lo == 0 && skip g' then [[]] else unparse value isDefault leaveOut keywords fuel g'
    | .anyOf gs =>
      let shown := gs.filter fun g' => !skip g'
      product (if shown.isEmpty then gs.take 1 else shown)
    | .allOf gs => product gs
    | .oneOf gs =>
      ((gs.filter fun g' => keywords || !(propsOf fuel g').isEmpty).flatMap
        (unparse value isDefault leaveOut keywords fuel)).take 8
    | .req g' => unparse value isDefault leaveOut keywords fuel g'
    | _ => []

/-- The pieces of an unparsed value as text: one space between pieces, none before a comma. -/
def joinPieces (pieces : List String) : String := (" ".intercalate pieces).replace " ," ","

/-- `recombine`, with `fuel` for a shorthand whose parts are shorthands. -/
def recombineF : Nat → Property → (String → String) → String
  | 0, _, _ => ""
  | fuel + 1, row, get =>
    let vs := row.longhands.map get
    if vs.any (· == "") then ""
    else if row.name == "background" then backgroundText get
    else if row.name == "background-position" then
      let xs := listItems (get "background-position-x")
      let ys := listItems (get "background-position-y")
      if xs.length != ys.length then "" else ", ".intercalate ((xs.zip ys).map fun (x, y) => positionText x y)
    else if gapRuleShorthands.contains row.name && vs.any (fun v => isRuleList (stripWs (CV.parse v))) then
      -- a list of rules: each item put together from the same item of each longhand
      let lists := vs.map fun v => (splitCommas (stripWs (CV.parse v))).map stripWs
      let n := (lists.headD []).length
      if !lists.all (·.length == n) then ""
      else
        let single := fun (item : List (List CV)) =>
          recombineF fuel row fun l => match row.longhands.idxOf? l with
            | some k => serialize (item.getD k [])
            | none => ""
        let items := (List.range n).map fun i =>
          let item := lists.map fun xs => xs.getD i []
          match item.map repeatParts with
          | [some (c1, r1), some (c2, r2), some (c3, r3)] =>
            if serialize c1 == serialize c2 && serialize c2 == serialize c3 && r1.length == r2.length && r2.length == r3.length then
              let inner := (List.range r1.length).map fun j => single [r1.getD j [], r2.getD j [], r3.getD j []]
              if inner.any (· == "") then "" else "repeat(" ++ serialize c1 ++ ", " ++ ", ".intercalate inner ++ ")"
            else ""
          | [none, none, none] => single item
          | _ => ""
        if items.any (· == "") then "" else ", ".intercalate items
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
          | some .same => if rest.all (· == v) then v else ""
          | some .pair =>
            match vs with
            | [a, b] => if a == b then a else a ++ " " ++ b
            | _ => ""
          | some (.byGrammar g) =>
            let value := fun (n : String) =>
              if row.longhands.contains n then get n
              else match lookup n with
                | some sub => recombineF fuel sub get
                | none => ""
            let want := row.longhands.map fun l => (l, get l)
            -- a longhand is at its default when it has the value it would get if left out
            let atDefault := fun (l : String) => get l == missingDefault row.name "" want l
            let isDefault := fun (n : String) =>
              if row.longhands.contains n then atDefault n
              else match lookup n with
                | some sub => sub.longhands.all atDefault
                | none => false
            let attempt := fun (leaveOut : Bool) =>
              (unparse value isDefault leaveOut (row.name != "flex") 24 g).findSome? fun pieces =>
                let text := joinPieces pieces
                if text != "" && expandF 4 row.name text == some want then some text else none
            -- the `corner` shorthands (CSS Borders 4 §5.4) with every shape `round` are their radii
            let radii := (propsOf 24 g).find? fun n => n.startsWith "border-" && n.endsWith "radius"
            let roundOnly := row.name.startsWith "corner" && row.longhands.all fun l =>
              !(l.startsWith "corner-" && l.endsWith "-shape") || get l == "round"
            let sameRadius := match radii.bind lookup with
              | some sub => match sub.longhands.map get with
                | v :: rest => if v != "" && rest.all (· == v) && !v.contains ' ' then some v else none
                | [] => none
              | none => none
            match sameRadius, roundOnly with
            | some r, true => r
            | _, _ => ((attempt (row.name != "flex")).orElse fun _ => attempt false).getD ""
          | some .font =>
            let resetOk := row.longhands.all fun l => fontWritten.contains l || get l == initialSpecified l
            let variant := get "font-variant-caps"
            -- computed forms: a width keyword is a percentage, and a weight of 400 is `normal`
            let widthKeyword := fun (v : String) =>
              (["ultra-condensed", "extra-condensed", "condensed", "semi-condensed", "normal", "semi-expanded",
                "expanded", "extra-expanded", "ultra-expanded"].find? fun k => fontWidthName k == v).getD v
            let get := fun (l : String) =>
              let v := get l
              if l == "font-stretch" then widthKeyword v
              else if l == "font-weight" && v == "400" then "normal"
              else v
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
              let initial := initialSpecified head
              (v, uniform, v == initial)
            if parts.any (fun (_, uniform, _) => !uniform) then ""
            else
              match parts.filter (fun (_, _, isInitial) => !isInitial) with
              | [] => (parts.head?.map (·.1)).getD ""
              | shown => " ".intercalate (shown.map (·.1))

/-- A shorthand that `recombine` writes from its longhands: one of a generic shape, or
`background` and `background-position` (written by layers). -/
def recombinable (row : Property) : Bool :=
  (shapeOf row).isSome || row.name == "background" || row.name == "background-position"

/-- The value of a shorthand of a generic shape from the values of its longhands (`get`
answers "" for one that is not set): "" when it can not be written as one value. -/
def recombine (row : Property) (get : String → String) : String := recombineF 4 row get

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

/-- The filter functions whose argument is a number or percentage: whether the computed
value is clamped to 1 (Filter Effects 1 §11). -/
def filterAmounts : List (String × Bool) :=
  [("brightness", false), ("contrast", false), ("saturate", false),
   ("grayscale", true), ("invert", true), ("opacity", true), ("sepia", true)]

/-- The computed form of the filter functions in a value: a left-out argument is its
default, a percentage is a number, and the amount is clamped where the function says. The
recursion is on the nesting of the value. -/
def filterComputed : Nat → List CV → List CV
  | 0, cvs => cvs
  | fuel + 1, cvs => cvs.map fun cv => match cv with
    | .fn name args =>
      let n := lower name
      match filterAmounts.lookup n with
      | some clampOne =>
        let amount : Option Rat := match stripWs args with
          | [] => some 1
          | [.tok (.num x _)] => some x
          | [.tok (.pct x)] => some (x / 100)
          | _ => none
        match amount with
        | some x => .fn name [.tok (.num (if clampOne then ratMin 1 x else x) false)]
        | none => .fn name args
      | none =>
        if n == "blur" && (stripWs args).isEmpty then .fn name [.tok (.dim 0 true "px")]
        else if n == "hue-rotate" && (stripWs args).isEmpty then .fn name [.tok (.dim 0 true "deg")]
        else .fn name (filterComputed fuel args)
    | cv => cv

/-- The numeric keywords of `font-width` as percentages (CSS Fonts 4 §2.5). -/
def fontWidthKeyword : String → Option String
  | "ultra-condensed" => some "50%" | "extra-condensed" => some "62.5%" | "condensed" => some "75%"
  | "semi-condensed" => some "87.5%" | "normal" => some "100%" | "semi-expanded" => some "112.5%"
  | "expanded" => some "125%" | "extra-expanded" => some "150%" | "ultra-expanded" => some "200%"
  | _ => none

/-- The position keywords of one axis as percentages (CSS Backgrounds 3 §3.6). -/
def axisKeyword : String → Option String
  | "left" => some "0%" | "top" => some "0%" | "center" => some "50%" | "right" => some "100%" | "bottom" => some "100%"
  | _ => none

/-- The properties whose computed value is a number clamped to [0, 1]. -/
def unitIntervalProperties : List String :=
  ["opacity", "fill-opacity", "stroke-opacity", "stop-opacity", "flood-opacity", "shape-image-threshold"]

/-- The computed form of a `position-area` of logical keywords (CSS Anchor Positioning 1
§3.1.3): with the block axis first and the inline axis second the axis names are left out
(`block-start inline-end` is `start end`), equal keywords are one, and a keyword beside
`span-all` stands alone with its axis named. A value with a physical keyword, and a single
keyword, stay as they are. -/
def positionAreaComputed (v : String) : String :=
  let physical := fun (k : String) => ["left", "right", "top", "bottom", "x-", "y-"].any fun part =>
    (k.splitOn part).length > 1
  let strip := fun (k : String) => (k.replace "block-" "").replace "inline-" ""
  let named := fun (axis k : String) =>
    if k.endsWith "start" then (k.dropEnd 5).toString ++ axis ++ "start"
    else if k.endsWith "end" then (k.dropEnd 3).toString ++ axis ++ "end"
    else k
  match v.splitOn " " with
  | [b, i] =>
    if physical b || physical i then v
    else
      let b' := strip b
      let i' := strip i
      if b' == i' then b'
      else if i' == "span-all" && (b'.endsWith "start" || b'.endsWith "end") then named "block-" b'
      else if b' == "span-all" && (i'.endsWith "start" || i'.endsWith "end") then named "inline-" i'
      else b' ++ " " ++ i'
  | _ => v

/-- The computed forms that the grammar's leaves do not give, by property. -/
def computedForm (p v : String) : String :=
  -- a sum of a percentage and no length is the percentage
  let v := if (v.splitOn "+ 0px)").length > 1 then serialize (dropZeroLengths 8 (CV.parse v)) else v
  if lineWidthProperties.contains p then (lineWidthKeyword v).getD v
  else if shapeProperties.contains p then (shapeValue true p v).getD v
  else if p == "rotate" then rotateCanon v
  else if p == "offset-rotate" then offsetRotateComputed v
  else if p == "zoom" then zoomComputed v
  else if p == "word-spacing" then (if v == "normal" then "0px" else v)
  else if p == "letter-spacing" then (if v == "0px" then "normal" else v)
  else if p == "font-weight" then (if v == "normal" then "400" else if v == "bold" then "700" else v)
  else if p == "font-stretch" || p == "font-width" then (fontWidthKeyword v).getD v
  else if p == "position-area" then positionAreaComputed v
  else if p == "filter" || p == "backdrop-filter" then
    let cvs := stripWs (CV.parse v)
    serialize (filterComputed 8 cvs)
  else if unitIntervalProperties.contains p then
    match stripWs (CV.parse v) with
    | [.tok (.num x _)] => fmtRat (ratMax 0 (ratMin 1 x))
    | [.tok (.pct x)] => fmtRat (ratMax 0 (ratMin 1 (x / 100)))
    | _ => v
  else if ["background-position-x", "background-position-y", "mask-position-x", "mask-position-y"].contains p then
    ", ".intercalate ((splitCommas (stripWs (CV.parse v))).map fun item => match item with
      | [.tok (.ident k)] => (axisKeyword k).getD k
      | item => serialize item)
  else v

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
        let form := computedForm p (canonical p ((matchText (some ctx) row.name (stripWs cvs)).getD value))
        if p == "box-shadow" then shadowComputed 4 ctx.currentColor form
        else if p == "text-shadow" then shadowComputed 3 ctx.currentColor form
        else form

/-- The computed initial value of a property. -/
def initialComputed (ctx : ComputeCtx) (row : Property) : String :=
  match specified row.name row.initial with
  | some s => computed ctx row.name s
  | none => row.initial

/-! ### Tests -/

-- rule lists (CSS Gaps 1 §4.3)
#guard expand "column-rule" "repeat(auto, 5px solid yellow, 10px dotted blue)" == some [("column-rule-width", "repeat(auto, 5px, 10px)"),
  ("column-rule-style", "repeat(auto, solid, dotted)"), ("column-rule-color", "repeat(auto, yellow, blue)")]
#guard expand "column-rule" "thick, dashed, hotpink" == some [("column-rule-width", "thick, medium, medium"),
  ("column-rule-style", "none, dashed, none"), ("column-rule-color", "currentcolor, currentcolor, hotpink")]
#guard (lookup "column-rule").map (fun r => recombine r fun l => match l with
  | "column-rule-width" => "5px, repeat(4, 6px, 5px)" | "column-rule-style" => "double, repeat(4, none, solid)"
  | _ => "salmon, repeat(4, currentcolor, red)") == some "5px double salmon, repeat(4, 6px, 5px solid red)"
#guard specified "will-change" "auto, transform" == none && specified "will-change" "transform, none" == none
#guard specified "will-change" "transform, opacity" == some "transform, opacity" && specified "will-change" "auto" == some "auto"
-- a math function of a non-legacy colour function stays in the specified value (CSS Color 4)
#guard specified "color" "color(srgb calc(0.5 + 1) calc(0.5 - 1) calc(0.5) / calc(-0.5 + 1))" ==
  some "color(srgb calc(1.5) calc(-0.5) calc(0.5) / calc(0.5))"
#guard specified "color" "lab(calc(50 * 3) calc(0.5 - 1) calc(1.5) / calc(-0.5 + 1))" ==
  some "lab(calc(150) calc(-0.5) calc(1.5) / calc(0.5))"
#guard specified "color" "lab(calc(50%) 62.5 0.5)" == some "lab(calc(50%) 62.5 0.5)"
#guard specified "color" "lab(none 20 calc(0.5))" == some "lab(none 20 calc(0.5))"
#guard specified "color" "rgb(calc(255) 0 0)" == some "rgb(255, 0, 0)"
#guard computed {} "color" "lab(calc(50 * 3) 0 0)" == "lab(100 0 0)"
-- infinities and NaN in colour channels (color-valid-rgb.html, color-computed-lab.html)
#guard specified "color" "rgb(calc(infinity), 0, 0)" == some "rgb(255, 0, 0)"
#guard specified "color" "rgba(0, 0, 0, calc(NaN))" == some "rgba(0, 0, 0, 0)"
#guard specified "color" "hsl(calc(infinity) 100% 50%)" == some "rgb(255, 0, 0)"
-- the default interpolation method of a gradient is left out (gradient-interpolation-method-valid.html)
#guard specified "background-image" "linear-gradient(in oklab, color(srgb 1 0 0), blue)" == some "linear-gradient(color(srgb 1 0 0), blue)"
#guard specified "background-image" "linear-gradient(30deg in srgb, red, blue)" == some "linear-gradient(30deg, red, blue)"
#guard specified "background-image" "linear-gradient(in srgb, red, 50%, blue)" == some "linear-gradient(red, 50%, blue)"
#guard specified "background-image" "linear-gradient(in oklab, red, blue)" == some "linear-gradient(in oklab, red, blue)"
#guard specified "background-image" "linear-gradient(in oklch longer hue, red, blue)" == some "linear-gradient(in oklch longer hue, red, blue)"
-- background (background-valid.html)
#guard expand "background" "none" == some [("background-image", "none"), ("background-position-x", "0%"),
  ("background-position-y", "0%"), ("background-size", "auto"), ("background-repeat", "repeat"),
  ("background-attachment", "scroll"), ("background-origin", "padding-box"), ("background-clip", "border-box"),
  ("background-color", "transparent")]
#guard (expand "background" "border-box content-box").map (·.lookup "background-clip") == some (some "content-box")
#guard (lookup "background").map (fun r => recombine r fun l => ((expand "background" "url(\"a\") 1px 2px / 3px 4px space round local padding-box content-box, rgb(5, 6, 7) url(\"a\") 1px 2px / 3px 4px space round local padding-box content-box").getD []).lookup l |>.getD "") ==
  some "url(\"a\") 1px 2px / 3px 4px space round local padding-box content-box, url(\"a\") 1px 2px / 3px 4px space round local padding-box content-box rgb(5, 6, 7)"
#guard (lookup "background").map (fun r => recombine r fun l => ((expand "background" "none").getD []).lookup l |>.getD "") == some "none"
#guard (lookup "background").map (fun r => recombine r fun l => ((expand "background" "red").getD []).lookup l |>.getD "") == some "red"
#guard positionXY "top left" == some ("left", "top") && positionXY "right 10px top 5px" == some ("right 10px", "top 5px")
#guard specified "flex" "0 1 1" == none
#guard specified "flex" "0 1" == some "0 1" && (specified "flex" "0 auto").isSome && (specified "flex" "1 0 0").isSome
#guard specified "color" "RED" == some "red"
#guard specified "color" "#f00" == some "rgb(255, 0, 0)"
#guard specified "color" "1px" == none
#guard specified "COLOR" "inherit" == some "inherit"
#guard specified "width" "calc(1px + 2px)" == some "calc(3px)"
#guard specified "width" "-1px" == none
#guard specified "width" "var(--x)" == some "var(--x)"
#guard specified "--x" " a  b " == some "a  b"
#guard specified "--x" "{ a: b }" == some "{ a: b }"
#guard specified "--x" "a ; b" == none
#guard specified "--x" "a )" == none
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
#guard expand "flex" "1" == some [("flex-grow", "1"), ("flex-shrink", "1"), ("flex-basis", "0%")]
#guard expand "flex" "none" == some [("flex-grow", "0"), ("flex-shrink", "0"), ("flex-basis", "auto")]
#guard expand "flex" "auto" == some [("flex-grow", "1"), ("flex-shrink", "1"), ("flex-basis", "auto")]
#guard expand "grid-row" "2 / span 3" == some [("grid-row-start", "2"), ("grid-row-end", "span 3")]
#guard expand "grid-row" "foo" == some [("grid-row-start", "foo"), ("grid-row-end", "foo")]
#guard expand "grid-row" "2" == some [("grid-row-start", "2"), ("grid-row-end", "auto")]
#guard expand "grid-area" "a / b" == some [("grid-row-start", "a"), ("grid-column-start", "b"), ("grid-row-end", "a"), ("grid-column-end", "b")]
#guard expand "rule-inset" "10px 20px / 30px" == some [("column-rule-inset-cap-start", "10px"), ("column-rule-inset-cap-end", "20px"),
  ("column-rule-inset-junction-start", "30px"), ("column-rule-inset-junction-end", "30px"),
  ("row-rule-inset-cap-start", "10px"), ("row-rule-inset-cap-end", "20px"),
  ("row-rule-inset-junction-start", "30px"), ("row-rule-inset-junction-end", "30px")]
#guard expand "corner-shape" "bevel scoop" == some [("corner-top-left-shape", "bevel"), ("corner-top-right-shape", "scoop"),
  ("corner-bottom-right-shape", "bevel"), ("corner-bottom-left-shape", "scoop")]
#guard expand "container" "foo / inline-size" == some [("container-name", "foo"), ("container-type", "inline-size")]
#guard (lookup "flex").map (fun row => recombine row fun l => if l == "flex-basis" then "0%" else "1") == some "1 1 0%"
#guard (lookup "grid-row").map (fun row => recombine row fun l => if l == "grid-row-start" then "2" else "auto") == some "2"
#guard (lookup "grid-row").map (fun row => recombine row fun l => if l == "grid-row-start" then "2" else "span 3") == some "2 / span 3"
#guard (lookup "container").map (fun row => recombine row fun l => if l == "container-name" then "foo" else "normal") == some "foo"
#guard computed {} "width" "2em" == "32px"
#guard computed {} "filter" "blur()" == "blur(0px)"
#guard computed {} "filter" "invert(200%) brightness(300%)" == "invert(1) brightness(3)"
#guard computed {} "filter" "hue-rotate() drop-shadow(1px 2px red)" == "hue-rotate(0deg) drop-shadow(rgb(255, 0, 0) 1px 2px)"
#guard computed {} "opacity" "-2" == "0"
#guard computed {} "position-area" "block-start inline-start" == "start"
#guard computed {} "position-area" "block-end span-inline-start" == "end span-start"
#guard computed {} "position-area" "span-block-end center" == "span-end center"
#guard computed {} "position-area" "center self-inline-end" == "center self-end"
#guard computed {} "position-area" "self-start span-all" == "self-block-start"
#guard computed {} "position-area" "left top" == "left top"
#guard computed {} "position-area" "block-start" == "block-start"
#guard computed {} "opacity" "50%" == "0.5"
#guard computed {} "font-stretch" "condensed" == "75%"
#guard computed {} "background-position-x" "center, left" == "50%, 0%"
#guard specified "scale" "100% 200% 1" == some "1 2"
#guard specified "scale" "2 2" == some "2"
#guard specified "scale" "1%" == some "0.01"
#guard computed {} "color" "red" == "rgb(255, 0, 0)"
#guard computed { currentColor := some "rgb(0, 128, 0)" } "border-top-color" "currentcolor" == "rgb(0, 128, 0)"
#guard computed {} "border-top-width" "medium" == "3px"
#guard computed {} "margin-top" "calc(1em + 2px)" == "18px"

end L4Factoidal.Rendering.CssValues
