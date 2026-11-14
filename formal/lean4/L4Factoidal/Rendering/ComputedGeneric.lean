/-
L4Factoidal.Rendering.ComputedGeneric — `getComputedStyle` for every property of the
property table (`CssValues`), beside the layout profile's own answers (`ComputedValues`).

The layout profile (`Style.Computed`) computes the properties layout reads. A page script
may ask for any property. For a property outside the profile, and for the keyword and
colour properties of the profile when the element itself declares them, the answer is made
here, when it is asked for: the cascade of that one property over the rules that match the
element and its `style` attribute (CSS Cascade 4 §6.1, the same order as
`CSS.computedFrom`), then inheritance or the initial value (§7), `var()` substitution
(CSS Variables 1 §3), and the computed value of the table's grammar
(`CssValues.computed`).

Nothing here runs unless a script reads a computed style: the page's cascade and layout
do not use it.
-/
import L4Factoidal.Rendering.Style
import L4Factoidal.Rendering.ComputedValues
import L4Factoidal.Rendering.CssValues.Declaration
import L4Factoidal.Rendering.CssRegister
import Std.Data.HashMap

namespace L4Factoidal.Rendering.ComputedGeneric
open L4Factoidal.Rendering.CSS
open L4Factoidal.Rendering

/-- A custom function (`@function`, CSS Mixins 1 §2): its parameters (name, syntax text or
"" for none, default value), its return syntax ("" for none), its local custom properties
in order, and its `result`. -/
structure FnDef where
  params : List (String × String × Option String) := []
  returns : String := ""
  locals : List (String × String) := []
  result : Option String := none
  deriving Inhabited

/-- What the answers are made from: the document, the rules that match an element, the
layout profile's styles, and the viewport in px. -/
structure View where
  dom : DOM.Dom
  matchesOf : Nat → List Match
  styles : Array Computed
  viewportW : Nat := 800
  viewportH : Nat := 600
  /-- The registered custom properties (CSS Properties and Values API 1): name and
  registration, the one that counts first. Read only when a custom property is asked for. -/
  registered : Thunk (List (String × CssRegister.PropertyRule)) := Thunk.pure []
  /-- The rules of the page, for the styles of pseudo-elements (`computedPseudo`). -/
  rules : List CSS.Rule := []
  /-- The page's custom functions (`@function`), read when a value calls one. -/
  functions : Thunk (List (String × FnDef)) := Thunk.pure []
  /-- The padding box of an element's laid-out box, width and height in CSS pixels, when the
  host has laid the page out: the containing block of percentage insets (`insetBase`). Asked
  only for an inset that is a percentage. -/
  paddingBox : Nat → Option (Float × Float) := fun _ => none

/-- The properties registered by scripts (`CSS.registerProperty`), as the document node
keeps them (`Hosts.Dom.Command.registerProperty`: attributes whose name starts with U+0001
and `property `). They win over `@property` rules (§3). -/
def registrationsOfDocument (dom : DOM.Dom) : List (String × CssRegister.PropertyRule) :=
  if dom.nodes.isEmpty then []
  else (dom.get 0).attrs.toList.filterMap fun a =>
    if a.lname.startsWith "\x01property " then
      (CssRegister.entryRule a.value).map fun r => ((a.lname.drop 10).toString, r)
    else none

/-- The registrations of the `@property` rules of a document's style sheets (§3), the last
of a name first. A sheet text with no `@property` is not read again. -/
def registrationsOf (source : String) : List (String × CssRegister.PropertyRule) :=
  if (source.splitOn "@property").length ≤ 1 then []
  else
    ((CSS.sheetLeaves source).toList.filterMap fun leaf =>
      if leaf.kind == "property" then
        (CssRegister.propertyRuleOf leaf.prelude leaf.body).map fun r => (leaf.prelude.trimAscii.toString, r)
      else none).reverse

/-- A non-negative float as a rational, to a thousandth. -/
def ratOf (x : Float) : Rat :=
  if x.isFinite && x > 0 then ((x * 1000).round.toUInt64.toNat : Rat) / 1000 else 0

/-- The order of cascade keys: the cascade's own (`CSS.lexLE`). -/
abbrev keyLE : List Nat → List Nat → Bool := CSS.lexLE

/-- For each property, the names of the shorthands that have it as a longhand, and the
legacy names of the property and of those shorthands. Built once (a lazy constant). -/
def coverIndex : Thunk (Std.HashMap String (List String)) := Thunk.mk fun _ =>
  let add := fun (m : Std.HashMap String (List String)) (k v : String) => m.insert k (v :: (m[k]?).getD [])
  let m := CssValues.Data.properties.foldl (fun m (n, _, _, _, ls) =>
    if ls == "" then m else (ls.splitOn " ").foldl (fun m l => if l == "" then m else add m l n) m) {}
  CssValues.Data.aliases.foldl (fun m (alias, target) =>
    -- the alias of a longhand sets it; the alias of a shorthand sets its longhands
    let m := add m target alias
    match CssValues.lookup target with
    | some row => row.longhands.foldl (fun m l => add m l alias) m
    | none => m) m

/-- The property names whose declarations can set property `p`: `p`, the shorthands that
have it as a longhand, and the legacy names of those. -/
def coveringNames (p : String) : List String := p :: (coverIndex.get[p]?).getD []

/-- A rule that matches the element, or its `style` attribute, may declare a flow-relative
property (`CssValues.Logical.mentions`). When none does, a physical property is cascaded
alone and the element's flow is not looked up. -/
def usesLogical (v : View) (id : Nat) : Bool :=
  ((v.matchesOf id).any fun (_, rule, _) => rule.usesLogical) ||
    (CssValues.declNames (attrValue (v.dom.get id) "style")).any CssValues.Logical.mentions

/-- A cascaded value that is a shorthand declaration kept whole because it holds `var()`
(CSS Variables 1 §3: "pending-substitution"): the shorthand's name and its value, marked
so that no value text is taken for it. -/
def pendingShorthand (shorthand raw : String) : String := "\x02" ++ shorthand ++ "\x00" ++ raw

/-- The shorthand and value of a `pendingShorthand` text. -/
def pendingOf (value : String) : Option (String × String) :=
  if value.startsWith "\x02" then
    match ((value.drop 1).toString).splitOn "\x00" with
    | sh :: rest => some (sh, "\x00".intercalate rest)
    | [] => none
  else none

#guard pendingOf (pendingShorthand "margin" "var(--a) 1px") == some ("margin", "var(--a) 1px")
#guard pendingOf "1px" == none

/-- The cascaded value of property `p` (a name of the table, or a custom property) on
element `id`: the canonical specified value of the winning declaration. `also` is the
flow-relative name of `p` in the element's flow, when it has one (CSS Logical 1 §4.1): its
declarations are declarations of `p`. -/
def cascadedAll (v : View) (id : Nat) (p : String) (also : Option String := none) : List (List Nat × String) := Id.run do
  let n := v.dom.get id
  -- `all` sets every property but `direction`, `unicode-bidi` and the custom properties
  -- (CSS Cascade 4 §3.2), to a CSS-wide keyword
  let allApplies := !CssValues.isCustom p && p != "direction" && p != "unicode-bidi"
  let names := if allApplies then "all" :: coveringNames p else coveringNames p
  let names := match also with
    | some q => names ++ coveringNames q
    | none => names
  let mut best : List (List Nat × String) := []
  let mut order : Nat := 0
  let consider := fun (best : List (List Nat × String)) (key : List Nat) (d : Declaration) =>
    if names.contains d.property then
      let value := if d.property == "all" then CssValues.specified "all" d.value
        else (CssValues.expand d.property d.value).bind fun ls =>
          ((ls.lookup p).orElse fun _ => also.bind fun q => ls.lookup q).orElse fun _ =>
            -- a shorthand kept whole for its `var()`: its longhands are known after substitution
            (ls.lookup d.property).bind fun raw => if d.property != p then some (pendingShorthand d.property raw) else none
      match value with
      | some value => (key, value) :: best
      | none => best
    else best
  for (origin, rule, matched) in v.matchesOf id do
    let specificity := matched.foldl (fun m s =>
      if keyLE [m.1, m.2.1, m.2.2] [s.specificity.1, s.specificity.2.1, s.specificity.2.2] then s.specificity else m) (0, 0, 0)
    let onlyVisited := matched.all (·.visitedDependent)
    for d in rule.declarations do
      if !onlyVisited || visitedProperties.contains d.property then
        best := consider best (ruleKey d.important origin rule.scope.isSome rule.layer specificity order) d
      order := order + 1
  for d in CssValues.Block.parseOnly names (attrValue n "style") do
    let key := inlineKey d.important order
    if d.name == p || d.name == "all" || some d.name == also then best := (key, d.value) :: best
    else if CssValues.hasSubstitution (CssValues.CV.parse d.value) then
      -- a covering shorthand kept whole for its `var()`
      best := (key, pendingShorthand d.name d.value) :: best
    order := order + 1
  return best

/-- The winning value among cascaded declarations (key, value), with `revert-layer` and
`revert` rolled back (CSS Cascade 5 §7.3.2, §7.3.1): `revert-layer` gives the best
declaration of an earlier layer (the first four entries of the key: importance, origin and
context, attachment, layer); `revert` the best one of an earlier origin (the first two).
`none`: no declaration is left. At most one step for each declaration. -/
def bestOf (cands : List (List Nat × String)) : Option (List Nat × String) :=
  cands.foldl (fun (b : Option (List Nat × String)) c =>
    match b with
    | some b' => if keyLE b'.1 c.1 then some c else some b'
    | none => some c) none

/-- `winning` with `fuel` steps of rolling back (a tail call). -/
def winningF : Nat → List (List Nat × String) → Option String
  | 0, _ => none
  | fuel + 1, left =>
    match bestOf left with
    | none => none
    | some (key, value) =>
      if CssValues.lower value == "revert-layer" then winningF fuel (left.filter fun c => !keyLE (key.take 4) (c.1.take 4))
      else if CssValues.lower value == "revert" then winningF fuel (left.filter fun c => !keyLE (key.take 2) (c.1.take 2))
      else some value

def winning (cands : List (List Nat × String)) : Option String := winningF (cands.length + 1) cands

/-- Kind: policy. Says: the cascaded value is never `revert` or `revert-layer`: those roll
back to another declaration, or to none. -/
theorem winningF_not_revert (fuel : Nat) (cands : List (List Nat × String)) (v : String)
    (h : winningF fuel cands = some v) :
    CssValues.lower v ≠ "revert-layer" ∧ CssValues.lower v ≠ "revert" := by
  induction fuel generalizing cands with
  | zero => simp [winningF] at h
  | succ n ih =>
    unfold winningF at h
    split at h
    · simp at h
    · rename_i key value _
      split at h
      · exact ih _ h
      · split at h
        · exact ih _ h
        · rename_i h1 h2
          simp at h
          subst h
          exact ⟨fun e => h1 (by simp [e]), fun e => h2 (by simp [e])⟩

/-- The cascaded value of property `p` on element `id` (see `cascadedAll`), with
`revert-layer` and `revert` rolled back. -/
def cascaded (v : View) (id : Nat) (p : String) (also : Option String := none) : Option String :=
  winning (cascadedAll v id p also)

#guard winning [([0, 2, 0, 1, 0], "red"), ([0, 2, 0, 3, 0], "revert-layer"), ([0, 2, 0, 2, 0], "blue")] == some "blue"
#guard winning [([0, 2, 0, 1, 0], "red"), ([0, 2, 0, 1, 1], "revert-layer")] == none
#guard winning [([0, 0, 0, 0, 0], "ua"), ([0, 2, 0, 1, 0], "red"), ([0, 2, 0, 9, 0], "revert")] == some "ua"
#guard winning [([0, 2, 0, 1, 0], "red"), ([0, 2, 0, 1, 1], "green")] == some "green"

/-- The pseudo-elements whose computed style a page may ask for, in the order of their
numbers (`valueAt`: `pseudoBase` times the position plus one, plus the property's index). -/
def pseudoNames : List String :=
  ["before", "after", "marker", "first-line", "first-letter", "placeholder", "selection", "backdrop",
   "file-selector-button", "target-text", "spelling-error", "grammar-error", "details-content", "checkmark",
   "picker-icon", "scroll-marker", "column"]

/-- Whether property `p` applies to pseudo-element `pe` (CSS Pseudo-Elements 4 §2.3, §2.5,
§3.1, §4.2): `::first-line` and `::placeholder` take the font, colour, background and text
decoration properties and the like; `::first-letter` those and the box properties;
`::marker` the font and colour and a few more; the highlight pseudo-elements a handful of
paint properties. A declaration of another property there is ignored. -/
def appliesToPseudo (pe p : String) : Bool :=
  let pre := fun (xs : List String) => xs.any fun x => p.startsWith x
  let lineProps := CssValues.isCustom p || pre ["font", "background", "text-decoration", "text-emphasis", "animation", "transition"] ||
    ["color", "opacity", "word-spacing", "letter-spacing", "text-justify", "text-shadow", "text-transform",
     "text-underline-position", "text-underline-offset", "vertical-align", "line-height", "ruby-position", "all"].contains p
  match pe with
  | "first-line" | "placeholder" => lineProps
  | "first-letter" => lineProps || pre ["margin", "padding", "border", "box-shadow", "float", "inset", "corner"]
  | "marker" => CssValues.isCustom p || pre ["font", "animation", "transition"] ||
      ["color", "white-space", "white-space-collapse", "text-wrap-mode", "text-combine-upright", "unicode-bidi",
       "direction", "content", "line-height", "all"].contains p
  | "selection" | "target-text" | "spelling-error" | "grammar-error" =>
    CssValues.isCustom p || pre ["text-decoration"] ||
      ["color", "background-color", "text-shadow", "stroke-color", "fill-color", "stroke-width", "all"].contains p
  | _ => true

#guard appliesToPseudo "first-line" "font-size" && !appliesToPseudo "first-line" "margin-left"
#guard appliesToPseudo "first-letter" "margin-left" && !appliesToPseudo "marker" "background-color"

/-- The cascaded value of property `p` on pseudo-element `pe` of element `id` (CSS
Pseudo-Elements 4 §3): the declarations of the rules whose selectors name `pe` and match the
element, in the order of the cascade (`winning`). -/
def cascadedPseudo (v : View) (id : Nat) (pe : String) (p : String) : Option String :=
  if !appliesToPseudo pe p then none else
  let names := "all" :: coveringNames p
  let cands := (v.rules.zipIdx).foldl (fun acc (rule, order) =>
    match rule.selectors.find? (fun sel => match sel.complex with
        | some c => DOM.Selectors.matchesPseudo v.dom id c pe
        | none => false) with
    | none => acc
    | some sel =>
      rule.declarations.foldl (fun acc d =>
        if !names.contains d.property then acc
        else
          let value := if d.property == "all" then CssValues.specified "all" d.value
            else (CssValues.expand d.property d.value).bind (·.lookup p)
          match value with
          | some value => (ruleKey d.important 1 rule.scope.isSome rule.layer sel.specificity order, value) :: acc
          | none => acc) acc) []
  winning cands

def parentElement (dom : DOM.Dom) (id : Nat) : Option Nat :=
  match (dom.get id).parent with
  | some p => if (dom.get p).type == .element then some p else none
  | none => none

/-- The root element of the document of the view. -/
def rootElement (dom : DOM.Dom) : Option Nat :=
  (dom.get 0).kids.toList.find? fun k => (dom.get k).type == .element

/-- The lengths a computed value is computed against, for element `id`. -/
def numCtx (v : View) (id : Nat) : CssValues.Ctx :=
  let style := v.styles[id]?.getD {}
  let root := ((rootElement v.dom).bind (v.styles[·]?)).getD {}
  { fontSize := ratOf style.fontSize, rootFontSize := ratOf root.fontSize,
    lineHeight := ratOf style.lineHeight, rootLineHeight := ratOf root.lineHeight,
    viewportW := (v.viewportW : Rat), viewportH := (v.viewportH : Rat) }

/-- The kind of a component value for the table of CSS Syntax 3 §9 (two tokens that would
read as other tokens when written next to each other). -/
def tokKind (cv : CssValues.CV) : String :=
  match cv with
  | .tok (.ident _) => "ident"
  | .tok (.func _) | .fn _ _ => "function"
  | .tok (.url _) | .tok .badUrl => "url"
  | .tok (.atKeyword _) => "at"
  | .tok (.hash _ _) => "hash"
  | .tok (.num _ _) => "number"
  | .tok (.pct _) => "percentage"
  | .tok (.dim _ _ _) => "dimension"
  | .tok .cdc => "cdc"
  | .tok (.delim c) => String.singleton c
  | .block '(' _ => "("
  | _ => ""

/-- Whether a comment must be written between `a` and `b` (CSS Syntax 3 §9). -/
def needsComment (a b : CssValues.CV) : Bool :=
  let x := tokKind a
  let y := tokKind b
  let identLike := ["ident", "function", "url", "-", "number", "percentage", "dimension", "cdc"]
  if x == "ident" then identLike.contains y || y == "("
  else if x == "at" || x == "hash" || x == "dimension" then identLike.contains y
  else if x == "#" || x == "-" then ["ident", "function", "url", "-", "number", "percentage", "dimension"].contains y && !(x == "-" && y == "-")
  else if x == "number" then ["ident", "function", "url", "number", "percentage", "dimension", "%"].contains y
  else if x == "@" then ["ident", "function", "url", "-"].contains y
  else if x == "." || x == "+" then ["number", "percentage", "dimension"].contains y
  else if x == "/" then y == "*"
  else false

/-- `a` followed by `b`, with an empty comment between them where the two would otherwise
read as other tokens. -/
def joinTokens (a b : List CssValues.CV) : List CssValues.CV :=
  match a.getLast?, b.head? with
  | some x, some y => if needsComment x y then a ++ [.raw "/**/"] ++ b else a ++ b
  | _, _ => a ++ b

#guard needsComment (.tok (.ident "foo")) (.tok (.ident "bar")) && !needsComment (.tok (.ident "a")) (.tok .comma)

/-- The groups of `cvs` between top-level tokens `sep`. -/
def splitAt (sep : CssValues.Tok) (cvs : List CssValues.CV) : List (List CssValues.CV) :=
  let (groups, last) := cvs.foldl (fun (acc : List (List CssValues.CV) × List CssValues.CV) cv =>
    match cv with
    | .tok t => if t == sep then (acc.2.reverse :: acc.1, []) else (acc.1, cv :: acc.2)
    | cv => (acc.1, cv :: acc.2)) ([], [])
  (last.reverse :: groups).reverse

/-- A condition of `if()` (CSS Values 5 §9.1): `style()`, `supports()` and `media()`
queries, `not`, `and`, `or` and parentheses; `else` holds. A style query compares a custom
property's computed value with a value (`var()` in it substituted by `subst`; `initial`
is the guaranteed-invalid value), or asks that it has one. `none`: not a condition.
The recursion is on the nesting of the condition. -/
def ifCondition (get : String → String) (subst : List CssValues.CV → Option (List CssValues.CV)) :
    Nat → List CssValues.CV → Option Bool
  | 0, _ => none
  | fuel + 1, cvs =>
    let ts := CssValues.stripWs cvs
    let isKw := fun (k : String) (cv : CssValues.CV) => match cv with
      | .tok (.ident s) => CssValues.lower s == k
      | _ => false
    -- `a and b and c`, `a or b`: one operator at a level
    let parts := fun (k : String) =>
      let (groups, last) := ts.foldl (fun (acc : List (List CssValues.CV) × List CssValues.CV) cv =>
        if isKw k cv then (acc.2.reverse :: acc.1, []) else (acc.1, cv :: acc.2)) ([], [])
      (last.reverse :: groups).reverse
    let ands := parts "and"
    let ors := parts "or"
    if ands.length > 1 then (ands.mapM (ifCondition get subst fuel)).map (·.all id)
    else if ors.length > 1 then (ors.mapM (ifCondition get subst fuel)).map (·.any id)
    else
      match ts with
      | [k] => if isKw "else" k then some true else
        match k with
        | .block '(' inner => ifCondition get subst fuel inner
        | .fn name args =>
          let n := CssValues.lower name
          if n == "supports" then some (CssSupports.ruleHolds (CssValues.rawText args) || CssSupports.ruleHolds ("(" ++ CssValues.rawText args ++ ")"))
          else if n == "media" then none
          else if n == "style" then
            let inner := CssValues.stripWs args
            match inner with
            | [.block '(' _] | _ :: _ :: _ =>
              -- a style query: `--x: v`, `--x`, or a condition of them in parentheses
              match inner with
              | .tok (.ident x) :: .tok .colon :: v =>
                if !CssValues.isCustom x then none
                else
                  let want := CssValues.stripWs v
                  let cur := (get x).trimAscii.toString
                  match want with
                  | [.tok (.ident k)] =>
                    if CssValues.lower k == "initial" then some (cur == "")
                    else if CssValues.cssWide.contains (CssValues.lower k) then some false
                    else some (cur == CssValues.rawText want)
                  | _ =>
                    match subst want with
                    | some w => some (cur == (CssValues.rawText w).trimAscii.toString && cur != "")
                    | none => some false
              | _ => ifCondition get subst fuel (inner.map fun cv => match cv with
                  | .block '(' b => CssValues.CV.fn "style" b
                  | cv => cv)
            | [.tok (.ident x)] => if CssValues.isCustom x then some ((get x) != "") else none
            | _ => none
          else none
        | _ => none
      | [k, x] => if isKw "not" k then (ifCondition get subst fuel [x]).map (!·) else none
      | _ => none


/-- The syntax text of a parameter or return type: `<length>`, `type(<length> | auto)`, `*`. -/
def typeText (cvs : List CssValues.CV) : String :=
  match CssValues.stripWs cvs with
  | [.fn n args] => if CssValues.lower n == "type" then CssValues.rawText args else CssValues.rawText cvs
  | ts => CssValues.rawText ts

/-- An `@function` rule from its prelude and the declarations of its block, when the prelude
is `--name(<parameters>) [returns <type>]`. -/
def fnDefOf (prelude : String) (decls : List SheetReader.Decl) : Option (String × FnDef) :=
  match CssValues.stripWs (CssValues.CV.parse prelude) with
  | .fn name args :: rest =>
    if !CssValues.isCustom name then none
    else
      let params := (CssValues.splitCommas args).filterMap fun g =>
        match CssValues.stripWs g with
        | .tok (.ident p) :: more =>
          let (ty, dflt) := match splitAt .colon more with
            | [t] => (typeText t, none)
            | t :: d => (typeText t, some (CssValues.rawText (CssValues.stripWs (d.foldl (· ++ ·) []))))
            | [] => ("", none)
          some (p, ty, dflt)
        | _ => none
      let returns := match rest with
        | .tok (.ident r) :: ty => if CssValues.lower r == "returns" then typeText ty else ""
        | _ => ""
      let locals := decls.filterMap fun d => if CssValues.isCustom d.name then some (d.name, d.value) else none
      let result := (decls.filter (·.name == "result")).getLast?.map (·.value)
      some (name, { params, returns, locals, result })
  | _ => none

/-- The value of a typed parameter or result: its computed value by the syntax, `none` when
it is not a value of it; an untyped one as it is. -/
def typedValue (ty value : String) : Option String :=
  if ty == "" || ty.trimAscii.toString == "*" then some value
  else CssRegister.computedValue {} ty value

/-- A value with a custom function call (`--name(...)`) in it. -/
def hasDashedFn : Nat → List CssValues.CV → Bool
  | 0, _ => false
  | fuel + 1, cvs => cvs.any fun cv => match cv with
    | .fn n args => CssValues.isCustom n || hasDashedFn fuel args
    | .block _ b => hasDashedFn fuel b
    | _ => false

/-- The custom functions of a document's style sheets (`@function`, CSS Mixins 1 §2), the
last of a name first. A sheet text with no `@function` is not read again. -/
def functionsOf (source : String) : List (String × FnDef) :=
  if (source.splitOn "@function").length ≤ 1 then []
  else
    ((CSS.sheetLeaves source).toList.filterMap fun leaf =>
      if leaf.kind == "function" then fnDefOf leaf.prelude (SheetReader.splitDecls leaf.body) else none).reverse

/-- The value of a call of custom function `f` with arguments `args` (CSS Mixins 1 §2.4):
the arguments (substituted in the caller's scope) bound to the parameters, a missing one to
its default (read in the function's scope so far) or to the guaranteed-invalid value; the
locals in order; then the result. A typed parameter or result takes its computed value by
its syntax, and a value not of it makes the call invalid (`none`). `subst g` substitutes
with lookup `g`. -/
def callFn (get : String → String) (f : FnDef) (args : List CssValues.CV)
    (subst : (String → String) → List CssValues.CV → Option (List CssValues.CV)) : Option (List CssValues.CV) := do
  let argGroups := ((CssValues.splitCommas args).map CssValues.stripWs).filter (fun a => !a.isEmpty)
  let argVals ← argGroups.mapM fun a => (subst get a).map CssValues.rawText
  if argVals.length > f.params.length then failure
  let mut env : List (String × String) := []
  for ((p, ty, dflt), i) in f.params.zipIdx do
    let scope := env
    let look := fun (n : String) => (scope.lookup n).getD (get n)
    let raw : Option String := match argVals[i]? with
      | some a => some a
      | none => dflt.map fun d => ((subst look (CssValues.CV.parse d)).map CssValues.rawText).getD ""
    match raw with
    | some r =>
      if r == "" then env := (p, "") :: env
      else
        let t ← typedValue ty r
        env := (p, t) :: env
    | none => env := (p, "") :: env
  for (n, val) in f.locals do
    let scope := env
    let look := fun (x : String) => (scope.lookup x).getD (get x)
    let t := ((subst look (CssValues.CV.parse val)).map fun ts => (CssValues.rawText ts).trimAscii.toString).getD ""
    env := (n, t) :: env
  let scope := env
  let look := fun (x : String) => (scope.lookup x).getD (get x)
  let r ← f.result
  let ts ← subst look (CssValues.CV.parse r)
  let t ← typedValue f.returns (CssValues.rawText ts).trimAscii.toString
  return CssValues.CV.parse t

/-- Replace each `var()` by the value of its custom property, or by its fallback (CSS
Variables 1 §3). `none`: a variable with no value and no fallback, so the declaration is
invalid at computed-value time. -/
def substitute (get : String → String) (fns : List (String × FnDef)) : Nat → List CssValues.CV → Option (List CssValues.CV)
  | 0, _ => none
  | fuel + 1, cvs =>
    cvs.foldl (fun (acc : Option (List CssValues.CV)) cv =>
      match acc with
      | none => none
      | some out =>
        match cv with
        | .fn name args =>
          if CssValues.lower name == "if" then
            -- `if(<condition>: <value>; ...)`: the value of the first condition that holds,
            -- else nothing (CSS Values 5 §9.1)
            let branches := (splitAt .semicolon args).filter fun b => !(CssValues.stripWs b).isEmpty
            let pick := branches.foldl (fun (acc : Option (Option (List CssValues.CV))) b =>
              match acc with
              | some (some _) => acc
              | none => none
              | some none =>
                match splitAt .colon b with
                | cond :: rest =>
                  if rest.isEmpty then none
                  else
                    let value := (rest.foldl (fun a g => if a.isEmpty then g else a ++ [CssValues.CV.tok .colon] ++ g) [])
                    match ifCondition get (substitute get fns fuel) 16 cond with
                    | some true => some (some (value.dropWhile (·.isWs)))
                    | some false => some none
                    | none => none
                | [] => none) (some none)
            match pick with
            | none => none
            | some none => some out
            | some (some v) => (substitute get fns fuel v).map (joinTokens out ·)
          else if CssValues.lower name == "env" then
            -- `env(<name>, <fallback>?)` (CSS Environment Variables 1 §3): the safe area,
            -- title bar and keyboard insets of a window with none are 0px; another name
            -- takes the fallback, else the declaration is invalid at computed-value time
            let groups := CssValues.splitCommas args
            let known := match CssValues.stripWs (groups.headD []) with
              | [.tok (.ident e)] =>
                let e := CssValues.lower e
                if ["safe-area-inset-top", "safe-area-inset-right", "safe-area-inset-bottom", "safe-area-inset-left",
                    "safe-area-max-inset-top", "safe-area-max-inset-right", "safe-area-max-inset-bottom",
                    "safe-area-max-inset-left", "titlebar-area-x", "titlebar-area-y", "titlebar-area-width",
                    "titlebar-area-height", "keyboard-inset-top", "keyboard-inset-right", "keyboard-inset-bottom",
                    "keyboard-inset-left", "keyboard-inset-width", "keyboard-inset-height"].contains e then some "0px" else none
              | _ => none
            match known with
            | some val => some (joinTokens out (CssValues.CV.parse val))
            | none =>
              match groups with
              | _ :: fb :: more =>
                let fallback := more.foldl (fun acc g => acc ++ [CssValues.CV.tok .comma] ++ g) fb
                (substitute get fns fuel (fallback.dropWhile (·.isWs))).map (joinTokens out ·)
              | _ => none
          else if CssValues.lower name == "attr" then
            -- `attr(<name> <type>?, <fallback>?)` (CSS Values 5 §7.7): the element's attribute,
            -- asked through `get` as U+0001 "attr " and the name (U+0000 when it has none)
            let groups := CssValues.splitCommas args
            let spec := CssValues.stripWs (groups.headD [])
            let fallback := match groups with
              | _ :: fb :: more => some (more.foldl (fun acc g => acc ++ [CssValues.CV.tok .comma] ++ g) fb)
              | _ => none
            let useFallback := fun (_ : Unit) => match fallback with
              | some fb => (substitute get fns fuel fb).map (joinTokens out ·)
              | none => none
            match spec with
            | .tok (.ident an) :: ty =>
              let raw := get ("\x01attr " ++ CssValues.lower an)
              if raw == "\x00" then useFallback ()
              else
                let typed : Option (List CssValues.CV) := match ty with
                  | [] => some [.tok (.str raw)]
                  | [.tok (.ident u)] =>
                    let u := CssValues.lower u
                    if u == "raw-string" then some [.tok (.str raw)]
                    else
                      match CssValues.stripWs (CssValues.CV.parse raw) with
                      | [.tok (.num x _)] => some (CssValues.CV.parse (CssValues.fmtRat x ++ (if u == "percent" then "%" else u)))
                      | _ => none
                  | [.fn t targs] =>
                    if CssValues.lower t != "type" then none
                    else (typedValue (CssValues.rawText targs) raw).map CssValues.CV.parse
                  | _ => none
                match typed with
                | some ts => some (joinTokens out ts)
                | none => useFallback ()
            | _ => none
          else if CssValues.lower name == "var" then
            let groups := CssValues.splitCommas args
            let nameText := match CssValues.stripWs (groups.headD []) with
              | [.tok (.ident s)] => s
              | _ => ""
            let value := if nameText == "" then "" else get nameText
            if value != "" then some (joinTokens out (CssValues.CV.parse value))
            else
              match groups with
              | _ :: fb :: more =>
                let fallback := more.foldl (fun acc g => acc ++ [CssValues.CV.tok .comma] ++ g) fb
                (substitute get fns fuel fallback).map (joinTokens out ·)
              | _ => none
          else if CssValues.isCustom name then
            -- a custom function (CSS Mixins 1 §2.4)
            match fns.lookup name with
            | none => none
            | some f => (callFn get f args (fun g cvs => substitute g fns fuel cvs)).map (joinTokens out ·)
          else (substitute get fns fuel args).map fun args' => out ++ [.fn name args']
        | .block o body => (substitute get fns fuel body).map fun body' => out ++ [.block o body']
        | cv => some (joinTokens out [cv])) (some [])

/-- Kind: bound. Says: substitution refuses (the value is invalid at computed-value time)
when its fuel, the nesting of functions and references it follows, is spent. -/
theorem substitute_zero (get : String → String) (fns : List (String × FnDef)) (cvs : List CssValues.CV) :
    substitute get fns 0 cvs = none := by
  simp [substitute]

/-- Kind: bound. Says: an if() condition nested past its fuel is no condition. -/
theorem ifCondition_zero (get : String → String) (subst : List CssValues.CV → Option (List CssValues.CV))
    (cvs : List CssValues.CV) : ifCondition get subst 0 cvs = none := by
  simp [ifCondition]

def mentionsCurrentColor (value : String) : Bool :=
  ((CssValues.lower value).splitOn "currentcolor").length > 1

/-- The computed value of longhand or custom property `p` on element `id`. `fuel` bounds
the walk to the root and the chain of variables. -/
def computedLonghand (v : View) : Nat → Nat → String → String
  | 0, _, _ => ""
  | fuel + 1, id, p =>
    -- what substitution looks up: a custom property of the element, or (U+0001 "attr " and
    -- a name) one of its attributes, U+0000 when it has none
    let lookupVar := fun (name : String) =>
      if name.startsWith "\x01attr " then
        let an := (name.drop 6).toString
        match ((v.dom.get id).attrs.find? fun a => a.ns.isNone && a.lname == an) with
        | some a => a.value
        | none => "\x00"
      else if (v.registered.get.lookup name).isSome then computedLonghand v fuel id name
      else
        -- an unregistered custom property: the value the cascade resolved for the element
        -- (`Computed.vars`: each custom property once, cycles and over-long values already
        -- invalid), unless it holds a function only computed values substitute (if(),
        -- attr(), env(), a custom function); without the map, the property's own value
        match v.styles[id]? with
        | some st =>
          match st.vars.get? name with
          | some text =>
            let cvs := CssValues.CV.parse text
            if CssValues.hasFn "if" 32 cvs || CssValues.hasFn "attr" 32 cvs || CssValues.hasFn "env" 32 cvs ||
                hasDashedFn 32 cvs then computedLonghand v fuel id name
            else text
          | none => if st.vars.isEmpty then computedLonghand v fuel id name else ""
        | none => computedLonghand v fuel id name
    -- the element's flow, looked up only for a property of a logical property group
    let flow := fun (_ : Unit) =>
      CssValues.Logical.Flow.of (computedLonghand v fuel id "writing-mode") (computedLonghand v fuel id "direction")
    let physicalName := if CssValues.Logical.mentions p && (CssValues.Logical.physical {} p).isSome
      then CssValues.Logical.physical (flow ()) p else none
    match physicalName with
    | some name =>
      -- a flow-relative property has the computed value of the physical property it is
      computedLonghand v fuel id name
    | none =>
    let also := if (CssValues.Logical.logical {} p).isSome && usesLogical v id
      then CssValues.Logical.logical (flow ()) p else none
    let custom := CssValues.isCustom p
    let row := CssValues.lookup p
    -- a registered custom property: its syntax, inheritance and initial value
    let reg := if custom then v.registered.get.lookup p else none
    let inherited := if custom then (reg.map (·.inherits)).getD true else (row.map (·.inherited)).getD false
    let ctxOf : String → CssValues.ComputeCtx := fun value =>
      { num := numCtx v id
        currentColor :=
          if mentionsCurrentColor value || p == "box-shadow" || p == "text-shadow" then
            if p == "color" then (parentElement v.dom id).map fun pid => computedLonghand v fuel pid "color"
            else some (computedLonghand v fuel id "color")
          else none }
    let initial := fun (_ : Unit) =>
      if custom then
        match reg with
        | some r => (r.initial.bind fun iv => CssRegister.computedValue (ctxOf iv) r.syn iv).getD ""
        | none => ""
      else match row with
        | some r =>
          match CssValues.specified r.name r.initial with
          | some s => CssValues.computed (ctxOf s) r.name s
          | none => r.initial
        | none => ""
    let fromParent := fun (_ : Unit) =>
      match parentElement v.dom id with
      | some pid => computedLonghand v fuel pid p
      | none => initial ()
    let default := fun (_ : Unit) => if inherited then fromParent () else initial ()
    -- an absolutely positioned box does not float (CSS 2 §9.7)
    if p == "float" && ["absolute", "fixed"].contains (computedLonghand v fuel id "position") then "none" else
    match (if p == "font-size" then v.styles[id]? else none) with
    -- the computed font size is the layout profile's: an absolute length for every form
    -- (keywords, `larger`, `em`, percentages, the `font` shorthand)
    | some style => ComputedValues.px style.fontSize
    | none =>
    match cascaded v id p also with
    | none => default ()
    | some value =>
      match pendingOf value with
      | some (shorthand, raw) =>
        -- substitute, then read the shorthand's longhand `p`; invalid at computed-value
        -- time is as if not declared
        match substitute lookupVar v.functions.get 16 (CssValues.CV.parse raw) with
        | none => default ()
        | some cvs' =>
          match (CssValues.expand shorthand (CssValues.rawText cvs')).bind (·.lookup p) with
          | some s =>
            if s == "inherit" then fromParent ()
            else if s == "initial" then initial ()
            else if CssValues.cssWide.contains s then default ()
            else CssValues.computed (ctxOf s) p s
          | none => default ()
      | none =>
      if value == "inherit" then fromParent ()
      else if value == "initial" then initial ()
      else if value == "unset" || value == "revert" || value == "revert-layer" then default ()
      else
        let cvs := CssValues.CV.parse value
        if CssValues.hasFn "var" 32 cvs || CssValues.hasFn "if" 32 cvs || CssValues.hasFn "attr" 32 cvs || CssValues.hasFn "env" 32 cvs ||
            (!v.functions.get.isEmpty && hasDashedFn 32 cvs) then
          match substitute lookupVar v.functions.get 16 cvs with
          -- a custom property invalid at computed-value time has the guaranteed-invalid
          -- value (CSS Variables 1 §3.1), not its parent's
          | none => if custom then "" else default ()
          | some cvs' =>
            let text := CssValues.rawText cvs'
            -- a value past the length limit is invalid (`CssVars.maxValueBytes`)
            if text.utf8ByteSize > CssVars.maxValueBytes then (if custom then "" else default ())
            else if custom then
              match reg with
              | some r => (CssRegister.computedValue (ctxOf text) r.syn text).getD (default ())
              | none => text
            else
              match CssValues.specified p text with
              | some s =>
                if CssValues.cssWide.contains s then default () else CssValues.computed (ctxOf s) p s
              | none => default ()
        else if custom then
          match reg with
          | some r => (CssRegister.computedValue (ctxOf value) r.syn value).getD (default ())
          | none => value
        else CssValues.computed (ctxOf value) p value

/-- The most ancestors and variable links a computed value follows (each is a stack frame). -/
def depthBound : Nat := 256

/-- The computed value of any property of the table on element `id`: a longhand, a
shorthand put together from its longhands, or a shorthand that is kept whole. -/
def computedOfWith (v : View) (id : Nat) (property : String) (longhand : String → String) : String :=
  let p := CssValues.propertyName property
  match CssValues.lookup p with
  | none => if CssValues.isCustom p then computedLonghand v depthBound id p else ""
  | some row =>
    if row.longhands.isEmpty then longhand p
    else if CssValues.recombinable row then CssValues.recombine row longhand
    else computedLonghand v depthBound id p

/-- `computedOfWith` with each longhand's computed value by the property table. -/
def computedOf (v : View) (id : Nat) (property : String) : String :=
  computedOfWith v id property (computedLonghand v depthBound id)

/-- The computed value of a longhand on pseudo-element `pe` of element `id`: its cascaded
value there, computed against the element's font size; else the element's value for an
inherited property (a pseudo-element inherits from its element) or the initial value. -/
def computedPseudoLonghand (v : View) (id : Nat) (pe : String) (p : String) : String :=
  let row := CssValues.lookup p
  let inherited := CssValues.isCustom p || (row.map (·.inherited)).getD false
  let initial := fun (_ : Unit) => match row with
    | some r => match CssValues.specified r.name r.initial with
      | some s => CssValues.computed { num := numCtx v id } r.name s
      | none => r.initial
    | none => ""
  let fromElement := fun (_ : Unit) => computedLonghand v depthBound id p
  -- the user agent's ::marker styles (CSS Lists 3 §3.1.1)
  let uaMarker : Option String := if pe != "marker" then none else match p with
    | "unicode-bidi" => some "isolate"
    | "font-variant-numeric" => some "tabular-nums"
    | "text-transform" => some "none"
    | "text-indent" => some "0px"
    | _ => none
  match cascadedPseudo v id pe p with
  | none =>
    match uaMarker with
    | some ua => ua
    | none => if inherited then fromElement () else initial ()
  | some value =>
    if value == "inherit" then fromElement ()
    else if value == "initial" then initial ()
    else if CssValues.cssWide.contains value then (if inherited then fromElement () else initial ())
    else if CssValues.isCustom p then value
    else if CssValues.hasFn "var" 32 (CssValues.CV.parse value) then (if inherited then fromElement () else initial ())
    else CssValues.computed { num := numCtx v id } p value

/-- The computed value of any property on pseudo-element `pe` of element `id`. -/
def computedPseudo (v : View) (id : Nat) (pe : String) (property : String) : String :=
  computedOfWith v id property (computedPseudoLonghand v id pe)

/-- The properties of the layout profile whose computed value is the specified value
(keywords and colours): when the element itself declares one, the answer is the
declaration's computed value, which may be one the profile does not model (`display: grid`,
a colour with alpha). The other profile properties are resolved values from layout. -/
def declaredWins : List String :=
  ["display", "color", "background-color", "visibility", "text-decoration-line", "overflow",
   "border-top-style", "border-right-style", "border-bottom-style", "border-left-style",
   "border-top-color", "border-right-color", "border-bottom-color", "border-left-color",
   "border-collapse", "caption-side", "vertical-align", "table-layout", "object-fit",
   "text-align", "direction", "unicode-bidi"]

/-- The prefixes of the profile's length properties for which a declared absolute length is
the answer. -/
def absoluteWins : List String := ["margin-", "padding-", "min-", "max-"]

/-- The names a computed style lists: the layout profile's (in its order), then every
other longhand of the table (legacy aliases and prefixed names left out); and the other
names it answers for (shorthands and legacy names). Built once (a lazy constant). -/
def nameLists : Thunk (Array String × Array String) := Thunk.mk fun _ =>
  let profile := (ComputedValues.values {}).map (·.1)
  let aliases := CssValues.aliasMap.get
  let longhands := profile ++ CssValues.Data.properties.toList.filterMap fun (n, _, _, _, ls) =>
    if ls == "" && !profile.contains n && n.toList.head? != some '-' && !aliases.contains n then some n else none
  let listed : Std.HashMap String Unit := longhands.foldl (fun m n => m.insert n ()) {}
  let others := CssValues.Data.properties.toList.filterMap fun (n, _, _, _, _) => if listed.contains n then none else some n
  (longhands.toArray, others.toArray)

def longhandNames : List String := nameLists.get.1.toList

def otherNames : List String := nameLists.get.2.toList

/-- The answer of a page for the names of a computed style: the listed names separated by
U+0000, then U+0001, then the other names. -/
def namesText : String :=
  "\x00".intercalate longhandNames ++ "\x01" ++ "\x00".intercalate otherNames

/-- The number of properties of the layout profile: the first names of `nameLists`. -/
def profileCount : Nat := (ComputedValues.values {}).length

/-- The custom properties declared for element `id` or one of its ancestors (they are
inherited), in the order found: by a matching rule or by a `style` attribute. A computed
style answers for these too. A loop up the ancestors (a tail call). -/
def customNamesLoop (v : View) : Nat → Option Nat → List String → List String
  | 0, _, acc => acc.reverse
  | fuel + 1, node, acc =>
    match node with
    | none => acc.reverse
    | some id =>
      let fromRules := (v.matchesOf id).flatMap fun (_, rule, _) =>
        rule.declarations.filterMap fun d => if CssValues.isCustom d.property then some d.property else none
      let fromStyle := (CssValues.declNames (attrValue (v.dom.get id) "style")).filter CssValues.isCustom
      let acc := (fromRules ++ fromStyle).foldl (fun acc n => if acc.contains n then acc else n :: acc) acc
      customNamesLoop v fuel (parentElement v.dom id) acc

def customNames (v : View) (id : Nat) : List String :=
  let declared := customNamesLoop v depthBound (some id) []
  -- a registered property has a value on every element (its initial value at least)
  declared ++ ((v.registered.get.map (·.1)).eraseDups.filter fun n => !declared.contains n)

/-- The answer of a page for the custom properties of a computed style: the names
separated by U+0000. The value of the `i`-th is `valueAt` at the count of the table's
names plus `i`. -/
def customNamesText (v : View) (id : Nat) : String := "\x00".intercalate (customNames v id)

/-- From this index on, `valueAt` answers the computed value of name `k - computedBase` by
the property table alone, for every property (the layout profile's too). -/
def computedBase : Nat := 100000

/-- The flow of element `id`: its computed `writing-mode` and `direction`. -/
def flowOf (v : View) (id : Nat) : CssValues.Logical.Flow :=
  CssValues.Logical.Flow.of (computedLonghand v depthBound id "writing-mode") (computedLonghand v depthBound id "direction")

/-- The physical property that a flow-relative property is on element `id` (CSS Logical 1);
any other name is itself. -/
def physicalNameOf (v : View) (id : Nat) (name : String) : String :=
  if CssValues.Logical.mentions name && (CssValues.Logical.physical {} name).isSome then
    (CssValues.Logical.physical (flowOf v id) name).getD name
  else name

/-- The flow-relative name of physical property `name` on element `id`, when the property
is in a logical property group and a declaration of the element may be flow-relative. -/
def alsoOf (v : View) (id : Nat) (name : String) : Option String :=
  if (CssValues.Logical.logical {} name).isSome && usesLogical v id then CssValues.Logical.logical (flowOf v id) name
  else none

/-- A name that is not flow-relative is its own physical name: no flow is looked up. -/
theorem physicalNameOf_plain (v : View) (id : Nat) (name : String) (h : CssValues.Logical.mentions name = false) :
    physicalNameOf v id name = name := by
  simp [physicalNameOf, h]

/-- The nearest of `p` and its ancestor elements that satisfies `ok`, looking at most `fuel`
elements up. A loop up the tree (a tail call). -/
def ancestorWhere (v : View) (ok : Nat → Bool) : Nat → Option Nat → Option Nat
  | 0, _ => none
  | _, none => none
  | fuel + 1, some p => if ok p then some p else ancestorWhere v ok fuel (parentElement v.dom p)

/-- The number of CSS pixels of a computed length text such as `2px`, else 0. -/
def pxNumber (t : String) : Float :=
  match CssValues.stripWs (CssValues.CV.parse t) with
  | [.tok (.dim x _ u)] => if CssValues.lower u == "px" then Float.ofInt x.num / Float.ofNat x.den else 0
  | _ => 0

/-- The size of the containing block that the percentage insets of element `id` refer to
(CSS Position 3 §2.1, CSS 2 §10.1), width and height: for a relatively positioned or sticky
box the content box of its parent; for an absolutely positioned box the padding box of the
nearest ancestor that is positioned or has a transform, for a fixed one of the nearest with a
transform; with no such ancestor, the viewport. `none` for a box that is not positioned, or
when the host gave no boxes. The walk up looks at most at as many elements as the document
has. -/
def insetBase (v : View) (id : Nat) : Option (Float × Float) :=
  let pos := computedLonghand v depthBound id "position"
  let viewport := (Float.ofNat v.viewportW, Float.ofNat v.viewportH)
  let side := fun (p : Nat) (n : String) => pxNumber (computedLonghand v depthBound p n)
  if pos == "relative" || pos == "sticky" then
    match parentElement v.dom id with
    | some p => (v.paddingBox p).map fun (w, h) =>
        (max 0 (w - side p "padding-left" - side p "padding-right"), max 0 (h - side p "padding-top" - side p "padding-bottom"))
    | none => some viewport
  else if pos == "absolute" || pos == "fixed" then
    let fixed := pos == "fixed"
    let holds := fun (p : Nat) =>
      computedLonghand v depthBound p "transform" != "none" ||
        (!fixed && computedLonghand v depthBound p "position" != "static")
    match ancestorWhere v holds (v.dom.nodes.size + 1) (parentElement v.dom id) with
    | some p => v.paddingBox p
    | none => some viewport
  else none

/-- An inset (`top`, `right`, `bottom`, `left`) of a positioned box that is a percentage, in
pixels of its containing block (CSSOM §9: the resolved value of an inset is the used value
when the box is positioned); any other value as it is. -/
def insetPx (v : View) (id : Nat) (name value : String) : String :=
  match CssValues.stripWs (CssValues.CV.parse value) with
  | [.tok (.pct x)] =>
    match insetBase v id with
    | some (w, h) =>
      let base := if name == "top" || name == "bottom" then h else w
      ComputedValues.px (Float.ofInt x.num / Float.ofNat x.den / 100 * base)
    | none => value
  | _ => value

/-- A value that is no percentage is left as it is. -/
theorem insetPx_auto (v : View) (id : Nat) (name : String) : insetPx v id name "auto" = "auto" := by
  rfl

/-- The resolved value of a longhand (CSSOM §9.1): for a property of the layout profile, the
profile's answer, or the declaration's computed value where that is the answer
(`declaredWins`, `absoluteWins`); for any other, the computed value by the property table. -/
def resolvedLonghand (v : View) (id : Nat) (name : String) : String :=
  let name := physicalNameOf v id name
  let also := alsoOf v id name
  match (ComputedValues.values (v.styles[id]?.getD {})).lookup name with
  | some value =>
    -- with flow-relative declarations in play, a border side (the profile has one border
    -- for all sides) and any side or size in a vertical writing mode (the profile lays out
    -- horizontal lines) are answered by the property table
    if also.isSome && (name.startsWith "border-" || (flowOf v id).vertical) then computedOf v id name
    else if declaredWins.contains name then
      match cascaded v id name also with
      | some declared => if CssValues.cssWide.contains declared then value else computedOf v id name
      | none => value
    else if absoluteWins.any (fun pre => name.startsWith pre) then
      -- a margin, padding or size limit the element declares as an absolute length (also
      -- through calc() and units the layout profile does not read): that length
      match cascaded v id name also with
      | some declared =>
        if CssValues.cssWide.contains declared then value
        else
          let g := computedOf v id name
          match CssValues.stripWs (CssValues.CV.parse g) with
          | [.tok (.dim _ _ "px")] => g
          | _ => value
      | none => value
    else value
  | none =>
    let value := computedLonghand v depthBound id name
    match opposite name with
    | some opp =>
      let value := insetPx v id name value
      -- a relatively positioned box (CSS Position 3 §3.4): an `auto` inset is the opposite
      -- one negated, or 0px when both are `auto` (CSSOM §9 resolved value)
      if value == "auto" && computedLonghand v depthBound id "position" == "relative" then
        let o := insetPx v id opp (computedLonghand v depthBound id opp)
        if o == "auto" then "0px"
        else match CssValues.stripWs (CssValues.CV.parse o) with
          | [.tok (.dim x _ u)] => if CssValues.lower u == "px" then CssValues.fmtRat (-x) ++ "px" else value
          | _ => value
      else if value == "auto" && (computedLonghand v depthBound id "position" == "absolute" ||
          computedLonghand v depthBound id "position" == "fixed") then
        -- an absolutely positioned box with one inset `auto` on an axis (CSS Position 3
        -- §4.1): that inset is what is left of the containing block past the other inset
        -- and the box's margin box
        let o := insetPx v id opp (computedLonghand v depthBound id opp)
        match CssValues.stripWs (CssValues.CV.parse o), insetBase v id with
        | [.tok (.dim x _ u)], some (w, h) =>
          if CssValues.lower u != "px" then value else
          let vertical := name == "top" || name == "bottom"
          let (pw, ph) := (v.paddingBox id).getD (0, 0)
          let len := fun (n : String) => pxNumber (computedLonghand v depthBound id n)
          -- a border with no style has no width
          let border := fun (side : String) =>
            let st := computedLonghand v depthBound id ("border-" ++ side ++ "-style")
            if st == "none" || st == "hidden" then 0 else len ("border-" ++ side ++ "-width")
          let outer := if vertical then
              ph + border "top" + border "bottom" + len "margin-top" + len "margin-bottom"
            else pw + border "left" + border "right" + len "margin-left" + len "margin-right"
          ComputedValues.px ((if vertical then h else w) - Float.ofInt x.num / Float.ofNat x.den - outer)
        | _, _ => value
      else value
    | none => value
where
  /-- The inset on the other side. -/
  opposite : String → Option String
    | "top" => some "bottom" | "bottom" => some "top" | "left" => some "right" | "right" => some "left"
    | _ => none

/-- The step between the operation numbers of pseudo-elements in `valueAt`. -/
def pseudoBase : Nat := 1000000

/-- The computed value of the `k`-th name (`longhandNames` then `otherNames`) on element
`id`, with `profileValue` the layout profile's answer for a profile property. -/
def valueAt (v : View) (id : Nat) (k : Nat) : String :=
  if k ≥ pseudoBase then
    -- a property of a pseudo-element: `pseudoBase` × (its place in `pseudoNames` + 1) + k
    let (longhands, others) := nameLists.get
    let j := k % pseudoBase
    let name := if j < longhands.size then longhands[j]? else others[j - longhands.size]?
    match pseudoNames[k / pseudoBase - 1]?, name with
    | some pe, some name => computedPseudo v id pe name
    | _, _ => ""
  else if k ≥ computedBase then
    -- the computed value, not the resolved one: percentages and `auto` stay (Typed OM's
    -- computedStyleMap, CSS Typed OM 1 §4.2)
    let (longhands, others) := nameLists.get
    let j := k - computedBase
    let name := if j < longhands.size then longhands[j]? else others[j - longhands.size]?
    match name with
    | some name => computedOf v id name
    | none =>
      match (customNames v id)[j - longhands.size - others.size]? with
      | some name => computedLonghand v depthBound id name
      | none => ""
  else
  let (longhands, others) := nameLists.get
  let name := if k < longhands.size then longhands[k]? else others[k - longhands.size]?
  match name with
  | some name =>
    if k < profileCount then resolvedLonghand v id name
    else computedOfWith v id name (resolvedLonghand v id)
  | none =>
    -- past the table's names: the custom properties of the element, in `customNames` order
    match (customNames v id)[k - longhands.size - others.size]? with
    | some name => computedLonghand v depthBound id name
    | none => ""

/-! ### Tests: the computed value of element `t` of a page with one sheet -/

private def computedAt (html css prop : String) : String :=
  let dom := DOM.parseHtmlDocument html
  match CSS.parse css, dom.getElementById 0 "t" with
  | .ok rules, some id =>
    match computeAll dom rules with
    | .ok styles =>
      computedOf { dom := dom, matchesOf := fun i => matchedRules dom i rules, styles := styles,
                   viewportW := 800, viewportH := 600, registered := Thunk.mk fun _ => registrationsOf css,
                   functions := Thunk.mk fun _ => functionsOf css } id prop
    | .error _ => "error"
  | _, _ => "error"

-- a shorthand with var() gives its longhands after substitution
#guard computedAt "<div id=t></div>" "#t { --x: pre; white-space: var(--x) }" "white-space" == "pre"
#guard computedAt "<div id=t></div>" "#t { --c: red; background: var(--c) }" "background-color" == "rgb(255, 0, 0)"
#guard computedAt "<div id=t></div>" "#t { --m: 3px; margin: var(--m) 5px }" "margin-left" == "5px"
-- the font shorthand and keyword sizes; float of an absolutely positioned box
#guard computedAt "<div id=t></div>" "#t { font: xx-small serif }" "font" == "9px serif"
#guard computedAt "<div id=t></div>" "#t { position: absolute; float: left; display: none }" "float" == "none"
-- custom properties: a cycle and a missing reference are the guaranteed-invalid value
#guard computedAt "<div><div id=t></div></div>" "div { --c: inherited } #t { --c: var(--zz) }" "--c" == ""
-- registered custom properties (@property): initial value, syntax computation, inheritance
#guard computedAt "<div id=t></div>" "@property --x { syntax: '<length>'; inherits: false; initial-value: 10px }" "--x" == "10px"
#guard computedAt "<div><p id=t>x</p></div>"
  "@property --x { syntax: '<length>'; inherits: false; initial-value: 0px } div { --x: 4px }" "--x" == "0px"
#guard computedAt "<div id=t></div>" "@property --c { syntax: '<color>'; inherits: true; initial-value: red } #t { --c: green }" "--c" ==
  "rgb(0, 128, 0)"
#guard computedAt "<div id=t></div>" "@property --c { syntax: '<color>'; inherits: true; initial-value: red } #t { --c: 10px }" "--c" ==
  "rgb(255, 0, 0)"
#guard computedAt "<div id=t></div>" "@property --x { syntax: '<length>'; inherits: true } #t { --x: 2px }" "--x" == "2px"
-- a property registered by a script is kept on the document node
#guard (let d := DOM.parseHtmlDocument "<p>x</p>"
  let d := d.setNode 0 fun e => { e with attrs := e.attrs.push { lname := "\x01property --x", value := "<length>\x000\x0011px" } }
  (registrationsOfDocument d).map (·.1)) == ["--x"]
-- overflow: clip is not the profile's hidden; the legacy -webkit-box
#guard computedAt "<div id=t></div>" "#t { overflow: clip }" "overflow" == "clip"
#guard computedAt "<div id=t></div>" "#t { display: -webkit-box }" "display" == "-webkit-box"
-- tokens that would read as one are written with a comment between them
#guard computedAt "<div id=t></div>" "#t { --a: foo; --b: bar; --r: var(--a)var(--b) }" "--r" == "foo/**/bar"
#guard computedAt "<div id=t></div>" "#t { --a: foo; --b: ,bar; --r: var(--a)var(--b) }" "--r" == "foo,bar"
-- if() (CSS Values 5 §9.1), from if-conditionals.html
#guard computedAt "<div id=t></div>" "#t { --x: 3; --r: if(style(--x: 3): true_value) }" "--r" == "true_value"
#guard computedAt "<div id=t></div>" "#t { --x: 3; --r: if(style(--x: 4): a; else: b) }" "--r" == "b"
#guard computedAt "<div id=t></div>" "#t { --r: if(style(--x): a; else: b) }" "--r" == "b"
#guard computedAt "<div id=t></div>" "#t { --x: 3; --y: 3; --r: if(style(--x: 3) and style(--y: 3): yes) }" "--r" == "yes"
#guard computedAt "<div id=t></div>" "#t { --r: if(supports(display: table-cell): yes; else: no) }" "--r" == "yes"
#guard computedAt "<div id=t></div>" "#t { --r: if(style(--n: initial): yes; else: no) }" "--r" == "yes"
-- custom functions (CSS Mixins 1), from dashed-function-eval.html
#guard computedAt "<div id=t></div>" "@function --f() { result: 12px; } #t { --actual: --f(); }" "--actual" == "12px"
#guard computedAt "<div id=t></div>" "@function --f(--x) { result: var(--x); } #t { --actual: --f(3px); }" "--actual" == "3px"
#guard computedAt "<div id=t></div>" "@function --f(--x: 10px) { --y: var(--x); result: var(--y); } #t { --actual: --f(); }" "--actual" == "10px"
#guard computedAt "<div id=t></div>" "@function --f() returns <length> { result: calc(1px + 1px); } #t { --actual: --f(); }" "--actual" == "2px"
#guard computedAt "<div id=t></div>" "@function --f() returns <length> { result: red; } #t { --actual: --f(); }" "--actual" == ""
-- resolved insets of a relatively positioned box
private def resolvedAt (html css prop : String) : String :=
  let dom := DOM.parseHtmlDocument html
  match CSS.parse css, dom.getElementById 0 "t" with
  | .ok rules, some id =>
    match computeAll dom rules with
    | .ok styles => resolvedLonghand { dom := dom, matchesOf := fun i => matchedRules dom i rules, styles := styles } id prop
    | .error _ => "error"
  | _, _ => "error"
#guard resolvedAt "<div id=t></div>" "#t { position: relative; bottom: 3px }" "top" == "-3px"
#guard resolvedAt "<div id=t></div>" "#t { position: relative }" "left" == "0px"
#guard resolvedAt "<div id=t></div>" "#t { position: static }" "left" == "auto"
-- percentage insets in pixels of the containing block, with every box 200 × 100 pixels
private def resolvedBoxed (html css prop : String) : String :=
  let dom := DOM.parseHtmlDocument html
  match CSS.parse css, dom.getElementById 0 "t" with
  | .ok rules, some id =>
    match computeAll dom rules with
    | .ok styles =>
      let v : View := { dom := dom, matchesOf := fun i => matchedRules dom i rules, styles := styles }
      resolvedLonghand { v with paddingBox := fun _ => some (200, 100) } id prop
    | .error _ => "error"
  | _, _ => "error"
#guard resolvedBoxed "<div><div id=t></div></div>" "#t { position: relative; top: 10% }" "top" == "10px"
#guard resolvedBoxed "<div><div id=t></div></div>" "#t { position: relative; top: 10% }" "bottom" == "-10px"
#guard resolvedBoxed "<div style='padding: 1px 2px'><div id=t></div></div>" "#t { position: relative; left: 50% }" "left" == "98px"
#guard resolvedBoxed "<div style='position: relative'><div><div id=t></div></div></div>" "#t { position: absolute; top: 100% }" "top" == "100px"
#guard resolvedBoxed "<div><div id=t></div></div>" "#t { position: fixed; left: 10% }" "left" == "80px"
#guard resolvedBoxed "<div><div id=t></div></div>" "#t { top: 10% }" "top" == "10%"
-- the box itself is 200 × 100 here too: bottom = 100 - 1 - 100; left = 800 - 4 - (200 + 1 + 1)
#guard resolvedBoxed "<div style='position: relative'><div id=t></div></div>" "#t { position: absolute; top: 1px }" "bottom" == "-1px"
#guard resolvedBoxed "<div><div id=t></div></div>" "#t { position: absolute; right: 4px; margin: 1px }" "left" == "594px"
#guard resolvedBoxed "<div><div id=t></div></div>" "#t { position: absolute; right: 4px; border: 2px solid }" "left" == "592px"
#guard resolvedBoxed "<div><div id=t></div></div>" "#t { position: absolute }" "left" == "auto"
#guard resolvedAt "<div><div id=t></div></div>" "#t { position: relative; top: 10% }" "top" == "10%"
-- the background shorthand by its longhands
#guard computedAt "<div id=t></div>" "#t { background: url(a.png) no-repeat red }" "background-repeat" == "no-repeat"
#guard computedAt "<div id=t></div>" "#t { background: red }" "background-color" == "rgb(255, 0, 0)"
-- cycles of custom properties are invalid, and a long chain is read once (variable-cycles.html)
#guard computedAt "<div id=t></div>" "#t { --a: var(--b); --b: var(--a); --s: valid }" "--a" == ""
#guard computedAt "<div id=t></div>" "#t { --a: var(--b); --b: var(--a); --s: valid }" "--s" == "valid"
#guard computedAt "<div id=t></div>"
  "#t { --v0: x; --v1: var(--v0) var(--v0); --v2: var(--v1) var(--v1); --v3: var(--v2) var(--v2); --v4: var(--v3) var(--v3); --v5: var(--v4) var(--v4); --v6: var(--v5) var(--v5); --v7: var(--v6) var(--v6); --v8: var(--v7) var(--v7); --v9: var(--v8) var(--v8); --v10: var(--v9) var(--v9); --v11: var(--v10) var(--v10); --v12: var(--v11) var(--v11); --v13: var(--v12) var(--v12); --v14: var(--v13) var(--v13); --v15: var(--v14) var(--v14); --v16: var(--v15) var(--v15); --v17: var(--v16) var(--v16); --v18: var(--v17) var(--v17); --v19: var(--v18) var(--v18); --v20: var(--v19) var(--v19); --v21: var(--v20) var(--v20) }"
  "--v3" == "x x x x x x x x"
-- env()
#guard computedAt "<div id=t></div>" "#t { --a: env(unknown-env-name, 10px); }" "--a" == "10px"
#guard computedAt "<div id=t></div>" "#t { --a: env(safe-area-inset-top); }" "--a" == "0px"
#guard computedAt "<div id=t></div>" "#t { --a: env(nonexistent); }" "--a" == ""
-- attr() (CSS Values 5 §7.7)
#guard computedAt "<div id=t data-foo=abc></div>" "#t { --a: attr(data-foo); }" "--a" == "\"abc\""
#guard computedAt "<div id=t data-foo=3></div>" "#t { width: attr(data-foo px); }" "width" == "3px"
#guard computedAt "<div id=t></div>" "#t { --a: attr(data-foo, fallback); }" "--a" == "fallback"
#guard computedAt "<div id=t data-foo=10px></div>" "#t { --a: attr(data-foo type(<length>)); }" "--a" == "10px"
-- the styles of pseudo-elements
private def pseudoAt (html css pe prop : String) : String :=
  let dom := DOM.parseHtmlDocument html
  match CSS.parse css, dom.getElementById 0 "t" with
  | .ok rules, some id =>
    match computeAll dom rules with
    | .ok styles =>
      computedPseudo { dom := dom, matchesOf := fun i => matchedRules dom i rules, styles := styles, rules := rules } id pe prop
    | .error _ => "error"
  | _, _ => "error"
#guard pseudoAt "<p id=t>x</p>" "#t::before { content: 'a'; color: red } p { color: blue }" "before" "color" == "rgb(255, 0, 0)"
#guard pseudoAt "<p id=t>x</p>" "#t::before { content: 'a' } p { color: blue }" "before" "color" == "rgb(0, 0, 255)"
#guard pseudoAt "<p id=t>x</p>" "#t::marker { font-size: 20px } #t::before { font-size: 30px }" "marker" "font-size" == "20px"
#guard pseudoAt "<p id=t>x</p>" "p::after { margin-left: 3px }" "before" "margin-left" == "0px"
#guard pseudoAt "<ul><li id=t>x</li></ul>" "li { text-transform: lowercase }" "marker" "text-transform" == "none"
-- revert-layer rolls back to the layer before; with no earlier layer, to the default
#guard computedAt "<div id=t class=r></div>"
  "@layer a { #t { color: red } } @layer b { #t { color: blue } } @layer c { #t.r { color: revert-layer } }" "color" ==
  "rgb(0, 0, 255)"
#guard computedAt "<div id=t class=r></div>" "@layer a { #t { all: initial } } @layer b { #t { vertical-align: 12px } }
  @layer c { #t.r { all: revert-layer } }" "vertical-align" == "12px"
#guard computedAt "<div><p id=t>x</p></div>" "div { margin-left: 3px } @layer a { #t { margin-left: revert-layer } }"
  "margin-left" == "0px"

end L4Factoidal.Rendering.ComputedGeneric
