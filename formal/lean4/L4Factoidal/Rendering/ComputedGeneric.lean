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

/-- Replace each `var()` by the value of its custom property, or by its fallback (CSS
Variables 1 §3). `none`: a variable with no value and no fallback, so the declaration is
invalid at computed-value time. -/
def substitute (get : String → String) : Nat → List CssValues.CV → Option (List CssValues.CV)
  | 0, _ => none
  | fuel + 1, cvs =>
    cvs.foldl (fun (acc : Option (List CssValues.CV)) cv =>
      match acc with
      | none => none
      | some out =>
        match cv with
        | .fn name args =>
          if CssValues.lower name == "var" then
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
                (substitute get fuel fallback).map (joinTokens out ·)
              | _ => none
          else (substitute get fuel args).map fun args' => out ++ [.fn name args']
        | .block o body => (substitute get fuel body).map fun body' => out ++ [.block o body']
        | cv => some (joinTokens out [cv])) (some [])

def mentionsCurrentColor (value : String) : Bool :=
  ((CssValues.lower value).splitOn "currentcolor").length > 1

/-- The computed value of longhand or custom property `p` on element `id`. `fuel` bounds
the walk to the root and the chain of variables. -/
def computedLonghand (v : View) : Nat → Nat → String → String
  | 0, _, _ => ""
  | fuel + 1, id, p =>
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
        match substitute (fun name => computedLonghand v fuel id name) 16 (CssValues.CV.parse raw) with
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
        if CssValues.hasFn "var" 32 cvs then
          match substitute (fun name => computedLonghand v fuel id name) 16 cvs with
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
    else if (CssValues.shapeOf row).isSome then CssValues.recombine row longhand
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
  | none => computedLonghand v depthBound id name

/-- The computed value of the `k`-th name (`longhandNames` then `otherNames`) on element
`id`, with `profileValue` the layout profile's answer for a profile property. -/
def pseudoBase : Nat := 1000000

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
                   viewportW := 800, viewportH := 600, registered := Thunk.mk fun _ => registrationsOf css } id prop
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
