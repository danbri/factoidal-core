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
def cascaded (v : View) (id : Nat) (p : String) (also : Option String := none) : Option String := Id.run do
  let n := v.dom.get id
  -- `all` sets every property but `direction`, `unicode-bidi` and the custom properties
  -- (CSS Cascade 4 §3.2), to a CSS-wide keyword
  let allApplies := !CssValues.isCustom p && p != "direction" && p != "unicode-bidi"
  let names := if allApplies then "all" :: coveringNames p else coveringNames p
  let names := match also with
    | some q => names ++ coveringNames q
    | none => names
  let mut best : Option (List Nat × String) := none
  let mut order : Nat := 0
  let consider := fun (best : Option (List Nat × String)) (key : List Nat) (d : Declaration) =>
    if names.contains d.property && (best.map (fun b => keyLE b.1 key)).getD true then
      let value := if d.property == "all" then CssValues.specified "all" d.value
        else (CssValues.expand d.property d.value).bind fun ls =>
          ((ls.lookup p).orElse fun _ => also.bind fun q => ls.lookup q).orElse fun _ =>
            -- a shorthand kept whole for its `var()`: its longhands are known after substitution
            (ls.lookup d.property).bind fun raw => if d.property != p then some (pendingShorthand d.property raw) else none
      match value with
      | some value => some (key, value)
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
    if (best.map (fun b => keyLE b.1 key)).getD true then
      if d.name == p || d.name == "all" || some d.name == also then best := some (key, d.value)
      else if CssValues.hasSubstitution (CssValues.CV.parse d.value) then
        -- a covering shorthand kept whole for its `var()`
        best := some (key, pendingShorthand d.name d.value)
    order := order + 1
  return best.map (·.2)

/-- The parent element of a node. -/
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
            if value != "" then some (out ++ CssValues.CV.parse value)
            else
              match groups with
              | _ :: fb :: more =>
                let fallback := more.foldl (fun acc g => acc ++ [CssValues.CV.tok .comma] ++ g) fb
                (substitute get fuel fallback).map (out ++ ·)
              | _ => none
          else (substitute get fuel args).map fun args' => out ++ [.fn name args']
        | .block o body => (substitute get fuel body).map fun body' => out ++ [.block o body']
        | cv => some (out ++ [cv])) (some [])

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
    let inherited := custom || (row.map (·.inherited)).getD false
    let ctxOf : String → CssValues.ComputeCtx := fun value =>
      { num := numCtx v id
        currentColor :=
          if mentionsCurrentColor value || p == "box-shadow" || p == "text-shadow" then
            if p == "color" then (parentElement v.dom id).map fun pid => computedLonghand v fuel pid "color"
            else some (computedLonghand v fuel id "color")
          else none }
    let initial := fun (_ : Unit) =>
      if custom then ""
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
            else if custom then text
            else
              match CssValues.specified p text with
              | some s =>
                if CssValues.cssWide.contains s then default () else CssValues.computed (ctxOf s) p s
              | none => default ()
        else if custom then value
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

/-- The properties of the layout profile whose computed value is the specified value
(keywords and colours): when the element itself declares one, the answer is the
declaration's computed value, which may be one the profile does not model (`display: grid`,
a colour with alpha). The other profile properties are resolved values from layout. -/
def declaredWins : List String :=
  ["display", "color", "background-color", "visibility", "text-decoration-line",
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

def customNames (v : View) (id : Nat) : List String := customNamesLoop v depthBound (some id) []

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
def valueAt (v : View) (id : Nat) (k : Nat) : String :=
  if k ≥ computedBase then
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
                   viewportW := 800, viewportH := 600 } id prop
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

end L4Factoidal.Rendering.ComputedGeneric
