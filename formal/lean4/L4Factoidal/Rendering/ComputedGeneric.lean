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

def keyLE : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then keyLE as bs else a < b

/-- The property names whose declarations can set property `p`: `p`, the shorthands that
have it as a longhand, and the legacy names of those. One pass over the table for a
query, so that each declaration of the cascade is then one list lookup. -/
def coveringNames (p : String) : List String :=
  let direct := p :: CssValues.Data.properties.toList.filterMap fun (n, _, _, _, ls) =>
    if ls == "" then none else if (ls.splitOn " ").contains p then some n else none
  direct ++ CssValues.Data.aliases.toList.filterMap fun (alias, target) =>
    if direct.contains target then some alias else none

/-- The cascaded value of property `p` (a name of the table, or a custom property) on
element `id`: the canonical specified value of the winning declaration. -/
def cascaded (v : View) (id : Nat) (p : String) : Option String := Id.run do
  let n := v.dom.get id
  let names := coveringNames p
  let mut best : Option (List Nat × String) := none
  let mut order : Nat := 0
  let consider := fun (best : Option (List Nat × String)) (key : List Nat) (d : Declaration) =>
    if names.contains d.property && (best.map (fun b => keyLE b.1 key)).getD true then
      match (CssValues.expand d.property d.value).bind (·.lookup p) with
      | some value => some (key, value)
      | none => best
    else best
  for (origin, rule, matched) in v.matchesOf id do
    let specificity := matched.foldl (fun m s =>
      if keyLE [m.1, m.2.1, m.2.2] [s.specificity.1, s.specificity.2.1, s.specificity.2.2] then s.specificity else m) (0, 0, 0)
    let onlyVisited := matched.all (·.visitedDependent)
    for d in rule.declarations do
      if !onlyVisited || visitedProperties.contains d.property then
        let context := if (origin == 1 && rule.scope.isSome) == d.important then 1 else 0
        let key := [if d.important then 1 else 0, origin * 2 + context, 0, specificity.1, specificity.2.1, specificity.2.2, order]
        best := consider best key d
      order := order + 1
  for d in CssValues.Block.parseOnly names (attrValue n "style") do
    let key := [if d.important then 1 else 0, 2 + (if d.important then 0 else 1), 1, 0, 0, 0, order]
    if d.name == p && (best.map (fun b => keyLE b.1 key)).getD true then best := some (key, d.value)
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
    let custom := CssValues.isCustom p
    let row := CssValues.lookup p
    let inherited := custom || (row.map (·.inherited)).getD false
    let ctxOf : String → CssValues.ComputeCtx := fun value =>
      { num := numCtx v id
        currentColor :=
          if mentionsCurrentColor value then
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
    match cascaded v id p with
    | none => default ()
    | some value =>
      if value == "inherit" then fromParent ()
      else if value == "initial" then initial ()
      else if value == "unset" || value == "revert" || value == "revert-layer" then default ()
      else
        let cvs := CssValues.CV.parse value
        if CssValues.hasFn "var" 32 cvs then
          match substitute (fun name => computedLonghand v fuel id name) 16 cvs with
          | none => default ()
          | some cvs' =>
            let text := CssValues.rawText cvs'
            if custom then text
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
def computedOf (v : View) (id : Nat) (property : String) : String :=
  let p := CssValues.propertyName property
  match CssValues.lookup p with
  | none => if CssValues.isCustom p then computedLonghand v depthBound id p else ""
  | some row =>
    if row.longhands.isEmpty then computedLonghand v depthBound id p
    else if (CssValues.shapeOf row).isSome then
      CssValues.recombine row fun l => computedLonghand v depthBound id l
    else computedLonghand v depthBound id p

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
other longhand of the table (legacy aliases and prefixed names left out). -/
def longhandNames : List String :=
  let profile := (ComputedValues.values {}).map (·.1)
  profile ++ CssValues.Data.properties.toList.filterMap fun (n, _, _, _, ls) =>
    if ls == "" && !profile.contains n && n.toList.head? != some '-' && !(CssValues.Data.aliases.any fun a => a.1 == n) then some n
    else none

/-- The other names a computed style answers for: shorthands and legacy names. -/
def otherNames : List String :=
  let listed := longhandNames
  CssValues.Data.properties.toList.filterMap fun (n, _, _, _, _) => if listed.contains n then none else some n

/-- The answer of a page for the names of a computed style: the listed names separated by
U+0000, then U+0001, then the other names. -/
def namesText : String :=
  "\x00".intercalate longhandNames ++ "\x01" ++ "\x00".intercalate otherNames

/-- The computed value of the `k`-th name (`longhandNames` then `otherNames`) on element
`id`, with `profileValue` the layout profile's answer for a profile property. -/
def valueAt (v : View) (id : Nat) (k : Nat) : String :=
  let profile := ComputedValues.values (v.styles[id]?.getD {})
  match profile[k]? with
  | some (name, value) =>
    if declaredWins.contains name then
      match cascaded v id name with
      | some declared => if CssValues.cssWide.contains declared then value else computedOf v id name
      | none => value
    else if absoluteWins.any (fun pre => name.startsWith pre) then
      -- a margin, padding or size limit the element declares as an absolute length (also
      -- through calc() and units the layout profile does not read): that length
      match cascaded v id name with
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
    match (longhandNames ++ otherNames)[k]? with
    | some name => computedOf v id name
    | none => ""

end L4Factoidal.Rendering.ComputedGeneric
