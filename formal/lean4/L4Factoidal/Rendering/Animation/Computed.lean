/-
L4Factoidal.Rendering.Animation.Computed: the computed values the animation engine reads,
over the property table (`Rendering.CssValues`) and `getComputedStyle`'s answers
(`Rendering.ComputedGeneric`).

- `valueOf`: the computed value of a property of an element by name, as
  `getComputedStyle` gives it (`ComputedGeneric.valueAt`): the before-change and
  after-change values of a transition, and the underlying value of an effect.
- `computeIn`: the computed value of a specified value in an element's context: a
  keyframe's value (Web Animations 1 §5.3.2 "computed keyframes"), with the CSS-wide
  keywords resolved against the parent and the initial value.
- `declaredNames`: the longhands the rules that match an element and its `style`
  attribute declare: the properties whose value can differ between two style changes
  without an inherited value changing. `declarationText`: those declarations as one text,
  the cheap test that comes first.
-/
import L4Factoidal.Rendering.ComputedGeneric
import L4Factoidal.Rendering.Animation.Css
import Std.Data.HashMap

namespace L4Factoidal.Rendering.Animation.Computed
open L4Factoidal.Rendering

/-- The position of each name of a computed style (`ComputedGeneric.valueAt`'s `k`). Made
when a page with animations asks, not at start. -/
def nameIndex (_ : Unit) : Std.HashMap String Nat :=
  let names := ComputedGeneric.longhandNames ++ ComputedGeneric.otherNames
  (names.zip (List.range names.length)).foldl (fun m (n, k) => if m.contains n then m else m.insert n k) {}

/-- The computed value of the property named on element `id`; none for a name the table
does not have. -/
def valueOf (index : Std.HashMap String Nat) (v : ComputedGeneric.View) (id : Nat) (name : String) : Option String :=
  if CssValues.isCustom name then some (ComputedGeneric.computedOf v id name)
  else (index[name]?).map fun k => ComputedGeneric.valueAt v id k

/-- The computed value of `property: value` in the context of element `id`; none when the
value is not one the property takes, or holds a `var()` (not resolved here). `inherit` is
the parent's computed value, `initial` the initial one, `unset` and `revert` one of the
two by the property's inheritance. -/
def computeIn (index : Std.HashMap String Nat) (v : ComputedGeneric.View) (id : Nat) (property value : String) :
    Option String :=
  let p := CssValues.propertyName property
  if CssValues.isCustom p then some (CssValues.trimText value)
  else
    match CssValues.specified p value, CssValues.lookup p with
    | some s, some row =>
      let ctx : CssValues.ComputeCtx := {
        num := ComputedGeneric.numCtx v id
        currentColor := if ComputedGeneric.mentionsCurrentColor s then some (ComputedGeneric.computedOf v id "color") else none }
      let initial := fun (_ : Unit) => some (CssValues.initialComputed ctx row)
      let inherit := fun (_ : Unit) =>
        match ComputedGeneric.parentElement v.dom id with
        | some pid => valueOf index v pid p
        | none => initial ()
      if s == "inherit" then inherit ()
      else if s == "initial" then initial ()
      else if s == "unset" || s == "revert" || s == "revert-layer" then (if row.inherited then inherit () else initial ())
      else if CssValues.hasSubstitution (CssValues.CV.parse s) then none
      else some (CssValues.computed ctx p s)
    | _, _ => none

/-- The longhands (and custom properties) that the rules matching element `id` and its
`style` attribute declare, each once. -/
def declaredNames (v : ComputedGeneric.View) (id : Nat) : List String := Id.run do
  let mut out : Array String := #[]
  let add := fun (out : Array String) (name : String) =>
    let p := CssValues.propertyName name
    if CssValues.isCustom p then (if out.contains p then out else out.push p)
    else if (CssValues.lookup p).isNone then out
    else (Css.longhandsOf p).foldl (fun o l => if o.contains l then o else o.push l) out
  for (_, rule, _) in v.matchesOf id do
    for d in rule.declarations do out := add out d.property
  for d in CssValues.Block.parse (CSS.attrValue (v.dom.get id) "style") do out := add out d.name
  return out.toList

/-- The declarations that the cascade of element `id` reads, as one text: those of the
rules that match it, in order, and its `style` attribute. Two style changes with the same
text give the element the same declared values, so only a change of this text makes the
engine compare the element's values outside the layout profile (a page whose every
element has a transition pays this text, not a cascade, for each element). -/
def declarationText (v : ComputedGeneric.View) (id : Nat) : String := Id.run do
  let mut out := ""
  for (origin, rule, _) in v.matchesOf id do
    out := out ++ toString origin ++ "{"
    for d in rule.declarations do
      out := out ++ d.property ++ ":" ++ d.value ++ (if d.important then "!;" else ";")
    out := out ++ "}"
  return out ++ CSS.attrValue (v.dom.get id) "style"

/-! ## Tests: styles again for part of the tree (`CSS.restyleWith`)

A page before and after a write of one element's `style` attribute, or with an animated
value on one element: the styles of the page before with that element's subtree styled
again are the styles of the whole cascade of the page after. -/

private def firstWithId (dom : DOM.Dom) (name : String) : Option Nat :=
  (List.range dom.size).find? fun i => CSS.attrValue (dom.get i) "id" == name

private def restyleAgrees (before after sheet : String) (animated : List (String × String × Bool) := []) : Bool :=
  let d0 := DOM.parseHtmlDocument before
  let d1 := DOM.parseHtmlDocument after
  match CSS.parse sheet, firstWithId d1 "t" with
  | .ok rules, some t =>
    let state : CSS.ElementState := { animated := animated.map fun (p, v, tr) => (t, p, v, tr) }
    match CSS.computeAll d0 rules, CSS.computeAll d1 rules 1 state with
    | .ok s0, .ok s1 =>
      let ix := CSS.RuleIndex.build rules
      let matchesOf := CSS.withAnimated state fun id => ix.matched (CSS.readKeys d1) d1 id state
      (match CSS.restyleWith matchesOf d1 s0 [t] with
        | .ok s => s.toList.map ComputedValues.text == s1.toList.map ComputedValues.text
        | .error _ => false)
    | _, _ => false
  | _, _ => false

private def restylePage (style : String) : String :=
  "<div><p id=\"t\" style=\"" ++ style ++ "\">a <b>b</b></p><p>c <i>d</i></p></div>"
-- a new value of the element and of what its descendants inherit
#guard restyleAgrees (restylePage "color: red") (restylePage "color: blue; width: 20px") "p { margin-left: 3px } b { width: 5px }"
-- the declaration leaves
#guard restyleAgrees (restylePage "font-size: 30px") (restylePage "") "p { line-height: 2 }"
-- an animated value on the element, with the same document
#guard restyleAgrees (restylePage "width: 10px") (restylePage "width: 10px") "" [("width", "44px", false), ("color", "rgb(1, 2, 3)", true)]
-- and it is a change: the styles before are not the styles after
#guard (match CSS.computeAll (DOM.parseHtmlDocument (restylePage "color: red")) [], CSS.computeAll (DOM.parseHtmlDocument (restylePage "color: blue")) [] with
  | .ok a, .ok b => a.toList.map ComputedValues.text != b.toList.map ComputedValues.text
  | _, _ => false)
-- a rule that reads the `style` attribute is seen (the styles are then made whole)
#guard (match CSS.parse "p[style] { color: red } div:not([style*=x]) { color: blue }" with
  | .ok rules => CSS.readsStyleAttribute rules
  | .error _ => false)
#guard (match CSS.parse "p[title] { color: red } .a > b { color: blue }" with
  | .ok rules => !CSS.readsStyleAttribute rules
  | .error _ => false)

end L4Factoidal.Rendering.Animation.Computed
