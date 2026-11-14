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

/-- The border box of element `id` from its computed style, when its width and height
are lengths: the reference box of its transforms (CSS Transforms 1 §6), with no layout.
None for `auto` or a percentage size. -/
def boxOf (v : ComputedGeneric.View) (id : Nat) : Option (Float × Float) :=
  let px := fun (name : String) => match Value.parse (ComputedGeneric.resolvedLonghand v id name) with
    | [.dim n "px"] => some (Value.toFloat n)
    | _ => none
  let border := ComputedGeneric.resolvedLonghand v id "box-sizing" == "border-box"
  let side := fun (size : String) (around : List String) =>
    (px size).map fun s => if border then s else around.foldl (fun acc n => acc + (px n).getD 0) s
  match side "width" ["padding-left", "padding-right", "border-left-width", "border-right-width"],
        side "height" ["padding-top", "padding-bottom", "border-top-width", "border-bottom-width"] with
  | some w, some h => some (w, h)
  | _, _ => none

/-- The width and the height of a border box from a layout answer "x y w h …" (measure op
17); none for an answer that does not read or a box of no size. -/
def sizeOfBox (answer : String) : Option (Float × Float) :=
  match (answer.splitOn " ").filter (· != "") with
  | _ :: _ :: w :: h :: _ =>
    match Fix.parse w, Fix.parse h with
    | some w, some h => if w > 0 || h > 0 then some (Value.toFloat w, Value.toFloat h) else none
    | _, _ => none
  | _ => none

#guard (sizeOfBox "8 58 50 50 0 0 50 50").map (fun (w, h) => (w == 50, h == 50)) == some (true, true)
#guard (sizeOfBox "0 0 0 0 0 0 0 0").isNone && (sizeOfBox "").isNone && (sizeOfBox "1 2 x 4").isNone

/-- The answer of `getComputedStyle` for the `k`-th name: `ComputedGeneric.valueAt`, and
the resolved values of the transform properties (CSSOM §9.1, CSS Transforms 1 §15):
`transform` as one `matrix()` or `matrix3d()` (`Value.resolvedTransform`), the percentages
of `transform-origin` and `perspective-origin` as lengths of the element's box. The box is
read only when the value has a percentage: from the computed sizes when they are lengths,
else from the layout (`laidBox`: the caller's, made only then). The engine itself reads `valueOf`: the list of
functions and the percentages, which is what interpolates. -/
def resolvedAt (v : ComputedGeneric.View) (id : Nat) (k : Nat)
    (laidBox : Unit → Option (Float × Float) := fun _ => none) : String :=
  let text := ComputedGeneric.valueAt v id k
  if k ≥ ComputedGeneric.computedBase then text else
  let name := ComputedGeneric.nameLists.get.1[k]?
  -- the box of the computed sizes when they are lengths (no layout); else the laid out one
  let box := fun (_ : Unit) => if text.contains '%' then (boxOf v id).orElse laidBox else none
  if name == some "transform" then Value.resolvedTransformText text (box ())
  else if name == some "transform-origin" || name == some "perspective-origin" then Value.resolvedOriginText text (box ())
  else text

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
`style` attribute declare, each once. The animated values of the view are not
declarations of the element (`CSS.withAnimated` gives them origins 2 and 3): they are left
out. -/
def declaredNames (v : ComputedGeneric.View) (id : Nat) : List String := Id.run do
  let mut out : Array String := #[]
  let add := fun (out : Array String) (name : String) =>
    let p := CssValues.propertyName name
    if CssValues.isCustom p then (if out.contains p then out else out.push p)
    else if (CssValues.lookup p).isNone then out
    else (Css.longhandsOf p).foldl (fun o l => if o.contains l then o else o.push l) out
  for (origin, rule, _) in v.matchesOf id do
    if origin ≥ 2 then continue
    for d in rule.declarations do out := add out d.property
  for d in CssValues.Block.parse (CSS.attrValue (v.dom.get id) "style") do out := add out d.name
  return out.toList

/-- The declarations that the cascade of element `id` reads, as one text: those of the
rules that match it, in order, and its `style` attribute. Two style changes with the same
text give the element the same declared values, so only a change of this text makes the
engine compare the element's values outside the layout profile (a page whose every
element has a transition pays this text, not a cascade, for each element). -/
def ruleDeclarationText (v : ComputedGeneric.View) (id : Nat) : String := Id.run do
  let mut out := ""
  for (origin, rule, _) in v.matchesOf id do
    -- an animated value is not a declaration of the element: with them in the text, the
    -- style with animated values would never compare equal to the style without
    if origin ≥ 2 then continue
    out := out ++ toString origin ++ "{"
    for d in rule.declarations do
      out := out ++ d.property ++ ":" ++ d.value ++ (if d.important then "!;" else ";")
    out := out ++ "}"
  return out

/-- `ruleDeclarationText` with the `style` attribute after it. -/
def declarationText (v : ComputedGeneric.View) (id : Nat) : String :=
  ruleDeclarationText v id ++ CSS.attrValue (v.dom.get id) "style"

/-- The declarations of the element's `style` attribute as longhands with their values
(and importance), in `Css.cascadedText` form. -/
def styleAttributeText (v : ComputedGeneric.View) (id : Nat) : String :=
  Css.cascadedText ((CssValues.Block.parse (CSS.attrValue (v.dom.get id) "style")).map fun d =>
    (d.name, if d.important then d.value ++ "!" else d.value))

/-- The longhands that two `style` attributes (`styleAttributeText`) declare differently:
in one and not the other, or with another value (the first value of a name, as `lookup`
reads it). -/
def styleAttributeDiff (before after : String) : List String :=
  let a := Css.ofCascadedText before
  let b := Css.ofCascadedText after
  ((a.map (·.1)) ++ (b.map (·.1))).eraseDups.filter fun k => a.lookup k != b.lookup k

/-- A longhand whose change can change the computed value of another property of the
element: the font (font-relative lengths), the colour (`currentcolor`), the line height,
the flow, the zoom, a custom property (`var()`). A change of one of these in a `style`
attribute is not a change of that one property alone. -/
def reachesOthers (name : String) : Bool :=
  CssValues.isCustom name || name.startsWith "font" || name == "color" || name == "line-height" ||
    name == "direction" || name == "writing-mode" || name == "text-orientation" || name == "zoom" ||
    name == "color-scheme"

-- two attributes that differ in one declaration; the same; one more declaration
#guard styleAttributeDiff (Css.cascadedText [("rotate", "10deg"), ("width", "3px")]) (Css.cascadedText [("rotate", "20deg"), ("width", "3px")]) == ["rotate"]
#guard styleAttributeDiff (Css.cascadedText [("rotate", "10deg")]) (Css.cascadedText [("rotate", "10deg")]) == []
#guard styleAttributeDiff (Css.cascadedText [("rotate", "10deg")]) (Css.cascadedText [("rotate", "10deg"), ("opacity", "0")]) == ["opacity"]
#guard styleAttributeDiff (Css.cascadedText [("rotate", "10deg"), ("opacity", "0")]) "" == ["rotate", "opacity"]
#guard reachesOthers "font-size" && reachesOthers "--x" && !reachesOthers "rotate"

/-- Kind: soundness of the narrowing. Says: a longhand that the two attributes declare
alike (with one value, or not at all) is never in their difference. Does not say: that
the computed value of such a longhand is the same in the two styles (another declaration
may reach it: `reachesOthers`). -/
theorem styleAttributeDiff_same (before after k : String)
    (h : (Css.ofCascadedText before).lookup k = (Css.ofCascadedText after).lookup k) :
    k ∉ styleAttributeDiff before after := by
  simp [styleAttributeDiff, h]

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

/-! ## Cost test: the nodes styled again

`restyleWith` must style the named subtrees and nothing else, whatever the size of the
page: the interpolation tests write one element's style and read a computed value some
hundreds of times a page. The count is taken from outside: the rules given for the second
pass put a width on every element, which the styles before do not have, so exactly the
nodes that are styled again differ from the styles before. -/

private def restyledCount (paragraphs : Nat) : Option Nat :=
  let html := "<div>" ++ String.join (List.replicate paragraphs "<p>a <b>b</b></p>") ++ "<p id=\"t\">a <b>b</b></p></div>"
  let d := DOM.parseHtmlDocument html
  match CSS.parse "* { width: 77px }", firstWithId d "t", CSS.computeAll d [] with
  | .ok marked, some t, .ok before =>
    let ix := CSS.RuleIndex.build marked
    match CSS.restyleWith (fun id => ix.matched (CSS.readKeys d) d id {}) d before [t] with
    | .ok after =>
      some ((List.range d.size).filter fun i =>
        (after[i]?).map ComputedValues.text != (before[i]?).map ComputedValues.text).length
    | .error _ => none
  | _, _, _ => none

-- the element and its one element child, on a page of 10 paragraphs and of 400
#guard restyledCount 10 == some 2
#guard restyledCount 400 == some 2

end L4Factoidal.Rendering.Animation.Computed
