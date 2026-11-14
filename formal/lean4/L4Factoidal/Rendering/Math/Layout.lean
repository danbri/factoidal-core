/-
L4Factoidal.Rendering.Math.Layout — MathML Core layout over the DOM arena: the walk of a
MathML subtree that gives each element its box.

Specification: MathML Core (https://w3c.github.io/mathml-core/) §3: `math` and the
elements laid out as `mrow` (`mrow`, `merror`, `mstyle`, `mphantom`, `semantics`,
`maction`, `a`, unknown elements), token elements (`mi`, `mn`, `mo`, `mtext`, `ms`),
`mspace`, `mpadded`, `mfrac`, `msqrt`, `mroot`, `msub`, `msup`, `msubsup`,
`mmultiscripts`, `munder`, `mover`, `munderover`, `mtable`, `mtr`, `mtd`.

The arithmetic of each construct is `Math.Box` (exact integers in layout units, with
theorems). This module reads the document and the styles, asks `leaf` for the inline
content of a token element (the text layout belongs to `Rendering.Layout`, which calls
this module), and answers boxes relative to the root's left edge and baseline. It makes
no paint: the caller draws the boxes' backgrounds and borders, the rules (fraction bar,
radical overbar) and the leaves.

Limits (see docs/designissues/2026-11-14-mathml-core-layout.md): no OpenType MATH table
is read, so every font parameter is the fallback of a font with no MATH table, taken
from the font size (x-height: half an em; rule thickness: 1/16 em; math axis: a quarter
em); operators are not stretched (of the operator dictionary only `lspace` and `rspace`
are used, and `movablelimits`); the radical sign is not drawn; a table is a grid of centred cells with no row
or column spans.

Only elements in the MathML namespace enter this module (`Rendering.Layout` tests the
namespace), so a page with no MathML pays nothing for it.
-/
import L4Factoidal.Rendering.Style
import L4Factoidal.Rendering.Math.Box
import L4Factoidal.Rendering.Math.Attributes
import L4Factoidal.Rendering.Math.OperatorDictionary

namespace L4Factoidal.Rendering.Math
open L4Factoidal.DOM
open L4Factoidal.Rendering.CSS (Computed)

/-- CSS pixels to layout units (1/64 px), rounded; not a number gives 0. -/
def lu (x : Float) : Int :=
  if x >= 0 then Int.ofNat (x * 64).round.toUInt64.toNat else -Int.ofNat ((-x) * 64).round.toUInt64.toNat

/-- Layout units to CSS pixels. -/
def px (u : Int) : Float := Float.ofInt u / 64

/-- A box of an element in the answer: left and top from the origin's left edge and
baseline (top is negative above the baseline). -/
structure PBox where
  source : Nat
  x : Int
  y : Int
  w : Int
  h : Int
  deriving Repr, Inhabited

/-- The spaces an embellished operator asks before and after it, for each form its place
can give it (§3.2.4.2): the group that holds it knows the place. -/
structure OpSpaces where
  pre : Int × Int
  inf : Int × Int
  post : Int × Int
  deriving Repr, Inhabited

def OpSpaces.forForm (o : OpSpaces) : Form → Int × Int
  | .pre => o.pre | .inf => o.inf | .post => o.post

/-- A laid-out subtree. `box` is its margin box; `boxes` the border boxes of its
elements, `rules` the bars to paint in an element's colour, `leaves` the inline content
of its token elements (a payload of the caller with the left and top of its line box),
all relative to this subtree's left edge and baseline. `op`: the subtree is an
embellished operator (§3.2.4.1) that asks these spaces before and after it. `spaceLike`:
the subtree is space-like (§3.2.5.1). -/
structure Out (α : Type) where
  box : MBox := {}
  boxes : Array PBox := #[]
  rules : Array PBox := #[]
  leaves : Array (α × Int × Int) := #[]
  op : Option OpSpaces := none
  spaceLike : Bool := false
  /-- The core operator of this embellished operator has `movablelimits` (§3.2.4.2). -/
  movable : Bool := false

instance {α : Type} : Inhabited (Out α) := ⟨{}⟩

/-- The subtree moved by `dx` right and `dy` down. -/
def Out.shift {α : Type} (o : Out α) (dx dy : Int) : Out α :=
  if dx == 0 && dy == 0 then o else
  { o with boxes := o.boxes.map fun b => { b with x := b.x + dx, y := b.y + dy },
           rules := o.rules.map fun b => { b with x := b.x + dx, y := b.y + dy },
           leaves := o.leaves.map fun (a, x, y) => (a, x + dx, y + dy) }

/-- `parent` with the content of `child` placed at `p`. The parent's box is not changed.
`rtl`: the parent's direction is right to left, so `p.dx` is measured from the parent's
right edge to the child's right edge (the layout is mirrored on the inline axis). -/
def Out.add {α : Type} (parent child : Out α) (p : At) (rtl : Bool := false) : Out α :=
  let q := if rtl then mirror parent.box child.box p else p
  let c := child.shift q.dx q.dy
  { parent with boxes := parent.boxes ++ c.boxes, rules := parent.rules ++ c.rules,
                leaves := parent.leaves ++ c.leaves }

/-- The parameters of a font with no MATH table, from the font size, in layout units. -/
structure Params where
  em : Int
  xHeight : Int
  rule : Int
  axis : Int
  deriving Repr

def Params.of (s : Computed) : Params :=
  let em := lu s.fontSize
  { em, xHeight := em / 2, rule := max 1 (em / 16), axis := em / 4 }

/-- A length attribute of element `n` in layout units, `none` when absent or not a length. -/
def lengthAttr (n : DOM.Node) (s : Computed) (key : String) (basis : Option Float := none) : Option Int :=
  ((attr? n key).bind fun v => lengthPx s.fontSize v basis).map lu

/-- A size in pixels as layout units; `none` for `auto` and for the units this layout
does not resolve (a percentage, viewport units). -/
def pixels : CSS.Length → Option Int
  | .px v => some (lu v)
  | _ => none

/-- A content size under the `width` or `height` property and its limits (CSS 2.1 §10.4:
the property, then the maximum, then the minimum). -/
def sized (content : Int) (size min max : CSS.Length) : Int :=
  let v := (pixels size).getD content
  let v := match pixels max with | some m => Min.min v m | none => v
  match pixels min with | some m => Max.max v m | none => v

/-- Kind: specification conformance (CSS 2.1 §10.4).
Says: when the style gives a minimum in pixels, the size is at least that minimum,
whatever the property and the maximum are: a minimum wins over a maximum.
Does not say: anything about percentages and other units (they are not resolved here). -/
theorem sized_min (content m : Int) (size min max : CSS.Length) (h : pixels min = some m) :
    m ≤ sized content size min max := by
  simp only [sized, h]
  exact Int.le_max_right _ _

/-- Kind: specification conformance (CSS 2.1 §10.4).
Says: with `auto` for the property and no pixel limits, the size is the content's.
Does not say: what a percentage does (nothing here: it is read as `auto`). -/
theorem sized_auto (content : Int) (size min max : CSS.Length)
    (hs : pixels size = none) (hmin : pixels min = none) (hmax : pixels max = none) :
    sized content size min max = content := by
  simp [sized, hs, hmin, hmax]

/-- The element's own box around its content (CSS 2.1 §8.1; MathML Core §3.1.2): the
content box takes the `width` and `height` of the style when they are lengths (the
content stays at the start edge and keeps its baseline: a height changes the descent),
then padding, border and margin are added; the border box is recorded for the element. -/
def wrap {α : Type} (id : Nat) (s : Computed) (o : Out α) : Out α :=
  let b := s.borderEdges
  let p := s.padding
  let m := s.margin
  let left := lu (m.left + b.left + p.left)
  let right := lu (p.right + b.right + m.right)
  let top := lu (b.top + p.top)
  let bottom := lu (b.bottom + p.bottom)
  let width := sized o.box.width s.width s.minWidth s.maxWidth
  let height := sized (o.box.ascent + o.box.descent) s.height s.minHeight s.maxHeight
  let descent := height - o.box.ascent
  let c := o.shift left 0
  let own : PBox := ⟨id, lu m.left, -(o.box.ascent + top),
    width + lu (b.left + p.left) + lu (p.right + b.right), o.box.ascent + top + descent + bottom⟩
  { c with box := ⟨left + width + right, o.box.ascent + top + lu m.top, descent + bottom + lu m.bottom⟩,
           boxes := #[own] ++ c.boxes }

/-- §3.1.3.2: children on one baseline, each embellished operator with its spaces. A row
whose children are one embellished operator and otherwise only space-like elements is
itself an embellished operator (§3.2.4.1): the spaces are added by the row above it. A
row of space-like children only (or of none) is space-like (§3.2.5.1). -/
def row {α : Type} (kids : Array (Out α)) (rtl : Bool := false) : Out α := Id.run do
  let operators := kids.filter (·.op.isSome)
  let embellished := operators.size == 1 && kids.all (fun k => k.op.isSome || k.spaceLike)
  -- the form of an operator with no `form` attribute comes from its place in this row
  let items : List RowItem := (List.range kids.size).map fun i =>
    let k := kids[i]!
    match k.op with
    | some o =>
      if embellished then ⟨k.box, 0, 0⟩ else
      let (l, r) := o.forForm (formAt i kids.size)
      ⟨k.box, l, r⟩
    | none => ⟨k.box, 0, 0⟩
  let offsets := rowOffsets items
  let mut out : Out α := { box := rowBox items, op := if embellished then (operators[0]?.bind (·.op)) else none,
                           spaceLike := kids.all (·.spaceLike),
                           movable := embellished && ((operators[0]?.map (·.movable)).getD false) }
  for i in [0:kids.size] do
    out := out.add kids[i]! ⟨offsets.getD i 0, 0⟩ rtl
  return out

/-- §3.3.2: a fraction. `linethickness` is a length, a percentage of the default
thickness; zero gives a stack with no bar. -/
def fractionOut {α : Type} (id : Nat) (n : DOM.Node) (s : Computed) (num den : Out α) : Out α :=
  let P := Params.of s
  let display := !s.mathCompact
  let rule := max 0 ((lengthAttr n s "linethickness" (some (px P.rule))).getD P.rule)
  let gap := if rule == 0 then (if display then 7 else 3) * P.rule / 2 else (if display then 3 else 1) * P.rule
  let f := fraction { axis := P.axis, rule, numGap := gap, denGap := gap } num.box den.box
  -- a fraction whose numerator is an embellished operator is one (§3.2.4.1)
  let o : Out α := { box := f.box, rules := if rule > 0 then #[⟨id, 0, f.barTop, f.box.width, rule⟩] else #[],
                     op := num.op, movable := num.movable }
  (o.add num f.num).add den f.den

/-- §3.4.1: a base with scripts after it. An embellished base makes the element one. -/
def scriptsOut {α : Type} (s : Computed) (base : Out α) (sub sup : Option (Out α)) : Out α :=
  let P := Params.of s
  let r := scripts { subShift := P.xHeight / 3, supShift := P.xHeight, gap := 4 * P.rule }
    base.box (sub.map (·.box)) (sup.map (·.box))
  let rtl := s.direction == .rtl
  let o : Out α := { box := r.box, op := base.op, movable := base.movable }
  let o := o.add base r.base rtl
  let o := match sub with | some c => o.add c r.sub rtl | none => o
  match sup with | some c => o.add c r.sup rtl | none => o

/-- §3.4.2: a base with a script under it and a script over it. -/
def underOverOut {α : Type} (base : Out α) (under over : Option (Out α)) : Out α :=
  let r := underOver base.box (under.map (·.box)) (over.map (·.box))
  let o : Out α := { box := r.box, op := base.op, movable := base.movable }
  let o := o.add base r.base
  let o := match under with | some c => o.add c r.under | none => o
  match over with | some c => o.add c r.over | none => o

/-- The radical parameters of the style (§3.3.3, fallbacks of a font with no MATH table). -/
def radicalParams (s : Computed) : RadicalParams :=
  let P := Params.of s
  { signWidth := P.em / 2, rule := P.rule,
    gap := if s.mathCompact then P.rule * 5 / 4 else P.rule + P.xHeight / 4, extra := P.rule }

/-- §3.3.3: content under a radical; the overbar is a rule. -/
def radicalOut {α : Type} (id : Nat) (s : Computed) (content : Out α) : Out α :=
  let p := radicalParams s
  let (box, at_) := radical p content.box
  let rtl := s.direction == .rtl
  let o : Out α := { box, rules := #[⟨id, if rtl then 0 else p.signWidth, -(content.box.ascent + p.gap + p.rule),
                                      content.box.width, p.rule⟩] }
  o.add content at_ rtl

/-- §3.3.3 `mroot`: the radical, and the index before it, raised to 60% of the radical's
height, with the kerns 5/18 em before and -10/18 em after. -/
def rootOut {α : Type} (id : Nat) (s : Computed) (base index : Out α) : Out α :=
  let P := Params.of s
  let r := radicalOut id s base
  let height := r.box.ascent + r.box.descent
  let before := P.em * 5 / 18
  let lead := max 0 (before + index.box.width - P.em * 10 / 18)
  let indexX := if lead == 0 then 0 else before
  let indexY := r.box.descent - 6 * height / 10 - index.box.descent
  let o : Out α := { box := ⟨lead + r.box.width, max r.box.ascent (index.box.ascent - indexY),
                             max r.box.descent (index.box.descent + indexY)⟩ }
  let rtl := s.direction == .rtl
  (o.add r ⟨lead, 0⟩ rtl).add index ⟨indexX, indexY⟩ rtl

/-- §3.3.6: `mpadded`. -/
def paddedOut {α : Type} (n : DOM.Node) (s : Computed) (content : Out α) : Out α :=
  let (box, at_) := padded content.box (lengthAttr n s "width") (lengthAttr n s "height") (lengthAttr n s "depth")
    ((lengthAttr n s "lspace").getD 0) ((lengthAttr n s "voffset").getD 0)
  ({ box, op := content.op, spaceLike := content.spaceLike, movable := content.movable } : Out α).add content at_
    (s.direction == .rtl)

/-- The text of the text children of element `id`, with the white space at its ends
removed: the content of an `mo` that the dictionary is read by. -/
def textContent (dom : Dom) (id : Nat) : String :=
  ((dom.get id).kids.foldl (fun acc k =>
    let kn := dom.get k
    if kn.type == .text then acc ++ kn.data else acc) "").trimAscii.toString

/-- The spaces an `mo` asks before and after it (§3.2.4.2): the `lspace` and `rspace`
attributes, else the dictionary's for its content and form. The form is the `form`
attribute's, else the one its place gives: the three answers are made here. -/
def operatorSpaces (dom : Dom) (id : Nat) (n : DOM.Node) (s : Computed) : OpSpaces :=
  let content := textContent dom id
  let explicit := (attr? n "form").bind formOf
  let em := lu s.fontSize
  let one := fun (f : Form) =>
    let p := lookup content (explicit.getD f) explicit.isSome
    ((lengthAttr n s "lspace").getD (em * (p.lspace : Int) / 18),
     (lengthAttr n s "rspace").getD (em * (p.rspace : Int) / 18))
  ⟨one .pre, one .inf, one .post⟩

/-- `movablelimits` of an `mo` (§3.2.4.2): the attribute (`true` or `false`), else the
dictionary's for its content (in its `form` attribute's form, else in any form). -/
def operatorMovable (dom : Dom) (id : Nat) (n : DOM.Node) : Bool :=
  if attrIs n "movablelimits" "true" then true
  else if attrIs n "movablelimits" "false" then false
  else
    let explicit := (attr? n "form").bind formOf
    (lookup (textContent dom id) (explicit.getD .inf) explicit.isSome).movablelimits

/-- §3.5: a table from its rows of cells: each column as wide as its widest cell, each
row as tall as its tallest cell above and below the row's baseline; cells centred in
their columns; the table centred on the math axis. `rows`: the row element and its
cells, laid out. -/
def tableOut {α : Type} (s : Computed) (rows : Array (Nat × Array (Out α))) : Out α := Id.run do
  let P := Params.of s
  let columns := rows.foldl (fun m r => max m r.2.size) 0
  let mut widths : Array Int := Array.replicate columns 0
  for (_, cells) in rows do
    for i in [0:cells.size] do
      widths := widths.set! i (max (widths.getD i 0) cells[i]!.box.width)
  let width := widths.foldl (· + ·) 0
  let heights := rows.map fun (_, cells) =>
    (cells.foldl (fun a c => max a c.box.ascent) 0, cells.foldl (fun a c => max a c.box.descent) 0)
  let height := heights.foldl (fun h r => h + r.1 + r.2) 0
  let ascent := height / 2 + P.axis
  let mut out : Out α := { box := ⟨width, ascent, height - ascent⟩ }
  let mut top : Int := -ascent
  for k in [0:rows.size] do
    let (rowId, cells) := rows[k]!
    let (a, d) := heights.getD k (0, 0)
    out := { out with boxes := out.boxes.push ⟨rowId, 0, top, width, a + d⟩ }
    let mut x : Int := 0
    for i in [0:cells.size] do
      let w := widths.getD i 0
      out := out.add cells[i]! ⟨x + (w - cells[i]!.box.width) / 2, top + a⟩ (s.direction == .rtl)
      x := x + w
    top := top + a + d
  return out

/-- §3.4.3: `mmultiscripts`: the base, then pairs of a subscript and a superscript, then
after an `mprescripts` the pairs that go before the base. `kids`: the laid-out children
with whether each is an `mprescripts`. Each pair is a column of scripts on the row. -/
def multiscriptsOut {α : Type} (s : Computed) (kids : Array (Out α × Bool)) : Out α := Id.run do
  let some (base, _) := kids[0]? | return {}
  let mut post : Array (Out α) := #[]
  let mut pre : Array (Out α) := #[]
  let mut seenPre := false
  let mut pending : Option (Out α) := none
  for i in [1:kids.size] do
    let (k, isPre) := kids[i]!
    if isPre then
      seenPre := true
      pending := none
    else
      match pending with
      | none => pending := some k
      | some sub =>
        let column := scriptsOut s ({} : Out α) (some sub) (some k)
        if seenPre then pre := pre.push column else post := post.push column
        pending := none
  return row ((pre.push base) ++ post) (s.direction == .rtl)

def tokenNames : List String := ["mi", "mn", "mo", "mtext", "ms"]

/-- The default padding of an `mtd` (appendix A: `padding: 0.5ex 0.4em`), which the
layout profile does not read from the user agent declarations: used when the cell's
style has no padding. -/
def cellStyle (s : Computed) : Computed :=
  let p := s.padding
  if p.top == 0 && p.right == 0 && p.bottom == 0 && p.left == 0 then
    { s with padding := ⟨s.fontSize / 4, s.fontSize * 0.4, s.fontSize / 4, s.fontSize * 0.4⟩ }
  else s

/-- The box of element `id` and of everything in it. `leaf k` lays out the inline
content of element `k` (a token element, or an element that is not MathML) and answers
its inline size, ascent and descent in CSS pixels with the caller's payload. Children
that are not elements, and elements with `display: none` or with `position: absolute` or
`fixed`, take no part (§3.1.1: such a child has no box in its parent's layout here). One level of
`fuel` for each element: the nesting bound of the rendering (64) is shared. -/
def layoutNode {α : Type} (dom : Dom) (styles : Array Computed)
    (leaf : Nat → Except String (Float × Float × Float × α)) : Nat → Nat → Except String (Out α)
  | 0, _ => throw "unsupported MathML nesting depth (maximum 64)"
  | fuel + 1, id => do
    let n := dom.get id
    let s := styles[id]!
    let name := if n.ns == some mathmlNS then n.lname else ""
    if name == "" || tokenNames.contains name then
      let (w, a, d, payload) ← leaf id
      let o : Out α := { box := ⟨lu w, lu a, lu d⟩, leaves := #[(payload, 0, -(lu a))] }
      return wrap id s (if name == "mo" then { o with op := some (operatorSpaces dom id n s),
                                                         movable := operatorMovable dom id n }
        else if name == "mtext" then { o with spaceLike := true } else o)
    if name == "mspace" then
      let len := fun (key : String) => (lengthAttr n s key).getD 0
      return wrap id s { box := space (len "width") (len "height") (len "depth"), spaceLike := true }
    if name == "mtable" then
      let mut rows : Array (Nat × Array (Out α)) := #[]
      for r in n.kids do
        if (dom.get r).type == .element && (styles[r]!).display != .none && !(styles[r]!).outOfFlow then
          let mut cells : Array (Out α) := #[]
          for c in (dom.get r).kids do
            if (dom.get c).type == .element && (styles[c]!).display != .none && !(styles[c]!).outOfFlow then
              cells := cells.push (← layoutNode dom styles leaf fuel c)
          rows := rows.push (r, cells)
      return wrap id s (tableOut s rows)
    let mut kids : Array (Out α) := #[]
    let mut pres : Array Bool := #[]
    for k in n.kids do
      let kn := dom.get k
      if kn.type == .element && (styles[k]!).display != .none && !(styles[k]!).outOfFlow then
        kids := kids.push (← layoutNode dom styles leaf fuel k)
        pres := pres.push (kn.ns == some mathmlNS && kn.lname == "mprescripts")
    -- §3.4.2: under and over scripts of an operator with movable limits are laid out as
    -- subscripts and superscripts when the math style is compact
    let limits := s.mathCompact && ((kids[0]?.map (·.movable)).getD false)
    let rtl := s.direction == .rtl
    let content : Out α := match name, kids.size with
      | "mfrac", 2 => fractionOut id n s kids[0]! kids[1]!
      | "msub", 2 => scriptsOut s kids[0]! (some kids[1]!) none
      | "msup", 2 => scriptsOut s kids[0]! none (some kids[1]!)
      | "msubsup", 3 => scriptsOut s kids[0]! (some kids[1]!) (some kids[2]!)
      | "munder", 2 => if limits then scriptsOut s kids[0]! (some kids[1]!) none
                       else underOverOut kids[0]! (some kids[1]!) none
      | "mover", 2 => if limits then scriptsOut s kids[0]! none (some kids[1]!)
                      else underOverOut kids[0]! none (some kids[1]!)
      | "munderover", 3 => if limits then scriptsOut s kids[0]! (some kids[1]!) (some kids[2]!)
                           else underOverOut kids[0]! (some kids[1]!) (some kids[2]!)
      | "mroot", 2 => rootOut id s kids[0]! kids[1]!
      | "msqrt", _ => radicalOut id s (row kids rtl)
      | "mpadded", _ => paddedOut n s (row kids rtl)
      | "mmultiscripts", _ => multiscriptsOut s (kids.zip pres)
      | _, _ => row kids rtl
    return wrap id (if name == "mtd" then cellStyle s else s) content

/-! ### Axioms of the theorems above (the build log shows them) -/

#print axioms sized_min
#print axioms sized_auto

end L4Factoidal.Rendering.Math
