import L4Factoidal.Rendering.Style

/-! The interface between formatting contexts: constraints in, fragments out.

`Layout.layoutTask` lays out a box and its descendants; flex and grid containers lay
out their items through this interface, so every context nests in every other:

- `Result` is a laid-out fragment: its paint, the border boxes of its elements, its
  glyph runs and its height. Positions are absolute; `Result.shift` moves a fragment.
- `Constraints` is what a parent context imposes on a child box.
- `Item` is a child of a flex or grid container (an element, or an anonymous item of
  text), and `Children` is what a context may ask about its items. The callbacks are
  given by `layoutTask`, which calls itself with the smaller fuel, so a context is an
  ordinary function with no recursion of its own.
- `ContentBox` is the container's content box, resolved by `layoutTask` as for any box.

A context is two functions: its layout
`Children → Computed → Array Item → ContentBox → Except String Result` (the result's
`height` is the content height) and its intrinsic widths
`Children → Computed → Array Item → Except String (Float × Float)` (the min-content
and max-content widths of the content box). -/
namespace L4Factoidal.Rendering.Layout
open DOM CSS

/-- The border box of an element. -/
structure Box where
  source : Nat
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr

/-- A laid-out fragment. For a box, `boxes[0]` is its own border box and `height` is the
height of its margin box. -/
structure Result where
  nodes : Array Node := #[]
  boxes : Array Box := #[]
  runs : Array GlyphRun := #[]
  height : Float := 0
  deriving Repr
instance : Inhabited Result := ⟨{}⟩

/-- A fragment moved by `(dx,dy)`: its paint in a translated group, its boxes and glyph
positions moved by the same amount. Not moved at all: the fragment itself. -/
def Result.shift (dx dy : Float) (r : Result) : Result :=
  if dx == 0 && dy == 0 then r else
  {r with nodes := if r.nodes.isEmpty then #[] else #[.group none ⟨1,0,0,1,dx,dy⟩ r.nodes.toList],
          boxes := r.boxes.map fun b => {b with x := b.x+dx, y := b.y+dy},
          runs := r.runs.map fun run => {run with glyphs := run.glyphs.map fun g => {g with x := g.x+dx, y := g.y+dy}}}

/-- Two fragments in one: the paint of `b` over that of `a`. The height is `a`'s. -/
def Result.over (a b : Result) : Result :=
  {a with nodes := a.nodes ++ b.nodes, boxes := a.boxes ++ b.boxes, runs := a.runs ++ b.runs}

/-- What a parent formatting context imposes on a child box. -/
structure Constraints where
  /-- The width of the containing block: percentages resolve on it. -/
  available : Float
  /-- The used width of the border box, when the parent decides it (a flex item's main
  size, a stretched item, a grid area): the box's own `width`, `min-width` and
  `max-width` are then not read. -/
  width : Option Float := none
  /-- The used height of the border box, when the parent decides it. -/
  height : Option Float := none
  deriving Repr

/-- A child of a flex or grid container. -/
inductive Item where
  /-- An element child: its box is blockified (CSS Display 3 §2.7). -/
  | element (id : Nat)
  /-- A run of text children `kids` of `container`: an anonymous item. -/
  | anonymous (container : Nat) (kids : Array Nat)
  deriving Repr, Inhabited

/-- What a formatting context may ask about its items. -/
structure Children where
  /-- The item's computed style; an anonymous item has its container's inherited values
  and no box edges. -/
  style : Item → Computed
  /-- The min-content and max-content widths of the item's margin box. -/
  intrinsic : Item → Except String (Float × Float)
  /-- The item's box laid out whole with its margin box at `(x,y)`. -/
  layout : Item → (x y : Float) → Constraints → Except String Result
  /-- The contents only of the item's box, for a border box `width` wide whose margin box
  is at `(x,y)`: no background, border or box of its own; the result's `height` is the
  content height. With `frame`, a box whose height the parent decides after seeing its
  content is laid out once. -/
  content : Item → (x y width : Float) → Except String Result
  /-- The item's box around `content` (from `content` with the same `x`, `y`, `width`),
  with a border box `height` high: decorations, the own box, the margin-box height. -/
  frame : Item → (x y width height : Float) → Result → Result
  /-- The item's contents depend on its height (a flex or grid container): then it is
  laid out again with `layout` when its height changes, not just framed. -/
  heightSensitive : Item → Bool

/-- A container's content box, as `layoutTask` resolved it. -/
structure ContentBox where
  x : Float
  y : Float
  width : Float
  /-- The content height when it is definite (a specified or imposed height). -/
  height : Option Float := none
  minHeight : Float := 0
  maxHeight : Option Float := none
  deriving Repr

/-- White space only (CSS Text 3 §4.1.1 document white space). -/
def blankText (s : String) : Bool := s.all fun c => c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\x0c'

/-- The items of a flex or grid container (CSS Flexbox 1 §4, CSS Grid 2 §6): each element
child that generates a box, and each run of text that is not only white space as an
anonymous item, in document order. -/
def collectItems (dom : Dom) (styles : Array Computed) (container : Nat) : Array Item := Id.run do
  let mut out : Array Item := #[]
  let mut text : Array Nat := #[]
  for k in (dom.get container).kids do
    let n := dom.get k
    if n.type == .text then
      text := text.push k
    else if n.type == .element then
      if (styles[k]!).display != .none then
        if text.any (fun t => !blankText (dom.get t).data) then out := out.push (.anonymous container text)
        text := #[]
        out := out.push (.element k)
  if text.any (fun t => !blankText (dom.get t).data) then out := out.push (.anonymous container text)
  return out

end L4Factoidal.Rendering.Layout
