import L4Factoidal.Rendering.Style
import L4Factoidal.Rendering.Floats

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

/-- An absolutely positioned box (CSS Positioned Layout 3 §2.1: `absolute` or `fixed`) that
is not laid out yet: its containing block is an ancestor's padding box, known only when
that ancestor's height is. `(x,y)` is its static position (§4.1): where its margin box
would be in the flow. -/
structure Pending where
  id : Nat
  x : Float
  y : Float
  /-- For a child of a flex or grid container, the static position is that of the box
  aligned in the container's content box (CSS Flexbox 1 §4.1): `(x,y)` is that box's
  corner, `width` by `height` its size, and `fx`, `fy` the share of the free space before
  the box on each axis (0 start, 0.5 centre, 1 end). In flow these are zero. -/
  width : Float := 0
  height : Float := 0
  fx : Float := 0
  fy : Float := 0
  deriving Repr

/-- The grid of a grid container, kept in its fragment until the container places its
absolutely positioned descendants (CSS Grid 2 §9.1: their containing block is a grid
area). `x`, `y`, `width`, `height`: the content box (px); the starts and sizes of the
tracks of the implicit grid in layout units from the content box's start edge (for a
right-to-left container, the right edge); the line names of the explicit grid and the
implicit tracks before it. -/
structure GridFrame where
  x : Float
  y : Float
  width : Float
  height : Float
  rtl : Bool := false
  colNames : Array (List String) := #[]
  rowNames : Array (List String) := #[]
  colLead : Nat := 0
  rowLead : Nat := 0
  colStarts : Array Int := #[]
  rowStarts : Array Int := #[]
  colSizes : Array Nat := #[]
  rowSizes : Array Nat := #[]
  deriving Repr

/-- A laid-out fragment. For a box, `boxes[0]` is its own border box and `height` is the
height of its margin box. `pending` are the absolutely positioned descendants that the
nearest positioned ancestor (or the root) still has to lay out. -/
structure Result where
  nodes : Array Node := #[]
  boxes : Array Box := #[]
  runs : Array GlyphRun := #[]
  height : Float := 0
  pending : Array Pending := #[]
  /-- The part of `height` that is the bottom margin of the box (or of the last block of
  a flow): it collapses with the margin that follows it (CSS 2.1 §8.3.1). -/
  marginBottom : Float := 0
  /-- The floats of the block formatting context after this fragment (CSS 2.1 §9.5): what
  the flow that follows must still avoid. Empty for a box that contains its floats. -/
  floats : Array Floats.Box := #[]
  /-- The grid of the grid container whose contents this is (`GridFrame`); none
  elsewhere. -/
  grid : Option GridFrame := none
  deriving Repr
instance : Inhabited Result := ⟨{}⟩

/-- A fragment moved by `(dx,dy)`: its paint in a translated group, its boxes and glyph
positions moved by the same amount. Not moved at all: the fragment itself. -/
def Result.shift (dx dy : Float) (r : Result) : Result :=
  if dx == 0 && dy == 0 then r else
  {r with nodes := if r.nodes.isEmpty then #[] else #[.group none ⟨1,0,0,1,dx,dy⟩ r.nodes.toList],
          boxes := r.boxes.map fun b => {b with x := b.x+dx, y := b.y+dy},
          runs := r.runs.map fun run => {run with glyphs := run.glyphs.map fun g => {g with x := g.x+dx, y := g.y+dy}},
          pending := r.pending.map fun p => {p with x := p.x+dx, y := p.y+dy},
          floats := r.floats.map fun f => {f with x := f.x+LU.ofPx dx, y := f.y+LU.ofPx dy},
          grid := r.grid.map fun g => {g with x := g.x+dx, y := g.y+dy}}

/-- Two fragments in one: the paint of `b` over that of `a`. The height is `a`'s. -/
def Result.over (a b : Result) : Result :=
  {a with nodes := a.nodes ++ b.nodes, boxes := a.boxes ++ b.boxes, runs := a.runs ++ b.runs,
          pending := a.pending ++ b.pending}

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
  /-- The min-content and max-content widths of the item's contents (its content box),
  whatever its `width` says: the content size suggestion of the automatic minimum size
  (CSS Flexbox 1 §4.5), and the base size of an item with no definite size. -/
  contentIntrinsic : Item → Except String (Float × Float)
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
  /-- The element whose content box this is, when the context records used values for it
  (grid: the used track sizes, for `getComputedStyle`). -/
  source : Option Nat := none
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
      -- an absolutely positioned child is not an item (CSS Flexbox 1 §4.1)
      if (styles[k]!).display != .none && !(styles[k]!).pos.isAbsolute then
        if text.any (fun t => !blankText (dom.get t).data) then out := out.push (.anonymous container text)
        text := #[]
        out := out.push (.element k)
  if text.any (fun t => !blankText (dom.get t).data) then out := out.push (.anonymous container text)
  return out

/-- CSS 2.1 §10.5: the content height of the box of `id` when its `height` is definite
from the styles alone: a length, or a percentage of a containing block (its parent
element's box) whose height is definite in the same way. `none`: the height depends on
content, or on a containing block known only in layout (an absolutely positioned box, the
root). The limits `min-height` and `max-height` of the ancestors are not read. A loop up
the ancestors; an element whose height is a length costs one step. -/
def definiteHeight (dom : Dom) (styles : Array Computed) (id : Nat) : Option Float := Id.run do
  -- the height of `id` is `scale` times the height that `cur`'s percentage is of, plus `offset`
  let mut scale : Float := 1
  let mut offset : Float := 0
  let mut cur := id
  for _ in [0:256] do
    let s := styles[cur]!
    match s.height with
    | .px h => return some (scale*(max 0 h)+offset)
    | .percent p => scale := scale*p
    | .calc p v =>
      offset := offset+scale*v
      scale := scale*p
    | _ => return none
    if s.pos.isAbsolute then return none
    match (dom.get cur).parent with
    | some parent => if (dom.get parent).type == .element then cur := parent else return none
    | none => return none
  return none

/-- The length that a percentage `height` of `id` resolves to (`definiteHeight`); `none`
when the height is not a percentage, when the containing block's height depends on
content, and for an absolutely positioned box, which resolves its own where it is placed. -/
def resolvedHeight (dom : Dom) (styles : Array Computed) (id : Nat) : Option Float :=
  let s := styles[id]!
  match s.height with
  | .percent _ | .calc _ _ => if s.pos.isAbsolute then none else definiteHeight dom styles id
  -- `height: stretch` (CSS Sizing 4 §6.1): the margin box fills a definite containing height
  | .stretch =>
    if s.pos.isAbsolute then none else
    match (dom.get id).parent with
    | some parent =>
      if (dom.get parent).type == .element then
        (definiteHeight dom styles parent).map fun h =>
          max 0 (h-s.margin.top-s.margin.bottom-s.borderEdges.top-s.borderEdges.bottom-s.padding.top-s.padding.bottom)
      else none
    | none => none
  | _ => none

/-- The style of `id` with a percentage `height` that resolves as that length. -/
def percentHeight (dom : Dom) (styles : Array Computed) (id : Nat) : Computed :=
  match resolvedHeight dom styles id with
  | some h => {styles[id]! with height := .px h}
  | none => styles[id]!

/-- The styles with each percentage `height` that `definiteHeight` resolves as that
length (CSS 2.1 §10.5); a percentage of a height that depends on content stays, and is
read as `auto`. -/
def percentHeights (dom : Dom) (styles : Array Computed) : Array Computed :=
  (Array.range styles.size).map (percentHeight dom styles)

/-- Kind: structure. Says: resolving percentage heights keeps one style per node. -/
theorem percentHeights_size (dom : Dom) (styles : Array Computed) :
    (percentHeights dom styles).size = styles.size := by
  simp [percentHeights]

/-- Kind: structure. Says: the style of a node after the pass is `percentHeight` of it. -/
theorem percentHeights_get (dom : Dom) (styles : Array Computed) (id : Nat) (hid : id < styles.size) :
    (percentHeights dom styles)[id]! = percentHeight dom styles id := by
  simp [percentHeights, hid]

/-- Kind: frame. Says: the pass changes nothing of a style but its `height`: two styles
that differ at most there before it differ at most there after it. Does not say: what
the new height is (a `Float`: tested). -/
theorem percentHeight_rest (dom : Dom) (styles : Array Computed) (id : Nat) (h : CSS.Length) :
    {percentHeight dom styles id with height := h} = {styles[id]! with height := h} := by
  unfold percentHeight
  split <;> rfl

/-- Kind: frame. Says: a height that is a length is left as it is. -/
theorem percentHeight_px (dom : Dom) (styles : Array Computed) (id : Nat) (v : Float)
    (h : (styles[id]!).height = .px v) : percentHeight dom styles id = styles[id]! := by
  simp [percentHeight, resolvedHeight, h]

/-- Kind: frame. Says: `height: auto` is left as it is. -/
theorem percentHeight_auto (dom : Dom) (styles : Array Computed) (id : Nat)
    (h : (styles[id]!).height = .auto) : percentHeight dom styles id = styles[id]! := by
  simp [percentHeight, resolvedHeight, h]

theorem resolvedHeight_absolute (dom : Dom) (styles : Array Computed) (id : Nat)
    (h : (styles[id]!).pos.isAbsolute = true) : resolvedHeight dom styles id = none := by
  unfold resolvedHeight
  simp only [h]
  split <;> rfl

/-- Kind: frame. Says: the style of an absolutely positioned box is left as it is: its
percentage height is of its containing block's padding box, known where it is placed. -/
theorem percentHeight_absolute (dom : Dom) (styles : Array Computed) (id : Nat)
    (h : (styles[id]!).pos.isAbsolute = true) : percentHeight dom styles id = styles[id]! := by
  simp [percentHeight, resolvedHeight_absolute dom styles id h]

/-- A width given as a sizing keyword (CSS Sizing 3 §3.2, §5.1), as a content-box width:
`lo` and `hi` are the min-content and max-content widths of the box's contents and `fill`
the content width with which the box fills its containing block. `none` when `l` is not
a keyword. -/
def keywordWidth (l : CSS.Length) (lo hi fill : Float) : Option Float :=
  match l with
  | .minContent => some lo
  | .maxContent => some hi
  | .fitContent => some (min hi (max lo fill))
  | .stretch => some (max 0 fill)
  | _ => none

/-- The margin-box width of a box that shrinks to fit (a float, an inline-block, an
absolutely positioned box): by its `width` keyword, else fit-content (CSS 2.1 §10.3.5).
`lo` and `hi` are its min-content and max-content margin-box widths, `room` the
available width. -/
def shrinkWidth (l : CSS.Length) (lo hi room : Float) : Float :=
  match l with
  | .minContent => lo
  | .maxContent => hi
  | .stretch => room
  | _ => min hi (max lo room)

/-- Kind: totality. Says: a width is taken from the contents or the fill width exactly
when it is a sizing keyword; any other length is left to `CSS.resolve`. -/
theorem keywordWidth_isSome (l : CSS.Length) (lo hi fill : Float) :
    (keywordWidth l lo hi fill).isSome = l.isKeyword := by
  cases l <;> rfl

/-- Kind: frame. Says: a sizing keyword is not a number: wherever the layout asks
`CSS.resolve` for one it gets `none`, as for `auto`, so code that does not know the
keywords lays the box out as `auto`. -/
theorem resolve_keyword (basis : Float) (l : CSS.Length) (h : l.isKeyword = true) : CSS.resolve basis l = none := by
  cases l <;> first | rfl | (simp [CSS.Length.isKeyword] at h)

/-- Says: a box that shrinks to fit takes exactly its min-content or max-content width
when its `width` says so, and the fit-content width when it is `auto`. -/
theorem shrinkWidth_minContent (lo hi room : Float) : shrinkWidth .minContent lo hi room = lo := rfl
theorem shrinkWidth_maxContent (lo hi room : Float) : shrinkWidth .maxContent lo hi room = hi := rfl
theorem shrinkWidth_auto (lo hi room : Float) : shrinkWidth .auto lo hi room = min hi (max lo room) := rfl

/-- An inline-block whose contents are not all inline (CSS 2.1 §9.2.2, §10.1): it has a
child that is a block-level box or a float, or it is positioned and has element children
(it is then the containing block of its absolutely positioned descendants). Such a box is
laid out as a block container; one with inline content only stays a line of its own. -/
def blockInside (dom : Dom) (styles : Array Computed) (id : Nat) : Bool :=
  (dom.get id).kids.any fun k =>
    (dom.get k).type == .element &&
      ((styles[id]!).pos.isPositioned ||
        ((styles[k]!).display != .none && ((styles[k]!).display.isBlockLevel || (styles[k]!).pos.float != .none)))

/-- The room beside `floats` for a line or box `h` high at `y`, in a content box from `x`,
`width` wide: how far its left edge is from `x`, and its width. With no floats: all of it. -/
def floatBand (floats : Array Floats.Box) (x width y h : Float) : Float × Float :=
  if floats.isEmpty then (0,width) else
  let (l,w) := Floats.band floats.toList (LU.ofPx x) (LU.ofPx width) (LU.ofPx y) (LU.ofPx (max h 1))
  (LU.toPx l-x,LU.toPx w)

/-- The bottom of the lowest float, as a height from `y`; 0 with no float below `y`. -/
def floatsHeight (floats : Array Floats.Box) (y : Float) : Float :=
  if floats.isEmpty then 0 else LU.toPx (Floats.below floats.toList (LU.ofPx y))-y

/-- `box-sizing: border-box` (CSS Sizing 3 §3.3) taken out of a style: `width`, `height`
and their limits as content-box sizes, which is what the layout reads. A percentage
becomes that percentage less the padding and border. A table's `width` is read as its
border box by the table layout itself. -/
def contentBoxed (s : Computed) : Computed :=
  if !s.pos.borderBox || s.display.isTable then s else
  let b := s.borderEdges
  let p := s.padding
  let h := b.left+b.right+p.left+p.right
  let v := b.top+b.bottom+p.top+p.bottom
  let less := fun (d : Float) (l : CSS.Length) => match l with
    | .px w => CSS.Length.px (max 0 (w-d))
    | .percent q => .calc q (-d)
    | .calc q x => .calc q (x-d)
    | other => other
  {s with width := less h s.width, minWidth := less h s.minWidth, maxWidth := less h s.maxWidth,
          height := less v s.height, minHeight := less v s.minHeight, maxHeight := less v s.maxHeight}

end L4Factoidal.Rendering.Layout
