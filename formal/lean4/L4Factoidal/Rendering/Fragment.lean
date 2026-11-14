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
  /-- The first baseline of the fragment (CSS Box Alignment 3 §9.1), page y: that of its
  first line box; none when it has no line box (the consumer then synthesizes one from
  the border box). Combining fragments keeps the first one. -/
  baseline : Option Float := none
  /-- The last baseline of the fragment, page y: that of its last line box. Combining
  fragments keeps the last one. An inline-block sits on its line by it (CSS 2.1 §10.8.1). -/
  lastBaseline : Option Float := none
  /-- The number of box layouts that this fragment took, with those of a measuring pass
  whose result was laid out again: the counter that `workLimit` bounds. -/
  work : Nat := 0
  /-- The fragment was laid out to be measured (`Constraints.measure`) and a second layout
  of something inside it was left out: its size is right, the places of what is inside
  may not be. It is laid out again before it is used as the final fragment. -/
  rough : Bool := false
  deriving Repr
instance : Inhabited Result := ⟨{}⟩

/-- The most box layouts that the layout of a document of `nodes` nodes may take. A layout
lays a box out once, or twice when a flex or grid container first measures an item and
then gives it its final size; a container that is itself only being measured leaves the
second layout out (`Constraints.measure`), so the count grows with the nodes times the
nesting depth (at most 64), not with a power of the depth. A document that would take
more is refused (`overWork`), and the engine goes on. -/
def workLimit (nodes : Nat) : Nat := 256 * (nodes + 64)

/-- The refusal at the bound: a fragment that took more work than the document's limit. -/
def overWork (nodes work : Nat) : Bool := decide (workLimit nodes < work)

/-- Says: the layout is refused exactly when its work is over the limit of the document. -/
theorem overWork_iff (nodes work : Nat) : overWork nodes work = true ↔ workLimit nodes < work := by
  simp [overWork]

/-- Says: a larger document never has a smaller limit: adding content can not turn a
layout that was within the limit into a refused one by the limit alone. -/
theorem workLimit_mono (a b : Nat) (h : a ≤ b) : workLimit a ≤ workLimit b := by
  unfold workLimit; omega

/-- A fragment moved by `(dx,dy)`: its paint in a translated group, its boxes and glyph
positions moved by the same amount. Not moved at all: the fragment itself. -/
def Result.shift (dx dy : Float) (r : Result) : Result :=
  if dx == 0 && dy == 0 then r else
  {r with nodes := if r.nodes.isEmpty then #[] else #[.group none ⟨1,0,0,1,dx,dy⟩ r.nodes.toList],
          boxes := r.boxes.map fun b => {b with x := b.x+dx, y := b.y+dy},
          runs := r.runs.map fun run => {run with glyphs := run.glyphs.map fun g => {g with x := g.x+dx, y := g.y+dy}},
          pending := r.pending.map fun p => {p with x := p.x+dx, y := p.y+dy},
          floats := r.floats.map fun f => {f with x := f.x+LU.ofPx dx, y := f.y+LU.ofPx dy},
          grid := r.grid.map fun g => {g with x := g.x+dx, y := g.y+dy},
          baseline := r.baseline.map (·+dy), lastBaseline := r.lastBaseline.map (·+dy)}

/-- A fragment under the transform `t` (CSS Transforms 1 §6): its paint in a group with
the transform; its boxes as the bounding boxes of where they are drawn, so that a point
on the picture is a point in the box; its glyphs and pending boxes moved with it. The
fragment's height and floats are as laid out: a transform does not change the flow. -/
def Result.transformed (t : Transform) (r : Result) : Result :=
  let point := fun (x y : Float) => Math.Affine2.applyPoint .float t x y
  {r with nodes := if r.nodes.isEmpty then #[] else #[.group none t r.nodes.toList],
          boxes := r.boxes.map fun b =>
            let (x,y,w,h) := CSS.BoxTransform.bounds t b.x b.y b.width b.height
            {b with x, y, width := w, height := h},
          runs := r.runs.map fun run => {run with glyphs := run.glyphs.map fun g =>
            let (x,y) := point g.x g.y
            {g with x, y}},
          pending := r.pending.map fun p =>
            let (x,y) := point p.x p.y
            {p with x, y}}

/-- Says: a transform keeps the work, the height and the floats of a fragment. -/
theorem Result.transformed_flow (t : Transform) (r : Result) :
    (r.transformed t).work = r.work ∧ (r.transformed t).height = r.height ∧ (r.transformed t).floats = r.floats :=
  ⟨rfl, rfl, rfl⟩

/-- Says: a transform keeps the boxes one for one, with their nodes. -/
theorem Result.transformed_sources (t : Transform) (r : Result) :
    (r.transformed t).boxes.map (·.source) = r.boxes.map (·.source) := by
  simp [Result.transformed, Array.map_map, Function.comp_def]

/-- Two fragments in one: the paint of `b` over that of `a`. The height is `a`'s. -/
def Result.over (a b : Result) : Result :=
  {a with nodes := a.nodes ++ b.nodes, boxes := a.boxes ++ b.boxes, runs := a.runs ++ b.runs,
          pending := a.pending ++ b.pending, baseline := a.baseline <|> b.baseline,
          lastBaseline := b.lastBaseline <|> a.lastBaseline,
          work := a.work + b.work, rough := a.rough || b.rough}

/-- Says: putting fragments together adds their work: no layout goes uncounted. -/
theorem Result.over_work (a b : Result) : (a.over b).work = a.work + b.work := rfl

/-- Says: moving a fragment does not change its work. -/
theorem Result.shift_work (dx dy : Float) (r : Result) : (r.shift dx dy).work = r.work := by
  unfold Result.shift; split <;> rfl

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
  /-- Only the size of the fragment is wanted (a measuring pass): a container laid out
  with it does not lay its own items out a second time (`Result.rough`). -/
  measure : Bool := false
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
  /-- The container is only being measured (`Constraints.measure`). -/
  measure : Bool := false
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

/-- The length that a `min-height` or `max-height` `l` of `id` resolves to when it is a
percentage or `stretch` (CSS 2.1 §10.7; CSS Sizing 4 §6.1) and the containing block's
height is definite from the styles (`definiteHeight` of the parent element): the
percentage of that height, or what fills it inside the box's margins, borders and padding.
`none` for any other value, when that height depends on content (the limit then does not
apply), and for an absolutely positioned box. -/
def resolvedLimit (dom : Dom) (styles : Array Computed) (id : Nat) (l : CSS.Length) : Option Float :=
  let s := styles[id]!
  let containing := fun (_ : Unit) =>
    if s.pos.isAbsolute then none else
    match (dom.get id).parent with
    | some parent => if (dom.get parent).type == .element then definiteHeight dom styles parent else none
    | none => none
  match l with
  | .percent p => (containing ()).map fun h => max 0 (h*p)
  | .stretch => (containing ()).map fun h =>
      max 0 (h-s.margin.top-s.margin.bottom-s.borderEdges.top-s.borderEdges.bottom-s.padding.top-s.padding.bottom)
  | _ => none

/-- A limit as the length it resolves to, or as it is. -/
def limitLength (dom : Dom) (styles : Array Computed) (id : Nat) (l : CSS.Length) : CSS.Length :=
  match resolvedLimit dom styles id l with
  | some v => .px v
  | none => l

/-- The style of `id` with a percentage `height` that resolves as that length, and its
`min-height` and `max-height` likewise. -/
def percentHeight (dom : Dom) (styles : Array Computed) (id : Nat) : Computed :=
  let s := styles[id]!
  let height := match resolvedHeight dom styles id with
    | some h => .px h
    | none => s.height
  {s with height, minHeight := limitLength dom styles id s.minHeight, maxHeight := limitLength dom styles id s.maxHeight}

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

/-- Kind: frame. Says: the pass changes nothing of a style but its `height`, `min-height`
and `max-height`: two styles that differ at most there before it differ at most there
after it. Does not say: what the new values are (`Float`: tested). -/
theorem percentHeight_rest (dom : Dom) (styles : Array Computed) (id : Nat) (h lo hi : CSS.Length) :
    {percentHeight dom styles id with height := h, minHeight := lo, maxHeight := hi} =
      {styles[id]! with height := h, minHeight := lo, maxHeight := hi} := by
  unfold percentHeight
  rfl

/-- Kind: frame. Says: a limit that is a length, `auto` or a content keyword is left as it is. -/
theorem limitLength_px (dom : Dom) (styles : Array Computed) (id : Nat) (v : Float) :
    limitLength dom styles id (.px v) = .px v := rfl

theorem limitLength_auto (dom : Dom) (styles : Array Computed) (id : Nat) :
    limitLength dom styles id .auto = .auto := rfl

/-- Kind: frame. Says: a height that is a length, with limits that are lengths or `auto`,
is left as it is. -/
theorem percentHeight_px (dom : Dom) (styles : Array Computed) (id : Nat) (v : Float)
    (h : (styles[id]!).height = .px v)
    (lo : limitLength dom styles id (styles[id]!).minHeight = (styles[id]!).minHeight)
    (hi : limitLength dom styles id (styles[id]!).maxHeight = (styles[id]!).maxHeight) :
    percentHeight dom styles id = styles[id]! := by
  unfold percentHeight
  simp only [resolvedHeight, h, lo, hi]
  generalize styles[id]! = s at h
  cases s
  simp_all

/-- Kind: frame. Says: `height: auto` with such limits is left as it is. -/
theorem percentHeight_auto (dom : Dom) (styles : Array Computed) (id : Nat)
    (h : (styles[id]!).height = .auto)
    (lo : limitLength dom styles id (styles[id]!).minHeight = (styles[id]!).minHeight)
    (hi : limitLength dom styles id (styles[id]!).maxHeight = (styles[id]!).maxHeight) :
    percentHeight dom styles id = styles[id]! := by
  unfold percentHeight
  simp only [resolvedHeight, h, lo, hi]
  generalize styles[id]! = s at h
  cases s
  simp_all

theorem resolvedLimit_absolute (dom : Dom) (styles : Array Computed) (id : Nat) (l : CSS.Length)
    (h : (styles[id]!).pos.isAbsolute = true) : resolvedLimit dom styles id l = none := by
  unfold resolvedLimit
  simp only [h]
  split <;> rfl

theorem resolvedHeight_absolute (dom : Dom) (styles : Array Computed) (id : Nat)
    (h : (styles[id]!).pos.isAbsolute = true) : resolvedHeight dom styles id = none := by
  unfold resolvedHeight
  simp only [h]
  split <;> rfl

/-- Kind: frame. Says: the style of an absolutely positioned box is left as it is: its
percentage height is of its containing block's padding box, known where it is placed. -/
theorem percentHeight_absolute (dom : Dom) (styles : Array Computed) (id : Nat)
    (h : (styles[id]!).pos.isAbsolute = true) : percentHeight dom styles id = styles[id]! := by
  simp [percentHeight, limitLength, resolvedHeight_absolute dom styles id h, resolvedLimit_absolute dom styles id _ h]

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
      ((styles[id]!).pos.containsAbsolutes ||
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

/-- The style with the percentage parts of its margins and padding resolved against a
containing block `width` wide (CSS 2.1 §8.3, §8.4: all four sides are of the width). -/
def withEdges (s : Computed) (width : Float) : Computed :=
  if !s.pos.percentEdges then s else
  let m := s.pos.marginOf
  let p := s.pos.paddingOf
  {s with margin := ⟨s.margin.top+m.1*width,s.margin.right+m.2.1*width,s.margin.bottom+m.2.2.1*width,s.margin.left+m.2.2.2*width⟩,
          padding := ⟨s.padding.top+max 0 (p.1*width),s.padding.right+max 0 (p.2.1*width),
                      s.padding.bottom+max 0 (p.2.2.1*width),s.padding.left+max 0 (p.2.2.2*width)⟩,
          pos := {s.pos with marginOf := (0,0,0,0), paddingOf := (0,0,0,0)}}

/-- The content width of the box of a node when the styles alone make it definite, given
the width `cb` of its containing block (when that is definite) and its own style with its
edges resolved: a length; a percentage of `cb`; for a block-level box in the flow with
`width: auto`, what `cb` leaves inside its margins, borders and padding. An inline box
passes its containing block on. `none`: the width depends on content (a float, an
inline-block, a table cell, an absolutely positioned box with no length). Limits that are
lengths apply. -/
def definiteWidth (s : Computed) (element : Bool) (cb : Option Float) : Option Float :=
  if !element then cb else
  if s.display == .none then none else
  if s.display == .inline then cb else
  let b := s.borderEdges
  let inside := b.left+b.right+s.padding.left+s.padding.right
  -- `box-sizing: border-box`: a width names the border box
  let content := fun (w : Float) => if s.pos.borderBox then max 0 (w-inside) else w
  let limit := fun (w : Float) =>
    let w := match s.maxWidth with
      | .px m => min w (content m)
      | _ => w
    match s.minWidth with
    | .px m => max w (content m)
    | _ => w
  match s.width with
  | .px w => some (limit (content w))
  | .percent p => if s.pos.isAbsolute then none else cb.map fun c => limit (content (max 0 (c*p)))
  | .auto =>
    if s.pos.isAbsolute || s.pos.float != .none || !s.display.isBlockLevel || s.display.isTable then none
    else cb.map fun c => limit (max 0 (c-s.margin.left-s.margin.right-inside))
  | _ => none

/-- The pass down the tree: `pending` holds nodes with the width of their containing block.
One step a node; `fuel` is the number of nodes. -/
def percentEdgesLoop (dom : Dom) : Nat → List (Nat × Option Float) → Array Computed → Array Computed
  | 0, _, out => out
  | _+1, [], out => out
  | fuel+1, (id,cb) :: rest, out =>
    let n := dom.get id
    let s := out[id]!
    -- an absolutely positioned box resolves against a padding box known only in layout
    let s := match cb with
      | some w => if s.pos.isAbsolute then s else withEdges s w
      | none => s
    let own := definiteWidth s (n.type == .element) cb
    percentEdgesLoop dom fuel (n.kids.toList.map (fun k => (k,own)) ++ rest) (out.set! id s)

/-- The styles with the percentage margins and padding of each box resolved against the
width of its containing block, where the styles make that width definite (`definiteWidth`:
the viewport `width` for the root, then down through blocks in the flow and boxes with a
length for a width); elsewhere a percentage part stays out, as before it was read. A page
with no percentage margin or padding pays one pass over its styles. -/
def percentEdges (dom : Dom) (styles : Array Computed) (width : Float) : Array Computed :=
  if !(styles.any fun s => s.pos.percentEdges) then styles
  else percentEdgesLoop dom (dom.size+1) [(0,some width)] styles

/-- Kind: frame. Says: a page with no percentage margin or padding is left as it is. -/
theorem percentEdges_unused (dom : Dom) (styles : Array Computed) (width : Float)
    (h : (styles.any fun s => s.pos.percentEdges) = false) : percentEdges dom styles width = styles := by
  simp [percentEdges, h]

/-- Kind: structure. Says: the pass keeps one style a node. -/
theorem percentEdgesLoop_size (dom : Dom) (fuel : Nat) (pending : List (Nat × Option Float)) (out : Array Computed) :
    (percentEdgesLoop dom fuel pending out).size = out.size := by
  induction fuel generalizing pending out with
  | zero => rfl
  | succ fuel ih =>
    cases pending with
    | nil => rfl
    | cons head rest =>
      obtain ⟨id, cb⟩ := head
      unfold percentEdgesLoop
      simp only []
      rw [ih]
      simp

theorem percentEdges_size (dom : Dom) (styles : Array Computed) (width : Float) :
    (percentEdges dom styles width).size = styles.size := by
  unfold percentEdges
  split
  · rfl
  · exact percentEdgesLoop_size ..

/-- Kind: frame. Says: resolving the edges of a style changes its margin, its padding and
its position record only. -/
theorem withEdges_rest (s : Computed) (width : Float) (m p : Edges) (q : PositionStyle) :
    {withEdges s width with margin := m, padding := p, pos := q} = {s with margin := m, padding := p, pos := q} := by
  unfold withEdges
  split <;> rfl

/-- Kind: frame. Says: a style with no percentage edge is left as it is. -/
theorem withEdges_none (s : Computed) (width : Float) (h : s.pos.percentEdges = false) : withEdges s width = s := by
  simp [withEdges, h]

end L4Factoidal.Rendering.Layout
