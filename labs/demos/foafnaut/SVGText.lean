import SVGCurves

/-! SVG text layout (issue 1270): where each glyph of a `text` element goes.

SVG 1.1 §10 and the SVG 2 Text chapter, a subset: per-character `x`, `y`, `dx`,
`dy` and `rotate`; text chunks and `text-anchor`; `letter-spacing` and
`word-spacing`; common `dominant-baseline` values; and `textPath` (SVG 1.1 §10.13):
the midpoint of each glyph's advance goes on the path at its distance along the
path, and the glyph turns to the tangent there. A glyph whose midpoint is off the
path is not drawn.

The glyphs come from a `Shaper`, which the caller makes from the same font profile
as HTML text, so there is no second shaper here. This module computes positions
only; `SVG.lean` reads the elements and paints the outlines. -/
namespace NativeSVGText
open NativeSVG NativeSVGPath

inductive Anchor where
  | start | middle | finish
  deriving Repr, BEq, Inhabited

/-- The inherited text properties of SVG that this subset reads. -/
structure Props where
  size : Float := 16
  anchor : Anchor := .start
  letterSpacing : Float := 0
  wordSpacing : Float := 0
  /-- `dominant-baseline` (or `alignment-baseline` on the element itself). -/
  baseline : String := "auto"
  deriving Repr, Inhabited

/-- One shaped glyph, in font units: its origin relative to the word, its
advance, the index of its first character in the word, and its outline. The
outline is y-down, with y = 0 at the ascent line (FontProvider.outlineGeometry). -/
structure Glyph where
  x : Float
  y : Float
  advance : Float
  cluster : Nat
  contours : List Contour

structure Word where
  unitsPerEm : Float
  ascent : Float
  descent : Float
  advance : Float
  glyphs : Array Glyph

/-- Text and font size in user units to a shaped word. -/
abbrev Shaper := String → Float → Except String Word

/-- A run of characters with one style: a text node of `text`, `tspan` or `textPath`. -/
structure Piece where
  chars : Array Char
  props : Props
  /-- The caller's index of the run's paint. -/
  style : Nat
  /-- The index of the run's first character among the addressable characters. -/
  start : Nat
  /-- The index of the `textPath` that holds the run. -/
  path : Option Nat := none
  deriving Inhabited

/-- Per-character values, by addressable character index (SVG 2 §11.? "resolved
character positions"). -/
structure Positions where
  x : Array (Option Float)
  y : Array (Option Float)
  dx : Array Float
  dy : Array Float
  rotate : Array Float

def Positions.empty (n : Nat) : Positions :=
  ⟨Array.replicate n none,Array.replicate n none,Array.replicate n 0,Array.replicate n 0,Array.replicate n 0⟩

/-! ### A path as a polyline with arc lengths -/

structure Polyline where
  points : Array Point
  /-- Arc length at each point; `lengths[0] = 0`. -/
  lengths : Array Float
  /-- `jumps[i]`: the step from point `i-1` to point `i` is a move to a new subpath. -/
  jumps : Array Bool

def Polyline.length (p : Polyline) : Float := p.lengths.back?.getD 0

/-- The flattened subpaths in order; a move to the next subpath adds no length. -/
def Polyline.ofContours (contours : List LinearContour) : Polyline := Id.run do
  let mut points : Array Point := #[]
  let mut lengths : Array Float := #[]
  let mut jumps : Array Bool := #[]
  let mut total : Float := 0
  for c in contours do
    let closing := match c.points.head? with
      | some first => if c.closed && c.points.length > 1 then [first] else []
      | none => []
    let mut first := true
    for q in c.points ++ closing do
      match points.back? with
      | none => pure ()
      | some p => if !first then total := total+Float.sqrt ((q.x-p.x)^2+(q.y-p.y)^2)
      points := points.push q
      lengths := lengths.push total
      jumps := jumps.push (first && !points.isEmpty && points.size > 1)
      first := false
  return ⟨points,lengths,jumps⟩

/-- The point at distance `d` along the path and the tangent angle there, in radians.
`none` off the path: before its start or past its end. -/
def Polyline.at (p : Polyline) (d : Float) : Option (Point × Float) := Id.run do
  let n := p.points.size
  if n < 2 || d < 0 || d > p.length then return none
  -- The last i with lengths[i] ≤ d, by bisection: a loop of at most 64 halvings.
  let mut lo := 0
  let mut hi := n-1
  for _ in [0:64] do
    if hi-lo ≤ 1 then break
    let mid := (lo+hi)/2
    if p.lengths[mid]! ≤ d then lo := mid else hi := mid
  -- A move adds no length: the segment that holds d is the next drawn one.
  let mut i := lo
  for _ in [0:n] do
    if i+1 < n && p.jumps[i+1]! then i := i+1 else break
  if i+1 ≥ n then i := n-2
  let a := p.points[i]?.getD ⟨0,0⟩
  let b := p.points[i+1]?.getD ⟨0,0⟩
  let span := p.lengths[i+1]!-p.lengths[i]!
  let f := if span > 0 then max 0 (min 1 ((d-p.lengths[i]!)/span)) else 0
  return some (⟨a.x+(b.x-a.x)*f,a.y+(b.y-a.y)*f⟩,Float.atan2 (b.y-a.y) (b.x-a.x))

/-- Before its start, no point of the path is found, so no glyph is drawn there. -/
theorem Polyline.at_before_start (p : Polyline) (d : Float) (before : d < 0) : p.at d = none := by
  simp [Polyline.at, before]

/-! ### Clusters -/

/-- A cluster: the glyphs of one or more characters that move as one. Offsets and
the advance are in user units; the outlines stay in font units. -/
structure Unit where
  piece : Nat
  /-- Its first addressable character, and how many characters it covers. -/
  char : Nat
  chars : Nat
  advance : Float
  /-- (x offset, y offset, advance, outline) of each glyph. -/
  glyphs : Array (Float × Float × Float × List Contour)
  scale : Float
  ascent : Float
  /-- Down shift of the baseline from `dominant-baseline`, in user units. -/
  shift : Float
  deriving Inhabited

private def baselineShift (props : Props) (w : Word) (scale : Float) : Float :=
  match props.baseline with
  | "middle" | "central" => (w.ascent-w.descent)/2*scale
  | "hanging" | "text-before-edge" | "text-top" | "before-edge" => w.ascent*scale
  | "mathematical" => w.ascent*scale/2
  | "text-after-edge" | "text-bottom" | "ideographic" | "after-edge" => -w.descent*scale
  | _ => 0

/-- The clusters of a shaped word whose first character is addressable character
`first`. Clusters in increasing character order each become a unit; otherwise
(right-to-left text from the nominal fallback) the word is one unit. -/
def wordUnits (piece first : Nat) (props : Props) (text : String) (w : Word) : Array Unit := Id.run do
  let scale := props.size/w.unitsPerEm
  let shift := baselineShift props w scale
  let length := text.length
  let ordered := (w.glyphs.toList.zip (w.glyphs.toList.drop 1)).all fun (a,b) => a.cluster ≤ b.cluster
  let base : Unit := {piece,char := first,chars := length,advance := 0,glyphs := #[],scale,ascent := w.ascent,shift}
  if !ordered then
    let glyphs := w.glyphs.map fun g => (g.x*scale,g.y*scale,g.advance*scale,g.contours)
    return #[{base with advance := w.advance*scale,glyphs}]
  let mut out : Array Unit := #[]
  let mut pen : Float := 0
  let mut current : Option (Nat × Float × Unit) := none
  for g in w.glyphs do
    match current with
    | some (cluster,start,u) =>
      if g.cluster == cluster then
        current := some (cluster,start,{u with advance := u.advance+g.advance*scale,glyphs := u.glyphs.push ((g.x-start)*scale,g.y*scale,g.advance*scale,g.contours)})
      else
        out := out.push {u with chars := g.cluster-cluster}
        current := some (g.cluster,pen,{base with char := first+g.cluster,advance := g.advance*scale,glyphs := #[((g.x-pen)*scale,g.y*scale,g.advance*scale,g.contours)]})
    | none =>
      current := some (g.cluster,pen,{base with char := first+g.cluster,advance := g.advance*scale,glyphs := #[((g.x-pen)*scale,g.y*scale,g.advance*scale,g.contours)]})
    pen := pen+g.advance
  if let some (cluster,_,u) := current then out := out.push {u with chars := length-cluster}
  return out

/-- The clusters of all runs, in logical order. A space is a unit of its own with
the space's advance plus `word-spacing`. -/
def units (shaper : Shaper) (pieces : Array Piece) : Except String (Array Unit) := do
  let mut out : Array Unit := #[]
  for (piece,index) in pieces.zipIdx do
    let space ← shaper " " piece.props.size
    let spaceScale := piece.props.size/space.unitsPerEm
    let mut word : Array Char := #[]
    let mut wordStart := 0
    for i in [0:piece.chars.size+1] do
      let c := piece.chars[i]?
      if c == some ' ' || c.isNone then
        if !word.isEmpty then
          let text := String.ofList word.toList
          let shaped ← shaper text piece.props.size
          out := out ++ wordUnits index (piece.start+wordStart) piece.props text shaped
          word := #[]
        if c == some ' ' then
          out := out.push {piece := index,char := piece.start+i,chars := 1,advance := space.advance*spaceScale+piece.props.wordSpacing,glyphs := #[],scale := spaceScale,ascent := space.ascent,shift := 0}
      else
        if word.isEmpty then wordStart := i
        word := word.push c.get!
  return out

/-! ### Placement -/

/-- A glyph on the page: the outline point (px, py) in font units goes to
`origin + R(angle) (lx + px*scale, ly + (py-ascent)*scale)`. -/
structure Placed where
  piece : Nat := 0
  ox : Float := 0
  oy : Float := 0
  angle : Float := 0
  lx : Float := 0
  ly : Float := 0
  scale : Float := 1
  ascent : Float := 0
  contours : List Contour := []

instance : Inhabited Placed := ⟨{}⟩

def Placed.map (g : Placed) (p : Point) : Point :=
  let u := g.lx+p.x*g.scale
  let v := g.ly+(p.y-g.ascent)*g.scale
  let c := Float.cos g.angle
  let s := Float.sin g.angle
  ⟨g.ox+u*c-v*s,g.oy+u*s+v*c⟩

/-- The outline of a placed glyph in user units. Font outlines have no arcs; an
arc keeps its flags and turns and scales with the glyph. -/
def Placed.outline (g : Placed) : List Contour :=
  g.contours.map fun
    | .empty closed => .empty closed
    | .path start segments closed => .path (g.map start) (segments.map fun
        | .line p => .line (g.map p)
        | .quadratic a p => .quadratic (g.map a) (g.map p)
        | .cubic a b p => .cubic (g.map a) (g.map b) (g.map p)
        | .arc rx ry rotation large sweep p =>
          .arc (rx*g.scale) (ry*g.scale) (rotation+g.angle*180/3.141592653589793) large sweep (g.map p)) closed

def anchorShift (anchor : Anchor) (width : Float) : Float :=
  match anchor with
  | .start => 0
  | .middle => -width/2
  | .finish => -width

/-- One `textPath`: its polyline, its `startOffset` in user units, and `side=right`
(the path read backwards). -/
structure PathInfo where
  line : Polyline
  startOffset : Float

private structure Chunk where
  start : Float
  finish : Float
  anchor : Anchor
  first : Nat

/-- Place every glyph. The current text position starts at (0, 0); an absolute
`x` or `y` starts a new text chunk, and each chunk is moved by its `text-anchor`
(SVG 1.1 §10.9.1). A `textPath` run is one chunk, anchored along the path. -/
def place (pieces : Array Piece) (positions : Positions) (paths : Array PathInfo)
    (units : Array Unit) : Array Placed := Id.run do
  let mut out : Array Placed := #[]
  let mut cx : Float := 0
  let mut cy : Float := 0
  let mut chunks : Array Chunk := #[]
  let mut chunk : Option Chunk := none
  -- On a path: its index, the distance along it and the offset across it.
  let mut along : Option (Nat × Float × Float) := none
  for i in [0:units.size] do
    let u := units[i]!
    let piece := pieces[u.piece]!
    let props := piece.props
    let k := u.char
    let dx := positions.dx[k]?.getD 0
    let dy := positions.dy[k]?.getD 0
    let rotate := (positions.rotate[k]?.getD 0)*3.141592653589793/180
    match piece.path with
    | some p =>
      let line := (paths[p]?.map (·.line)).getD ⟨#[],#[],#[]⟩
      let (entering,d0,across0) := match along with
        | some (q,d,across) => if q == p then (false,d,across) else (true,0,0)
        | none => (true,0,0)
      let mut d := d0
      let mut across := across0
      -- A new path: the whole advance of its run gives the anchor shift.
      if entering then
        if let some c := chunk then chunks := chunks.push {c with finish := cx}
        chunk := none
        let mut total : Float := 0
        for j in [i:units.size] do
          let v := units[j]!
          if pieces[v.piece]!.path != some p then break
          total := total+v.advance+pieces[v.piece]!.props.letterSpacing+(positions.dx[v.char]?.getD 0)
        d := ((paths[p]?.map (·.startOffset)).getD 0)+anchorShift props.anchor total
        across := 0
      d := d+dx
      across := across+dy
      for (gx,gy,advance,contours) in u.glyphs do
        if let some (point,angle) := line.at (d+gx+advance/2) then
          out := out.push {piece := u.piece,ox := point.x,oy := point.y,angle := angle+rotate,lx := -advance/2,ly := gy+across+u.shift,scale := u.scale,ascent := u.ascent,contours}
      d := d+u.advance+props.letterSpacing
      along := some (p,d,across)
      -- Leaving the path: the text goes on from where the path text ended.
      let leaving := match units[i+1]? with
        | some v => pieces[v.piece]!.path != some p
        | none => true
      if leaving then
        let ends := if line.points.isEmpty then none else line.at (max 0 (min line.length d))
        if let some (point,_) := ends then cx := point.x; cy := point.y
        along := none
    | none =>
      let newChunk := (positions.x[k]?.join).isSome || (positions.y[k]?.join).isSome
      if let some x := positions.x[k]?.join then cx := x
      if let some y := positions.y[k]?.join then cy := y
      if newChunk || chunk.isNone then
        if let some c := chunk then chunks := chunks.push {c with finish := cx}
        chunk := some {start := cx,finish := cx,anchor := props.anchor,first := out.size}
      if newChunk then
        if let some c := chunk then chunk := some {c with start := cx}
      cx := cx+dx
      cy := cy+dy
      for (gx,gy,_,contours) in u.glyphs do
        out := out.push {piece := u.piece,ox := cx+gx,oy := cy,angle := rotate,lx := 0,ly := gy+u.shift,scale := u.scale,ascent := u.ascent,contours}
      cx := cx+u.advance+props.letterSpacing
      if let some c := chunk then chunk := some {c with finish := cx}
  if let some c := chunk then chunks := chunks.push c
  -- Each chunk moves along x by its anchor: the glyphs from its first to the next chunk's first.
  for (c,j) in chunks.zipIdx do
    let shift := anchorShift c.anchor (c.finish-c.start)
    if shift != 0 then
      let last := (chunks[j+1]?.map (·.first)).getD out.size
      for g in [c.first:last] do
        out := out.modify g fun p => {p with ox := p.ox+shift}
  return out

/-! ### Checks, with a monospace test font: each character advances 500 of 1000
units and is a 400 × 700 box standing on the baseline. -/

private def box : List Contour :=
  [.path ⟨0,100⟩ [.line ⟨400,100⟩,.line ⟨400,800⟩,.line ⟨0,800⟩] true]
private def mono : Shaper := fun text _ =>
  let glyphs := (List.range text.length).toArray.map fun i =>
    ({x := Float.ofNat (500*i),y := 0,advance := 500,cluster := i,contours := if text.toList[i]! == ' ' then [] else box} : Glyph)
  .ok {unitsPerEm := 1000,ascent := 800,descent := 200,advance := Float.ofNat (500*text.length),glyphs}

private def layout (pieces : Array Piece) (positions : Positions) (paths : Array PathInfo := #[]) : Array Placed :=
  match units mono pieces with
  | .ok us => place pieces positions paths us
  | .error _ => #[]
private def origins (gs : Array Placed) : List (Float × Float) := gs.toList.map fun g => (g.ox,g.oy)
private def near (a b : Float) : Bool := (a-b).abs < 1e-6
private def nearAll (a b : List (Float × Float)) : Bool :=
  a.length == b.length && (a.zip b).all fun (p,q) => near p.1 q.1 && near p.2 q.2

private def plain (text : String) (anchor : Anchor := .start) : Array Piece :=
  #[{chars := text.toList.toArray,props := {size := 20,anchor},style := 0,start := 0}]
private def at10 (n : Nat) : Positions := {Positions.empty n with x := (Positions.empty n).x.set! 0 (some 10),y := (Positions.empty n).y.set! 0 (some 50)}

-- Start: glyphs from x = 10, 10 user units apart (20 × 500/1000); the space draws nothing.
#guard nearAll (origins (layout (plain "ab c") (at10 4))) [(10,50),(20,50),(40,50)]
-- Middle and end: the chunk of width 40 moves left by 20 and by 40.
#guard nearAll (origins (layout (plain "ab c" .middle) (at10 4))) [(-10,50),(0,50),(20,50)]
#guard nearAll (origins (layout (plain "ab c" .finish) (at10 4))) [(-30,50),(-20,50),(0,50)]
-- An absolute x on the third character starts a second chunk there.
#guard nearAll (origins (layout (plain "abc") {at10 3 with x := (at10 3).x.set! 2 (some 100)})) [(10,50),(20,50),(100,50)]
-- dx and dy move the current position and stay moved.
#guard nearAll (origins (layout (plain "abc") {at10 3 with dx := #[0,5,0],dy := #[0,-8,0]})) [(10,50),(25,42),(35,42)]
-- Letter spacing adds after each character.
#guard nearAll (origins (layout #[{chars := #['a','b'],props := {size := 20,letterSpacing := 3},style := 0,start := 0}] (at10 2))) [(10,50),(23,50)]
-- A glyph's outline: the box corner (0, 100) of font units is 14 units above the baseline at size 20.
#guard (layout (plain "a") (at10 1))[0]!.map ⟨0,100⟩ |> fun p => near p.x 10 && near p.y 36
-- Rotate turns a glyph about its origin: 90° puts the box's far corner below-left.
#guard (layout (plain "a") {at10 1 with rotate := #[90]})[0]!.map ⟨400,100⟩ |> fun p => near p.x 24 && near p.y 58

/-- A straight path from (0, 50) to (100, 50) as a polyline. -/
private def straight : Polyline := Polyline.ofContours [⟨[⟨0,50⟩,⟨100,50⟩],false⟩]
#guard straight.length == 100
#guard (straight.at 25).map (fun (p,a) => (p.x,p.y,a)) == some (25,50,0)
#guard (straight.at 101).isNone
-- On a path: each glyph's midpoint at its distance; the origin is half an advance back.
#guard
  let gs := layout #[{chars := #['a','b'],props := {size := 20},style := 0,start := 0,path := some 0}]
    (Positions.empty 2) #[⟨straight,30⟩]
  nearAll (gs.toList.map (fun g => (g.ox+g.lx,g.oy))) [(30,50),(40,50)]
-- Anchor middle at 50%: the two glyphs (width 20) centre on distance 50.
#guard
  let gs := layout #[{chars := #['a','b'],props := {size := 20,anchor := .middle},style := 0,start := 0,path := some 0}]
    (Positions.empty 2) #[⟨straight,50⟩]
  nearAll (gs.toList.map (fun g => (g.ox+g.lx,0))) [(40,0),(50,0)]
-- A glyph whose midpoint is past the end is not drawn.
#guard
  (layout #[{chars := #['a','b','c'],props := {size := 20},style := 0,start := 0,path := some 0}]
    (Positions.empty 3) #[⟨straight,90⟩]).size == 1
-- On a vertical path the glyph turns 90°: its baseline points down the page.
#guard
  let down := Polyline.ofContours [⟨[⟨10,0⟩,⟨10,100⟩],false⟩]
  let gs := layout #[{chars := #['a'],props := {size := 20},style := 0,start := 0,path := some 0}] (Positions.empty 1) #[⟨down,0⟩]
  gs.size == 1 && near gs[0]!.angle (3.141592653589793/2) && near (gs[0]!.map ⟨0,800⟩).x 10 && near (gs[0]!.map ⟨0,800⟩).y 0
-- A closed square path: its length includes the closing side.
#guard (Polyline.ofContours [⟨[⟨0,0⟩,⟨10,0⟩,⟨10,10⟩,⟨0,10⟩],true⟩]).length == 40
-- Two subpaths: the move between them adds no length.
#guard (Polyline.ofContours [⟨[⟨0,0⟩,⟨10,0⟩],false⟩,⟨[⟨50,0⟩,⟨60,0⟩],false⟩]).length == 20
#guard ((Polyline.ofContours [⟨[⟨0,0⟩,⟨10,0⟩],false⟩,⟨[⟨50,0⟩,⟨60,0⟩],false⟩]).at 15).map (·.1.x) == some 55

end NativeSVGText
