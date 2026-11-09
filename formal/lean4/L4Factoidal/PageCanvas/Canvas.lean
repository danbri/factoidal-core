/-
L4Factoidal.PageCanvas.Canvas: the canvases of a page and the commands that draw on them
(HTML §4.12.5.1, CanvasRenderingContext2D; record docs/designissues/2026-11-08-canvas-2d.md).

A page's script records its Canvas 2D calls; at the end of a task (or before a call that
needs an answer) it sends them in one batch, which `Wire.decode` turns into a list of
`Cmd`: the display list of that batch. `Store.run` applies it: each drawing command is
rasterised by Lean into the canvas bitmap (premultiplied RGBA, `Raster.composite`), so
the bitmap is always current: `getImageData` reads it and draws nothing again.

Theorems (`Theorems.lean`): every command keeps a canvas's bitmap at `width × height × 4`
bytes; every draw visits only pixels inside the canvas (`Raster.boxOf_within`), and a
pixel outside the clip region keeps its value (`Raster.blendPixel_outside_clip`); the
host gets pixels of exactly the canvas's size; `save`/`restore` is a stack
(`State.Stack.restore_setters_save`).
-/
import L4Factoidal.PageCanvas.Text
import L4Factoidal.PageCanvas.Png
import L4Factoidal.JS.Number

namespace L4Factoidal.PageCanvas
open L4Factoidal.Rendering

/-- What the engine gives the canvases of a page: the fonts it holds, the SVG path
parser (for `new Path2D(d)`), and the decoded images of the page by URL key. -/
structure Env where
  fonts : Array SfntProfile.Font := #[]
  svgPath : String → Option (List Rendering.Contour) := fun _ => none
  image : String → Option Bitmap := fun _ => none

instance : Inhabited Env := ⟨{}⟩

/-- Largest canvas side and area; a larger canvas has no bitmap and draws nothing (as a
browser that cannot allocate it). -/
def maxSide : Nat := 8192
def maxArea : Nat := 16777216
/-- Most bytes of bitmaps (canvases, patterns, image bitmaps) a page holds. -/
def maxBytes : Nat := 268435456
/-- Most gradients, paths and patterns a page holds; past it the oldest go. -/
def maxObjects : Nat := 65536

structure Canvas where
  width : Nat
  height : Nat
  bitmap : ByteArray
  stack : Stack := {}
  path : Path := {}
  /-- Drawn since the host last had its pixels. -/
  dirty : Bool := true
  /-- A `canvas` element of the page (its pixels are composited), not an OffscreenCanvas. -/
  element : Bool := true
  deriving Inhabited

def Canvas.make (w h : Nat) (element : Bool) : Canvas :=
  let (w', h') := if w ≤ maxSide && h ≤ maxSide && w * h ≤ maxArea then (w, h) else (0, 0)
  { width := w', height := h', bitmap := ByteArray.mk (Array.replicate (w' * h' * 4) 0), element }

theorem Canvas.make_size (w h : Nat) (e : Bool) :
    (Canvas.make w h e).bitmap.size = (Canvas.make w h e).width * (Canvas.make w h e).height * 4 := by
  unfold Canvas.make
  split <;> exact Array.size_replicate

/-- The canvases and objects of a page. -/
structure Store where
  canvases : Std.HashMap Nat Canvas := {}
  paths : Std.HashMap Nat Path := {}
  gradients : Std.HashMap Nat Gradient := {}
  patterns : Std.HashMap Nat Pattern := {}
  bitmaps : Std.HashMap Nat Bitmap := {}
  /-- Shaped text, by font and text (a frame draws the same labels again). -/
  shaped : Std.HashMap String Text.Shaped := {}
  /-- The canvas sizes the host has textures for. -/
  textures : Std.HashMap Nat (Nat × Nat) := {}
  /-- Images of the page decoded for drawing, by URL key (decoded once). -/
  images : Std.HashMap String Bitmap := {}
  deriving Inhabited

/-- One command of a batch: the display list of a canvas. -/
inductive Cmd where
  | select (id : Nat)
  | init (id w h : Nat) (element : Bool)
  | save | restore | reset
  | setTransform (m : Matrix) | transform (m : Matrix) | resetTransform
  | translate (x y : Float) | scale (x y : Float) | rotate (t : Float)
  | alpha (v : Float) | composite (name : String)
  | fillColor (s : String) | strokeColor (s : String)
  | fillObj (kind id : Nat) | strokeObj (kind id : Nat)
  | lineWidth (v : Float) | lineCap (s : String) | lineJoin (s : String) | miterLimit (v : Float)
  | lineDash (v : Array Float) | dashOffset (v : Float)
  | shadowColor (s : String) | shadowBlur (v : Float) | shadowX (v : Float) | shadowY (v : Float)
  | font (s : String) | textAlign (s : String) | textBaseline (s : String) | direction (s : String)
  | smoothing (b : Bool) | smoothingQuality (s : String) | filter (s : String)
  | letterSpacing (s : String) | wordSpacing (s : String) | fontKerning (s : String)
  | fontStretch (s : String) | fontVariantCaps (s : String) | textRendering (s : String) | lang (s : String)
  /-- Path commands go to the context's path (0) or a `Path2D` (its id). -/
  | pathTarget (id : Nat)
  | beginPath | moveTo (x y : Float) | lineTo (x y : Float) | quadTo (cx cy x y : Float)
  | bezierTo (ax ay bx by_ x y : Float) | arc (x y r a0 a1 : Float) (ccw : Bool)
  | arcTo (x1 y1 x2 y2 r : Float) | ellipse (x y rx ry rot a0 a1 : Float) (ccw : Bool)
  | rect (x y w h : Float) | roundRect (x y w h : Float) (radii : Array (Float × Float)) | closePath
  | pathNew (id : Nat) (from_ : Nat) | pathSvg (id : Nat) (d : String) | addPath (id src : Nat) (m : Matrix)
  | fill (path : Nat) (rule : FillRule) | stroke (path : Nat) | clip (path : Nat) (rule : FillRule)
  | fillRect (x y w h : Float) | strokeRect (x y w h : Float) | clearRect (x y w h : Float)
  | fillText (s : String) (x y maxW : Float) | strokeText (s : String) (x y maxW : Float)
  | drawImage (kind : Nat) (src : Nat) (key : String) (sx sy sw sh dx dy dw dh : Float)
  | putImageData (data : ByteArray) (w h : Nat) (dx dy : Int) (rx ry rw rh : Int)
  | gradientNew (id : Nat) (kind : GradientKind)
  | patternTransform (id : Nat) (m : Matrix)
  | bitmapNew (id : Nat) (kind src : Nat) (key : String) (data : ByteArray) (sx sy sw sh : Float)
  | release (kind id : Nat)
  deriving Inhabited

/-! ### The current canvas while a batch runs

The canvas being drawn is held outside the map (`Run.cur`), so its bitmap has one owner
and each pixel write changes it in place. -/

structure Run where
  store : Store
  env : Env
  cur : Option (Nat × Canvas) := none
  /-- Where path commands go: 0 the context's path, else a `Path2D`. -/
  target : Nat := 0
  errors : Array String := #[]

def Run.put (r : Run) : Run :=
  match r.cur with
  | some (id, c) => { r with cur := none, store := { r.store with canvases := r.store.canvases.insert id c } }
  | none => r

def Run.take (r : Run) (id : Nat) : Run :=
  let r := r.put
  match r.store.canvases.get? id with
  | some c => { r with cur := some (id, c), store := { r.store with canvases := r.store.canvases.erase id } }
  | none => r

def Run.gradient (r : Run) (id : Nat) : Option Gradient := r.store.gradients.get? id
def Run.pattern (r : Run) (id : Nat) : Option Pattern := r.store.patterns.get? id

/-- `b` when it has `n` bytes, else `n` zero bytes. -/
def fitTo (n : Nat) (b : ByteArray) : ByteArray := if b.size == n then b else ByteArray.mk (Array.replicate n 0)

theorem zeros_size (n : Nat) : (ByteArray.mk (Array.replicate n 0)).size = n := by
  show (Array.replicate n (0 : UInt8)).size = n
  exact Array.size_replicate

theorem fitTo_size (n : Nat) (b : ByteArray) : (fitTo n b).size = n := by
  unfold fitTo
  split
  · next h => exact beq_iff_eq.mp h
  · exact zeros_size n

def zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

/-- Run `f` on the bitmap with the canvas holding no reference to it (so `f` changes it in
place), and keep the result only at the same size. -/
@[inline] def Canvas.onBitmap (c : Canvas) (f : ByteArray → ByteArray) : Canvas :=
  let n := c.bitmap.size
  let bm := c.bitmap
  let c := { c with bitmap := ByteArray.empty }
  { c with bitmap := fitTo n (f bm), dirty := true }

theorem Canvas.onBitmap_size (c : Canvas) (f : ByteArray → ByteArray) :
    (c.onBitmap f).bitmap.size = c.bitmap.size := fitTo_size _ _

/-- A canvas whose bitmap does not have `width × height × 4` bytes gets a blank one (a
final check; no command makes one). -/
def Canvas.fix (c : Canvas) : Canvas :=
  if c.bitmap.size == c.width * c.height * 4 then c else { c with bitmap := zeros (c.width * c.height * 4) }

theorem Canvas.fix_size (c : Canvas) : c.fix.bitmap.size = c.fix.width * c.fix.height * 4 := by
  unfold Canvas.fix
  split
  · next h => exact beq_iff_eq.mp h
  · exact zeros_size _

/-! ### Drawing -/

/-- Shadows (HTML §4.12.5.1.16): drawn when the colour is not transparent and there is a
blur or an offset. The shape's alpha, moved by the offset (not transformed) and blurred
(three box blurs, for a Gaussian of σ = blur / 2), in the shadow colour. -/
def shadowOn (st : DrawState) : Bool :=
  st.shadowColor.a > 0 && (st.shadowBlur > 0 || st.shadowX != 0 || st.shadowY != 0)

/-- A box blur of radius `r` along rows (`horizontal`) or columns of a `w × h` alpha map. -/
def boxBlur (w h r : Nat) (src : FloatArray) (horizontal : Bool) : FloatArray := Id.run do
  if r == 0 then return src
  let mut out := FloatArray.mk (Array.replicate (w * h) 0)
  let (lines, len) := if horizontal then (h, w) else (w, h)
  let k := 1 / nf (2 * r + 1)
  for l in [0:lines] do
    let at_ := fun (i : Nat) => if horizontal then l * w + i else i * w + l
    let mut sum := 0.0
    for i in [0:min r len] do sum := sum + src[at_ i]!
    for i in [0:len] do
      if i + r < len then sum := sum + src[at_ (i + r)]!
      out := out.set! (at_ i) (sum * k)
      if i ≥ r then sum := sum - src[at_ (i - r)]!
  return out

/-- Edges moved by `(dx, dy)`. -/
def shiftEdges (es : Array Edge) (dx dy : Float) : Array Edge :=
  es.map fun e => { e with x0 := e.x0 + dx, y0 := e.y0 + dy, x1 := e.x1 + dx, y1 := e.y1 + dy }

/-- The shadow of a draw as a draw (HTML §4.12.5.1.16): the shape moved by the offset
(device pixels, not transformed), its alpha times the paint's alpha at the shape's own
place, blurred, in the shadow colour, over the whole canvas. The shape's edges are moved,
so a shape outside the canvas casts a shadow inside it. -/
def shadowDraw (W H : Nat) (st : DrawState) (d : Draw) (es : Array Edge) (rule : FillRule) : Draw := Id.run do
  let ox := st.shadowX
  let oy := st.shadowY
  let cov := coverage W H (shiftEdges es ox oy) rule
  let box := cov.box
  let mut a := FloatArray.mk (Array.replicate (W * H) 0)
  for j in [0:box.h] do
    for i in [0:box.w] do
      let c := cov.cov[j * box.w + i]!
      if c <= 0 then continue
      let s := d.ready.atF (nf (box.x + i) + 0.5 - ox) (nf (box.y + j) + 0.5 - oy)
      a := a.set! ((box.y + j) * W + box.x + i) (c * s.a)
  let sigma := st.shadowBlur / 2
  let r := if sigma <= 0 then 0 else (sigma * 0.94).round.toUInt64.toNat   -- three boxes of 2r+1 ≈ σ√12/√3
  let r := min r 128
  let mut b := a
  for _ in [0:3] do
    b := boxBlur W H r (boxBlur W H r b true) false
  return { d with ready := .solid st.shadowColor.px, cov := ⟨⟨0, 0, W, H⟩, b⟩ }

/-- Composite a draw (with its shadow first) into the canvas. `shape` gives the draw's
edges and rule, asked for only when there is a shadow. -/
def Canvas.paint (c : Canvas) (st : DrawState) (d : Draw) (shape : Unit → Array Edge × FillRule) : Canvas :=
  let W := c.width
  let H := c.height
  c.onBitmap fun bm =>
    let bm := if shadowOn st then
        let (es, rule) := shape ()
        composite W H bm (shadowDraw W H st d es rule)
      else bm
    composite W H bm d

/-- Draw the coverage of polygons (device space) with a style. -/
def Run.drawPolys (r : Run) (c : Canvas) (polys : Array Poly) (rule : FillRule) (style : Style) : Canvas :=
  let st := c.stack.cur
  let es := edgesOf polys
  let cov := coverage c.width c.height es rule
  let ready := style.ready r.gradient r.pattern st.ctm st.smoothing
  c.paint st ⟨ready, cov, Color.clamp01 st.alpha, st.op, st.clip⟩ fun _ => (es, rule)

/-- Fill a path in device space. -/
def Run.fillDevice (r : Run) (c : Canvas) (p : Path) (rule : FillRule) : Canvas :=
  r.drawPolys c (p.flatten 0.1) rule c.stack.cur.fill

/-- Stroke a path given in user space (HTML: the line width and dashes are in the
coordinate space of the current transform). -/
def Run.strokeUser (r : Run) (c : Canvas) (p : Path) (style : Style) : Canvas :=
  let st := c.stack.cur
  let k := max 1e-9 st.ctm.stretch
  let tol := 0.1 / k
  -- A segment's end is square to its chord: finer curves for wide lines keep caps true.
  let hw := st.line.width * k / 2
  let polys := mapPolys st.ctm (strokePolys st.line (p.flatten (tol / max 1 (hw * hw))) tol)
  r.drawPolys c polys .nonzero style

/-- The path a fill, stroke or clip names, in device space: the context's path, or a
`Path2D` through the current transform. -/
def Run.devicePath (r : Run) (c : Canvas) (id : Nat) : Path :=
  if id == 0 then c.path else ((r.store.paths.get? id).getD {}).map c.stack.cur.ctm

/-- The same path in user space (for strokes). `none` when the transform is singular. -/
def Run.userPath (r : Run) (c : Canvas) (id : Nat) : Option Path :=
  if id == 0 then c.stack.cur.ctm.inverse?.map fun inv => c.path.map inv
  else if c.stack.cur.ctm.inverse?.isNone then none else some ((r.store.paths.get? id).getD {})

def rectPath (x y w h : Float) : Path :=
  (((({} : Path).moveTo x y).lineTo (x + w) y).lineTo (x + w) (y + h)).lineTo x (y + h) |>.close

def finite (xs : List Float) : Bool := xs.all Float.isFinite

/-- `fillRect` and `clearRect`: an axis-aligned transform gives exact coverage. -/
def Run.rectDraw (r : Run) (c : Canvas) (x y w h : Float) (style : Style) (clear : Bool) : Canvas :=
  let st := c.stack.cur
  if !finite [x, y, w, h] || w == 0 || h == 0 then c else
  let m := st.ctm
  let cov := if m.b == 0 && m.c == 0 then
      let (x0, y0) := m.apply x y
      let (x1, y1) := m.apply (x + w) (y + h)
      rectCoverage c.width c.height (min x0 x1) (min y0 y1) (max x0 x1) (max y0 y1)
    else coverage c.width c.height (edgesOf ((rectPath x y w h).map m |>.flatten)) .nonzero
  if clear then
    -- HTML: clearRect clears to transparent black, ignoring alpha, operator and shadow.
    let full := cov.box == ⟨0, 0, c.width, c.height⟩ && st.clip.isNone && m.b == 0 && m.c == 0 &&
      cov.cov.data.all (· >= 1)
    if full then c.onBitmap fun bm => zeros bm.size
    else c.onBitmap fun bm => composite c.width c.height bm ⟨.solid ⟨1, 1, 1, 1⟩, cov, 1, .destinationOut, st.clip⟩
  else
    c.paint st ⟨style.ready r.gradient r.pattern m st.smoothing, cov, Color.clamp01 st.alpha, st.op, st.clip⟩
      fun _ => (edgesOf ((rectPath x y w h).map m |>.flatten), .nonzero)

/-! ### Paths -/

/-- Apply a path command to a path whose points are mapped by `m` as they are added
(the context's path is in device space, HTML: "transformed by the current transform
when added"). -/
def pathCmd (m : Matrix) (p : Path) : Cmd → Path
  | .moveTo x y => if finite [x, y] then let (x, y) := m.apply x y; p.moveTo x y else p
  | .lineTo x y => if finite [x, y] then let (x, y) := m.apply x y; p.lineTo x y else p
  | .quadTo cx cy x y =>
    if !finite [cx, cy, x, y] then p else
    let (cx, cy) := m.apply cx cy; let (x, y) := m.apply x y; p.quadTo cx cy x y
  | .bezierTo ax ay bx by_ x y =>
    if !finite [ax, ay, bx, by_, x, y] then p else
    let (ax, ay) := m.apply ax ay; let (bx, by_) := m.apply bx by_; let (x, y) := m.apply x y
    p.cubicTo ax ay bx by_ x y
  | .closePath => p.close
  | .rect x y w h =>
    if !finite [x, y, w, h] then p else
    let pt := fun (a b : Float) => m.apply a b
    let (x0, y0) := pt x y
    let (x1, y1) := pt (x + w) y
    let (x2, y2) := pt (x + w) (y + h)
    let (x3, y3) := pt x (y + h)
    ((((p.moveTo x0 y0).lineTo x1 y1).lineTo x2 y2).lineTo x3 y3).close
  | .arc x y r a0 a1 ccw => ellipseInto m p x y r r 0 a0 a1 ccw
  | .ellipse x y rx ry rot a0 a1 ccw => ellipseInto m p x y rx ry rot a0 a1 ccw
  | .arcTo x1 y1 x2 y2 r => arcToInto m p x1 y1 x2 y2 r
  | .roundRect x y w h radii => roundRectInto m p x y w h radii
  | _ => p
where
  /-- HTML §4.12.5.1.9 `ellipse()`: a line to the arc's start (or a move when the path
  is empty), then the arc. -/
  ellipseInto (m : Matrix) (p : Path) (x y rx ry rot a0 a1 : Float) (ccw : Bool) : Path :=
    if !finite [x, y, rx, ry, rot, a0, a1] || rx < 0 || ry < 0 then p else
    let frame := m.mul ((Matrix.translate x y).mul ((Matrix.rotate rot).mul (Matrix.scale rx ry)))
    let (sx, sy) := frame.apply (Float.cos a0) (Float.sin a0)
    let p := if p.subpath then p.lineTo sx sy else p.moveTo sx sy
    let sweep := ellipseSweep a0 a1 ccw
    if sweep == 0 then p else
    (arcSegs frame a0 sweep).foldl (fun q s => match s with
      | .cubic ax ay bx by_ x y => q.cubicTo ax ay bx by_ x y
      | _ => q) p
  /-- HTML `arcTo()`, with the last point taken back to user space. -/
  arcToInto (m : Matrix) (p : Path) (x1 y1 x2 y2 r : Float) : Path :=
    if !finite [x1, y1, x2, y2, r] || r < 0 then p else
    let (dx1, dy1) := m.apply x1 y1
    if !p.subpath then p.moveTo dx1 dy1 else
    match m.inverse? with
    | none => p.lineTo dx1 dy1
    | some inv =>
      let (x0, y0) := inv.apply p.lastX p.lastY
      let collinear := ((x1 - x0) * (y2 - y1) - (y1 - y0) * (x2 - x1)).abs < 1e-12
      if (x0 == x1 && y0 == y1) || (x1 == x2 && y1 == y2) || r == 0 || collinear then p.lineTo dx1 dy1 else
      -- The circle of radius r tangent to both lines.
      let v1x := x0 - x1
      let v1y := y0 - y1
      let v2x := x2 - x1
      let v2y := y2 - y1
      let l1 := Float.sqrt (v1x * v1x + v1y * v1y)
      let l2 := Float.sqrt (v2x * v2x + v2y * v2y)
      let (u1x, u1y, u2x, u2y) := (v1x / l1, v1y / l1, v2x / l2, v2y / l2)
      let cosT := u1x * u2x + u1y * u2y
      let theta := Float.acos (max (-1) (min 1 cosT))
      let t := r / Float.tan (theta / 2)
      let (t1x, t1y) := (x1 + u1x * t, y1 + u1y * t)
      let (t2x, t2y) := (x1 + u2x * t, y1 + u2y * t)
      let bx := u1x + u2x
      let by_ := u1y + u2y
      let bl := Float.sqrt (bx * bx + by_ * by_)
      let d := r / Float.sin (theta / 2)
      let (cx, cy) := (x1 + bx / bl * d, y1 + by_ / bl * d)
      let a0 := Float.atan2 (t1y - cy) (t1x - cx)
      let a1 := Float.atan2 (t2y - cy) (t2x - cx)
      let (tx, ty) := m.apply t1x t1y
      let p := p.lineTo tx ty
      -- The arc between the two tangent points on the corner's side is less than half a turn.
      let sweep := let s := a1 - a0
        if s > pi then s - tau else if s < -pi then s + tau else s
      let frame := m.mul ((Matrix.translate cx cy).mul (Matrix.scale r r))
      (arcSegs frame a0 sweep).foldl (fun q s => match s with
        | .cubic ax ay bx by_ x y => q.cubicTo ax ay bx by_ x y
        | _ => q) p
  /-- HTML `roundRect()`: the radii already normalised to four corners (top-left,
  top-right, bottom-right, bottom-left), scaled down when they overlap. -/
  roundRectInto (m : Matrix) (p : Path) (x y w h : Float) (radii : Array (Float × Float)) : Path :=
    if !finite [x, y, w, h] || radii.size != 4 then p else
    -- A negative width or height draws the rectangle mirrored, so its direction turns
    -- (HTML: "flip"): the frame below mirrors it, and the corners swap with it.
    let m := m.mul ((Matrix.translate x y).mul (Matrix.scale (if w < 0 then -1 else 1) (if h < 0 then -1 else 1)))
    let (x, y, w, h) := (0.0, 0.0, w.abs, h.abs)
    let r := radii
    let (tl, tr, br, bl) := (r[0]!, r[1]!, r[2]!, r[3]!)
    let top := tl.1 + tr.1
    let right := tr.2 + br.2
    let bottom := br.1 + bl.1
    let left := tl.2 + bl.2
    let f := [if top > 0 then w / top else 1, if bottom > 0 then w / bottom else 1,
      if left > 0 then h / left else 1, if right > 0 then h / right else 1].foldl min 1
    let sc := fun (q : Float × Float) => (q.1 * f, q.2 * f)
    let (tl, tr, br, bl) := (sc tl, sc tr, sc br, sc bl)
    let corner := fun (q : Path) (cx cy rx ry a0 : Float) =>
      -- A corner of radius 0 is the corner point itself.
      if rx <= 0 || ry <= 0 then let (px, py) := m.apply cx cy; q.lineTo px py
      else
        let frame := m.mul ((Matrix.translate cx cy).mul (Matrix.scale rx ry))
        let (sx, sy) := frame.apply (Float.cos a0) (Float.sin a0)
        let q := q.lineTo sx sy
        (arcSegs frame a0 (pi / 2)).foldl (fun q s => match s with
          | .cubic ax ay bx by_ px py => q.cubicTo ax ay bx by_ px py
          | _ => q) q
    let (sx, sy) := m.apply (x + tl.1) y
    let q := p.moveTo sx sy
    let q := corner q (x + w - tr.1) (y + tr.2) tr.1 tr.2 (-pi / 2)
    let q := corner q (x + w - br.1) (y + h - br.2) br.1 br.2 0
    let q := corner q (x + bl.1) (y + h - bl.2) bl.1 bl.2 (pi / 2)
    let q := corner q (x + tl.1) (y + tl.2) tl.1 tl.2 pi
    let q := q.close
    let (mx, my) := m.apply x y
    q.moveTo mx my

/-! ### State -/

def capOf? : String → Option Cap
  | "butt" => some .butt | "round" => some .round | "square" => some .square | _ => none
def joinOf? : String → Option Join
  | "miter" => some .miter | "round" => some .round | "bevel" => some .bevel | _ => none
def alignOf? : String → Option Align
  | "start" => some .start | "end" => some .end_ | "left" => some .left | "right" => some .right
  | "center" => some .center | _ => none
def baselineOf? : String → Option Baseline
  | "top" => some .top | "hanging" => some .hanging | "middle" => some .middle
  | "alphabetic" => some .alphabetic | "ideographic" => some .ideographic | "bottom" => some .bottom | _ => none
def directionOf? : String → Option Direction
  | "ltr" => some .ltr | "rtl" => some .rtl | "inherit" => some .inherit | _ => none

/-- A setter of the drawing state, or `none` when the command is not one. Invalid values
leave the state as it is (HTML: "on setting, … ignore"). -/
def setterOf (r : Run) : Cmd → Option (DrawState → DrawState)
  | .setTransform m => some fun s => if m.finite then { s with ctm := m } else s
  | .transform m => some fun s => if m.finite then { s with ctm := s.ctm.mul m } else s
  | .resetTransform => some fun s => { s with ctm := {} }
  | .translate x y => some fun s => if finite [x, y] then { s with ctm := s.ctm.mul (Matrix.translate x y) } else s
  | .scale x y => some fun s => if finite [x, y] then { s with ctm := s.ctm.mul (Matrix.scale x y) } else s
  | .rotate t => some fun s => if t.isFinite then { s with ctm := s.ctm.mul (Matrix.rotate t) } else s
  | .alpha v => some fun s => if v.isFinite && v >= 0 && v <= 1 then { s with alpha := v } else s
  | .composite n => some fun s => match Op.ofName? n with | some o => { s with op := o } | none => s
  | .fillColor t => some fun s => match Color.parse? t with | some c => { s with fill := .color c } | none => s
  | .strokeColor t => some fun s => match Color.parse? t with | some c => { s with stroke := .color c } | none => s
  | .fillObj k id => some fun s => if k == 1 && r.store.gradients.contains id then { s with fill := .gradient id }
      else if k == 2 && r.store.patterns.contains id then { s with fill := .pattern id } else s
  | .strokeObj k id => some fun s => if k == 1 && r.store.gradients.contains id then { s with stroke := .gradient id }
      else if k == 2 && r.store.patterns.contains id then { s with stroke := .pattern id } else s
  | .lineWidth v => some fun s => if v.isFinite && v > 0 then { s with line := { s.line with width := v } } else s
  | .lineCap t => some fun s => match capOf? t with | some c => { s with line := { s.line with cap := c } } | none => s
  | .lineJoin t => some fun s => match joinOf? t with | some j => { s with line := { s.line with join := j } } | none => s
  | .miterLimit v => some fun s => if v.isFinite && v > 0 then { s with line := { s.line with miterLimit := v } } else s
  | .lineDash v => some fun s =>
      if v.any (fun x => !x.isFinite || x < 0) then s
      else { s with line := { s.line with dash := if v.size % 2 == 1 then v ++ v else v } }
  | .dashOffset v => some fun s => if v.isFinite then { s with line := { s.line with dashOffset := v } } else s
  | .shadowColor t => some fun s => match Color.parse? t with | some c => { s with shadowColor := c } | none => s
  | .shadowBlur v => some fun s => if v.isFinite && v >= 0 then { s with shadowBlur := v } else s
  | .shadowX v => some fun s => if v.isFinite then { s with shadowX := v } else s
  | .shadowY v => some fun s => if v.isFinite then { s with shadowY := v } else s
  | .font t => some fun s => match Text.parseFont? t with | some f => { s with font := f } | none => s
  | .textAlign t => some fun s => match alignOf? t with | some a => { s with align := a } | none => s
  | .textBaseline t => some fun s => match baselineOf? t with | some b => { s with baseline := b } | none => s
  | .direction t => some fun s => match directionOf? t with | some d => { s with direction := d } | none => s
  | .smoothing b => some fun s => { s with smoothing := b }
  | .smoothingQuality t => some fun s => if ["low", "medium", "high"].contains t then { s with smoothingQuality := t } else s
  | .filter t => some fun s => { s with filter := t }
  | .letterSpacing t => some fun s => match Text.sizePx? (Color.asciiLower (Color.trim t)) with
      | some v => { s with letterSpacing := v } | none => s
  | .wordSpacing t => some fun s => match Text.sizePx? (Color.asciiLower (Color.trim t)) with
      | some v => { s with wordSpacing := v } | none => s
  | .fontKerning t => some fun s => if ["auto", "normal", "none"].contains t then { s with fontKerning := t } else s
  | .fontStretch t => some fun s => if ["ultra-condensed", "extra-condensed", "condensed", "semi-condensed", "normal",
      "semi-expanded", "expanded", "extra-expanded", "ultra-expanded"].contains t then { s with fontStretch := t } else s
  | .fontVariantCaps t => some fun s => if ["normal", "small-caps", "all-small-caps", "petite-caps", "all-petite-caps",
      "unicase", "titling-caps"].contains t then { s with fontVariantCaps := t } else s
  | .textRendering t => some fun s => if ["auto", "optimizeSpeed", "optimizeLegibility", "geometricPrecision"].contains t
      then { s with textRendering := t } else s
  | .lang t => some fun s => { s with lang := t }
  | _ => none

/-- The text of `s` shaped with the state's font, kept for later frames. -/
def Run.shape (r : Run) (font : Font) (s : String) : Run × Option Text.Shaped :=
  let key := font.text ++ "\x00" ++ s
  match r.store.shaped.get? key with
  | some w => (r, some w)
  | none =>
    match Text.shape r.env.fonts font s with
    | some w =>
      let cache := if r.store.shaped.size ≥ 1024 then {} else r.store.shaped
      ({ r with store := { r.store with shaped := cache.insert key w } }, some w)
    | none => (r, none)

/-- The outline of text at `(x, y)` in user space, as HTML §4.12.5.1.13 places it. -/
def Run.textPath (r : Run) (st : DrawState) (s : String) (x y maxW : Float) : Run × Option Path :=
  if !finite [x, y] || (!maxW.isNaN && (!maxW.isFinite || maxW <= 0)) then (r, none) else
  let (r, sh) := r.shape st.font s
  match sh with
  | none => (r, none)
  | some sh =>
    let width := sh.word.advance * sh.scale
    let sx := if !maxW.isNaN && width > maxW && width > 0 then maxW / width else 1
    let x0 := x + Text.alignShift st.align st.direction (width * sx)
    let y0 := y + Text.baselineShift st.baseline sh - sh.word.ascent * sh.scale
    (r, some (Text.outlinePath sh x0 y0 sx))

/-! ### Images -/

/-- The bitmap of an image source: 1 a canvas, 2 an `ImageBitmap`, 3 an image by key. -/
def Run.source (r : Run) (kind src : Nat) (key : String) : Option Bitmap :=
  match kind with
  | 1 => match r.cur with
    | some (id, c) => if id == src then some ⟨c.width, c.height, c.bitmap⟩
      else (r.store.canvases.get? src).map fun c => ⟨c.width, c.height, c.bitmap⟩
    | none => (r.store.canvases.get? src).map fun c => ⟨c.width, c.height, c.bitmap⟩
  | 2 => r.store.bitmaps.get? src
  | 3 => (r.store.images.get? key).orElse fun _ => r.env.image key
  | _ => none

/-- `source`, keeping a decoded image for later draws (at most 64 images). -/
def Run.sourceKept (r : Run) (kind src : Nat) (key : String) : Run × Option Bitmap :=
  let b := r.source kind src key
  if kind != 3 || r.store.images.contains key then (r, b) else
  match b with
  | some img =>
    let images := if r.store.images.size ≥ 64 then {} else r.store.images
    ({ r with store := { r.store with images := images.insert key img } }, b)
  | none => (r, none)

/-- The pixels `x .. x+w`, `y .. y+h` of a bitmap (whole pixels inside it). -/
def Bitmap.crop (b : Bitmap) (x y w h : Nat) : Bitmap := Id.run do
  let mut out := ByteArray.emptyWithCapacity (w * h * 4)
  for j in [0:h] do
    let i := ((y + j) * b.width + x) * 4
    out := out ++ b.data.extract i (i + w * 4)
  return ⟨w, h, out⟩

/-- HTML §4.12.5.1.14 `drawImage`: the source rectangle (default the whole image) clipped
to the image, the destination rectangle (default the source size) scaled with it. -/
def Run.drawImage (r : Run) (c : Canvas) (img : Bitmap) (sx sy sw sh dx dy dw dh : Float) : Canvas :=
  let iw := nf img.width
  let ih := nf img.height
  let (sx, sy, sw, sh) := if sw.isNaN then (0, 0, iw, ih) else (sx, sy, sw, sh)
  let (dw, dh) := if dw.isNaN then (sw, sh) else (dw, dh)
  if !finite [sx, sy, sw, sh, dx, dy, dw, dh] || sw == 0 || sh == 0 || dw == 0 || dh == 0 || img.width == 0 || img.height == 0 then c else
  -- Negative widths and heights name the same rectangle the other way round.
  let (sx, sw) := if sw < 0 then (sx + sw, -sw) else (sx, sw)
  let (sy, sh) := if sh < 0 then (sy + sh, -sh) else (sy, sh)
  let (dx, dw) := if dw < 0 then (dx + dw, -dw) else (dx, dw)
  let (dy, dh) := if dh < 0 then (dy + dh, -dh) else (dy, dh)
  -- Clip the source rectangle to the image; the destination follows.
  let kx := dw / sw
  let ky := dh / sh
  let cx0 := max 0 sx
  let cy0 := max 0 sy
  let cx1 := min iw (sx + sw)
  let cy1 := min ih (sy + sh)
  if cx1 <= cx0 || cy1 <= cy0 then c else
  let dx := dx + (cx0 - sx) * kx
  let dy := dy + (cy0 - sy) * ky
  let dw := (cx1 - cx0) * kx
  let dh := (cy1 - cy0) * ky
  let px0 := cx0.floor.toUInt64.toNat
  let py0 := cy0.floor.toUInt64.toNat
  let px1 := min img.width cx1.ceil.toUInt64.toNat
  let py1 := min img.height cy1.ceil.toUInt64.toNat
  let crop := img.crop px0 py0 (px1 - px0) (py1 - py0)
  let ox := cx0 - nf px0
  let oy := cy0 - nf py0
  let toUser : Matrix := { a := kx, d := ky, e := dx - ox * kx, f := dy - oy * ky }
  let pat : Pattern := ⟨crop, ⟨false, false⟩, toUser, true⟩
  let st := c.stack.cur
  let polys := ((rectPath dx dy dw dh).map st.ctm).flatten
  let es := edgesOf polys
  let cov := coverage c.width c.height es .nonzero
  c.paint st ⟨Ready.ofPattern pat st.ctm st.smoothing, cov, Color.clamp01 st.alpha, st.op, st.clip⟩ fun _ => (es, .nonzero)

/-- HTML `putImageData`: the dirty rectangle of the image data, clipped to the data and
the canvas, written as it is (no transform, alpha, operator or clip). -/
def Canvas.putImageData (c : Canvas) (data : ByteArray) (w h : Nat) (dx dy : Int) (rx ry rw rh : Int) : Canvas :=
  if data.size != w * h * 4 then c else
  let (rx, rw) := if rw < 0 then (rx + rw, -rw) else (rx, rw)
  let (ry, rh) := if rh < 0 then (ry + rh, -rh) else (ry, rh)
  -- The dirty rectangle inside the data, then inside the canvas.
  let x0 := max (max 0 rx) (-dx)
  let y0 := max (max 0 ry) (-dy)
  let x1 := min (min (Int.ofNat w) (rx + rw)) (Int.ofNat c.width - dx)
  let y1 := min (min (Int.ofNat h) (ry + rh)) (Int.ofNat c.height - dy)
  if x1 <= x0 || y1 <= y0 then c else
  let W := c.width
  c.onBitmap fun bm => Id.run do
    let mut bm := bm
    for j in [0:(y1 - y0).toNat] do
      let sy := (y0 + j).toNat
      let ty := (y0 + j + dy).toNat
      for i in [0:(x1 - x0).toNat] do
        let s := (sy * w + (x0 + i).toNat) * 4
        let t := (ty * W + (x0 + i + dx).toNat) * 4
        let a := data[s+3]!.toNat
        let k := fun (v : UInt8) => ((v.toNat * a + 127) / 255).toUInt8
        bm := bm.set! t (k data[s]!)
        bm := bm.set! (t+1) (k data[s+1]!)
        bm := bm.set! (t+2) (k data[s+2]!)
        bm := bm.set! (t+3) a.toUInt8
    return bm

/-! ### Running a batch -/

def Run.withCur (r : Run) (f : Canvas → Run → Canvas × Run) : Run :=
  match r.cur with
  | none => r
  | some (id, c) =>
    let r' := { r with cur := none }
    let (c, r') := f c r'
    { r' with cur := some (id, c) }

/-- Path commands on the target path. -/
def Run.onPath (r : Run) (cmd : Cmd) : Run :=
  if r.target == 0 then
    r.withCur fun c r => ({ c with path := pathCmd c.stack.cur.ctm c.path cmd }, r)
  else
    let p := (r.store.paths.get? r.target).getD {}
    { r with store := { r.store with paths := r.store.paths.insert r.target (pathCmd {} p cmd) } }

/-- A path from SVG path data (SVG 2 §9.3, parsed by the engine's SVG parser). -/
def pathOfContours (cs : List Rendering.Contour) : Path := Id.run do
  let mut p : Path := {}
  for c in cs do
    match c with
    | .empty _ => pure ()
    | .path st segs closed =>
      p := p.moveTo st.x st.y
      for s in segs do
        match s with
        | .line q => p := p.lineTo q.x q.y
        | .quadratic a q => p := p.quadTo a.x a.y q.x q.y
        | .cubic a b q => p := p.cubicTo a.x a.y b.x b.y q.x q.y
        | .arc rx ry rot large sweep q =>
          -- SVG 2 Appendix B.2.4: endpoint to centre parameterisation.
          let x1 := p.lastX
          let y1 := p.lastY
          if rx == 0 || ry == 0 then p := p.lineTo q.x q.y else
          let phi := rot * pi / 180
          let (cp, sp) := (Float.cos phi, Float.sin phi)
          let dx := (x1 - q.x) / 2
          let dy := (y1 - q.y) / 2
          let x1p := cp * dx + sp * dy
          let y1p := -sp * dx + cp * dy
          let rx := rx.abs
          let ry := ry.abs
          let lam := x1p * x1p / (rx * rx) + y1p * y1p / (ry * ry)
          let (rx, ry) := if lam > 1 then (rx * Float.sqrt lam, ry * Float.sqrt lam) else (rx, ry)
          let num := max 0 (rx * rx * ry * ry - rx * rx * y1p * y1p - ry * ry * x1p * x1p)
          let den := rx * rx * y1p * y1p + ry * ry * x1p * x1p
          let co := (if large == sweep then -1 else 1) * (if den == 0 then 0 else Float.sqrt (num / den))
          let cxp := co * rx * y1p / ry
          let cyp := -co * ry * x1p / rx
          let cx := cp * cxp - sp * cyp + (x1 + q.x) / 2
          let cy := sp * cxp + cp * cyp + (y1 + q.y) / 2
          let ang := fun (ux uy vx vy : Float) => Float.atan2 (ux * vy - uy * vx) (ux * vx + uy * vy)
          let t1 := ang 1 0 ((x1p - cxp) / rx) ((y1p - cyp) / ry)
          let dt := ang ((x1p - cxp) / rx) ((y1p - cyp) / ry) ((-x1p - cxp) / rx) ((-y1p - cyp) / ry)
          let dt := if !sweep && dt > 0 then dt - tau else if sweep && dt < 0 then dt + tau else dt
          let frame := (Matrix.translate cx cy).mul ((Matrix.rotate phi).mul (Matrix.scale rx ry))
          for sg in arcSegs frame t1 dt do
            match sg with
            | .cubic ax ay bx by_ x y => p := p.cubicTo ax ay bx by_ x y
            | _ => pure ()
      if closed then p := p.close
  return p

/-- Keep at most `maxObjects` entries: past it, the smallest ids (the oldest) go. -/
def bound {α} (m : Std.HashMap Nat α) : Std.HashMap Nat α :=
  if m.size < maxObjects then m else
  let keys := (m.toArray.map (·.1)).qsort (· < ·)
  (keys.extract 0 (maxObjects / 4)).foldl (fun m k => m.erase k) m

/-- Apply one command. -/
def Run.step (r : Run) (cmd : Cmd) : Run :=
  match cmd with
  | .select id => { r.take id with target := 0 }
  | .init id w h el =>
    let r := r.put
    let c := Canvas.make w h el
    { r with store := { r.store with canvases := r.store.canvases.insert id c } } |>.take id
  | .save => r.withCur fun c r => ({ c with stack := c.stack.save }, r)
  | .restore => r.withCur fun c r => ({ c with stack := c.stack.restore }, r)
  | .reset => r.withCur fun c r => ({ c with stack := {}, path := {} }.onBitmap fun bm => zeros bm.size, r)
  | .pathTarget id => { r with target := id }
  | .beginPath => if r.target == 0 then r.withCur (fun c r => ({ c with path := {} }, r))
      else { r with store := { r.store with paths := r.store.paths.insert r.target {} } }
  | .moveTo .. | .lineTo .. | .quadTo .. | .bezierTo .. | .arc .. | .arcTo .. | .ellipse .. | .rect ..
  | .roundRect .. | .closePath => r.onPath cmd
  | .pathNew id from_ =>
    let p := if from_ == 0 then {} else (r.store.paths.get? from_).getD {}
    { r with store := { r.store with paths := bound (r.store.paths.insert id p) } }
  | .pathSvg id d =>
    let p := match r.env.svgPath d with | some cs => pathOfContours cs | none => {}
    { r with store := { r.store with paths := bound (r.store.paths.insert id p) } }
  | .addPath id src m =>
    if !m.finite then r else
    let q := ((r.store.paths.get? src).getD {}).map m
    let p := (r.store.paths.get? id).getD {}
    { r with store := { r.store with paths := r.store.paths.insert id (p.append q) } }
  | .fill path rule => r.withCur fun c r => (r.fillDevice c (r.devicePath c path) rule, r)
  | .stroke path => r.withCur fun c r =>
      match r.userPath c path with
      | some p => (r.strokeUser c p c.stack.cur.stroke, r)
      | none => (c, r)
  | .clip path rule => r.withCur fun c r =>
      let cov := coverage c.width c.height (edgesOf ((r.devicePath c path).flatten 0.1)) rule
      let n := c.width * c.height
      let old := c.stack.cur.clip
      let mask := Id.run do
        let mut m := ByteArray.mk (Array.replicate n 0)
        let b := cov.box
        for j in [0:b.h] do
          for i in [0:b.w] do
            let idx := (b.y + j) * c.width + (b.x + i)
            let v := cov.cov[j * b.w + i]! * maskAt old idx
            m := m.set! idx (toByte v)
        return m
      ({ c with stack := c.stack.set fun s => { s with clip := some mask } }, r)
  | .fillRect x y w h => r.withCur fun c r => (r.rectDraw c x y w h c.stack.cur.fill false, r)
  | .clearRect x y w h => r.withCur fun c r => (r.rectDraw c x y w h c.stack.cur.fill true, r)
  | .strokeRect x y w h => r.withCur fun c r =>
      if !finite [x, y, w, h] then (c, r) else
      -- HTML: with one side zero the path is the closed line (so joins, not caps, at its ends).
      let p := if w == 0 && h == 0 then {} else rectPath x y w h
      if c.stack.cur.ctm.inverse?.isNone then (c, r) else (r.strokeUser c p c.stack.cur.stroke, r)
  | .fillText s x y maxW => r.withCur fun c r =>
      let (r, p) := r.textPath c.stack.cur s x y maxW
      match p with
      | some p => (r.fillDevice c (p.map c.stack.cur.ctm) .nonzero, r)
      | none => (c, r)
  | .strokeText s x y maxW => r.withCur fun c r =>
      let (r, p) := r.textPath c.stack.cur s x y maxW
      match p with
      | some p => (r.strokeUser c p c.stack.cur.stroke, r)
      | none => (c, r)
  | .drawImage kind src key sx sy sw sh dx dy dw dh =>
    match r.sourceKept kind src key with
    | (r, none) => r
    | (r, some img) => r.withCur fun c r => (r.drawImage c img sx sy sw sh dx dy dw dh, r)
  | .putImageData data w h dx dy rx ry rw rh => r.withCur fun c r => (c.putImageData data w h dx dy rx ry rw rh, r)
  | .gradientNew id kind =>
    { r with store := { r.store with gradients := bound (r.store.gradients.insert id { kind }) } }
  | .patternTransform id m =>
    match r.store.patterns.get? id with
    | some p => if m.finite then { r with store := { r.store with patterns := r.store.patterns.insert id { p with transform := m } } } else r
    | none => r
  | .bitmapNew id kind src key data sx sy sw sh =>
    let b := if kind == 4 then
        let w := sw.toUInt64.toNat
        let h := sh.toUInt64.toNat
        if data.size == w * h * 4 then some (Bitmap.ofStraight w h data) else none
      else r.source kind src key
    let b := b.map fun b =>
      if sw.isNaN || kind == 4 then b else
      let x0 := clampNat sx b.width
      let y0 := clampNat sy b.height
      let x1 := clampNat (sx + sw) b.width
      let y1 := clampNat (sy + sh) b.height
      b.crop x0 y0 (x1 - x0) (y1 - y0)
    match b with
    | some b => { r with store := { r.store with bitmaps := bound (r.store.bitmaps.insert id b) } }
    | none => r
  | .release kind id =>
    match kind with
    | 1 => { r with store := { r.store with gradients := r.store.gradients.erase id } }
    | 2 => { r with store := { r.store with patterns := r.store.patterns.erase id } }
    | 3 => { r with store := { r.store with paths := r.store.paths.erase id } }
    | 4 => { r with store := { r.store with bitmaps := r.store.bitmaps.erase id } }
    | 5 => { r.put with store := { r.store with canvases := r.store.canvases.erase id } }
    | _ => r
  | _ =>
    match setterOf r cmd with
    | some f => r.withCur fun c r => ({ c with stack := c.stack.set f }, r)
    | none => r

/-- Run a display list on the page's canvases. -/
def Store.run (s : Store) (env : Env) (cmds : Array Cmd) : Store :=
  let s := (cmds.foldl Run.step { store := s, env }).put.store
  { s with canvases := s.canvases.map fun _ c => c.fix }

/-! ### Queries -/

/-- A number as JavaScript prints it (`Number::toString`, which reads back exactly). -/
def bits (x : Float) : String := JS.numToString x

/-- Bytes as a string of the characters U+0000..U+00FF (the page reads `charCodeAt`). -/
def latin1 (b : ByteArray) : String := b.foldl (fun s x => s.push (Char.ofNat x.toNat)) ""

/-- Straight (not premultiplied) RGBA of `x .. x+w`, `y .. y+h`; transparent outside. -/
def Canvas.straight (c : Canvas) (x y : Int) (w h : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (w * h * 4)
  for j in [0:h] do
    let yy := y + j
    for i in [0:w] do
      let xx := x + i
      if xx < 0 || yy < 0 || xx >= c.width || yy >= c.height then
        out := (((out.push 0).push 0).push 0).push 0
      else
        let k := (yy.toNat * c.width + xx.toNat) * 4
        let a := c.bitmap[k+3]!.toNat
        let un := fun (v : UInt8) => if a == 0 then 0 else (min 255 ((v.toNat * 255 + a / 2) / a)).toUInt8
        out := (((out.push (un c.bitmap[k]!)).push (un c.bitmap[k+1]!)).push (un c.bitmap[k+2]!)).push a.toUInt8
  return out

def styleText : Style → String
  | .color c => Color.serialize c
  | .gradient id => s!"\x01g{id}"
  | .pattern id => s!"\x01p{id}"

def capName : Cap → String | .butt => "butt" | .round => "round" | .square => "square"
def joinName : Join → String | .miter => "miter" | .round => "round" | .bevel => "bevel"
def alignName : Align → String
  | .start => "start" | .end_ => "end" | .left => "left" | .right => "right" | .center => "center"
def baselineName : Baseline → String
  | .top => "top" | .hanging => "hanging" | .middle => "middle" | .alphabetic => "alphabetic"
  | .ideographic => "ideographic" | .bottom => "bottom"
def directionName : Direction → String | .ltr => "ltr" | .rtl => "rtl" | .inherit => "inherit"

/-- A getter of the drawing state. -/
def attr (st : DrawState) : String → Option String
  | "fillStyle" => styleText st.fill
  | "strokeStyle" => styleText st.stroke
  | "globalAlpha" => bits st.alpha
  | "globalCompositeOperation" => st.op.name
  | "lineWidth" => bits st.line.width
  | "lineCap" => capName st.line.cap
  | "lineJoin" => joinName st.line.join
  | "miterLimit" => bits st.line.miterLimit
  | "lineDashOffset" => bits st.line.dashOffset
  | "shadowColor" => Color.serialize st.shadowColor
  | "shadowBlur" => bits st.shadowBlur
  | "shadowOffsetX" => bits st.shadowX
  | "shadowOffsetY" => bits st.shadowY
  | "font" => st.font.text
  | "textAlign" => alignName st.align
  | "textBaseline" => baselineName st.baseline
  | "direction" => directionName st.direction
  | "imageSmoothingEnabled" => if st.smoothing then "1" else "0"
  | "imageSmoothingQuality" => st.smoothingQuality
  | "filter" => st.filter
  | "letterSpacing" => Text.num st.letterSpacing ++ "px"
  | "wordSpacing" => Text.num st.wordSpacing ++ "px"
  | "fontKerning" => st.fontKerning
  | "fontStretch" => st.fontStretch
  | "fontVariantCaps" => st.fontVariantCaps
  | "textRendering" => st.textRendering
  | "lang" => st.lang
  | _ => none

/-- Winding of a point by flattened polygons. -/
def winding (polys : Array Poly) (x y : Float) : Int := Id.run do
  let mut w : Int := 0
  for e in edgesOf polys do
    if e.y0 <= y && y < e.y1 then
      let ex := e.x0 + (y - e.y0) * (e.x1 - e.x0) / (e.y1 - e.y0)
      if ex > x then w := w + e.dir
  return w

def inside (rule : FillRule) (w : Int) : Bool := if rule == .nonzero then w != 0 else w % 2 != 0

/-- The point is on an edge of the polygons (HTML: a point on the path is inside it). -/
def onEdge (polys : Array Poly) (x y : Float) : Bool := Id.run do
  for p in polys do
    let n := p.count
    for i in [0:n] do
      let j := if i + 1 == n then 0 else i + 1
      let ax := p.pts[2*i]!
      let ay := p.pts[2*i+1]!
      let bx := p.pts[2*j]!
      let by_ := p.pts[2*j+1]!
      let cross := (bx - ax) * (y - ay) - (by_ - ay) * (x - ax)
      let len := Float.sqrt ((bx - ax) ^ 2 + (by_ - ay) ^ 2)
      if cross.abs <= 1e-6 * max 1 len && min ax bx - 1e-9 <= x && x <= max ax bx + 1e-9 &&
          min ay by_ - 1e-9 <= y && y <= max ay by_ + 1e-9 then return true
  return false

/-- A query of a page script: its answer and the store after it. -/
inductive Query where
  | attr (canvas : Nat) (name : String)
  | imageData (canvas : Nat) (x y : Int) (w h : Nat)
  | measure (canvas : Nat) (text : String)
  | inPath (canvas path : Nat) (x y : Float) (rule : FillRule)
  | inStroke (canvas path : Nat) (x y : Float)
  | transform (canvas : Nat)
  | dataURL (canvas : Nat) (type : String)
  | lineDash (canvas : Nat)
  | addStop (gradient : Nat) (offset : Float) (color : String)
  | pattern (id kind src : Nat) (key : String) (repetition : String)
  | size (kind src : Nat) (key : String)

def Store.answer (s : Store) (env : Env) (q : Query) : Store × String :=
  let canvas := fun (id : Nat) => s.canvases.get? id
  match q with
  | .attr id name => (s, ((canvas id).bind fun c => attr c.stack.cur name).getD "")
  | .imageData id x y w h =>
    match canvas id with
    | some c => (s, latin1 (c.straight x y w h))
    | none => (s, latin1 (ByteArray.mk (Array.replicate (w * h * 4) 0)))
  | .measure id text =>
    match canvas id with
    | none => (s, "")
    | some c =>
      let st := c.stack.cur
      let r : Run := { store := s, env }
      let (r, sh) := r.shape st.font text
      match sh with
      | none => (r.store, "")
      | some sh =>
        let k := sh.scale
        let width := sh.word.advance * k
        let a := sh.word.ascent * k
        let d := sh.word.descent * k
        let base := Text.baselineShift st.baseline sh
        let x0 := Text.alignShift st.align st.direction width
        -- The ink box from the outline's control points (they hold the curves).
        let p := Text.outlinePath sh x0 (base - a) 1
        let pts := p.flatten 0.05
        let (minX, minY, maxX, maxY) := pts.foldl (init := (1e30, 1e30, -1e30, -1e30)) fun acc poly =>
          (List.range poly.count).foldl (fun (a, b, c, d) i =>
            (min a poly.pts[2*i]!, min b poly.pts[2*i+1]!, max c poly.pts[2*i]!, max d poly.pts[2*i+1]!)) acc
        let empty := minX > maxX
        let nums := [width, if empty then 0 else -minX, if empty then 0 else maxX,
          a - base, d + base, if empty then 0 else -minY, if empty then 0 else maxY,
          a - base, d + base, a * 0.8 - base, -base, -d - base]
        (r.store, " ".intercalate (nums.map bits))
  | .inPath id path x y rule =>
    match canvas id with
    | none => (s, "0")
    | some c =>
      if !finite [x, y] then (s, "0") else
      let r : Run := { store := s, env }
      let polys := (r.devicePath c path).flatten 0.05
      (s, if inside rule (winding polys x y) || onEdge polys x y then "1" else "0")
  | .inStroke id path x y =>
    match canvas id with
    | none => (s, "0")
    | some c =>
      if !finite [x, y] then (s, "0") else
      let r : Run := { store := s, env }
      match r.userPath c path with
      | none => (s, "0")
      | some p =>
        let st := c.stack.cur
        let tol := 0.05 / max 1e-9 st.ctm.stretch
        let polys := mapPolys st.ctm (strokePolys st.line (p.flatten tol) tol)
        (s, if winding polys x y != 0 || onEdge polys x y then "1" else "0")
  | .transform id =>
    let m := ((canvas id).map (·.stack.cur.ctm)).getD {}
    (s, " ".intercalate ([m.a, m.b, m.c, m.d, m.e, m.f].map bits))
  | .dataURL id _ =>
    match canvas id with
    | none => (s, "data:,")
    | some c =>
      if c.width == 0 || c.height == 0 then (s, "data:,") else
      (s, "data:image/png;base64," ++ Png.base64 (Png.encode c.width c.height (c.straight 0 0 c.width c.height)))
  | .lineDash id => (s, " ".intercalate ((((canvas id).map (·.stack.cur.line.dash)).getD #[]).toList.map bits))
  | .addStop id offset color =>
    if !offset.isFinite || offset < 0 || offset > 1 then (s, "IndexSizeError") else
    match Color.parse? color, s.gradients.get? id with
    | none, _ => (s, "SyntaxError")
    | some col, some g => ({ s with gradients := s.gradients.insert id { g with stops := g.stops.push ⟨offset, col⟩ } }, "")
    | some _, none => (s, "")
  | .pattern id kind src key rep =>
    let repetition : Option Repeat := match rep with
      | "" | "repeat" => some {} | "repeat-x" => some { y := false } | "repeat-y" => some { x := false }
      | "no-repeat" => some { x := false, y := false } | _ => none
    match repetition with
    | none => (s, "SyntaxError")
    | some rp =>
      let r : Run := { store := s, env }
      match r.source kind src key with
      | none => (s, "null")
      | some b =>
        if b.width == 0 || b.height == 0 then (s, "InvalidStateError") else
        ({ s with patterns := bound (s.patterns.insert id { image := b, repetition := rp }) }, "")
  | .size kind src key =>
    let r : Run := { store := s, env }
    match r.source kind src key with
    | some b => (s, s!"{b.width} {b.height}")
    | none => (s, "")

/-! ### What the host gets -/

/-- A host command for the canvases of a page (beside `PageGpu.HostCmd`): a texture for
an element canvas, and its pixels (straight RGBA, the whole canvas). -/
inductive HostCmd where
  | texture (id node w h : Nat)
  | destroy (id : Nat)
  | pixels (id w h : Nat) (data : ByteArray)

/-- Texture ids of 2D canvases, apart from the page's own GPU objects. -/
def textureBase : Nat := 1073741824

/-- The host commands of one drawn canvas: a texture when the host has none of its size,
then its pixels, only with exactly `width × height × 4` bytes. -/
def emitOne (held : Option (Nat × Nat)) (id : Nat) (c : Canvas) : List HostCmd :=
  if c.width == 0 || c.height == 0 then [] else
  let tex := if held == some (c.width, c.height) then []
    else (if held.isSome then [HostCmd.destroy (textureBase + id)] else []) ++ [.texture (textureBase + id) id c.width c.height]
  let data := c.straight 0 0 c.width c.height
  tex ++ (if data.size == c.width * c.height * 4 then [.pixels (textureBase + id) c.width c.height data] else [])

/-- Every pixels command of `emitOne` is of the canvas's size, with that many bytes. -/
theorem emitOne_pixels (held : Option (Nat × Nat)) (id : Nat) (c : Canvas) (t w h : Nat) (d : ByteArray)
    (mem : HostCmd.pixels t w h d ∈ emitOne held id c) : w = c.width ∧ h = c.height ∧ d.size = w * h * 4 := by
  unfold emitOne at mem
  split at mem
  · simp at mem
  · simp only [List.mem_append] at mem
    rcases mem with m | m
    · split at m
      · simp at m
      · split at m <;> simp at m
    · split at m
      · simp at m; obtain ⟨_, rfl, rfl, rfl⟩ := m; simp_all
      · simp at m

def Store.drawn (s : Store) : List (Nat × Canvas) :=
  s.canvases.toList.filter fun (_, c) => c.dirty && c.element

/-- The host commands for the canvases drawn since the last turn. -/
def Store.hostCmds (s : Store) : List HostCmd :=
  s.drawn.flatMap fun (id, c) => emitOne (s.textures.get? id) id c

/-- The store once the host has the commands of `hostCmds`: none drawn, the textures known. -/
def Store.sent (s : Store) : Store :=
  let drawn := s.drawn
  if drawn.isEmpty then s else
  let textures := drawn.foldl (fun t (id, c) => if c.width == 0 || c.height == 0 then t else t.insert id (c.width, c.height)) s.textures
  let canvases := drawn.foldl (fun m (id, c) => m.insert id { c with dirty := false }) s.canvases
  { s with textures, canvases }

def Store.emit (s : Store) : Store × List HostCmd := (s.sent, s.hostCmds)

/-- The host gets pixels only of the size of a canvas of the page. -/
theorem emit_pixels (s : Store) (t w h : Nat) (d : ByteArray) (mem : HostCmd.pixels t w h d ∈ (s.emit).2) :
    ∃ id c, (id, c) ∈ s.drawn ∧ w = c.width ∧ h = c.height ∧ d.size = w * h * 4 := by
  simp only [Store.emit, Store.hostCmds, List.mem_flatMap] at mem
  obtain ⟨⟨id, c⟩, hm, hp⟩ := mem
  exact ⟨id, c, hm, emitOne_pixels _ _ _ _ _ _ _ hp⟩

/-- The pixel `i` of RGBA bytes as one word. -/
@[inline] def wordAt (d : ByteArray) (i : Nat) : UInt32 :=
  d[4*i]!.toUInt32 ||| (d[4*i+1]!.toUInt32 <<< 8) ||| (d[4*i+2]!.toUInt32 <<< 16) ||| (d[4*i+3]!.toUInt32 <<< 24)

def pushWord (b : ByteArray) (v : Nat) : ByteArray :=
  (((b.push (v % 256).toUInt8).push (v / 256 % 256).toUInt8).push (v / 65536 % 256).toUInt8).push (v / 16777216 % 256).toUInt8

/-- Run-length form of RGBA pixels for the host: runs, each a little-endian word, then
the pixels: with the high bit set, that many pixels follow as they are; without it, one
pixel follows, repeated that many times. A canvas is mostly runs (backgrounds, bars). -/
def rle (d : ByteArray) : ByteArray := Id.run do
  let n := d.size / 4
  let mut out := ByteArray.emptyWithCapacity (n / 4 + 16)
  let mut i := 0
  let mut lit := 0
  while i < n do
    let w := wordAt d i
    let mut j := i + 1
    while j < n && wordAt d j == w do j := j + 1
    if j - i >= 3 then
      if lit < i then
        out := pushWord out (2147483648 + (i - lit))
        out := out ++ d.extract (4 * lit) (4 * i)
      out := pushWord out (j - i)
      out := out ++ d.extract (4 * i) (4 * i + 4)
      lit := j
    i := j
  if lit < n then
    out := pushWord out (2147483648 + (n - lit))
    out := out ++ d.extract (4 * lit) (4 * n)
  return out

def HostCmd.json (page : Nat) : HostCmd → String
  | .texture id node w h =>
    s!"\{\"k\":\"canvas\",\"g\":[{page},{id}],\"node\":{node},\"w\":{w},\"h\":{h},\"usage\":22,\"twoD\":true}"
  | .destroy id => s!"\{\"k\":\"destroy\",\"g\":[{page},{id}]}"
  | .pixels id w h data => s!"\{\"k\":\"pixels\",\"g\":[{page},{id}],\"w\":{w},\"h\":{h},\"rle\":1,\"data\":\"{Png.base64 (rle data)}\"}"

end L4Factoidal.PageCanvas
