/-
L4Factoidal.PageCanvas.Raster: coverage and compositing for Canvas 2D
(record: docs/designissues/2026-11-08-canvas-2d.md).

- `coverage`: the fraction of each device pixel inside polygons under a fill rule
  (nonzero or even-odd). Each pixel row is cut at `subRows` sample rows; along a sample
  row the inside intervals are exact, so a pixel's coverage is exact horizontally and
  in steps of `1/subRows` vertically. The work is only in the box of the polygons,
  clamped to the canvas (`Box`, theorem `boxOf_within`).
- `Op`, `composite`: the compositing and blending operators of Compositing and Blending
  Level 1 §9 and §10 on premultiplied colours, as HTML §4.12.5.1.15 asks: the shape is
  drawn onto transparent black with its coverage, composited with the operator, and the
  clip region decides where the result replaces the destination.
-/
import L4Factoidal.PageCanvas.Paint
import L4Factoidal.Prim.Bytes

namespace L4Factoidal.PageCanvas

inductive FillRule where | nonzero | evenodd
  deriving Repr, Inhabited, BEq

structure Edge where
  x0 : Float
  y0 : Float
  x1 : Float
  y1 : Float
  dir : Int
  deriving Inhabited

/-- The edges of polygons, each closed back to its first point; horizontal edges and
non-finite points are left out. -/
def edgesOf (polys : Array Poly) : Array Edge := Id.run do
  let mut out := #[]
  for p in polys do
    let n := p.count
    if n < 2 then continue
    for i in [0:n] do
      let j := if i + 1 == n then 0 else i + 1
      let ax := p.pts[2*i]!
      let ay := p.pts[2*i+1]!
      let bx := p.pts[2*j]!
      let by_ := p.pts[2*j+1]!
      if !(ax.isFinite && ay.isFinite && bx.isFinite && by_.isFinite) then continue
      if ay < by_ then out := out.push ⟨ax, ay, bx, by_, 1⟩
      else if by_ < ay then out := out.push ⟨bx, by_, ax, ay, -1⟩
  return out

/-- A box of device pixels: columns `x .. x+w`, rows `y .. y+h`. -/
structure Box where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Repr, Inhabited, BEq

/-- Clamp a coordinate to `0 .. n`. -/
def clampNat (v : Float) (n : Nat) : Nat :=
  if v.isNaN || v <= 0 then 0 else if v >= nf n then n else v.toUInt64.toNat

/-- The pixels a box of floats touches, inside a canvas of `W × H`. -/
def boxOf (W H : Nat) (minX minY maxX maxY : Float) : Box :=
  let x0 := min (clampNat minX.floor W) W
  let y0 := min (clampNat minY.floor H) H
  let x1 := min (clampNat maxX.ceil W) W
  let y1 := min (clampNat maxY.ceil H) H
  ⟨x0, y0, x1 - x0, y1 - y0⟩

/-- Every box is inside its canvas. -/
theorem boxOf_within (W H : Nat) (a b c d : Float) :
    (boxOf W H a b c d).x + (boxOf W H a b c d).w ≤ W ∧ (boxOf W H a b c d).y + (boxOf W H a b c d).h ≤ H := by
  simp only [boxOf]
  constructor <;> omega

/-- The box of edges, inside the canvas. -/
def edgeBox (W H : Nat) (es : Array Edge) : Box :=
  if es.isEmpty then ⟨0, 0, 0, 0⟩ else
  let init := (es[0]!.x0, es[0]!.y0, es[0]!.x0, es[0]!.y0)
  let (a, b, c, d) := es.foldl (init := init) fun (a, b, c, d) e =>
    (min a (min e.x0 e.x1), min b e.y0, max c (max e.x0 e.x1), max d e.y1)
  boxOf W H a b c d

/-- Sample rows a pixel row is cut at. -/
def subRows : Nat := 16

/-- Coverage of the pixels of `box`, row by row (`box.w × box.h` values in 0..1), and
for each row the columns `[lo, hi)` (relative to the box) outside which it is 0. -/
structure Coverage where
  box : Box
  cov : FloatArray
  spans : Array (Nat × Nat) := #[]

/-- Insert a crossing into an array sorted by `x` (few crossings on one row). -/
private def insertSorted (xs : Array (Float × Int)) (x : Float) (d : Int) : Array (Float × Int) := Id.run do
  let mut i := xs.size
  while i > 0 && xs[i-1]!.1 > x do i := i - 1
  return xs.insertIdx! i (x, d)

/-- One merge of the sorted runs `a[lo..mid)` and `a[mid..hi)`: `fuel` outputs, in `out`. -/
private def sortMerge {α} [Inhabited α] (key : α → Float) (a : Array α) (mid hi : Nat) :
    Nat → Nat → Nat → Array α → Array α
  | 0, _, _, out => out
  | fuel+1, i, j, out =>
    if i < mid && (j ≥ hi || key a[i]! <= key a[j]!) then
      sortMerge key a mid hi fuel (i + 1) j (out.push a[i]!)
    else
      sortMerge key a mid hi fuel i (j + 1) (out.push a[j]!)

/-- A merge pass of run width `width`: `fuel` bounds the number of runs. -/
private def sortPass {α} [Inhabited α] (key : α → Float) (a : Array α) (n width : Nat) :
    Nat → Nat → Array α → Array α
  | 0, _, out => out
  | fuel+1, lo, out =>
    if lo ≥ n then out else
    let mid := min n (lo + width)
    let hi := min n (lo + 2 * width)
    sortPass key a n width fuel hi (sortMerge key a mid hi (hi - lo) lo mid out)

/-- Sorted by `key`, stable: a bottom-up merge sort (n log n whatever the input, also when many
keys are equal, as for shapes drawn over each other). Each step is a tail call: a `for` over a range in this
polymorphic function was left unspecialized by the compiler and took about five Wasm frames per
element (a chart of 700 edges overflowed the Hub worker's stack). -/
def sortBy {α} [Inhabited α] (key : α → Float) (xs : Array α) : Array α :=
  go xs.size xs 1
where
  /-- At most `n` passes (`width` doubles each time). -/
  go : Nat → Array α → Nat → Array α
    | 0, a, _ => a
    | fuel+1, a, width =>
      if width ≥ xs.size then a
      else go fuel (sortPass key a xs.size width xs.size 0 (Array.emptyWithCapacity xs.size)) (2 * width)

/-- One row of `coverageIn`: the running sum of `diff` plus `direct`, clamped to 0..1, into
`cov` at `base + i` for columns `i < w`, from column `i` to `stop - 1`, with `diff` and
`direct` set back to zero there. A tail call with the sum as a `Float` argument: as a `for`
loop the sum was loop state and was boxed at each pixel (issue 1098). -/
def rowSums (w base stop : Nat) : Nat → Nat → Float → FloatArray → FloatArray → FloatArray →
    FloatArray × FloatArray × FloatArray
  | 0, _, _, cov, diff, direct => (cov, diff, direct)
  | fuel+1, i, run, cov, diff, direct =>
    if i >= stop then (cov, diff, direct) else
    let run := run + diff[i]!
    let cov := if i < w then
        let c := run + direct[i]!
        cov.set! (base + i) (if c <= 0 then 0 else if c >= 1 then 1 else c)
      else cov
    rowSums w base stop fuel (i + 1) run cov (diff.set! i 0) (direct.set! i 0)

/-- The coverage values of polygons with edges `es` under `rule`, in `box`, and for each
row of the box the columns `[lo, hi)` that may be covered (outside them the value is 0). -/
def coverageIn (box : Box) (es : Array Edge) (rule : FillRule) : FloatArray × Array (Nat × Nat) := Id.run do
  if box.w == 0 || box.h == 0 then return (FloatArray.empty, #[])
  -- Edges by their first row, for an active list.
  let sorted := sortBy (·.y0) es
  let mut cov := fzeros (box.w * box.h)
  let mut spans : Array (Nat × Nat) := Array.emptyWithCapacity box.h
  let mut active : Array Edge := #[]
  let mut next := 0
  let bx := nf box.x
  let wgt := 1 / nf subRows
  -- One row's sums, kept zero outside the columns a row touched.
  let mut diff := fzeros (box.w + 2)
  let mut direct := fzeros (box.w + 2)
  for j in [0:box.h] do
    let row := nf (box.y + j)
    -- Edges that reach this row.
    while next < sorted.size && sorted[next]!.y0 < row + 1 do
      active := active.push sorted[next]!
      next := next + 1
    active := active.filter (·.y1 > row)
    if active.isEmpty then
      spans := spans.push (0, 0)
      continue
    let mut lo := box.w + 1
    let mut hi := 0
    for s in [0:subRows] do
      let ys := row + (nf s + 0.5) * wgt
      let mut xs : Array (Float × Int) := #[]
      for e in active do
        if e.y0 <= ys && ys < e.y1 then
          let x := e.x0 + (ys - e.y0) * (e.x1 - e.x0) / (e.y1 - e.y0)
          xs := xs.push (x, e.dir)
      -- Few crossings: insertion; many (overlapping shapes): a sort.
      xs := if xs.size ≤ 16 then xs.foldl (fun acc (x, d) => insertSorted acc x d) #[] else sortBy (·.1) xs
      let mut wind : Int := 0
      let mut start := 0.0
      for (x, d) in xs do
        let before := wind
        wind := wind + d
        let wasIn := if rule == .nonzero then before != 0 else before % 2 != 0
        let isIn := if rule == .nonzero then wind != 0 else wind % 2 != 0
        if !wasIn && isIn then start := x
        else if wasIn && !isIn then
          -- The interval [start, x), relative to the box.
          let xa := max 0 (min (nf box.w) (start - bx))
          let xb := max 0 (min (nf box.w) (x - bx))
          if xb > xa then
            let ia := xa.floor.toUInt64.toNat
            let ib := xb.floor.toUInt64.toNat
            lo := min lo ia
            hi := max hi (ib + 1)
            if ia == ib then
              direct := direct.set! ia (direct[ia]! + (xb - xa) * wgt)
            else
              direct := direct.set! ia (direct[ia]! + (nf ia + 1 - xa) * wgt)
              diff := diff.set! (ia + 1) (diff[ia+1]! + wgt)
              diff := diff.set! ib (diff[ib]! - wgt)
              if xb > nf ib then direct := direct.set! ib (direct[ib]! + (xb - nf ib) * wgt)
    let hiC := min hi box.w
    if lo >= hiC then
      spans := spans.push (0, 0)
    else
      spans := spans.push (lo, hiC)
    let (cov', diff', direct') := rowSums box.w (j * box.w) (hi + 1) (hi + 1 - lo) lo 0 cov diff direct
    cov := cov'
    diff := diff'
    direct := direct'
  return (cov, spans)

/-- The coverage of polygons with edges `es` under `rule`, in the canvas `W × H`. -/
def coverage (W H : Nat) (es : Array Edge) (rule : FillRule) : Coverage :=
  let box := edgeBox W H es
  let (cov, spans) := coverageIn box es rule
  ⟨box, cov, spans⟩

theorem edgeBox_within (W H : Nat) (es : Array Edge) :
    (edgeBox W H es).x + (edgeBox W H es).w ≤ W ∧ (edgeBox W H es).y + (edgeBox W H es).h ≤ H := by
  unfold edgeBox
  split
  · simp
  · exact boxOf_within ..

/-- A fill visits only pixels of its canvas. -/
theorem coverage_within (W H : Nat) (es : Array Edge) (rule : FillRule) :
    (coverage W H es rule).box.x + (coverage W H es rule).box.w ≤ W ∧
    (coverage W H es rule).box.y + (coverage W H es rule).box.h ≤ H :=
  edgeBox_within W H es

/-- The coverage values of an axis-aligned rectangle (exact) in `box`, the reference. -/
def rectCoverageInRef (box : Box) (x0 y0 x1 y1 : Float) : FloatArray := Id.run do
  let mut cov := fzeros (box.w * box.h)
  for j in [0:box.h] do
    let py := nf (box.y + j)
    let cy := max 0 (min (py + 1) y1 - max py y0)
    for i in [0:box.w] do
      let px := nf (box.x + i)
      let cx := max 0 (min (px + 1) x1 - max px x0)
      cov := cov.set! (j * box.w + i) (min 1 (cx * cy))
  return cov

/-- `rectCoverageInRef` with the horizontal share of each column computed once (the same
expression, so the same value) and the values pushed in row order (issue 1098: a full-canvas
`fillRect` made 1.6 M values, each with ten Float operations). -/
def rectCoverageIn (box : Box) (x0 y0 x1 y1 : Float) : FloatArray := Id.run do
  let mut cxs := FloatArray.emptyWithCapacity box.w
  for i in [0:box.w] do
    let px := nf (box.x + i)
    cxs := cxs.push (max 0 (min (px + 1) x1 - max px x0))
  let mut cov := FloatArray.emptyWithCapacity (box.w * box.h)
  for j in [0:box.h] do
    let py := nf (box.y + j)
    let cy := max 0 (min (py + 1) y1 - max py y0)
    for i in [0:box.w] do
      cov := cov.push (min 1 (cxs[i]! * cy))
  return cov

/-- The coverage of an axis-aligned rectangle (exact). -/
def rectCoverage (W H : Nat) (x0 y0 x1 y1 : Float) : Coverage :=
  let box := boxOf W H x0 y0 x1 y1
  ⟨box, rectCoverageIn box x0 y0 x1 y1, Array.replicate box.h (0, box.w)⟩

theorem rectCoverage_within (W H : Nat) (a b c d : Float) :
    (rectCoverage W H a b c d).box.x + (rectCoverage W H a b c d).box.w ≤ W ∧
    (rectCoverage W H a b c d).box.y + (rectCoverage W H a b c d).box.h ≤ H :=
  boxOf_within W H a b c d

/-! ### Compositing -/

/-- `globalCompositeOperation` values (HTML §4.12.5.1.15, Compositing and Blending §9-10). -/
inductive Op where
  | sourceOver | sourceIn | sourceOut | sourceAtop
  | destinationOver | destinationIn | destinationOut | destinationAtop
  | lighter | copy | xor | clear
  | multiply | screen | overlay | darken | lighten | colorDodge | colorBurn
  | hardLight | softLight | difference | exclusion | hue | saturation | color | luminosity
  deriving Repr, Inhabited, BEq, DecidableEq

def Op.names : List (String × Op) := [
  ("source-over", .sourceOver), ("source-in", .sourceIn), ("source-out", .sourceOut), ("source-atop", .sourceAtop),
  ("destination-over", .destinationOver), ("destination-in", .destinationIn), ("destination-out", .destinationOut),
  ("destination-atop", .destinationAtop), ("lighter", .lighter), ("copy", .copy), ("xor", .xor), ("clear", .clear),
  ("multiply", .multiply), ("screen", .screen), ("overlay", .overlay), ("darken", .darken), ("lighten", .lighten),
  ("color-dodge", .colorDodge), ("color-burn", .colorBurn), ("hard-light", .hardLight), ("soft-light", .softLight),
  ("difference", .difference), ("exclusion", .exclusion), ("hue", .hue), ("saturation", .saturation),
  ("color", .color), ("luminosity", .luminosity)]

def Op.ofName? (s : String) : Option Op := (Op.names.find? (·.1 == s)).map (·.2)
def Op.name (o : Op) : String := ((Op.names.find? (·.2 == o)).map (·.1)).getD "source-over"

/-- Operators that change the destination where the source is transparent: they run over
the whole clip region, not only under the shape. -/
def Op.unbounded : Op → Bool
  | .sourceIn | .sourceOut | .destinationIn | .destinationAtop | .copy => true
  | _ => false

/-- Separable blend functions B(Cb, Cs), Compositing and Blending §10.2. -/
def blendChannel (o : Op) (cb cs : Float) : Float :=
  let hard := fun (cb cs : Float) => if cs <= 0.5 then cb * 2 * cs else let s := 2 * cs - 1; cb + s - cb * s
  match o with
  | .multiply => cb * cs
  | .screen => cb + cs - cb * cs
  | .overlay => hard cs cb
  | .darken => min cb cs
  | .lighten => max cb cs
  | .colorDodge => if cb == 0 then 0 else if cs >= 1 then 1 else min 1 (cb / (1 - cs))
  | .colorBurn => if cb >= 1 then 1 else if cs <= 0 then 0 else 1 - min 1 ((1 - cb) / cs)
  | .hardLight => hard cb cs
  | .softLight =>
    if cs <= 0.5 then cb - (1 - 2 * cs) * cb * (1 - cb)
    else
      let d := if cb <= 0.25 then ((16 * cb - 12) * cb + 4) * cb else Float.sqrt cb
      cb + (2 * cs - 1) * (d - cb)
  | .difference => (cb - cs).abs
  | .exclusion => cb + cs - 2 * cb * cs
  | _ => cs

private def lum (r g b : Float) : Float := 0.3 * r + 0.59 * g + 0.11 * b
private def clipColor (r g b : Float) : Float × Float × Float :=
  let l := lum r g b
  let n := min r (min g b)
  let x := max r (max g b)
  let (r, g, b) := if n < 0 then (l + (r - l) * l / (l - n), l + (g - l) * l / (l - n), l + (b - l) * l / (l - n)) else (r, g, b)
  if x > 1 then (l + (r - l) * (1 - l) / (x - l), l + (g - l) * (1 - l) / (x - l), l + (b - l) * (1 - l) / (x - l)) else (r, g, b)
private def setLum (r g b l : Float) : Float × Float × Float :=
  let d := l - lum r g b
  clipColor (r + d) (g + d) (b + d)
private def sat (r g b : Float) : Float := max r (max g b) - min r (min g b)
private def setSat (r g b s : Float) : Float × Float × Float :=
  let mx := max r (max g b)
  let mn := min r (min g b)
  let f := fun (c : Float) => if mx == mn then 0 else if c == mx then s else if c == mn then 0 else (c - mn) * s / (mx - mn)
  if mx == mn then (0, 0, 0) else (f r, f g, f b)

/-- Non-separable blend functions, Compositing and Blending §10.3. -/
def blendNonSep (o : Op) (br bg bb sr sg sb : Float) : Float × Float × Float :=
  match o with
  | .hue => let (r, g, b) := setSat sr sg sb (sat br bg bb); setLum r g b (lum br bg bb)
  | .saturation => let (r, g, b) := setSat br bg bb (sat sr sg sb); setLum r g b (lum br bg bb)
  | .color => setLum sr sg sb (lum br bg bb)
  | .luminosity => setLum br bg bb (lum sr sg sb)
  | _ => (sr, sg, sb)

/-- Source `s` over destination `d` (both premultiplied) with operator `o`. -/
def compose (o : Op) (s d : Px) : Px :=
  let pd := fun (fa fb : Float) => (⟨s.r * fa + d.r * fb, s.g * fa + d.g * fb, s.b * fa + d.b * fb, s.a * fa + d.a * fb⟩ : Px)
  match o with
  | .sourceOver => pd 1 (1 - s.a)
  | .sourceIn => pd d.a 0
  | .sourceOut => pd (1 - d.a) 0
  | .sourceAtop => pd d.a (1 - s.a)
  | .destinationOver => pd (1 - d.a) 1
  | .destinationIn => pd 0 s.a
  | .destinationOut => pd 0 (1 - s.a)
  | .destinationAtop => pd (1 - d.a) s.a
  | .lighter => let p := pd 1 1; ⟨min 1 p.r, min 1 p.g, min 1 p.b, min 1 p.a⟩
  | .copy => s
  | .xor => pd (1 - d.a) (1 - s.a)
  | .clear => Px.zero
  | _ =>
    -- Blending: Cs' = (1 - ab) Cs + ab B(Cb, Cs), then source-over.
    let un := fun (c a : Float) => if a <= 0 then 0 else c / a
    let (cbr, cbg, cbb) := (un d.r d.a, un d.g d.a, un d.b d.a)
    let (csr, csg, csb) := (un s.r s.a, un s.g s.a, un s.b s.a)
    let (br, bg, bb) := match o with
      | .hue | .saturation | .color | .luminosity => blendNonSep o cbr cbg cbb csr csg csb
      | _ => (blendChannel o cbr csr, blendChannel o cbg csg, blendChannel o cbb csb)
    let mix := fun (cs b : Float) => (1 - d.a) * cs + d.a * b
    let sr := mix csr br * s.a
    let sg := mix csg bg * s.a
    let sb := mix csb bb * s.a
    ⟨sr + d.r * (1 - s.a), sg + d.g * (1 - s.a), sb + d.b * (1 - s.a), s.a + d.a * (1 - s.a)⟩

@[inline] def toByte (v : Float) : UInt8 :=
  if v.isNaN || v <= 0 then 0 else if v >= 1 then 255 else (v * 255).round.toUInt8

/-- One pixel: the destination `d`, the source `s` with coverage `c` (already times the
global alpha), the clip mask `m` in 0..1. The result replaces `d` where `m` is 1, and is
mixed with it where `m` is between. -/
@[inline] def blendPixel (o : Op) (s : Px) (c m : Float) (d : Px) : Px :=
  if m <= 0 then d else
  -- `clear` clears what the shape covers, whatever the source colour.
  let r := if o == .clear then d.scale (1 - c) else compose o (s.scale c) d
  if m >= 1 then r else
  ⟨d.r + (r.r - d.r) * m, d.g + (r.g - d.g) * m, d.b + (r.b - d.b) * m, d.a + (r.a - d.a) * m⟩

/-- A pixel outside the clip region is the destination, whatever is drawn. -/
theorem blendPixel_outside_clip (o : Op) (s : Px) (c m : Float) (d : Px) (h : m <= 0) :
    blendPixel o s c m d = d := by
  simp [blendPixel, h]

/-- A clip mask: one byte per canvas pixel (255 inside). `none` is no clip. -/
abbrev Mask := Option ByteArray

@[inline] def maskAt (m : Mask) (i : Nat) : Float :=
  match m with
  | none => 1
  | some b => b[i]!.toFloat / 255

/-- Byte `i` of `a`, or 0 outside it (as `a[i]!`), with the test on `USize`. -/
@[inline] def byteAt (a : ByteArray) (i : USize) : UInt8 :=
  if h : i < a.usize then a.uget i (Prim.Bytes.usize_lt_size h) else 0

theorem floatArray_usize_lt_size {a : FloatArray} {i : USize} (h : i < a.usize) : i.toNat < a.size := by
  have h1 := USize.lt_iff_toNat_lt.mp h
  simp only [FloatArray.usize, USize.toNat_ofNat', Nat.toUSize] at h1
  have := Nat.mod_le a.size (2 ^ System.Platform.numBits)
  omega

/-- Value `i` of `a`, or 0 outside it (as `a[i]!`), with the test on `USize`. -/
@[inline] def floatAt (a : FloatArray) (i : USize) : Float :=
  if h : i < a.usize then a.uget i (floatArray_usize_lt_size h) else 0

/-- The clip mask of a canvas of width `W` and `n` pixels after a clip with coverage `cov`,
inside the old mask `old` (HTML §4.12.5.1.15: the new clip region is the intersection), the
reference. -/
def clipMaskRef (W n : Nat) (cov : Coverage) (old : Mask) : ByteArray := Id.run do
  let mut m := bzeros n
  let b := cov.box
  for j in [0:b.h] do
    for i in [0:b.w] do
      let idx := (b.y + j) * W + (b.x + i)
      let v := cov.cov[j * b.w + i]! * maskAt old idx
      m := m.set! idx (toByte v)
  return m

/-- One row of `clipMask`: `n` pixels from canvas index `idx` and coverage index `ci`. -/
def clipRow (cov : FloatArray) (old : Mask) : Nat → USize → USize → ByteArray → ByteArray
  | 0, _, _, m => m
  | n+1, idx, ci, m =>
    let k : Float := match old with
      | none => 1
      | some o => (byteAt o idx).toFloat / 255
    clipRow cov old n (idx + 1) (ci + 1) (Prim.Bytes.setU8 m idx (toByte (floatAt cov ci * k)))

/-- `clipMaskRef` with each row a tail call on `USize` indices (issue 1098: the game sets a
clip of the whole canvas each frame). The same expression for each byte; a `#guard` of
`Tests.lean` compares the two. -/
def clipMask (W n : Nat) (cov : Coverage) (old : Mask) : ByteArray := Id.run do
  let mut m := bzeros n
  let b := cov.box
  for j in [0:b.h] do
    m := clipRow cov.cov old b.w ((b.y + j) * W + b.x).toUSize (j * b.w).toUSize m
  return m

/-- What a draw paints: the paint, its coverage and alpha, the operator and the clip. -/
structure Draw where
  ready : Ready
  cov : Coverage
  alpha : Float
  op : Op
  clip : Mask

/-- The pixels a draw visits: its coverage box, or for an unbounded operator the canvas. -/
def Draw.visits (W H : Nat) (dr : Draw) : Box := if dr.op.unbounded then ⟨0, 0, W, H⟩ else dr.cov.box

/-- A draw whose coverage is inside the canvas visits only pixels of the canvas. -/
theorem Draw.visits_within (W H : Nat) (dr : Draw)
    (h : dr.cov.box.x + dr.cov.box.w ≤ W ∧ dr.cov.box.y + dr.cov.box.h ≤ H) :
    (dr.visits W H).x + (dr.visits W H).w ≤ W ∧ (dr.visits W H).y + (dr.visits W H).h ≤ H := by
  unfold Draw.visits; split <;> simp_all

/-- Composite one draw into `bm` (`W × H`), the reference: each visited pixel through
`blendPixel` on `Px` values. Only the pixels of `Draw.visits` are visited; the clip mask
decides the rest. `composite` gives the same bytes faster for source-over. -/
def compositeRef (W H : Nat) (bm : ByteArray) (dr : Draw) : ByteArray := Id.run do
  let mut out := bm
  let box := dr.cov.box
  let v := dr.visits W H
  let (x0, y0, w, h) := (v.x, v.y, v.w, v.h)
  let bounded := !dr.op.unbounded
  for j in [0:h] do
    let y := y0 + j
    -- A bounded operator changes only covered pixels: the row's span is enough.
    let (lo, hi) := if bounded then dr.cov.spans.getD j (0, w) else (0, w)
    for i in [lo:hi] do
      let x := x0 + i
      let idx := y * W + x
      let m := maskAt dr.clip idx
      if m <= 0 then continue
      let c := if x >= box.x && x < box.x + box.w && y >= box.y && y < box.y + box.h then
        dr.cov.cov[(y - box.y) * box.w + (x - box.x)]! else 0
      if c <= 0 && !dr.op.unbounded then continue
      let s := dr.ready.at x y
      let k := idx * 4
      let d : Px := ⟨out[k]!.toFloat / 255, out[k+1]!.toFloat / 255, out[k+2]!.toFloat / 255, out[k+3]!.toFloat / 255⟩
      let r := blendPixel dr.op s (c * dr.alpha) m d
      out := out.set! k (toByte r.r)
      out := out.set! (k+1) (toByte r.g)
      out := out.set! (k+2) (toByte r.b)
      out := out.set! (k+3) (toByte r.a)
  return out

/-! ### Source-over without `Px` values (issue 1098)

A frame of a canvas game paints its whole canvas several times (a background, a gradient sky
under a clip, overlays with `globalAlpha`). `compositeRef` builds three or four `Px` values a
pixel (heap objects). `compositeOver` does the same arithmetic on the channels one by one,
with three exact shortcuts. Each result byte is the byte of `compositeRef`:

- `overChannel` is the arithmetic of `blendPixel .sourceOver` for one channel, in the same
  order (theorem `blendPixel_sourceOver`).
- An opaque source with weight 1 inside the clip (mask byte 255) gives the source itself:
  `s * 1 * 1 + d * (1 - 1 * 1)` is `s + d * 0`, which is `s` (or `+0` for `s = -0`) for every
  finite `d`, and `d` is a byte over 255. The four bytes are made once a draw (a colour) or
  once a row (a gradient that is constant along rows) and written with no arithmetic.
- A solid colour with weight `alpha` inside the clip changes each channel by a function of its
  own destination byte only. For a large draw, `overTable` holds that function for the 256
  bytes, made by `overChannel` itself, so a pixel is four table reads.
- A linear gradient whose direction has no x part, under a transform with no x part in its
  y row (`rowConstant`), has one colour along each row: `(u - x0) * dx` is a zero, and a
  zero added to a number is that number; only the sign of a zero can change, and the gradient
  lookup clamps both zeros to the first entry.

The two Float facts are not proved in Lean (Float arithmetic is opaque to the kernel): the
`#guard` cases of `Tests.lean` compare `composite` with `compositeRef` byte for byte on
scenes that take every branch. -/

/-- One channel of source-over (`blendPixel .sourceOver`): source channel `s`, weight `w`
(coverage times global alpha), weighted source alpha `sa = s.a * w`, mask `m`, destination
channel `d`. -/
@[inline] def overChannel (s w sa m d : Float) : Float :=
  let r := s * w * 1 + d * (1 - sa)
  if m >= 1 then r else d + (r - d) * m

/-- `blendPixel .sourceOver` is `overChannel` on each channel. -/
theorem blendPixel_sourceOver (s : Px) (c m : Float) (d : Px) :
    blendPixel .sourceOver s c m d =
      if m <= 0 then d else
      ⟨overChannel s.r c (s.a * c) m d.r, overChannel s.g c (s.a * c) m d.g,
       overChannel s.b c (s.a * c) m d.b, overChannel s.a c (s.a * c) m d.a⟩ := by
  have hc : (Op.sourceOver == Op.clear) = false := rfl
  unfold blendPixel compose Px.scale overChannel
  by_cases h0 : m <= 0
  · simp [h0]
  · by_cases h1 : m >= 1 <;> simp [h0, h1, hc]

/-- The byte `overChannel` gives for each destination byte, for the four channels of a
solid colour `p` at weight `w` inside the clip (`m = 1`): 1,024 bytes, channel-major. -/
def overTable (p : Px) (w : Float) : ByteArray := Id.run do
  let sa := p.a * w
  let mut t := ByteArray.emptyWithCapacity 1024
  for ch in [0:4] do
    let s := if ch == 0 then p.r else if ch == 1 then p.g else if ch == 2 then p.b else p.a
    for db in [0:256] do
      t := t.push (toByte (overChannel s w sa 1 (db.toUInt8.toFloat / 255)))
  return t

/-- A linear gradient with one colour along each device row (see the section comment). -/
def rowConstant : Ready → Bool
  | .linear inv x0 _ dx _ _ _ =>
    -- `u` stays finite on the canvas (sides at most `maxSide`) when these are bounded.
    let small := fun (v : Float) => v.abs <= 1e15
    dx == 0 && inv.b == 0 && small inv.a && small inv.c && small inv.e && small x0
  | _ => false

/-- Pixels a solid draw must cover before `overTable` is made for it. -/
def tableMin : Nat := 2048

/-- `n` pixels of one row of `compositeOver`: column `x`, mask index `idx` (the pixel's
index in the canvas), coverage index `ci`. A tail call on `USize` indices: as a `for` loop
over `Nat` each pixel paid `Nat` arithmetic and a bounds closure per byte (issue 1098). -/
def overSpan (dr : Draw) (y : Nat) (fixed opaqueRow useTable : Bool) (s : Px)
    (b0 b1 b2 b3 : UInt8) (table : ByteArray) : Nat → Nat → USize → USize → ByteArray → ByteArray
  | 0, _, _, _, out => out
  | n+1, x, idx, ci, out =>
    let mb : UInt8 := match dr.clip with
      | none => 255
      | some b => byteAt b idx
    let c := floatAt dr.cov.cov ci
    if mb == 0 || c <= 0 then overSpan dr y fixed opaqueRow useTable s b0 b1 b2 b3 table n (x + 1) (idx + 1) (ci + 1) out else
    let w := c * dr.alpha
    let k := idx * 4
    let out :=
      if mb == 255 && w == 1 && opaqueRow then
        Prim.Bytes.setU8 (Prim.Bytes.setU8 (Prim.Bytes.setU8 (Prim.Bytes.setU8 out k b0) (k+1) b1) (k+2) b2) (k+3) b3
      else if mb == 255 && useTable && c == 1 then
        let out := Prim.Bytes.setU8 out k (byteAt table (byteAt out k).toUSize)
        let out := Prim.Bytes.setU8 out (k+1) (byteAt table (256 + (byteAt out (k+1)).toUSize))
        let out := Prim.Bytes.setU8 out (k+2) (byteAt table (512 + (byteAt out (k+2)).toUSize))
        Prim.Bytes.setU8 out (k+3) (byteAt table (768 + (byteAt out (k+3)).toUSize))
      else
        let p := if fixed then s else dr.ready.at x y
        let m := mb.toFloat / 255
        let sa := p.a * w
        let out := Prim.Bytes.setU8 out k (toByte (overChannel p.r w sa m ((byteAt out k).toFloat / 255)))
        let out := Prim.Bytes.setU8 out (k+1) (toByte (overChannel p.g w sa m ((byteAt out (k+1)).toFloat / 255)))
        let out := Prim.Bytes.setU8 out (k+2) (toByte (overChannel p.b w sa m ((byteAt out (k+2)).toFloat / 255)))
        Prim.Bytes.setU8 out (k+3) (toByte (overChannel p.a w sa m ((byteAt out (k+3)).toFloat / 255)))
    overSpan dr y fixed opaqueRow useTable s b0 b1 b2 b3 table n (x + 1) (idx + 1) (ci + 1) out

/-- `compositeRef` for a bounded draw with source-over, with no `Px` built for most pixels
(see the section comment). -/
def compositeOver (W : Nat) (bm : ByteArray) (dr : Draw) : ByteArray := Id.run do
  let mut out := bm
  let box := dr.cov.box
  let (solid, sp) := match dr.ready with
    | .solid p => (true, p)
    | _ => (false, Px.zero)
  let rowConst := rowConstant dr.ready
  let fixed := solid || rowConst
  let useTable := solid && box.w * box.h >= tableMin
  let table := if useTable then overTable sp dr.alpha else ByteArray.empty
  for j in [0:box.h] do
    let y := box.y + j
    let (lo, hi) := dr.cov.spans.getD j (0, box.w)
    if lo >= hi then continue
    let s := if solid then sp else if rowConst then dr.ready.at (box.x + lo) y else Px.zero
    let opaqueRow := fixed && s.a == 1
    out := overSpan dr y fixed opaqueRow useTable s (toByte s.r) (toByte s.g) (toByte s.b) (toByte s.a) table
      (hi - lo) (box.x + lo) (y * W + box.x + lo).toUSize (j * box.w + lo).toUSize out
  return out

/-- Composite one draw into `bm` (`W × H`): `compositeOver` for source-over, else
`compositeRef`. Same bytes as `compositeRef` (the `#guard` cases of `Tests.lean`). -/
def composite (W H : Nat) (bm : ByteArray) (dr : Draw) : ByteArray :=
  if dr.op == .sourceOver then compositeOver W bm dr else compositeRef W H bm dr

/-- The draw's result, only when it has the size of the bitmap it was given (a final
check: every canvas command keeps its bitmap's size, `Canvas.apply_size`). -/
def sameSize (old new : ByteArray) : ByteArray := if new.size == old.size then new else old

theorem sameSize_size (old new : ByteArray) : (sameSize old new).size = old.size := by
  unfold sameSize; split <;> simp_all

end L4Factoidal.PageCanvas
