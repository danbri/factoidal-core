import L4Factoidal.Rendering.FontPolicy
import L4Factoidal.PageCanvas.Geometry

/-!
# Colour glyphs: the COLR and CPAL tables

OpenType 1.9.1 §COLR (versions 0 and 1) and §CPAL, read by Lean
(issue 1276). A colour glyph is a graph of paint operations over outline glyphs of
the same font. This module checks the tables and turns the graph of one base glyph
into a `Program`: a flat list of drawing steps on a stack of layers, in font units,
which `ColrRaster` draws with the Canvas 2D rasteriser of `PageCanvas`.

- `read`: the tables' headers, with every record array inside its table, the base
  glyph lists sorted (they are searched), and palette 0 of CPAL.
- `compile`: the paint graph of one base glyph, walked with a depth bound
  (`FontPolicy.Limits.colrDepth`) and a node budget (`maxNodes`), so a hostile font
  with a cycle (a `PaintColrGlyph` that names itself) or a graph that shares nodes to
  grow without end gives an error, not a hang. Palette indices are resolved here:
  an index outside the palette is an error (`resolveInk_ok`).
- `Program`: the steps, with the proofs that there are at most `maxSteps` of them and
  that their layer stack is well nested within `maxStack` (`Program.wellNested`).

Version 1 paints: layers, solid colours, linear, radial and sweep gradients, every
transform (affine, translate, scale, rotate, skew, about a centre or not), glyphs,
colour glyphs, composites in all 28 modes, and clip boxes. The variable forms
(`PaintVar*`) are read with their default values: the engine reads no variations.
Colour lines extend by `pad` only; `repeat` and `reflect` draw as `pad` (Noto Color
Emoji uses `pad` alone).
-/
namespace L4Factoidal.Rendering.SfntColr

open L4Factoidal.PageCanvas (Matrix RGBA)
open FontPolicy (TableRecord)

private def u8 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat
private def u16 (b : ByteArray) (i : Nat) : Nat := u8 b i * 256 + u8 b (i+1)
private def u24 (b : ByteArray) (i : Nat) : Nat := u16 b i * 256 + u8 b (i+2)
private def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i * 65536 + u16 b (i+2)
private def i16 (b : ByteArray) (i : Nat) : Int :=
  let v := u16 b i; if v ≥ 32768 then (v : Int) - 65536 else v
private def i32 (b : ByteArray) (i : Nat) : Int :=
  let v := u32 b i; if v ≥ 2147483648 then (v : Int) - 4294967296 else v
private def fl (v : Int) : Float := if v < 0 then -(Float.ofNat v.natAbs) else Float.ofNat v.natAbs
/-- F2DOT14 and Fixed (16.16). -/
private def f2dot14 (b : ByteArray) (i : Nat) : Float := fl (i16 b i) / 16384
private def fixed (b : ByteArray) (i : Nat) : Float := fl (i32 b i) / 65536

/-! ## Tables -/

/-- A colour: palette 0's entry, or the text colour (palette index 0xFFFF) with an alpha. -/
structure Ink where
  rgba : RGBA
  foreground : Bool := false
  deriving Repr, Inhabited, BEq

/-- Where the tables are, as absolute byte offsets in the font file, and palette 0. -/
structure Table where
  start : Nat
  stop : Nat
  version : Nat
  numGlyphs : Nat
  /-- Version 0: base glyph records and layer records (offset, count). -/
  baseV0 : Nat × Nat
  layersV0 : Nat × Nat
  /-- Version 1: BaseGlyphList, LayerList and ClipList (offset of the list, count; 0 for none). -/
  baseV1 : Nat × Nat := (0,0)
  layerList : Nat × Nat := (0,0)
  clipList : Nat × Nat := (0,0)
  palette : Array RGBA
  deriving Repr

/-- Paint nodes visited for one colour glyph: Noto Color Emoji needs at most 6,665. -/
def maxNodes : Nat := 32768

/-- Most entries of one palette, and most stops of one colour line. -/
def maxPaletteEntries : Nat := 65535
def maxStops : Nat := 256

private def tableOf (dir : Array TableRecord) (tag : String) : Option TableRecord := dir.find? (·.tag == tag)

private def within (t : Table) (off len : Nat) : Bool := t.start ≤ off && off + len ≤ t.stop

/-- Glyph ids of `count` records of `size` bytes from `off`, strictly increasing. -/
private def sortedIds (b : ByteArray) (off count size : Nat) : Bool := Id.run do
  for k in [1:count] do
    if u16 b (off + size*k) ≤ u16 b (off + size*(k-1)) then return false
  return true

/-- Palette 0 of CPAL (version 0 or 1), as straight RGBA. -/
def readPalette (b : ByteArray) (t : TableRecord) : Except String (Array RGBA) := do
  let o := t.offset
  if t.length < 14 then throw "font.table.colr: CPAL shorter than its header"
  let version := u16 b o
  if version > 1 then throw s!"font.table.colr: CPAL version {version}"
  let entries := u16 b (o+2)
  let palettes := u16 b (o+4)
  let records := u16 b (o+6)
  let arrayOff := u32 b (o+8)
  if palettes == 0 then throw "font.table.colr: CPAL has no palette"
  if 12 + 2*palettes > t.length then throw "font.table.colr: CPAL palette indices out of bounds"
  if arrayOff + 4*records > t.length then throw "font.table.colr: CPAL colour records out of bounds"
  let first := u16 b (o+12)
  if first + entries > records then throw "font.table.colr: CPAL palette 0 out of its records"
  let mut out := Array.mkEmpty entries
  for k in [0:entries] do
    let r := o + arrayOff + 4*(first+k)
    -- BGRA bytes.
    out := out.push ⟨Float.ofNat (u8 b (r+2)), Float.ofNat (u8 b (r+1)), Float.ofNat (u8 b r), Float.ofNat (u8 b (r+3)) / 255⟩
  return out

/-- A version 1 list whose offset is at `at_`: (offset, count), with its header of
`head` bytes and `count` records of `size` bytes inside the table; (0,0) for none. -/
private def listAt (b : ByteArray) (t : Table) (at_ head size : Nat) (count : Nat → Nat) :
    Except String (Nat × Nat) := do
  let rel := u32 b at_
  if rel == 0 then return (0,0)
  let off := t.start + rel
  if !within t off head then throw "font.table.colr: list header out of bounds"
  let n := count off
  if !within t off (head + size*n) then throw "font.table.colr: list records out of bounds"
  return (off,n)

/-- The COLR and CPAL tables of a font, checked. `none` when the font has no COLR. -/
def read (b : ByteArray) (dir : Array TableRecord) (numGlyphs : Nat) : Except String (Option Table) := do
  let some c := tableOf dir "COLR" | return none
  let some p := tableOf dir "CPAL" | throw "font.table.colr: COLR without CPAL"
  let palette ← readPalette b p
  let o := c.offset
  if c.length < 14 then throw "font.table.colr: COLR shorter than its header"
  let version := u16 b o
  if version > 1 then throw s!"font.table.colr: COLR version {version}"
  let t0 : Table :=
    { start := o, stop := o + c.length, version := version, numGlyphs := numGlyphs, palette := palette
      baseV0 := (o + u32 b (o+4), u16 b (o+2)), layersV0 := (o + u32 b (o+8), u16 b (o+12)) }
  let (bo,bn) := t0.baseV0
  let (lo,ln) := t0.layersV0
  if bn > 0 && !within t0 bo (6*bn) then throw "font.table.colr: base glyph records out of bounds"
  if ln > 0 && !within t0 lo (4*ln) then throw "font.table.colr: layer records out of bounds"
  if !sortedIds b bo bn 6 then throw "font.table.colr: base glyph records not sorted"
  for k in [0:bn] do
    let r := bo + 6*k
    if u16 b (r+2) + u16 b (r+4) > ln then throw "font.table.colr: base glyph layers out of the layer records"
  if version == 0 then return some t0
  if c.length < 34 then throw "font.table.colr: version 1 header out of bounds"
  let baseV1 ← listAt b t0 (o+14) 4 6 (u32 b ·)
  let layerList ← listAt b t0 (o+18) 4 4 (u32 b ·)
  let clipList ← listAt b t0 (o+22) 5 7 (fun off => u32 b (off+1))
  if baseV1.1 > 0 && !sortedIds b (baseV1.1 + 4) baseV1.2 6 then throw "font.table.colr: base glyph paint records not sorted"
  if clipList.2 > 0 && u8 b clipList.1 != 1 then throw "font.table.colr: clip list format"
  return some {t0 with baseV1, layerList, clipList}

/-- Binary search for `g` in `count` records of `size` bytes from `off` (glyph id first). -/
def search (b : ByteArray) (off count size g : Nat) : Option Nat := Id.run do
  let mut lo := 0
  let mut hi := count
  -- Each step halves `hi - lo`; 32 steps cover any u32 count.
  for _ in [0:33] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let id := u16 b (off + size*mid)
    if id == g then return some mid
    if id < g then lo := mid + 1 else hi := mid
  return none

/-- The index of base glyph `g` among all base glyphs (version 1 records first, then
version 0), for a cache. -/
def Table.baseIndex (t : Table) (b : ByteArray) (g : Nat) : Option Nat :=
  match search b (t.baseV1.1 + 4) t.baseV1.2 6 g with
  | some k => some k
  | none => (search b t.baseV0.1 t.baseV0.2 6 g).map (t.baseV1.2 + ·)

def Table.baseCount (t : Table) : Nat := t.baseV1.2 + t.baseV0.2

/-- The glyph id of base glyph number `k` (see `baseIndex`). -/
def Table.baseGlyph (t : Table) (b : ByteArray) (k : Nat) : Nat :=
  if k < t.baseV1.2 then u16 b (t.baseV1.1 + 4 + 6*k) else u16 b (t.baseV0.1 + 6*(k - t.baseV1.2))

/-- The clip box of `g` in font units (xMin, yMin, xMax, yMax), from the ClipList. -/
def Table.clipBox (t : Table) (b : ByteArray) (g : Nat) : Option (Int × Int × Int × Int) := Id.run do
  let (off,n) := t.clipList
  if n == 0 then return none
  -- Clips are sorted by their first glyph and do not overlap.
  let mut lo := 0
  let mut hi := n
  for _ in [0:33] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let r := off + 5 + 7*mid
    let first := u16 b r
    let last := u16 b (r+2)
    if g < first then hi := mid
    else if g > last then lo := mid + 1
    else
      let box := off + u24 b (r+4)
      if !within t box 9 then return none
      let fmt := u8 b box
      if fmt != 1 && fmt != 2 then return none
      return some (i16 b (box+1), i16 b (box+3), i16 b (box+5), i16 b (box+7))
  return none

/-! ## Inks: palette indices -/

/-- Palette index `i` with alpha `alpha`: 0xFFFF is the text colour; any other index
must be inside palette 0. -/
def resolveInk (palette : Array RGBA) (i : Nat) (alpha : Float) : Except String Ink :=
  if i == 0xFFFF then .ok ⟨⟨0,0,0,max 0 (min 1 alpha)⟩,true⟩
  else match palette[i]? with
    | some c => .ok ⟨{c with a := c.a * max 0 (min 1 alpha)},false⟩
    | none => .error s!"font.table.colr: palette index {i} outside the {palette.size} entries"

/-- An ink from the palette is a colour of the palette: a font can not reach outside
palette 0 through an index. -/
theorem resolveInk_ok (palette : Array RGBA) (i : Nat) (alpha : Float) (k : Ink)
    (h : resolveInk palette i alpha = .ok k) : i = 0xFFFF ∨ i < palette.size := by
  unfold resolveInk at h
  split at h
  · exact Or.inl (by simp_all)
  · right
    split at h
    · rename_i c hc; exact (Array.getElem?_eq_some_iff.mp hc).1
    · cases h

/-! ## Programs -/

/-- A colour stop: its offset on the colour line and its ink. -/
structure CStop where
  offset : Float
  ink : Ink
  deriving Repr, Inhabited

/-- What a step fills with. `m` maps the paint's own space to the glyph's root space
(font units, y up). -/
inductive Fill where
  | solid (ink : Ink)
  | linear (m : Matrix) (x0 y0 x1 y1 : Float) (stops : Array CStop)
  | radial (m : Matrix) (x0 y0 r0 x1 y1 r1 : Float) (stops : Array CStop)
  /-- Angles in radians, counter-clockwise in the paint's space. -/
  | sweep (m : Matrix) (cx cy start stop : Float) (stops : Array CStop)
  deriving Repr, Inhabited

/-- Compositing modes of COLR version 1, in table order (0 to 27). -/
def compositeModes : Nat := 28

/-- One step on the stack of layers. Every layer is the size of the clip box. -/
inductive Step where
  /-- Fill the outline of `glyph` (or, with none, the whole box) under `m` onto the top layer. -/
  | fill (glyph : Option Nat) (m : Matrix) (paint : Fill)
  /-- A new transparent layer on top. -/
  | push
  /-- Take the top layer off and draw it through the outline of `glyph` under `m` onto the next. -/
  | clip (glyph : Nat) (m : Matrix)
  /-- Take the top layer (source) off and composite it onto the next (backdrop) with mode `mode`. -/
  | composite (mode : Nat)
  /-- Take the top layer off and draw it over the next. -/
  | merge
  deriving Repr, Inhabited

/-- The stack depth after each step from `depth`, or `none` when a step takes a layer
that is not there or the depth passes `limit`. A program starts and ends at depth 1. -/
def stackAfter (steps : Array Step) (limit : Nat) : Option Nat := Id.run do
  let mut depth := 1
  for s in steps do
    match s with
    | .fill .. => pure ()
    | .push =>
      depth := depth + 1
      if depth > limit then return none
    | .clip .. | .composite _ | .merge =>
      if depth < 2 then return none
      depth := depth - 1
  return some depth

/-- Most steps of one program, and most layers on its stack. -/
def maxSteps : Nat := 65536
def maxStack : Nat := 130

/-- A colour glyph ready to draw: its steps, its box in font units, and whether it uses
the text colour. The proofs say that the steps are few and their stack well nested. -/
structure Program where
  steps : Array Step
  box : Int × Int × Int × Int
  foreground : Bool
  steps_le : steps.size ≤ maxSteps
  wellNested : stackAfter steps maxStack = some 1

instance : Repr Program where
  reprPrec p _ := s!"Program ({p.steps.size} steps)"

/-- A program has at most `maxSteps` steps (hostile fonts: a bounded drawing). -/
theorem Program.size_bounded (p : Program) : p.steps.size ≤ maxSteps := p.steps_le
/-- A program never takes a layer that is not there, and holds at most `maxStack`. -/
theorem Program.stack_bounded (p : Program) : stackAfter p.steps maxStack = some 1 := p.wellNested

/-! ## Compiling a paint graph -/

/-- What compiling one base glyph has made and spent. -/
structure Work where
  steps : Array Step := #[]
  nodes : Nat := 0
  foreground : Bool := false

abbrev M := StateT Work (Except String)

private def visit (limit : Nat) : M Unit := do
  let w ← get
  if w.nodes + 1 > limit then throw "font.table.colr: paint graph larger than the node budget"
  set {w with nodes := w.nodes + 1}

private def emit (s : Step) : M Unit := modify fun w => {w with steps := w.steps.push s}

private def noteInk (k : Ink) : M Ink := do
  if k.foreground then modify fun w => {w with foreground := true}
  return k

/-- The affine map `[xx xy dx; yx yy dy]` as a `Matrix`. -/
private def affine (xx yx xy yy dx dy : Float) : Matrix := {a := xx, b := yx, c := xy, d := yy, e := dx, f := dy}

private def aroundCentre (m : Matrix) (cx cy : Float) : Matrix :=
  (Matrix.translate cx cy).mul (m.mul (Matrix.translate (-cx) (-cy)))

/-- The transform of a transform paint (formats 12 to 31) at `off`, and its child. -/
private def transformOf (b : ByteArray) (t : Table) (fmt off : Nat) : Except String (Matrix × Nat) := do
  let child := off + u24 b (off+1)
  let at_ := fun (k : Nat) => off + 4 + k
  let m : Matrix ← match fmt with
    | 12 | 13 =>
      let a := off + u24 b (off+4)
      if !within t a (if fmt == 13 then 28 else 24) then throw "font.table.colr: affine out of bounds"
      pure (affine (fixed b a) (fixed b (a+4)) (fixed b (a+8)) (fixed b (a+12)) (fixed b (a+16)) (fixed b (a+20)))
    | 14 | 15 => pure (Matrix.translate (fl (i16 b (at_ 0))) (fl (i16 b (at_ 2))))
    | 16 | 17 => pure (Matrix.scale (f2dot14 b (at_ 0)) (f2dot14 b (at_ 2)))
    | 18 | 19 => pure (aroundCentre (Matrix.scale (f2dot14 b (at_ 0)) (f2dot14 b (at_ 2))) (fl (i16 b (at_ 4))) (fl (i16 b (at_ 6))))
    | 20 | 21 => let s := f2dot14 b (at_ 0); pure (Matrix.scale s s)
    | 22 | 23 => let s := f2dot14 b (at_ 0); pure (aroundCentre (Matrix.scale s s) (fl (i16 b (at_ 2))) (fl (i16 b (at_ 4))))
    | 24 | 25 => pure (Matrix.rotate (f2dot14 b (at_ 0) * PageCanvas.pi))
    | 26 | 27 => pure (aroundCentre (Matrix.rotate (f2dot14 b (at_ 0) * PageCanvas.pi)) (fl (i16 b (at_ 2))) (fl (i16 b (at_ 4))))
    | 28 | 29 | 30 | 31 =>
      -- fontTools `Transform.skew(-x, y)`: [1 tan(-x); tan(y) 1].
      let x := f2dot14 b (at_ 0) * PageCanvas.pi
      let y := f2dot14 b (at_ 2) * PageCanvas.pi
      let k := affine 1 (Float.tan y) (Float.tan (-x)) 1 0 0
      if fmt ≥ 30 then pure (aroundCentre k (fl (i16 b (at_ 4))) (fl (i16 b (at_ 6)))) else pure k
    | _ => throw s!"font.table.colr: paint format {fmt} is not a transform"
  if !m.finite then throw "font.table.colr: transform not finite"
  return (m,child)

/-- The size of a transform paint's fixed part, for its bounds check. -/
private def transformSize (fmt : Nat) : Nat :=
  match fmt with
  | 12 | 13 => 7 | 14 | 15 => 8 | 16 | 17 => 8 | 18 | 19 => 12 | 20 | 21 => 6 | 22 | 23 => 10
  | 24 | 25 => 6 | 26 | 27 => 10 | 28 | 29 => 8 | _ => 12

/-- The stops of the colour line at `off` (`var`: VarColorLine, 10 bytes a stop). -/
private def colorLine (b : ByteArray) (t : Table) (off : Nat) (var : Bool) : M (Array CStop) := do
  if !within t off 3 then throw "font.table.colr: colour line out of bounds"
  let n := u16 b (off+1)
  let size := if var then 10 else 6
  if n == 0 || n > maxStops then throw s!"font.table.colr: colour line with {n} stops"
  if !within t (off+3) (size*n) then throw "font.table.colr: colour stops out of bounds"
  let mut out := Array.mkEmpty n
  for k in [0:n] do
    let s := off + 3 + size*k
    let ink ← noteInk (← resolveInk t.palette (u16 b (s+2)) (f2dot14 b (s+4)))
    out := out.push ⟨f2dot14 b s, ink⟩
  return out

/-- The fill of a paint of formats 2 to 9 at `off`, under `m`. -/
private def fillAt (b : ByteArray) (t : Table) (fmt off : Nat) (m : Matrix) : M Fill := do
  let var := fmt % 2 == 1
  match fmt with
  | 2 | 3 =>
    if !within t off 5 then throw "font.table.colr: solid paint out of bounds"
    return .solid (← noteInk (← resolveInk t.palette (u16 b (off+1)) (f2dot14 b (off+3))))
  | 4 | 5 =>
    if !within t off 16 then throw "font.table.colr: linear gradient out of bounds"
    let stops ← colorLine b t (off + u24 b (off+1)) var
    let p := fun (k : Nat) => fl (i16 b (off + 4 + 2*k))
    let (x0,y0,x1,y1,x2,y2) := (p 0,p 1,p 2,p 3,p 4,p 5)
    -- OpenType: the gradient runs from p0 to the projection of p1 on the line through
    -- p0 perpendicular to p0p2; with p0 = p2 the rotation is undefined and p1 is used.
    let (nx,ny) := (y2-y0, -(x2-x0))
    let nn := nx*nx + ny*ny
    let (ex,ey) := if nn == 0 then (x1,y1) else
      let k := ((x1-x0)*nx + (y1-y0)*ny) / nn
      (x0 + k*nx, y0 + k*ny)
    return .linear m x0 y0 ex ey stops
  | 6 | 7 =>
    if !within t off 16 then throw "font.table.colr: radial gradient out of bounds"
    let stops ← colorLine b t (off + u24 b (off+1)) var
    return .radial m (fl (i16 b (off+4))) (fl (i16 b (off+6))) (Float.ofNat (u16 b (off+8)))
      (fl (i16 b (off+10))) (fl (i16 b (off+12))) (Float.ofNat (u16 b (off+14))) stops
  | _ =>
    if !within t off 12 then throw "font.table.colr: sweep gradient out of bounds"
    let stops ← colorLine b t (off + u24 b (off+1)) var
    return .sweep m (fl (i16 b (off+4))) (fl (i16 b (off+6)))
      (f2dot14 b (off+8) * PageCanvas.pi) (f2dot14 b (off+10) * PageCanvas.pi) stops

/-- The fill that the paint at `off` is, when it is one (a solid colour or a gradient
under any transforms), under `m`. `none` for anything else. -/
def fillOf (b : ByteArray) (t : Table) (limit : Nat) : Nat → Nat → Matrix → M (Option Fill)
  | 0, _, _ => throw "font.table.colr: paint graph deeper than the depth limit"
  | fuel+1, off, m => do
    if !within t off 1 then throw "font.table.colr: paint out of bounds"
    let fmt := u8 b off
    if 2 ≤ fmt && fmt ≤ 9 then return some (← fillAt b t fmt off m)
    if 12 ≤ fmt && fmt ≤ 31 then
      if !within t off (transformSize fmt) then throw "font.table.colr: transform paint out of bounds"
      let (k,child) ← transformOf b t fmt off
      visit limit
      return ← fillOf b t limit fuel child (m.mul k)
    return none

/-- The paint graph from the paint at `off`, under `m`, as steps. `fuel` bounds the depth. -/
def walk (b : ByteArray) (t : Table) (limit : Nat) : Nat → Nat → Matrix → M Unit
  | 0, _, _ => throw "font.table.colr: paint graph deeper than the depth limit"
  | fuel+1, off, m => do
    visit limit
    if !within t off 1 then throw "font.table.colr: paint out of bounds"
    let fmt := u8 b off
    match fmt with
    | 1 =>
      if !within t off 6 then throw "font.table.colr: layers paint out of bounds"
      let n := u8 b (off+1)
      let first := u32 b (off+2)
      let (lo,ln) := t.layerList
      if first + n > ln then throw "font.table.colr: layers outside the layer list"
      for k in [0:n] do
        walk b t limit fuel (lo + u32 b (lo + 4 + 4*(first+k))) m
    | 10 =>
      if !within t off 6 then throw "font.table.colr: glyph paint out of bounds"
      let child := off + u24 b (off+1)
      let g := u16 b (off+4)
      if g ≥ t.numGlyphs then throw "font.table.colr: glyph paint names no glyph"
      match ← fillOf b t limit fuel child m with
      | some f => emit (.fill (some g) m f)
      | none =>
        emit .push
        walk b t limit fuel child m
        emit (.clip g m)
    | 11 =>
      if !within t off 3 then throw "font.table.colr: colour glyph paint out of bounds"
      let g := u16 b (off+1)
      let (bo,bn) := t.baseV1
      match search b (bo+4) bn 6 g with
      | some k => walk b t limit fuel (bo + u32 b (bo + 4 + 6*k + 2)) m
      | none => throw "font.table.colr: colour glyph paint names no base glyph"
    | 32 =>
      if !within t off 8 then throw "font.table.colr: composite paint out of bounds"
      let mode := u8 b (off+4)
      if mode ≥ compositeModes then throw s!"font.table.colr: composite mode {mode}"
      emit .push
      walk b t limit fuel (off + u24 b (off+5)) m
      emit .push
      walk b t limit fuel (off + u24 b (off+1)) m
      emit (.composite mode)
      emit .merge
    | _ =>
      if 2 ≤ fmt && fmt ≤ 9 then emit (.fill none m (← fillAt b t fmt off m))
      else if 12 ≤ fmt && fmt ≤ 31 then
        if !within t off (transformSize fmt) then throw "font.table.colr: transform paint out of bounds"
        let (k,child) ← transformOf b t fmt off
        walk b t limit fuel child (m.mul k)
      else throw s!"font.table.colr: paint format {fmt}"

/-- The steps of base glyph `g`, or `none` when it is not a colour glyph. -/
private def workOf (b : ByteArray) (t : Table) (g : Nat) (limits : FontPolicy.Limits) :
    Except String (Option Work) := do
  let (bo,bn) := t.baseV1
  if let some k := search b (bo+4) bn 6 g then
    let off := bo + u32 b (bo + 4 + 6*k + 2)
    let ((),w) ← (walk b t maxNodes (min limits.colrDepth 64) off {}).run {}
    return some w
  let some k := search b t.baseV0.1 t.baseV0.2 6 g | return none
  let r := t.baseV0.1 + 6*k
  let first := u16 b (r+2)
  let mut w : Work := {}
  for j in [0:u16 b (r+4)] do
    let l := t.layersV0.1 + 4*(first+j)
    let layer := u16 b l
    if layer ≥ t.numGlyphs then throw "font.table.colr: layer names no glyph"
    let ink ← resolveInk t.palette (u16 b (l+2)) 1
    w := {w with steps := w.steps.push (.fill (some layer) {} (.solid ink)),
                 foreground := w.foreground || ink.foreground}
  return some w

/-- The program of base glyph `g`, or `none` when `g` is not a colour glyph. The depth
limit is the policy's (`colrDepth`), the node budget `maxNodes`. A glyph with no clip box
has the box (0,0,0,0); `ColrRaster` then bounds the outlines it fills. -/
def compile (b : ByteArray) (t : Table) (g : Nat) (limits : FontPolicy.Limits := {}) :
    Except String (Option Program) := do
  let some work ← workOf b t g limits | return none
  let box := (t.clipBox b g).getD (0,0,0,0)
  if h : work.steps.size ≤ maxSteps then
    match hs : stackAfter work.steps maxStack with
    | some 1 => return some ⟨work.steps, box, work.foreground, h, hs⟩
    | _ => throw "font.table.colr: layer stack too deep"
  else throw "font.table.colr: too many paint steps"

end L4Factoidal.Rendering.SfntColr
