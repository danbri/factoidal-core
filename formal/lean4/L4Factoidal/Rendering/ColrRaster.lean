import L4Factoidal.Rendering.SfntColr
import L4Factoidal.Rendering.SfntOutline
import L4Factoidal.Rendering.FontProvider
import L4Factoidal.PageCanvas.Raster

/-!
# Colour glyphs drawn by Lean

A colour glyph's `SfntColr.Program` drawn into a bitmap at a pixel size with the Canvas
2D rasteriser of `PageCanvas` (issue 1276): coverage of the outline glyphs (nonzero,
16 sample rows a pixel, exact along a row), the linear, two-circle radial and conic
gradients of Canvas 2D for COLR's linear, radial and sweep gradients, and the
compositing and blending operators of Compositing and Blending Level 1 for COLR's 28
composite modes, on a stack of premultiplied layers.

The bitmap is the glyph's clip box at that size, rounded out to whole pixels: the
drawing has no pixel outside it (`Raster.size_eq`). The scene draws it as an image
(`Layout`), one rectangle a glyph, so a page of emoji costs one primitive for each.

`Colour` holds a font's colour glyphs for the engine: each glyph's program and each
glyph's raster at each pixel size is computed once, when first asked for, and kept
with the font (`Thunk`), so a page that draws an emoji again, or lays out again,
does not draw it again. A glyph that uses the text colour (palette index 0xFFFF) is
drawn for each colour asked for and not kept.
-/
namespace L4Factoidal.Rendering.ColrRaster

open L4Factoidal.PageCanvas
open SfntColr (Program Step Fill CStop Ink)

private def fl (v : Int) : Float := if v < 0 then -(Float.ofNat v.natAbs) else Float.ofNat v.natAbs
private def floorI (v : Float) : Int := let f := v.floor; if f < 0 then -(Int.ofNat (-f).toUInt64.toNat) else Int.ofNat f.toUInt64.toNat
private def ceilI (v : Float) : Int := let f := v.ceil; if f < 0 then -(Int.ofNat (-f).toUInt64.toNat) else Int.ofNat f.toUInt64.toNat

/-- The outline commands of a glyph as a canvas path, in font units. -/
def pathOf (cmds : Array FontData.OutlineCommand) : Path :=
  cmds.foldl (init := {}) fun p c =>
    match c with
    | .move x y => p.moveTo (fl x) (fl y)
    | .line x y => p.lineTo (fl x) (fl y)
    | .quadratic cx cy x y => p.quadTo (fl cx) (fl cy) (fl x) (fl y)
    | .cubic ax ay bx by_ x y => p.cubicTo (fl ax) (fl ay) (fl bx) (fl by_) (fl x) (fl y)
    | .close => p.close

/-- A font's outlines, as `SfntOutline.outline` reads them. -/
structure Outlines where
  bytes : ByteArray
  dir : Array FontPolicy.TableRecord
  cff : Option SfntCff.Font := none

def Outlines.get (o : Outlines) (g : Nat) : Array FontData.OutlineCommand :=
  (SfntOutline.outline o.bytes o.dir g o.cff).toOption.getD #[]

/-- Largest side of a colour glyph's bitmap, in pixels. -/
def maxSide : Nat := 2048

/-- The box in font units: the clip box, or the bounds of the outlines the program fills
under their transforms (control points bound a curve). -/
def boxOf (o : Outlines) (p : Program) : Option (Float × Float × Float × Float) := Id.run do
  if p.box != (0,0,0,0) then
    let (a,b,c,d) := p.box
    return some (fl a, fl b, fl c, fl d)
  let mut box : Option (Float × Float × Float × Float) := none
  for s in p.steps do
    let (g,m) ← match s with
      | .fill (some g) m _ | .clip g m => pure (g,m)
      | _ => continue
    for c in o.get g do
      let pts : List (Int × Int) := match c with
        | .move x y | .line x y => [(x,y)]
        | .quadratic a b x y => [(a,b),(x,y)]
        | .cubic a b c d x y => [(a,b),(c,d),(x,y)]
        | .close => []
      for (x,y) in pts do
        let (u,v) := m.apply (fl x) (fl y)
        box := some <| match box with
          | none => (u,v,u,v)
          | some (a,b,c,d) => (min a u, min b v, max c u, max d v)
  return box

/-- A colour as the rasteriser takes it: the ink, or the text colour with the ink's alpha. -/
def inkColour (k : Ink) (fg : RGBA) : RGBA := if k.foreground then {fg with a := fg.a * k.rgba.a} else k.rgba

private def stopsOf (stops : Array CStop) (fg : RGBA) (scale : Float := 1) : Array Stop :=
  stops.map fun s => ⟨s.offset * scale, inkColour s.ink fg⟩

/-- A fill made ready for the device map `d` (font units to pixels). -/
def readyOf (d : Matrix) (f : Fill) (fg : RGBA) : Ready :=
  let grad := fun (m : Matrix) (kind : GradientKind) (stops : Array Stop) =>
    Style.ready (.gradient 0) (fun _ => some ⟨kind, stops⟩) (fun _ => none) (d.mul m) true
  match f with
  | .solid k => .solid (inkColour k fg).px
  | .linear m x0 y0 x1 y1 stops => grad m (.linear x0 y0 x1 y1) (stopsOf stops fg)
  | .radial m x0 y0 r0 x1 y1 r1 stops => grad m (.radial x0 y0 r0 x1 y1 r1) (stopsOf stops fg)
  | .sweep m cx cy start stop stops =>
    -- The colour line spans `stop - start` of a turn from `start`; the conic gradient
    -- of Canvas 2D spans a whole turn, so its stops are scaled to that part of it.
    let span := stop - start
    let span := if span > 0 && span ≤ tau then span else tau
    grad m (.conic start cx cy) (stopsOf stops fg (span / tau))

/-- The compositing operator of COLR composite mode `mode`; `none` for DEST (2), which
keeps the backdrop. -/
def opOf (mode : Nat) : Option Op :=
  match mode with
  | 0 => some .clear | 1 => some .copy | 2 => none | 3 => some .sourceOver | 4 => some .destinationOver
  | 5 => some .sourceIn | 6 => some .destinationIn | 7 => some .sourceOut | 8 => some .destinationOut
  | 9 => some .sourceAtop | 10 => some .destinationAtop | 11 => some .xor | 12 => some .lighter
  | 13 => some .screen | 14 => some .overlay | 15 => some .darken | 16 => some .lighten
  | 17 => some .colorDodge | 18 => some .colorBurn | 19 => some .hardLight | 20 => some .softLight
  | 21 => some .difference | 22 => some .exclusion | 23 => some .multiply | 24 => some .hue
  | 25 => some .saturation | 26 => some .color | _ => some .luminosity

/-- A colour glyph at one size: its pixels (straight RGBA, rows from the top), and where
its top-left corner is, in pixels, from the glyph's origin on the baseline (y down). -/
structure Raster where
  width : Nat
  height : Nat
  rgba : ByteArray
  left : Int
  top : Int
  size_eq : rgba.size = width * height * 4

/-- Premultiplied pixels to straight RGBA, `w × h` of them: exactly four bytes a pixel. -/
def straight (w h : Nat) (data : ByteArray) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := w*h*4) fun i =>
    let p := i.val / 4 * 4
    let a := (data.get! (p+3)).toNat
    if i.val % 4 == 3 then a.toUInt8
    else if a == 0 then 0
    else ((min 255 (((data.get! i.val).toNat * 255 + a/2) / a))).toUInt8)

theorem straight_size (w h : Nat) (data : ByteArray) : (straight w h data).size = w*h*4 := by
  simp [straight, ByteArray.size]

/-! Whole layers onto layers. A layer is premultiplied RGBA, four bytes a pixel, as
`PageCanvas.Bitmap`; these loops read both layers byte by byte, with no pattern sampling,
and skip transparent source pixels where the operator leaves the destination as it is. -/

@[inline] private def pxAt (b : ByteArray) (k : Nat) : Px :=
  ⟨b[k]!.toFloat / 255, b[k+1]!.toFloat / 255, b[k+2]!.toFloat / 255, b[k+3]!.toFloat / 255⟩

@[inline] private def putPx (b : ByteArray) (k : Nat) (p : Px) : ByteArray :=
  (((b.set! k (toByte p.r)).set! (k+1) (toByte p.g)).set! (k+2) (toByte p.b)).set! (k+3) (toByte p.a)

/-- `src` over `dst` where `src` is not transparent (source-over, premultiplied, in bytes). -/
def overLayer (src dst : ByteArray) : ByteArray := Id.run do
  let mut out := dst
  for i in [0:src.size/4] do
    let k := 4*i
    let sa := src[k+3]!.toNat
    if sa == 0 then continue
    if sa == 255 then
      out := (((out.set! k src[k]!).set! (k+1) src[k+1]!).set! (k+2) src[k+2]!).set! (k+3) 255
    else
      let keep := 255 - sa
      let mix := fun (s d : UInt8) => (min 255 (s.toNat + (d.toNat * keep + 127) / 255)).toUInt8
      out := (((out.set! k (mix src[k]! out[k]!)).set! (k+1) (mix src[k+1]! out[k+1]!)).set! (k+2) (mix src[k+2]! out[k+2]!)).set! (k+3) (mix src[k+3]! out[k+3]!)
  return out

/-- `src` composited onto `dst` with `op` at every pixel (Compositing and Blending §9-10).
A bounded operator leaves the destination where the source is transparent. -/
def compositeLayer (op : Op) (src dst : ByteArray) : ByteArray := Id.run do
  if op == .sourceOver then return overLayer src dst
  let mut out := dst
  for i in [0:src.size/4] do
    let k := 4*i
    if !op.unbounded && src[k+3]! == 0 then continue
    out := putPx out k (if op == .clear then Px.zero else compose op (pxAt src k) (pxAt out k))
  return out

/-- `src` through the coverage `cov` (a glyph outline) over `dst`. -/
def clipLayer (W : Nat) (cov : Coverage) (src dst : ByteArray) : ByteArray := Id.run do
  let mut out := dst
  let box := cov.box
  for j in [0:box.h] do
    let (lo,hi) := cov.spans.getD j (0,box.w)
    for i in [lo:hi] do
      let c := cov.cov[j*box.w+i]!
      if c <= 0 then continue
      let k := 4*((box.y+j)*W + box.x+i)
      if src[k+3]! == 0 then continue
      out := putPx out k (compose .sourceOver ((pxAt src k).scale c) (pxAt out k))
  return out

/-- Draw a program at `px` pixels to the em (`upem` font units), with `fg` for the text
colour. `none` when the glyph is empty or its box is larger than `maxSide`. -/
def draw (o : Outlines) (upem : Nat) (p : Program) (px : Nat) (fg : RGBA) : Option Raster := Id.run do
  if upem == 0 || px == 0 then return none
  let some (x0,y0,x1,y1) := boxOf o p | return none
  let s := nf px / nf upem
  let ox := floorI (x0*s)
  let oy := floorI (-y1*s)
  let wi := ceilI (x1*s) - ox
  let hi := ceilI (-y0*s) - oy
  if wi ≤ 0 || hi ≤ 0 || wi > maxSide || hi > maxSide then return none
  let (W,H) := (wi.toNat, hi.toNat)
  -- Font units (y up) to the pixels of the box (y down).
  let d : Matrix := {a := s, d := -s, e := -fl ox, f := -fl oy}
  let blank := (Bitmap.blank W H).data
  let full := rectCoverage W H 0 0 (nf W) (nf H)
  -- Each outline read once a drawing: a glyph is often filled several times (layers, scales).
  let mut paths : Std.HashMap Nat Path := {}
  for st in p.steps do
    let g? := match st with | .fill (some g) .. | .clip g _ => some g | _ => none
    if let some g := g? then
      unless paths.contains g do paths := paths.insert g (pathOf (o.get g))
  let read := paths
  let coverOf := fun (g : Nat) (m : Matrix) =>
    coverage W H (edgesOf (((read.getD g {}).map (d.mul m)).flatten 0.1)) .nonzero
  let put := fun (dst : ByteArray) (dr : Draw) => sameSize dst (composite W H dst dr)
  let mut stack : Array ByteArray := #[blank]
  for st in p.steps do
    match st with
    | .fill glyph m f =>
      let cov := match glyph with | some g => coverOf g m | none => full
      -- Taken off the stack first, so the layer has one owner and is changed in place.
      let top := stack.back!
      stack := stack.pop
      stack := stack.push (put top ⟨readyOf d f fg, cov, 1, .sourceOver, none⟩)
    | .push => stack := stack.push blank
    | .clip g m =>
      let src := stack.back!
      stack := stack.pop
      let top := stack.back!
      stack := stack.pop
      stack := stack.push (sameSize top (clipLayer W (coverOf g m) src top))
    | .composite mode =>
      let src := stack.back!
      stack := stack.pop
      let back := stack.back!
      match opOf mode with
      | some op =>
        stack := stack.pop
        stack := stack.push (sameSize back (compositeLayer op src back))
      | none => pure ()
    | .merge =>
      let src := stack.back!
      stack := stack.pop
      let top := stack.back!
      stack := stack.pop
      stack := stack.push (sameSize top (overLayer src top))
  return some ⟨W, H, straight W H stack[0]!, ox, oy, straight_size W H _⟩

/-- A drawn colour glyph is a bitmap of its box and nothing else: four bytes for each
of its `width × height` pixels. Every step draws through `Raster.composite`, which
visits only pixels of the box (`PageCanvas.coverage_within`, `Draw.visits_within`) and
keeps the layer's size (`sameSize_size`); so no paint lands outside the clip box. -/
theorem Raster.inBox (r : Raster) : r.rgba.size = r.width * r.height * 4 := r.size_eq

/-! ## A font's colour glyphs -/

/-- The colour glyphs of one font, each computed when first asked for and then kept. -/
structure Colour where
  table : SfntColr.Table
  outlines : Outlines
  upem : Nat
  /-- A number for the font, so that each raster has its own image id. -/
  key : Nat
  programs : Array (Thunk (Option Program))
  /-- For each base glyph, the raster at each pixel size from 0 to 512. -/
  rasters : Array (Thunk (Array (Thunk (Option Raster))))

/-- Image ids of colour glyphs start here, above those of pictures and icons. -/
def idBase : Nat := 2^40

def maxPixels : Nat := 512

def Colour.make (table : SfntColr.Table) (o : Outlines) (upem key : Nat) (limits : FontPolicy.Limits := {}) : Colour :=
  let n := table.baseCount
  let programs := (Array.range n).map fun k =>
    Thunk.mk fun _ => (SfntColr.compile o.bytes table (table.baseGlyph o.bytes k) limits).toOption.join
  let rasters := (Array.range n).map fun k =>
    Thunk.mk fun _ => (Array.range (maxPixels+1)).map fun px =>
      Thunk.mk fun _ => (programs[k]!.get).bind fun p => draw o upem p px ⟨0,0,0,1⟩
  {table, outlines := o, upem, key, programs, rasters}

/-- The image of base glyph number `k` at `px` pixels in text colour `fg` (0..1). -/
def Colour.image (c : Colour) (k px : Nat) (fg : Color) : Option FontProvider.ColourImage := do
  if px == 0 || px > maxPixels then none
  let program ← (← c.programs[k]?).get
  let toByte := fun (v : Float) => (max 0 (min 255 (v*255).round)).toUInt8.toNat
  let (r,tint) ← if program.foreground then
      let rgb := (toByte fg.r, toByte fg.g, toByte fg.b)
      (draw c.outlines c.upem program px ⟨nf rgb.1, nf rgb.2.1, nf rgb.2.2, 1⟩).map
        (·, 1 + rgb.1*65536 + rgb.2.1*256 + rgb.2.2)
    else (((← c.rasters[k]?).get)[px]!.get).map (·, 0)
  let id := idBase + ((c.key % 2^24) * 2^24 + k * (maxPixels+1) + px) + tint * 2^64
  return ⟨⟨r.width, r.height, r.rgba⟩, r.left, r.top, id⟩

end L4Factoidal.Rendering.ColrRaster
