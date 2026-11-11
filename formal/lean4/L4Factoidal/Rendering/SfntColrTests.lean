import L4Factoidal.Rendering.ColrRaster

/-! Tests of `SfntColr` and `ColrRaster` on small COLR and CPAL tables made here,
byte by byte: well-formed glyphs of versions 0 and 1, and hostile ones (a palette
index outside the palette, a colour glyph that names itself, layers that name
themselves, a record list longer than its table). -/
namespace L4Factoidal.Rendering.SfntColrTests

open SfntColr
open FontPolicy (TableRecord)

private def be16 (v : Nat) : List UInt8 := [(v / 256 % 256).toUInt8, (v % 256).toUInt8]
private def be24 (v : Nat) : List UInt8 := [(v / 65536 % 256).toUInt8, (v / 256 % 256).toUInt8, (v % 256).toUInt8]
private def be32 (v : Nat) : List UInt8 := be16 (v / 65536) ++ be16 (v % 65536)

/-- CPAL version 0, one palette: opaque red, half-transparent blue (BGRA records). -/
private def cpal : List UInt8 :=
  be16 0 ++ be16 2 ++ be16 1 ++ be16 2 ++ be32 14 ++ be16 0 ++
  [0, 0, 255, 255] ++ [255, 0, 0, 128]

/-- A COLR version 1 table with base glyph 5 painted by `paint` (placed after the
lists), a LayerList of `layers` (paint offsets relative to the list) and, when
`clip`, a clip box of (0,0)-(100,100) for glyph 5. -/
private def colr1 (paint : List UInt8) (layers : List (List UInt8) := []) (clip : Bool := true) : List UInt8 :=
  let header := 34
  let baseList := be32 1 ++ be16 5 ++ be32 0          -- offset patched below
  let layerHead := 4 + 4 * layers.length
  let layerOffsets := (layers.foldl (fun (acc : List Nat × Nat) l => (acc.1 ++ [acc.2], acc.2 + l.length)) ([], layerHead)).1
  let layerList := be32 layers.length ++ layerOffsets.flatMap be32 ++ layers.flatten
  let clipList := if clip then [1] ++ be32 1 ++ be16 5 ++ be16 5 ++ be24 12 ++ [1] ++ be16 0 ++ be16 0 ++ be16 100 ++ be16 100 else []
  let baseAt := header
  let layerAt := baseAt + baseList.length
  let clipAt := layerAt + layerList.length
  let paintAt := clipAt + clipList.length
  -- The base glyph's paint offset is relative to the BaseGlyphList.
  let baseList := be32 1 ++ be16 5 ++ be32 (paintAt - baseAt)
  be16 1 ++ be16 0 ++ be32 0 ++ be32 0 ++ be16 0 ++
  be32 baseAt ++ be32 (if layers.isEmpty then 0 else layerAt) ++ be32 (if clip then clipAt else 0) ++ be32 0 ++ be32 0 ++
  baseList ++ layerList ++ clipList ++ paint

/-- A font of nothing but the two tables, and its directory. -/
private def font (colr : List UInt8) : ByteArray × Array TableRecord :=
  let c := colr.length
  (⟨(colr ++ cpal).toArray⟩, #[⟨"COLR", 0, 0, c⟩, ⟨"CPAL", 0, c, cpal.length⟩])

private def program (colr : List UInt8) : Except String (Option Program) := do
  let (b, dir) := font colr
  let some t ← SfntColr.read b dir 10 | throw "no COLR"
  SfntColr.compile b t 5

private def solid (index : Nat) (alpha : Nat := 16384) : List UInt8 := [2] ++ be16 index ++ be16 alpha
/-- PaintGlyph of glyph 1 whose child is right after it. -/
private def glyph (child : List UInt8) : List UInt8 := [10] ++ be24 6 ++ be16 1 ++ child
private def errorOf (r : Except String α) : String := match r with | .error e => e | .ok _ => ""

-- Palette 0 is read as straight RGBA from BGRA records.
#guard (readPalette ⟨cpal.toArray⟩ ⟨"CPAL", 0, 0, cpal.length⟩).toOption.map (·.map (·.r)) == some #[255, 0]

-- A glyph filled with palette entry 1: one fill step with that colour.
#guard match program (colr1 (glyph (solid 1))) with
  | .ok (some p) => p.steps.size == 1 && p.box == (0, 0, 100, 100) && !p.foreground &&
      (match p.steps[0]! with | .fill (some 1) _ (.solid k) => k.rgba.b == 255 && k.rgba.a < 0.51 | _ => false)
  | _ => false
-- Palette index 0xFFFF is the text colour.
#guard match program (colr1 (glyph (solid 0xFFFF))) with
  | .ok (some p) => p.foreground
  | _ => false
-- An index outside the palette is refused (`resolveInk_ok`).
#guard (errorOf (program (colr1 (glyph (solid 7))))).startsWith "font.table.colr: palette index 7"
-- A glyph that is not a colour glyph has no program.
private def programOf (colr : List UInt8) (g : Nat) : Except String (Option Program) := do
  let (b, dir) := font colr
  let some t ← SfntColr.read b dir 10 | throw "no COLR"
  SfntColr.compile b t g
#guard match programOf (colr1 (glyph (solid 1))) 6 with
  | .ok none => true
  | _ => false
-- A colour glyph that names itself (PaintColrGlyph 5): the depth limit ends the walk.
#guard (errorOf (program (colr1 ([11] ++ be16 5)))).endsWith "deeper than the depth limit"
-- Layers that name themselves at each level: the depth limit ends the walk.
#guard (errorOf (program (colr1 ([1, 1] ++ be32 0) (layers := List.replicate 255 ([1, 255] ++ be32 0))))).endsWith "deeper than the depth limit"
-- A shallow graph that shares nodes: 255 layers, each of the same 255 layers, is 65,281
-- paint nodes from 510 records; the node budget ends the walk.
#guard (errorOf (program (colr1 ([1, 255] ++ be32 0)
    (layers := List.replicate 255 ([1, 255] ++ be32 255) ++ List.replicate 255 (solid 0))))).endsWith "larger than the node budget"
-- A layers paint that reaches past the layer list.
#guard (errorOf (program (colr1 ([1, 2] ++ be32 0) (layers := [solid 0])))).endsWith "layers outside the layer list"
-- A paint offset past the end of the table.
#guard (errorOf (program (colr1 ([10] ++ be24 200 ++ be16 1)))).endsWith "out of bounds"
-- A glyph paint that names a glyph the font does not have.
#guard (errorOf (program (colr1 ([10] ++ be24 6 ++ be16 99 ++ solid 0)))).endsWith "names no glyph"
-- A composite: backdrop and source each on a layer, then composited and merged; the
-- stack is well nested (`Program.stack_bounded`).
#guard match program (colr1 ([32] ++ be24 8 ++ [5] ++ be24 19 ++ glyph (solid 0) ++ glyph (solid 1))) with
  | .ok (some p) => p.steps.size == 6 && stackAfter p.steps maxStack == some 1
  | _ => false
-- An unknown composite mode is refused.
#guard (errorOf (program (colr1 ([32] ++ be24 8 ++ [40] ++ be24 19 ++ glyph (solid 0) ++ glyph (solid 1))))).endsWith "composite mode 40"
-- A list longer than its table is refused when the table is read.
#guard (errorOf (do
    let bytes := colr1 (glyph (solid 1))
    let bad := bytes.take 34 ++ be32 1000 ++ bytes.drop 38
    let (b, dir) := font bad
    SfntColr.read b dir 10)).endsWith "out of bounds"
-- A transform paint: translate (formats 14) under a glyph paint keeps a solid fill.
#guard match program (colr1 (glyph ([14] ++ be24 8 ++ be16 10 ++ be16 20 ++ solid 0))) with
  | .ok (some p) => p.steps.size == 1
  | _ => false

/-! COLR version 0: a base glyph record with two layers. -/
private def colr0 (palette1 : Nat) : List UInt8 :=
  be16 0 ++ be16 1 ++ be32 14 ++ be32 20 ++ be16 2 ++
  (be16 5 ++ be16 0 ++ be16 2) ++ (be16 1 ++ be16 0 ++ be16 2 ++ be16 palette1)
#guard match program (colr0 1) with
  | .ok (some p) => p.steps.size == 2 && p.box == (0, 0, 0, 0)
  | _ => false
#guard (errorOf (program (colr0 9))).startsWith "font.table.colr: palette index 9"

/-! Drawing: a top-level solid paint fills the whole clip box, and nothing else. -/
private def drawn (paint : List UInt8) (px : Nat) : Option ColrRaster.Raster := do
  let (b, dir) := font (colr1 paint)
  let some t := (SfntColr.read b dir 10).toOption.join | none
  let some p := (SfntColr.compile b t 5).toOption.join | none
  ColrRaster.draw ⟨b, dir, none⟩ 100 p px ⟨0, 0, 0, 1⟩

#guard match drawn (solid 0) 10 with
  | some r => r.width == 10 && r.height == 10 && r.left == 0 && r.top == -10 &&
      r.rgba.size == 400 && (List.range 100).all fun i => r.rgba.get! (4*i) == 255 && r.rgba.get! (4*i+3) == 255
  | none => false
-- Half-transparent blue stays straight (not premultiplied) in the bitmap.
#guard match drawn (solid 1) 4 with
  | some r => r.rgba.get! 2 == 255 && r.rgba.get! 3 == 128
  | none => false
-- A composite that clears its backdrop (mode 0, CLEAR) leaves the box transparent.
#guard match drawn ([32] ++ be24 8 ++ [0] ++ be24 13 ++ solid 0 ++ solid 1) 4 with
  | some r => (List.range 16).all fun i => r.rgba.get! (4*i+3) == 0
  | none => false

end L4Factoidal.Rendering.SfntColrTests
