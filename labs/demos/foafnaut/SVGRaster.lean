import SVG

/-! # The scene shader on the CPU

`docs/designissues/2026-11-08-cpu-render-backend.md`. A pure function from a scene to
the RGBA bytes that `NativeSVG.sceneShader` draws into a `width × height` target, for a
host with no GPU: the Hub when WebGPU is missing, native builds without a GPU, headless
pixel tests, and later microcontrollers.

`Scene.rasterSpec` is the reference. It states the WGSL of `sceneShader` per pixel:

* the pixel's tile and the record rows its list names (`Scene.tiles`, the words the GPU
  reads), so a primitive the GPU leaves out of a tile is left out here too;
* each sample folds `Primitive.sampleStep` over those records in paint order from white,
  the CPU statement of `samplePixel` that the readback probes (`Scene.checks`) already use;
* `adaptiveSample`: four samples, sixteen at an edge, as the fragment entry point;
* `rgba8unorm`: each channel clamped to `[0,1]`, times 255, rounded; alpha 255.

The arithmetic is binary64 on the scene's floats; the GPU runs binary32 on the same
floats rounded. The design record states the tolerance this gives.

`Scene.rasterFast` is what hosts call. It prepares each primitive once
(`Primitive.prepareSample`, `rasterPrepared_eq` ties the prepared fold to the reference
fold), keeps the prepared lists of one row of tiles, and tests each primitive's
conservative pixel box (`Primitive.screenBox`, the box the tile lists are made from)
before it samples it. Outside that box a primitive covers no sample, so a skipped step
is the step that changes nothing; this is the assumption the GPU tile lists already
make, and the differential test checks the two forms byte for byte. Output is one
`ByteArray` that only the loop holds, so each push is in place. -/
namespace NativeSVG.Raster

/-- A compiled primitive and the index of its record's first float in `Scene.data`. -/
abbrev Item := BackendPrimitive × Nat

/-- The scene shader's start colour and the colour outside its viewport. -/
def white : Color := ⟨1,1,1⟩

/-- The words of `Scene.tiles`: tile side, tiles across, tiles down, one start offset for
each tile and an end offset, then the record rows of every list. -/
structure Grid where
  words : Array Nat

namespace Grid
def size (g : Grid) : Nat := g.words[0]!
def across (g : Grid) : Nat := g.words[1]!
def down (g : Grid) : Nat := g.words[2]!
/-- `samplePixel`'s tile, `min(u32(p.y)/size,down-1)*across+min(u32(p.x)/size,across-1)`:
every sample of pixel `(x,y)` lies in `[x,x+1)×[y,y+1)`, so its `u32` coordinates are
`(x,y)`. -/
def tileRow (g : Grid) (y : Nat) : Nat := min (y / g.size) (g.down-1)
def tileColumn (g : Grid) (x : Nat) : Nat := min (x / g.size) (g.across-1)
def tile (g : Grid) (x y : Nat) : Nat := g.tileRow y * g.across + g.tileColumn x
/-- The record rows that tile `t` lists, in paint order: `tiles[listBase+item]` for
`item` from `tiles[3+t]` to `tiles[4+t]`. -/
def rows (g : Grid) (t : Nat) : List Nat :=
  let listBase := 4 + g.across*g.down
  let lo := g.words[3+t]!
  let hi := g.words[4+t]!
  (List.range (hi-lo)).map fun i => g.words[listBase+lo+i]!
end Grid

/-- The compiled primitives in paint order, each with its record's first float, and the
index of each by record row (rows from 2, as `Scene.tiles` counts them). -/
def items (s : Scene) : Array Item × Std.HashMap Nat Nat :=
  let step := fun (acc : Array Item × Std.HashMap Nat Nat × Nat) (p : BackendPrimitive) =>
    (acc.1.push (p,acc.2.2*4),acc.2.1.insert acc.2.2 acc.1.size,acc.2.2+p.rowCount)
  let (all,index,_) := s.compiled.foldl step (#[],{},2)
  (all,index)

/-- The items of tile `t`, in the order of its list. -/
def tileItems (g : Grid) (all : Array Item) (index : Std.HashMap Nat Nat) (t : Nat) : List Item :=
  (g.rows t).filterMap fun row => (index.get? row).bind (all[·]?)

/-- The page position of a screen sample: `(p-rows[0].zw)/rows[0].xy+rows[1].xy`. -/
def world (m : Mapping) (x y : Float) : Float × Float :=
  ((x-m.tx)/m.sx+m.minX,(y-m.ty)/m.sy+m.minY)

/-- A sample at or past the viewport's right or bottom edge is white. -/
def outside (m : Mapping) (x y : Float) : Bool := x >= m.viewportWidth || y >= m.viewportHeight

/-- `samplePixel` at one screen point with the given records. -/
def sampleSpec (m : Mapping) (data : Array Float) (items : List Item) (x y : Float) : Color :=
  if outside m x y then white
  else items.foldl (fun c (p,base) => p.sampleStep data base (world m x y) c) white

/-- One channel as `rgba8unorm` stores it. -/
def channel (v : Float) : UInt8 := (max 0 (min 255 (v*255))).round.toUInt8

def pixelBytes (c : Color) : List UInt8 := [channel c.r,channel c.g,channel c.b,255]

/-- The reference colour of pixel `(x,y)`. -/
def pixelSpec (s : Scene) (data : Array Float) (g : Grid) (all : Array Item)
    (index : Std.HashMap Nat Nat) (x y : Nat) : Color :=
  adaptiveSample (sampleSpec s.mapping data (tileItems g all index (g.tile x y))) (data.size/4) x y

/-- The reference: rows `top .. top+rows` of the scene's target, four bytes a pixel. -/
def _root_.NativeSVG.Scene.rasterSpec (s : Scene) (top rows : Nat) : ByteArray :=
  let data := s.data
  let g : Grid := ⟨s.tiles⟩
  let (all,index) := items s
  ⟨((List.range rows).flatMap fun j => (List.range s.width).flatMap fun x =>
    pixelBytes (pixelSpec s data g all index x (top+j))).toArray⟩

/-! ## Prepared samples -/

/-- `sampleSpec` with each record prepared once (`Primitive.prepareSample`). -/
def samplePrepared (m : Mapping) (prepared : List PreparedSample) (x y : Float) : Color :=
  if outside m x y then white
  else prepared.foldl (fun c r => r.apply (world m x y) c) white

theorem foldPrepared_eq (data : Array Float) (position : Float × Float) (items : List Item) (c : Color) :
    (items.map fun (p,base) => p.prepareSample data base).foldl (fun c r => r.apply position c) c =
      items.foldl (fun c (p,base) => p.sampleStep data base position c) c := by
  induction items generalizing c with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [Primitive.prepareSample_correct]
    exact ih _

/-- Preparing the records changes no sample. -/
theorem samplePrepared_eq (m : Mapping) (data : Array Float) (items : List Item) (x y : Float) :
    samplePrepared m (items.map fun (p,base) => p.prepareSample data base) x y = sampleSpec m data items x y := by
  unfold samplePrepared sampleSpec
  split
  · rfl
  · exact foldPrepared_eq data _ items white

/-- The pixel with prepared records. -/
def pixelPrepared (s : Scene) (rows : Nat) (prepared : List PreparedSample) (x y : Nat) : Color :=
  adaptiveSample (samplePrepared s.mapping prepared) rows x y

/-- Each pixel of the prepared form is the reference pixel. -/
theorem rasterPrepared_eq (s : Scene) (data : Array Float) (g : Grid) (all : Array Item)
    (index : Std.HashMap Nat Nat) (x y : Nat) :
    pixelPrepared s (data.size/4) ((tileItems g all index (g.tile x y)).map fun (p,base) => p.prepareSample data base) x y =
      pixelSpec s data g all index x y := by
  unfold pixelPrepared pixelSpec
  congr 1
  funext a b
  exact samplePrepared_eq s.mapping data _ a b

/-! ## The fast form -/

/-- A prepared record, the record itself, and its conservative box in target pixels. -/
structure Prep where
  item : Item
  sample : PreparedSample
  x0 : Float
  y0 : Float
  x1 : Float
  y1 : Float

private def infinity : Float := 1.0/0.0

/-- `Primitive.screenBox`, the box `Scene.tiles` lists by; no box means every pixel. -/
def prep (m : Mapping) (data : Array Float) (item : Item) : Prep :=
  let (x0,y0,x1,y1) := (item.1.screenBox m).getD (-infinity,-infinity,infinity,infinity)
  ⟨item,item.1.prepareSample data item.2,x0,y0,x1,y1⟩

/-- True when the box of `r` meets the pixel square at `(x,y)`. -/
@[inline] def Prep.meetsRow (r : Prep) (y : Float) : Bool := r.y0 <= y+1 && y <= r.y1
@[inline] def Prep.meetsColumn (r : Prep) (x : Float) : Bool := r.x0 <= x+1 && x <= r.x1

/-- The sample rows of a pixel, from its top: the sixteen `dy` of `adaptiveSampleAt`. -/
def sampleRows : Array Float :=
  ((NativeGraphics.pixelSampleFirstOffsets ++ NativeGraphics.pixelSampleRestOffsets).map (·.2)).toArray

/-- A path record for pixel row `y`: its fill tests only the edges that cross each of
the row's sixteen sample lines (`pathSpansAt`, `pathHitSpans`). A sample whose local `y`
is not one of those lines (a rotated path) tests every edge. -/
def Prep.forRow (m : Mapping) (data : Array Float) (yf : Float) (r : Prep) : Prep :=
  match r.item.1.pathEdges? with
  | none => r
  | some count =>
    let wx := (world m (max 0 r.x0) yf).1
    let spans := sampleRows.map fun dy =>
      let py := pathSampleY (r.item.1.localPoint wx (world m wx (yf+dy)).2)
      (py,pathSpansAt data r.item.2 count py)
    {r with sample := {r.sample with coverage := r.item.1.prepareCoverageSpans data r.item.2 spans}}

/-- One sample over the records whose box meets the pixel's column `x`. -/
def sampleFast (m : Mapping) (prepared : Array Prep) (column : Float) (x y : Float) : Color :=
  if outside m x y then white
  else
    let position := world m x y
    prepared.foldl (fun c r =>
      if r.meetsColumn column then
        -- A record that covers no sample leaves the colour as it is: its paint has
        -- alpha 0 in `overColors`, so the colour gains 0 and keeps all of itself.
        let hits := r.sample.coverage.eval position
        if hits.1 || hits.2 then overColors (r.sample.fill position) (r.sample.stroke position) r.sample.opacity hits c
        else c
      else c) white

@[inline] private def pushPixel (out : ByteArray) (c : Color) : ByteArray :=
  out.push (channel c.r) |>.push (channel c.g) |>.push (channel c.b) |>.push 255

/-- The pixels `x .. width` of one row. `row` holds, for each tile of the row, the
prepared records whose box meets pixel row `y`. -/
private def rowFrom (s : Scene) (g : Grid) (rows : Nat) (row : Array (Array Prep)) (yf : Float)
    (x : Nat) (out : ByteArray) : ByteArray :=
  if x < s.width then
    let xf := Float.ofNat x
    let c := adaptiveSampleAt (sampleFast s.mapping (row[g.tileColumn x]?.getD #[]) xf) rows xf yf
    rowFrom s g rows row yf (x+1) (pushPixel out c)
  else out
termination_by s.width - x

/-- The record indices of each tile of tile row `ty`, in list order. -/
def tileRowItems (g : Grid) (index : Std.HashMap Nat Nat) (ty : Nat) : Array (Array Nat) :=
  (Array.range g.across).map fun tx => ((g.rows (ty*g.across+tx)).filterMap index.get?).toArray

/-- The records of pixel row `y`, each prepared for the row once (`Prep.forRow`) however
many tiles list it, then each tile's list of those. -/
def rowPrep (m : Mapping) (data : Array Float) (all : Array Prep) (tiles : Array (Array Nat)) (yf : Float) :
    Array (Array Prep) := Id.run do
  let mut made : Std.HashMap Nat Prep := {}
  for list in tiles do
    for i in list do
      if !made.contains i then
        if let some r := all[i]? then
          if r.meetsRow yf then made := made.insert i (r.forRow m data yf)
  return tiles.map fun list => list.filterMap made.get?

private def rowsFrom (s : Scene) (g : Grid) (data : Array Float) (all : Array Prep) (index : Std.HashMap Nat Nat)
    (rows top count : Nat) (j : Nat) (tiles : Option (Nat × Array (Array Nat))) (out : ByteArray) :
    ByteArray :=
  if j < count then
    let y := top+j
    let ty := g.tileRow y
    let tiles := match tiles with
      | some (t,kept) => if t == ty then kept else tileRowItems g index ty
      | none => tileRowItems g index ty
    let yf := Float.ofNat y
    let row := rowPrep s.mapping data all tiles yf
    rowsFrom s g data all index rows top count (j+1) (some (ty,tiles)) (rowFrom s g rows row yf 0 out)
  else out
termination_by count - j

/-- Rows `top .. top+rows` of the scene's target, four bytes a pixel: `rasterSpec`
prepared and with each record tested against its pixel box first. -/
def _root_.NativeSVG.Scene.rasterFast (s : Scene) (top rows : Nat) : ByteArray :=
  let data := s.data
  let g : Grid := ⟨s.tiles⟩
  let (all,index) := items s
  let preps := all.map (prep s.mapping data)
  rowsFrom s g data preps index (data.size/4) top rows 0 none (ByteArray.emptyWithCapacity (s.width*rows*4))

/-- The scene's whole target: what a host shows in place of the GPU's texture. -/
def _root_.NativeSVG.Scene.rgba (s : Scene) : ByteArray := s.rasterFast 0 s.height

/-- A small scene with each kind of record the fast form treats apart: a rectangle fill
(prepared as a plain rectangle test), a stroked circle with opacity, an even-odd path, a
linear gradient and a transform. -/
private def guardScene : Option Scene := (parse ("<svg xmlns='http://www.w3.org/2000/svg' width='40' height='36'>" ++
  "<defs><linearGradient id='g'><stop offset='0' stop-color='yellow'/><stop offset='1' stop-color='purple'/></linearGradient></defs>" ++
  "<rect x='1.5' y='2.25' width='30' height='7' fill='url(#g)'/><rect x='3' y='12' width='9.5' height='4.5' fill='red'/>" ++
  "<circle cx='25' cy='22' r='9' fill='blue' stroke='green' stroke-width='2' opacity='0.5'/>" ++
  "<path d='M2 34 L18 19 L22 35 Z M8 30 L16 24 L17 32 Z' fill='#808000' fill-rule='evenodd'/>" ++
  "<g transform='rotate(20 20 18)'><rect x='14' y='6' width='12' height='5' fill='teal' stroke='black'/>" ++
  "<path d='M30 4 L38 12 L31 14 Z' fill='navy'/></g>" ++
  "<g transform='translate(0.3 0.7)'><path d='M24 26 C 30 20, 36 30, 38 34 L 26 35 Z' fill='maroon'/></g>" ++
  "<svg x='2' y='18' width='12' height='12' overflow='hidden'><circle cx='6' cy='6' r='9' fill='orange' stroke='black' stroke-dasharray='2 1'/>" ++
  "<path d='M0 0 L12 6 L0 12 Z' fill='gray' fill-opacity='0.7'/></svg></svg>") 40 36).toOption

-- The fast form gives the reference bytes on this scene, for the whole target and a band of rows.
#guard (guardScene.map fun s => (s.rasterFast 0 s.height).data == (s.rasterSpec 0 s.height).data) == some true
#guard (guardScene.map fun s => (s.rasterFast 9 20).data == (s.rasterSpec 9 20).data) == some true
#guard (guardScene.map fun s => (s.rgba.size,s.width*s.height*4)) == some (40*36*4,40*36*4)

#print axioms samplePrepared_eq
#print axioms rasterPrepared_eq

end NativeSVG.Raster
