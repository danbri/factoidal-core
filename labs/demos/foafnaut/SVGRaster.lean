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
/-- `samplePixel`'s row band of the tile, `min((u32(p.y)-tileY*size)/cellSize,cellsPerSide-1)`,
and its cell, `band*cellsPerSide+min((u32(p.x)-tileX*size)/cellSize,cellsPerSide-1)`. -/
def band (g : Grid) (y : Nat) : Nat := min ((y - g.tileRow y * g.size) / cellSize) (cellsPerSide-1)
def cell (g : Grid) (x y : Nat) : Nat :=
  g.band y * cellsPerSide + min ((x - g.tileColumn x * g.size) / cellSize) (cellsPerSide-1)
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

/-- `rasterSpec` with every record at every pixel: no tile lists. The tiles leave a record out
of a tile its paint box (`Primitive.paintBox`, the clips included) does not meet; the guards
below compare the two rasters byte for byte. -/
def _root_.NativeSVG.Scene.rasterAll (s : Scene) (top rows : Nat) : ByteArray :=
  let data := s.data
  let (all,_) := items s
  ⟨((List.range rows).flatMap fun j => (List.range s.width).flatMap fun x =>
    pixelBytes (adaptiveSample (sampleSpec s.mapping data all.toList) (data.size/4) x (top+j))).toArray⟩

/-! ## The tile edge lists

The scene shader walks, for a path's fill, the edge list that `tilesOf` made for the
pixel's tile, and for a stroke the tile's pieces. `rasterTiles` is `rasterSpec` with each
record of a tile tested over those lists (`Primitive.prepareCoverageTile`, `pathHitList`). `pathHitList_eq` states that a
list gives the full scan's fill at every point whose spanning edges it keeps; that the
margins of `Primitive.localRows` keep them for every sample of the tile rests on Float
comparisons, so it is checked: the guards below compare the two rasters byte for byte. -/

/-- The edge list word of item `k` of tile `t`, after the entries (`tilesOf`). -/
def Grid.edgeWord (g : Grid) (t k : Nat) : Nat :=
  let listBase := 4 + g.across*g.down
  let total := g.words[3+g.across*g.down]!
  g.words[listBase+total+g.words[3+t]!+k]!

/-- The list of cell form (`cellMark`) at word `w` with `parts` lists: the list of part `k`. -/
def Grid.cellPart (g : Grid) (w parts k : Nat) : Array Nat :=
  let s := g.words[w+1+k]!
  (Array.range (g.words[w+2+k]!-s)).map fun j => g.words[w+2+parts+s+j]!

/-- The edge list of the record at word `w` for the samples of row band `band`: a count, then
the edge indices, or in cell form the band's list; none for `allEdges` (as the record word or
as its count). -/
def Grid.edgeList (g : Grid) (w band : Nat) : Option (Array Nat) :=
  if w == allEdges then none
  else
    let n := g.words[w]!
    if n == allEdges then none
    else if n == cellMark then some (g.cellPart w cellsPerSide band)
    else some ((Array.range n).map fun j => g.words[w+1+j]!)

/-- The stroke piece list of the record at word `w` for the samples of cell `cell`, after its
edge part. -/
def Grid.pieceList (g : Grid) (w cell : Nat) : Option (Array Nat) :=
  if w == allEdges then none
  else
    let n := g.words[w]!
    let at_ := if n == allEdges then w+1
      else if n == cellMark then w+2+cellsPerSide+g.words[w+1+cellsPerSide]!
      else w+1+n
    let m := g.words[at_]!
    if m == allEdges then none
    else if m == cellMark then some (g.cellPart at_ (cellsPerSide*cellsPerSide) cell)
    else some ((Array.range m).map fun j => g.words[at_+1+j]!)

/-- The records of tile `t`, each prepared with the edge list of row band `band` for a path
fill and the piece list of cell `cell` for a stroke. -/
def tilePrepared (g : Grid) (data : Array Float) (all : Array Item) (index : Std.HashMap Nat Nat)
    (t band cell : Nat) : List PreparedSample :=
  ((g.rows t).zipIdx.filterMap fun (row,k) => (index.get? row).bind (all[·]?) |>.map fun (p,base) =>
    let sample := p.prepareSample data base
    let w := g.edgeWord t k
    match g.edgeList w band,g.pieceList w cell with
    | none,none => sample
    | edges,pieces => {sample with coverage := p.prepareCoverageTile data base edges pieces})

/-- `rasterSpec` with the tile edge lists of the scene shader. -/
def _root_.NativeSVG.Scene.rasterTiles (s : Scene) (top rows : Nat) : ByteArray :=
  let data := s.data
  let g : Grid := ⟨s.tiles⟩
  let (all,index) := items s
  ⟨((List.range rows).flatMap fun j => (List.range s.width).flatMap fun x =>
    pixelBytes (pixelPrepared s (data.size/4)
      (tilePrepared g data all index (g.tile x (top+j)) (g.band (top+j)) (g.cell x (top+j))) x (top+j))).toArray⟩

/-! ## The fast form -/

/-- The fill and stroke rows `[r,g,b,alpha]` of a record whose two paints are the same at every
point (`Primitive.constantPaintRow?`), as floats: `overColors` reads them with no list. -/
structure PaintRows where
  fr : Float
  fg : Float
  fb : Float
  fa : Float
  sr : Float
  sg : Float
  sb : Float
  sa : Float

def paintRows? (p : BackendPrimitive) : Option PaintRows :=
  match p.constantPaintRow? p.style.fill p.style.fillOpacity,p.constantPaintRow? p.style.stroke p.style.strokeOpacity with
  | some f,some s => some ⟨f[0]!,f[1]!,f[2]!,f[3]!,s[0]!,s[1]!,s[2]!,s[3]!⟩
  | _,_ => none

/-- A prepared record, the record itself, and its conservative box in target pixels. -/
structure Prep where
  item : Item
  sample : PreparedSample
  /-- `Primitive.pathEdges?` of the record, found once and not at each pixel row. -/
  edgeCount : Option Nat
  /-- The paint rows when both paints are constant, else none (the closures of `sample` are used). -/
  rows : Option PaintRows
  x0 : Float
  y0 : Float
  x1 : Float
  y1 : Float

private def infinity : Float := 1.0/0.0

/-- `Primitive.screenBox`, the box `Scene.tiles` lists by; no box means every pixel. -/
def prep (m : Mapping) (data : Array Float) (item : Item) : Prep :=
  let (x0,y0,x1,y1) := (item.1.screenBox m).getD (-infinity,-infinity,infinity,infinity)
  let sample := item.1.prepareSample data item.2
  -- A dashed stroke tests only the pieces whose box holds the point.
  let sample := if item.1.dashParts.isSome then {sample with coverage := item.1.prepareCoverageCulled data item.2} else sample
  ⟨item,sample,item.1.pathEdges?,paintRows? item.1,x0,y0,x1,y1⟩

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
  match r.edgeCount with
  | none => r
  | some count =>
    let wx := (world m (max 0 r.x0) yf).1
    let spans := sampleRows.map fun dy =>
      let py := pathSampleY (r.item.1.localPoint wx (world m wx (yf+dy)).2)
      (py,pathSpansAt data r.item.2 count py)
    {r with sample := {r.sample with coverage := r.item.1.prepareCoverageSpans data r.item.2 spans}}

/-- `overColors` with the paint rows as floats, the same Float operations in the same order. -/
@[inline] def overRows (r : PaintRows) (opacity : Float) (fillHit strokeHit : Bool) (dst : Color) : Color :=
  let fa : Float := if fillHit then r.fa else 0
  let sa : Float := if strokeHit then r.sa else 0
  let pr := r.sr*sa+r.fr*fa*(1-sa)
  let pg := r.sg*sa+r.fg*fa*(1-sa)
  let pb := r.sb*sa+r.fb*fa*(1-sa)
  let lr := pr*opacity
  let lg := pg*opacity
  let lb := pb*opacity
  let alpha := (sa+fa*(1-sa))*opacity
  ⟨lr + dst.r * (1 - alpha), lg + dst.g * (1 - alpha), lb + dst.b * (1 - alpha)⟩

/-- One sample over the records whose box meets the pixel's column `x`. -/
def sampleFast (m : Mapping) (prepared : Array Prep) (column : Float) (x y : Float) : Color :=
  if outside m x y || prepared.size == 0 then white
  else
    let position := world m x y
    prepared.foldl (fun c r =>
      if r.meetsColumn column then
        -- A record that covers no sample leaves the colour as it is: its paint has
        -- alpha 0 in `overColors`, so the colour gains 0 and keeps all of itself.
        let hits := r.sample.coverage.eval position
        if hits.1 || hits.2 then
          match r.rows with
          | some rows => overRows rows r.sample.opacity hits.1 hits.2 c
          | none => overColors (r.sample.fill position) (r.sample.stroke position) r.sample.opacity hits c
        else c
      else c) white

/-- The offsets of the first four and the other twelve samples of a pixel (`adaptiveSampleAt`),
as unboxed floats. -/
def firstDx : FloatArray := ⟨(NativeGraphics.pixelSampleFirstOffsets.map (·.1)).toArray⟩
def firstDy : FloatArray := ⟨(NativeGraphics.pixelSampleFirstOffsets.map (·.2)).toArray⟩
def restDx : FloatArray := ⟨(NativeGraphics.pixelSampleRestOffsets.map (·.1)).toArray⟩
def restDy : FloatArray := ⟨(NativeGraphics.pixelSampleRestOffsets.map (·.2)).toArray⟩

/-- The sample counts of `adaptiveSampleAt`: four, and sixteen at an edge. -/
def nFirst : Float := Float.ofNat NativeGraphics.pixelSampleFirstOffsets.length
def nAll : Float := nFirst + Float.ofNat NativeGraphics.pixelSampleRestOffsets.length

/-- Totals and extremes of the first samples of a pixel. -/
structure FirstStats where
  tr : Float
  tg : Float
  tb : Float
  lr : Float
  lg : Float
  lb : Float
  hr : Float
  hg : Float
  hb : Float

/-- The first samples `i ..` of a pixel: the loop of `adaptiveSampleAt` over
`pixelSampleFirstOffsets`, with the three running colours as floats. -/
private def firstFrom (m : Mapping) (prepared : Array Prep) (column px py : Float) (i : Nat)
    (tr tg tb lr lg lb hr hg hb : Float) : FirstStats :=
  if i < firstDx.size then
    let c := sampleFast m prepared column (px+firstDx.get! i) (py+firstDy.get! i)
    firstFrom m prepared column px py (i+1) (tr+c.r) (tg+c.g) (tb+c.b)
      (min lr c.r) (min lg c.g) (min lb c.b) (max hr c.r) (max hg c.g) (max hb c.b)
  else ⟨tr,tg,tb,lr,lg,lb,hr,hg,hb⟩
termination_by firstDx.size - i

/-- The other samples `i ..` of a pixel with an edge, added to the totals. -/
private def restFrom (m : Mapping) (prepared : Array Prep) (column px py : Float) (i : Nat)
    (tr tg tb : Float) : Color :=
  if i < restDx.size then
    let c := sampleFast m prepared column (px+restDx.get! i) (py+restDy.get! i)
    restFrom m prepared column px py (i+1) (tr+c.r) (tg+c.g) (tb+c.b)
  else
    ⟨tr/nAll,tg/nAll,tb/nAll⟩
termination_by restDx.size - i

/-- `adaptiveSampleAt (sampleFast m prepared column) rows px py` as loops over unboxed floats:
the same samples, additions, minima and maxima in the same order, with no closure, list or
colour made for each sample. A differential test (the `#guard`s below, and the SVG image
benchmark of the pixel hashes) checks it; no theorem states it. -/
def pixelFast (m : Mapping) (prepared : Array Prep) (column : Float) (rows : Nat) (px py : Float) : Color :=
  let s := firstFrom m prepared column px py 0 0 0 0 1e9 1e9 1e9 (-1e9) (-1e9) (-1e9)
  if rows <= NativeGraphics.pixelSampleRefineRowLimit && (s.hr-s.lr > NativeGraphics.pixelSampleEdgeThreshold ||
      s.hg-s.lg > NativeGraphics.pixelSampleEdgeThreshold || s.hb-s.lb > NativeGraphics.pixelSampleEdgeThreshold) then
    restFrom m prepared column px py 0 s.tr s.tg s.tb
  else
    ⟨s.tr/nFirst,s.tg/nFirst,s.tb/nFirst⟩

@[inline] private def pushPixel (out : ByteArray) (c : Color) : ByteArray :=
  out.push (channel c.r) |>.push (channel c.g) |>.push (channel c.b) |>.push 255

/-- The pixels `x .. width` of one row. `row` holds, for each tile of the row, the
prepared records whose box meets pixel row `y`. -/
private def rowFrom (s : Scene) (g : Grid) (rows : Nat) (row : Array (Array Prep)) (yf : Float)
    (x : Nat) (out : ByteArray) : ByteArray :=
  if x < s.width then
    let xf := Float.ofNat x
    let c := pixelFast s.mapping (row[g.tileColumn x]?.getD #[]) xf rows xf yf
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
private def guardScene (_ : Unit) : Option Scene := (parse ("<svg xmlns='http://www.w3.org/2000/svg' width='40' height='36'>" ++
  "<defs><linearGradient id='g'><stop offset='0' stop-color='yellow'/><stop offset='1' stop-color='purple'/></linearGradient></defs>" ++
  "<rect x='1.5' y='2.25' width='30' height='7' fill='url(#g)'/><rect x='3' y='12' width='9.5' height='4.5' fill='red'/>" ++
  "<circle cx='25' cy='22' r='9' fill='blue' stroke='green' stroke-width='2' opacity='0.5'/>" ++
  "<path d='M2 34 L18 19 L22 35 Z M8 30 L16 24 L17 32 Z' fill='#808000' fill-rule='evenodd'/>" ++
  "<g transform='rotate(20 20 18)'><rect x='14' y='6' width='12' height='5' fill='teal' stroke='black'/>" ++
  "<path d='M30 4 L38 12 L31 14 Z' fill='navy'/></g>" ++
  "<g transform='translate(0.3 0.7)'><path d='M24 26 C 30 20, 36 30, 38 34 L 26 35 Z' fill='maroon'/></g>" ++
  "<svg x='2' y='18' width='12' height='12' overflow='hidden'><circle cx='6' cy='6' r='9' fill='orange' stroke='black' stroke-dasharray='2 1'/>" ++
  "<path d='M0 0 L12 6 L0 12 Z' fill='gray' fill-opacity='0.7'/></svg>" ++
  "<ellipse cx='30' cy='8' rx='7' ry='4' fill='none' stroke='crimson' stroke-width='1.5' stroke-dasharray='3 2'/>" ++
  "<path d='M4 4 Q 12 0 18 8' fill='none' stroke='black' stroke-width='1' stroke-linejoin='miter'/></svg>") 40 36).toOption

-- The fast form gives the reference bytes on this scene, for the whole target and a band of rows.
-- (With the tile edge lists, `rasterTiles`, against the same reference bytes: see below.)
#guard ((guardScene ()).map fun s => let r := (s.rasterSpec 0 s.height).data;
  (s.rasterFast 0 s.height).data == r && (s.rasterTiles 0 s.height).data == r) == some true
#guard ((guardScene ()).map fun s => (s.rasterFast 9 20).data == (s.rasterSpec 9 20).data) == some true
#guard ((guardScene ()).map fun s => (s.rgba.size,s.width*s.height*4)) == some (40*36*4,40*36*4)

-- The tile edge lists give the reference bytes on the guard scene (above: paths in a rotation,
-- a translation, a nested svg and even-odd) and on a path zoomed far past its tiles.
private def zoomScene (k : String) : Option Scene := (parse ("<svg xmlns='http://www.w3.org/2000/svg' width='32' height='28' viewBox='0 0 96 80'>" ++
  "<g transform='translate(48 40) scale(" ++ k ++ ") translate(-48 -40)'>" ++
  "<path d='M10 70 Q48 -20 86 70 C70 90 26 90 10 70Z M40 40 C42 36 54 36 56 40 C58 46 50 50 48 50 C46 50 38 46 40 40Z' fill='#204080' fill-rule='evenodd'/>" ++
  "<path d='M47 37 L49 37 L49.5 39 L46.5 39Z' fill='#d04020' transform='rotate(30 48 38)'/></g></svg>") 32 28).toOption
#guard ((zoomScene "1").map fun s => (s.rasterTiles 0 s.height).data == (s.rasterSpec 0 s.height).data) == some true
#guard ((zoomScene "40").map fun s => (s.rasterTiles 0 s.height).data == (s.rasterSpec 0 s.height).data) == some true
-- The tile lists (paint boxes cut to the clips) give the bytes of every record at every
-- pixel: the guard scene's nested svg, and a path zoomed far past its clip.
private def clippedZoom (_ : Unit) : Option Scene := (parse ("<svg xmlns='http://www.w3.org/2000/svg' width='48' height='26'>" ++
  "<svg x='4' y='4' width='22' height='22' viewBox='0 0 96 96' overflow='hidden'><g transform='translate(48 48) scale(40) translate(-48 -48)'>" ++
  "<path d='M10 70 Q48 -20 86 70 C70 90 26 90 10 70Z' fill='#204080'/><circle cx='48' cy='48' r='0.4' fill='#d04020'/>" ++
  "<path d='M44 44 Q48 40 52 44 T60 44 L56 52 Z' fill='none' stroke='#802020' stroke-width='0.3' stroke-linejoin='round'/></g></svg>" ++
  "<rect x='36' y='4' width='10' height='18' fill='teal'/></svg>") 48 26).toOption
#guard ((guardScene ()).map fun s => (s.rasterSpec 0 s.height).data == (s.rasterAll 0 s.height).data) == some true
#guard ((clippedZoom ()).map fun s => let r := (s.rasterAll 0 s.height).data;
  (s.rasterSpec 0 s.height).data == r && (s.rasterTiles 0 s.height).data == r) == some true
-- The zoomed path (record row 2), whose own box covers every tile, is listed only in the one
-- tile that its clip meets.
#guard ((clippedZoom ()).map fun s => let g : Grid := ⟨s.tiles⟩;
  ((List.range (g.across*g.down)).filter fun t => (g.rows t).contains 2).length) == some 1
-- A stroke across several tiles, with round joins and miter joins: the tiles' piece lists give
-- the reference bytes, and the tiles list different pieces.
private def strokeScene (_ : Unit) : Option Scene := (parse ("<svg xmlns='http://www.w3.org/2000/svg' width='64' height='24'>" ++
  "<path d='M4 20 L12 4 L20 22 L28 5 L36 20 L44 4 L58 22' fill='none' stroke='#802020' stroke-width='3' stroke-linejoin='round'/>" ++
  "<path d='M6 14 Q32 -6 58 14' fill='none' stroke='navy' stroke-width='2' stroke-linejoin='miter'/></svg>") 64 24).toOption
#guard ((strokeScene ()).map fun s => (s.rasterTiles 0 s.height).data == (s.rasterAll 0 s.height).data) == some true
#guard ((strokeScene ()).map fun s =>
  let g : Grid := ⟨s.tiles⟩
  let sizes := (List.range (g.across*g.down)).filterMap fun t =>
    if (g.rows t).isEmpty then none
    else some ((List.range (cellsPerSide*cellsPerSide)).foldl (fun n c => n+((g.pieceList (g.edgeWord t 0) c).map (·.size)).getD 0) 0)
  decide (sizes.eraseDups.length > 1)) == some true
-- Edge lists are made: the zoomed scene's tile words hold lists shorter than the paths.
#guard ((zoomScene "40").map fun s =>
  let g : Grid := ⟨s.tiles⟩
  (List.range (g.across*g.down)).any fun t => (List.range (g.rows t).length).any fun k =>
    (List.range cellsPerSide).any fun b => match g.edgeList (g.edgeWord t k) b with | some e => e.size < 8 | none => false) == some true

-- The tile words written by counting (`tilesOfListingsRows`) are those of the first form, with
-- a list of pairs for each tile (`tilesOfListingsRef`), on every scene above.
private def refTiles (s : Scene) : Array Nat :=
  tilesOfListingsRef s.width s.height s.compiled
    (s.compiled.toArray.map (Primitive.tileListing s.mapping ((s.width+tileSize-1)/tileSize) ((s.height+tileSize-1)/tileSize)))
#guard [guardScene (),zoomScene "1",zoomScene "40",clippedZoom (),strokeScene ()].all fun o =>
  (o.map fun s => refTiles s == s.tiles) == some true
-- Cells list fewer pieces than their tile: on the stroke scene some tile's cells list
-- different numbers of pieces.
#guard ((strokeScene ()).map fun s =>
  let g : Grid := ⟨s.tiles⟩
  (List.range (g.across*g.down)).any fun t => !(g.rows t).isEmpty &&
    ((List.range (cellsPerSide*cellsPerSide)).map fun c => ((g.pieceList (g.edgeWord t 0) c).map (·.size)).getD 0).eraseDups.length > 1) == some true

#print axioms samplePrepared_eq
#print axioms rasterPrepared_eq

end NativeSVG.Raster
