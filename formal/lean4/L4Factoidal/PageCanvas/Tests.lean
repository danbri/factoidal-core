/-
L4Factoidal.PageCanvas.Tests: `#guard` cases for Canvas 2D: colours, fonts, and pixels of
small scenes against the values a browser gives (record
docs/designissues/2026-11-08-canvas-2d.md).
-/
import L4Factoidal.PageCanvas.Theorems

namespace L4Factoidal.PageCanvas.Tests
open L4Factoidal.PageCanvas

def ser (s : String) : String := ((Color.parse? s).map Color.serialize).getD "invalid"

#guard ser "#f00" == "#ff0000"
#guard ser "red" == "#ff0000"
#guard ser "rgba(0, 255, 0, 0.5)" == "rgba(0, 255, 0, 0.5)"
#guard ser "rgb(0 255 0 / 50%)" == "rgba(0, 255, 0, 0.5)"
#guard ser "hsl(120, 100%, 50%)" == "#00ff00"
#guard ser "hsla(120, 100%, 50%, 0.499)" == "rgba(0, 255, 0, 0.498)"
#guard ser "transparent" == "rgba(0, 0, 0, 0)"
#guard ser "#12345678" == "rgba(18, 52, 86, 0.47)"
#guard ser "rgb(255, 0, 0, 0.2)" == "rgba(255, 0, 0, 0.2)"
#guard ser "nonsense" == "invalid"
#guard ser "rgb(255, 0 0)" == "invalid"

def font (s : String) : String := ((Text.parseFont? s).map (·.text)).getD "invalid"
#guard font "20px serif" == "20px serif"
#guard font "bold 1.5em serif" == "bold 15px serif"
#guard font "italic 400 12px/2 Unknown Font, sans-serif" == "italic 12px Unknown Font, sans-serif"
#guard font "nonsense" == "invalid"

/-- Run a display list on one fresh canvas and give its straight RGBA at a pixel. -/
def pixel (w h : Nat) (cmds : List Cmd) (x y : Nat) : List Nat :=
  let s := ({} : Store).run {} (#[Cmd.init 1 w h true] ++ cmds.toArray)
  match s.canvases.get? 1 with
  | some c => (c.straight x y 1 1).toList.map (·.toNat)
  | none => []

#guard pixel 10 10 [.fillColor "#0f0", .fillRect 0 0 10 10] 5 5 == [0, 255, 0, 255]
#guard pixel 10 10 [.fillColor "#0f0", .fillRect 0 0 5 10] 7 5 == [0, 0, 0, 0]
-- A path: nonzero and even-odd rules on two nested squares of the same direction.
#guard pixel 20 20 [.fillColor "#00f", .rect 0 0 20 20, .rect 5 5 10 10, .fill 0 .evenodd] 10 10 == [0, 0, 0, 0]
#guard pixel 20 20 [.fillColor "#00f", .rect 0 0 20 20, .rect 5 5 10 10, .fill 0 .nonzero] 10 10 == [0, 0, 255, 255]
-- save, a change, restore: the colour of the save.
#guard pixel 10 10 [.fillColor "#f00", .save, .fillColor "#0f0", .restore, .fillRect 0 0 10 10] 5 5 == [255, 0, 0, 255]
-- Transforms: translate moves the rectangle.
#guard pixel 20 20 [.translate 10 0, .fillRect 0 0 5 5] 12 2 == [0, 0, 0, 255]
#guard pixel 20 20 [.translate 10 0, .fillRect 0 0 5 5] 2 2 == [0, 0, 0, 0]
-- globalAlpha and source-over.
#guard pixel 4 4 [.fillColor "#fff", .fillRect 0 0 4 4, .alpha 0.5, .fillColor "#000", .fillRect 0 0 4 4] 1 1 == [128, 128, 128, 255]
-- clearRect.
#guard pixel 4 4 [.fillRect 0 0 4 4, .clearRect 0 0 2 4] 1 1 == [0, 0, 0, 0]
#guard pixel 4 4 [.fillRect 0 0 4 4, .clearRect 0 0 2 4] 3 1 == [0, 0, 0, 255]
-- A clip: only inside the clip rectangle.
#guard pixel 10 10 [.rect 0 0 5 10, .clip 0 .nonzero, .fillColor "#0f0", .fillRect 0 0 10 10] 7 5 == [0, 0, 0, 0]
#guard pixel 10 10 [.rect 0 0 5 10, .clip 0 .nonzero, .fillColor "#0f0", .fillRect 0 0 10 10] 2 5 == [0, 255, 0, 255]
-- A stroke of width 4 along y = 5.
#guard pixel 10 10 [.lineWidth 4, .moveTo 0 5, .lineTo 10 5, .stroke 0] 5 5 == [0, 0, 0, 255]
#guard pixel 10 10 [.lineWidth 4, .moveTo 0 5, .lineTo 10 5, .stroke 0] 5 0 == [0, 0, 0, 0]
-- An arc filled: the centre is inside, a corner is not.
#guard pixel 20 20 [.arc 10 10 8 0 6.3 false, .fill 0 .nonzero] 10 10 == [0, 0, 0, 255]
#guard pixel 20 20 [.arc 10 10 8 0 6.3 false, .fill 0 .nonzero] 1 1 == [0, 0, 0, 0]
-- copy replaces outside the shape too.
#guard pixel 4 4 [.fillRect 0 0 4 4, .composite "copy", .fillColor "#f00", .fillRect 0 0 2 2] 3 3 == [0, 0, 0, 0]
-- destination-out removes.
#guard pixel 4 4 [.fillRect 0 0 4 4, .composite "destination-out", .fillRect 0 0 2 2] 1 1 == [0, 0, 0, 0]
-- A linear gradient from red to blue across 100 pixels: the middle is half of each.
#guard pixel 100 1 [.gradientNew 7 (.linear 0 0 100 0), .fillObj 1 7, .fillRect 0 0 100 1] 0 0 == [0, 0, 0, 0]

-- putImageData then getImageData gives the same straight pixels (opaque).
#guard
  let s := ({} : Store).run {} #[.init 1 2 1 true, .putImageData (ByteArray.mk #[10, 20, 30, 255, 40, 50, 60, 255]) 2 1 0 0 0 0 2 1]
  ((s.canvases.get? 1).map fun c => (c.straight 0 0 2 1).toList.map (·.toNat)) == some [10, 20, 30, 255, 40, 50, 60, 255]

-- The PNG of a canvas decodes back (zlib stream: 2 bytes, stored blocks, Adler-32).
#guard
  let png := Png.encode 2 1 (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8])
  let idat := png.extract (8 + 25 + 8) (png.size - 12 - 4)
  (L4Factoidal.Codec.inflate (idat.extract 2 (idat.size - 4))).toOption.map (·.toList) == some [0, 1, 2, 3, 4, 5, 6, 7, 8]

#guard Png.base64 "hello".toUTF8 == "aGVsbG8="

-- Numbers as text read back exactly (JavaScript's Number::toString forms).
#guard (Wire.textNumbers "1.5,-0.1,1e+21,123456789.123,5e-324,0.30000000000000004,-0".toUTF8).toList.map Float.toBits ==
  [1.5, -0.1, 1e21, 123456789.123, 5e-324, 0.30000000000000004, -0.0].map Float.toBits

-- The merge sort of crossings and edges: sorted, stable.
#guard (sortBy id #[3.0, 1, 2, 1, 5, 0, 4]).toList == [0, 1, 1, 2, 3, 4, 5]
#guard (sortBy (·.1) #[(1.0, 1), (0.0, 2), (1.0, 3)]).toList.map (·.2) == [2, 1, 3]
-- 1,000 rectangles at one place: the fill is the same as one.
#guard pixel 10 10 ((List.range 1000).map (fun _ => Cmd.rect 0 0 5 5) ++ [.fill 0 .nonzero]) 2 2 == [0, 0, 0, 255]

/-! ### `composite` against `compositeRef` (issue 1098)

The fast source-over path must give the bytes of the reference. Each case draws on a
destination of pseudo-random bytes, under each clip (none; random bytes with 0 and 255 among
them), and takes the opaque, table and per-pixel branches of `compositeOver`. -/

/-- Pseudo-random bytes (a linear congruential sequence). -/
def noise (n seed : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  let mut v := seed
  for _ in [0:n] do
    v := (v * 1103515245 + 12345) % 2147483648
    out := out.push (v / 65536 % 256).toUInt8
  return out

/-- A clip mask with whole, empty and partial pixels. -/
def noiseMask (n seed : Nat) : ByteArray :=
  (noise n seed).foldl (init := ByteArray.empty) fun acc b =>
    acc.push (if b < 70 then 0 else if b < 170 then 255 else b)

def diffW : Nat := 64
def diffH : Nat := 40

/-- Coverages of rectangles (whole, fractional, larger than the canvas) and polygons. -/
def diffCovs : List Coverage :=
  let W := diffW
  let H := diffH
  [ rectCoverage W H 0 0 (nf W) (nf H),
    rectCoverage W H 3.25 2.5 50.75 31.5,
    rectCoverage W H (-5) (-5) 100 100,
    coverage W H (edgesOf #[⟨FloatArray.mk #[2, 1, 60, 8, 20, 39], true⟩]) .nonzero,
    coverage W H (edgesOf #[⟨FloatArray.mk #[0, 0, 64, 0, 64, 40, 0, 40], true⟩,
      ⟨FloatArray.mk #[10, 10, 30, 10, 30, 30, 10, 30], true⟩]) .evenodd]

/-- Draws of every kind of paint and coverage, at each alpha. -/
def diffDraws : List Draw := Id.run do
  let covs := diffCovs
  let grad : Gradient := { kind := .linear 0 2 0 35, stops := #[⟨0, ⟨32, 48, 96, 1⟩⟩, ⟨1, ⟨192, 128, 80, 1⟩⟩] }
  let gradA : Gradient := { grad with stops := #[⟨0, ⟨255, 0, 0, 0.5⟩⟩, ⟨1, ⟨0, 0, 255, 1⟩⟩] }
  let gradX : Gradient := { grad with kind := .linear 3 0 60 4 }
  let rad : Gradient := { grad with kind := .radial 30 20 2 30 20 25 }
  let ready := fun (g : Gradient) (m : Matrix) => (Style.gradient 1).ready (fun _ => some g) (fun _ => none) m false
  let readies : List Ready := [
    .solid (RGBA.px ⟨16, 19, 31, 1⟩), .solid (RGBA.px ⟨224, 0, 0, 1⟩), .solid (RGBA.px ⟨255, 128, 0, 0.6⟩),
    .solid Px.zero, ready grad {}, ready grad { a := 1.25, d := 1.25 }, ready grad { a := -0.0, b := -0.0, c := 0, d := 2, f := -3 },
    ready gradA { a := 1.25, d := 1.25 }, ready gradX {}, ready rad {},
    .pattern {} ⟨⟨2, 2, ByteArray.mk #[255, 0, 0, 255, 0, 128, 0, 128, 0, 0, 255, 255, 10, 20, 30, 40]⟩, ⟨true, true⟩, {}, false⟩ true]
  let mut out := []
  for cov in covs do
    for r in readies do
      for a in [1.0, 0.5, 0.3] do
        for clip in [none, some (noiseMask (diffW * diffH) 7)] do
          out := ⟨r, cov, a, .sourceOver, clip⟩ :: out
  return out

/-- The draws whose fast result differs from the reference (none). -/
def diffFails : List Nat := Id.run do
  let bm := noise (diffW * diffH * 4) 11
  let mut bad := []
  let mut i := 0
  for d in diffDraws do
    if composite diffW diffH bm d != compositeRef diffW diffH bm d then bad := i :: bad
    i := i + 1
  return bad

#guard diffDraws.length == 330
#guard diffFails == []
-- The operators other than source-over are the reference itself.
#guard
  let bm := noise (diffW * diffH * 4) 3
  let d : Draw := ⟨.solid (RGBA.px ⟨255, 0, 0, 0.5⟩), rectCoverage diffW diffH 1 1 30 30, 1, .multiply, none⟩
  composite diffW diffH bm d == compositeRef diffW diffH bm d
-- The branches were taken: the opaque fill, the table (a draw of at least `tableMin` pixels) and
-- a constant gradient row.
#guard diffW * diffH ≥ tableMin
#guard rowConstant ((Style.gradient 1).ready (fun _ => some { kind := .linear 0 2 0 35, stops := #[⟨0, RGBA.black⟩] }) (fun _ => none) { a := 1.25, d := 1.25 } false)

-- The rectangle coverage with column shares computed once is the reference, value for value.
#guard [(⟨0, 0, 64, 40⟩, 0.0, 0.0, 64.0, 40.0), (⟨3, 2, 48, 30⟩, 3.25, 2.5, 50.75, 31.5),
    (⟨0, 0, 64, 40⟩, -5.0, -5.0, 100.0, 100.0), (⟨10, 10, 1, 1⟩, 10.2, 10.3, 10.7, 10.9),
    (⟨0, 0, 0, 5⟩, 1.0, 1.0, 1.0, 3.0)].all fun ((b : Box), x0, y0, x1, y1) =>
  (rectCoverageIn b x0 y0 x1 y1).data.map Float.toBits == (rectCoverageInRef b x0 y0 x1 y1).data.map Float.toBits

/-- The row loop of `coverageIn` as it was before `rowSums` (a `for` loop), the reference. -/
def rowSumsRef (w base lo hi : Nat) (cov diff direct : FloatArray) : FloatArray × FloatArray × FloatArray := Id.run do
  let mut cov := cov
  let mut diff := diff
  let mut direct := direct
  let mut run := 0.0
  for i in [lo:hi+1] do
    run := run + diff[i]!
    if i < w then
      let c := run + direct[i]!
      cov := cov.set! (base + i) (if c <= 0 then 0 else if c >= 1 then 1 else c)
    diff := diff.set! i 0
    direct := direct.set! i 0
  return (cov, diff, direct)

/-- Floats in -0.6 .. 1.4 from noise bytes, some of them exact multiples of 1/16. -/
def noiseFloats (n seed : Nat) : FloatArray :=
  (noise n seed).foldl (init := FloatArray.empty) fun acc b =>
    acc.push (if b % 3 == 0 then nf (b.toNat % 16) / 16 else nf b.toNat / 128 - 0.6)

-- `rowSums` is the old row loop, bit for bit, on every span of a 20-column row.
#guard (List.range 21).all fun lo => (List.range 21).all fun hi =>
  lo > hi ||
  let w := 20
  let (c1, d1, e1) := rowSums w 40 (hi + 1) (hi + 1 - lo) lo 0 (noiseFloats 80 lo) (noiseFloats 22 (hi + 5)) (noiseFloats 22 (lo + hi + 9))
  let (c2, d2, e2) := rowSumsRef w 40 lo hi (noiseFloats 80 lo) (noiseFloats 22 (hi + 5)) (noiseFloats 22 (lo + hi + 9))
  c1.data.map Float.toBits == c2.data.map Float.toBits && d1.data.map Float.toBits == d2.data.map Float.toBits &&
    e1.data.map Float.toBits == e2.data.map Float.toBits

-- The clip mask by rows on `USize` indices is the reference mask, under no clip and under one.
#guard diffCovs.all fun cov => [none, some (noiseMask (diffW * diffH) 7)].all fun old =>
  clipMask diffW (diffW * diffH) cov old == clipMaskRef diffW (diffW * diffH) cov old


-- Binary numbers of a batch (op 200): little-endian binary64, read at any offset.
#guard (Wire.f64 ⟨#[0, 0, 0, 0, 0, 0, 0xF8, 0x3F]⟩ 0).toBits == (1.5 : Float).toBits
#guard (Wire.f64 ⟨#[9, 0x9A, 0x99, 0x99, 0x99, 0x99, 0x99, 0xB9, 0xBF]⟩ 1).toBits == (-0.1 : Float).toBits

/-! ### Rectangle uploads (issue 1098)

The host keeps a texture and writes into it only the rectangle of each `pixels` command. After
every batch, that texture must equal the whole canvas (straight RGBA). -/

/-- The host's reading of `rleRect`'s output (`unrle` of page-gpu.mjs): `n` pixels. -/
def unrleBytes (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (n * 4)
  let mut i := 0
  let mut p := 0
  for _ in [0:n + 1] do
    if i + 4 > b.size || p >= n then break
    let head := Wire.u32 b i
    i := i + 4
    let k := min (head % 2147483648) (n - p)
    if head >= 2147483648 then
      for q in [0:4 * k] do out := out.push b[i + q]!
      i := i + 4 * (head % 2147483648)
    else
      for _ in [0:k] do out := (((out.push b[i]!).push b[i+1]!).push b[i+2]!).push b[i+3]!
      i := i + 4
    p := p + k
  return out

/-- Run the batches on one `w × h` canvas, apply each emitted rectangle to a texture, and
compare it with the canvas after every batch. Also the total pixels sent. -/
def uploads (w h : Nat) (batches : List (List Cmd)) : Bool × Nat := Id.run do
  let mut s : Store := {}
  let mut tex := ByteArray.mk (Array.replicate (w * h * 4) 0)
  let mut ok := true
  let mut sent := 0
  let mut first := true
  for b in batches do
    s := s.run {} ((if first then #[Cmd.init 1 w h true] else #[Cmd.select 1]) ++ b.toArray)
    first := false
    let (s', out) := s.emit
    s := s'
    for hc in out do
      match hc with
      | .pixels _ W _ x y pw ph data =>
        let px := unrleBytes (rleRect data W x y pw ph) (pw * ph)
        sent := sent + pw * ph
        for j in [0:ph] do
          for i in [0:pw * 4] do
            tex := tex.set! (((y + j) * w + x) * 4 + i) px[j * pw * 4 + i]!
      | _ => pure ()
    match s.canvases.get? 1 with
    | some c => ok := ok && tex.toList == (c.straight 0 0 w h).toList
    | none => ok := false
  return (ok, sent)

-- A small rect after the first frame sends only its own pixels (20 × 10 canvas: 200, then 6).
#guard uploads 20 10 [[.fillColor "#0f0", .fillRect 0 0 20 10], [.fillColor "#f00", .fillRect 3 4 3 2]] == (true, 206)
-- Fractional edges, alpha, a stroke, a clear, a partial clearRect, a path.
#guard (uploads 20 10 [[.fillColor "#00f", .fillRect 1.5 2.25 4.5 3],
  [.alpha 0.5, .fillColor "#f80", .fillRect 10.3 1.7 6 6],
  [.strokeColor "#000", .lineWidth 2, .strokeRect 2 2 8 5],
  [.clearRect 4 3 3 3],
  [.beginPath, .moveTo 1 1, .lineTo 18 8, .lineTo 3 9, .closePath, .fill 0 .nonzero],
  [.clearRect 0 0 20 10]]).1
-- An unbounded operator (copy) changes pixels outside the shape.
#guard (uploads 20 10 [[.fillColor "#0f0", .fillRect 0 0 20 10], [.composite "copy", .fillColor "#f00", .fillRect 2 2 3 3]]).1
-- A shadow is drawn outside the shape's box.
#guard (uploads 20 10 [[], [.shadowColor "#000", .shadowBlur 4, .shadowX 3, .shadowY 2, .fillColor "#f00", .fillRect 5 3 4 3]]).1
-- putImageData writes its own rectangle; reset clears all.
#guard (uploads 8 6 [[], [.putImageData ⟨#[255, 0, 0, 255, 0, 255, 0, 128, 0, 0, 255, 255, 9, 9, 9, 0]⟩ 2 2 3 1 0 0 2 2], [.reset]]).1
-- A batch that draws nothing sends nothing.
#guard uploads 20 10 [[.fillColor "#0f0", .fillRect 0 0 20 10], [.fillColor "#f00"]] == (true, 200)

-- The run scan reads two pixels at a time: runs of odd and even length, a run that ends one
-- pixel before the range, and a run cut by the end of a row (8 x 3 canvas, rect 1..7).
#guard (uploads 8 3 [[.fillColor "#0f0", .fillRect 0 0 8 3], [.fillColor "#f00", .fillRect 1 0 5 1, .fillRect 2 1 2 1, .fillRect 1 2 6 1]]).1
#guard (uploads 9 2 [[.fillColor "#00f", .fillRect 0 0 7 2], [.fillColor "#ff0", .fillRect 0 0 1 2, .fillRect 8 1 1 1]]).1
#guard unrleBytes (rleRect ⟨#[1,2,3,255, 1,2,3,255, 1,2,3,255, 1,2,3,255, 1,2,3,255, 9,9,9,255]⟩ 6 0 0 6 1) 6 ==
  ⟨#[1,2,3,255, 1,2,3,255, 1,2,3,255, 1,2,3,255, 1,2,3,255, 9,9,9,255]⟩
#guard rleRect ⟨#[1,2,3,255, 1,2,3,255, 1,2,3,255, 1,2,3,255, 1,2,3,255, 9,9,9,255]⟩ 6 0 0 6 1 ==
  ⟨#[5, 0, 0, 0, 1, 2, 3, 255, 1, 0, 0, 128, 9, 9, 9, 255]⟩

end L4Factoidal.PageCanvas.Tests
