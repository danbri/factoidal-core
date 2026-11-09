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

end L4Factoidal.PageCanvas.Tests
