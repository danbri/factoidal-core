import SVG
import L4Factoidal.JSON.Parser

namespace NativeSVGCurveTests
open NativeSVG NativeSVGPath
private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def unwrap (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error message => throw (IO.userError message)
private def wrap (body : String) (attrs : String := "") : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' width='64' height='64' " ++ attrs ++ ">" ++ body ++ "</svg>"
private def path (data : String) (attrs : String := "") : String :=
  wrap ("<path d='" ++ data ++ "' fill='red' " ++ attrs ++ "/>")
private def same (actual expected label : String) : IO Unit := do
  let a ← unwrap (parse (path actual))
  let b ← unwrap (parse (path expected))
  check ((← unwrap a.artifact) == (← unwrap b.artifact)) label
private def expectedGreen (inside : Float → Float → Bool) (x y : Nat) : Float :=
  let offsets : List (Float × Float) := [(0.25,0.25),(0.75,0.25),(0.25,0.75),(0.75,0.75)]
  let count := offsets.foldl (fun n (dx,dy) => n+if inside (Float.ofNat x+dx) (Float.ofNat y+dy) then 1 else 0) 0
  Float.ofNat (4-count)/4

/-- Independent exact-geometry controls. Predicates are derived directly from
    the hand-written curves, without calling the parser, flattener or winding
    implementation. These are local math controls, not upstream relations. -/
def controls : List (String × String × (Float → Float → Bool)) :=
  [("quadratic",path "M0 0 Q16 32 32 0 Z",
      fun x y => 0 <= x && x <= 32 && 0 <= y && y <= 2*x-x*x/16),
   ("cubic",path "M0 0 C8 0 16 0 24 24 L0 24 Z",
      fun x y => 0 <= x && x <= 24 && x*x*x/576 <= y && y <= 24),
   ("arc",path "M16 24 A8 8 0 0 1 32 24 A8 8 0 0 1 16 24 Z",
      fun x y => (x-24)*(x-24)+(y-24)*(y-24) <= 64),
   ("compact-relative-arc",path "m16 24 a8 8 0 0116 0 8 8 0 01-16 0z",
      fun x y => (x-24)*(x-24)+(y-24)*(y-24) <= 64),
   ("arc-stroke",wrap "<path d='M16 24A8 8 0 0 1 32 24A8 8 0 0 1 16 24Z' fill='none' stroke='red' stroke-width='2'/>",
      fun x y => let radius2 := (x-24)*(x-24)+(y-24)*(y-24); 49 <= radius2 && radius2 <= 81)]

def writeControls (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for (name,xml,inside) in controls do
    let scene ← unwrap (parse xml)
    IO.FS.writeFile (directory / (name ++ ".svg")) xml
    IO.FS.writeFile (directory / (name ++ ".json")) (← unwrap scene.artifact)
    let mut expected := ByteArray.empty
    for y in List.range 64 do
      for x in List.range 64 do
        let green := ((expectedGreen inside x y)*255).round.toUInt32.toUInt8
        expected := expected.push 255 |>.push green |>.push green |>.push 255
    IO.FS.writeBinFile (directory / (name ++ ".expected.rgba")) expected

private def compiledPointCount (scene : Scene) : Nat :=
  scene.compiled.foldl (fun total primitive => total+match primitive.geometry with
    | .path contours => contours.foldl (fun count contour => count+contour.points.length) 0
    | _ => 0) 0

def run : IO Unit := do
  let coordinates := (List.range 40).flatMap fun y => (List.range 48).map fun x => (x,y)
  for (name,xml,inside) in controls do
    let scene ← unwrap (parse xml)
    for ((x,y),color) in coordinates.zip (scene.samplePixels coordinates) do
      let green := expectedGreen inside x y
      check (color.r == 1 && color.g == green && color.b == green)
        s!"{name}: independent exact curve pixel {x},{y}"
    IO.println s!"PASS {name}: independent analytic quarter-grid raster"
  same "M2 20 c4 -16 8 -16 12 0 s8 16 12 0"
    "M2 20 C6 4 10 4 14 20 C18 36 22 36 26 20" "relative cubic/smooth reflection"
  same "M2 20 q6 -16 12 0 t12 0"
    "M2 20 Q8 4 14 20 Q20 36 26 20" "relative quadratic/smooth reflection"
  for (separator,current) in [("L16 20","16 20"),("M16 20","16 20"),
      ("A2 2 0 0 1 16 20","16 20"),("Z","2 20")] do
    same ("M2 20 C6 4 10 4 14 20 " ++ separator ++ " S22 36 26 20")
      ("M2 20 C6 4 10 4 14 20 " ++ separator ++ " C" ++ current ++ " 22 36 26 20")
      "smooth cubic control did not reset after unrelated command"
    same ("M2 20 Q8 4 14 20 " ++ separator ++ " T26 20")
      ("M2 20 Q8 4 14 20 " ++ separator ++ " Q" ++ current ++ " 26 20")
      "smooth quadratic control did not reset after unrelated command"
  same "M16 24A-8 -8 0 0132 24 8 8 0 0116 24Z"
    "M16 24A8 8 0 0 1 32 24A8 8 0 0 1 16 24Z" "negative radii or compact flags"
  same "M16 24A4 4 0 0 1 32 24A4 4 0 0 1 16 24Z"
    "M16 24A8 8 0 0 1 32 24A8 8 0 0 1 16 24Z" "SVG radii correction"
  same "M4 4A0 8 0 0 1 20 12L4 12Z" "M4 4L20 12L4 12Z" "zero radius arc line replacement"
  same "M4 4A8 0 0 0 1 20 12L4 12Z" "M4 4L20 12L4 12Z" "zero second radius arc"
  same "M4 4A8 8 0 0 1 4 4L20 4L20 20Z" "M4 4L20 4L20 20Z" "coincident arc omission"
  let large ← unwrap (parse (path "M24 16A8 8 0 1 1 32 24L24 24Z"))
  let small ← unwrap (parse (path "M24 16A8 8 0 0 1 32 24L24 24Z"))
  check ((large.samplePixel 36 16).g == 0 && (small.samplePixel 36 16).g == 1) "large arc flag has no geometry effect"
  let backwards ← unwrap (parse (path "M16 24A8 8 0 0 0 32 24A8 8 0 0 0 16 24Z"))
  check ((backwards.samplePixel 24 24).g == 0) "negative sweep arc did not fill circle"
  let arcData := "M16 24A8 8 0 0 1 32 24A8 8 0 0 1 16 24Z"
  let strokeXML := fun extra => wrap ("<path d='" ++ arcData ++ "' fill='none' stroke='red' stroke-width='2' " ++ extra ++ "/>")
  let solidStroke ← unwrap (parse (strokeXML ""))
  for (x,y) in [(31,23),(32,23)] do check ((solidStroke.samplePixel x y).g == 0) "curved annular stroke interior missing"
  for (x,y) in [(30,23),(33,23)] do check ((solidStroke.samplePixel x y).g == 1) "curved annular stroke hole or exterior painted"
  let dashed ← unwrap (parse (strokeXML "stroke-dasharray='4 100'"))
  check ((dashed.samplePixel 16 22).g == 0 && (dashed.samplePixel 23 16).g == 1) "curved dash phase or gap not rendered"
  let calibrated ← unwrap (parse (strokeXML "stroke-dasharray='10 100' pathLength='100'"))
  let ordinary ← unwrap (parse (strokeXML "stroke-dasharray='10 100'"))
  check ((calibrated.samplePixel 18 18).g == 1 && (ordinary.samplePixel 18 18).g == 0) "curve pathLength did not calibrate real stroke intervals"
  let percent ← unwrap (parse (strokeXML "stroke-dasharray='10% 100%'"))
  let percentCalibrated ← unwrap (parse (strokeXML "stroke-dasharray='10% 100%' pathLength='100'"))
  check ((← unwrap percent.artifact) == (← unwrap percentCalibrated.artifact)) "curve pathLength incorrectly calibrated percentage distances"
  let (some (_,quadratic,_)) := controls.head? | throw (IO.userError "quadratic control missing")
  let base ← unwrap (parse quadratic)
  let magnified ← unwrap (parse (quadratic.replace "width='64' height='64'" "width='64' height='64' viewBox='0 0 32 32'"))
  check (compiledPointCount magnified > compiledPointCount base) "root viewport magnification did not refine curve metric"
  let primitiveScaled ← unwrap (parse (path "M0 0Q16 32 32 0Z" "transform='scale(2)'"))
  check (compiledPointCount primitiveScaled == compiledPointCount magnified) "primitive and viewport scale use different flatness metric"
  let strokePath := wrap "<path d='M10 10' fill='none' stroke='red' stroke-width='4' stroke-linecap='round'/>"
  let noStroke ← unwrap (parse strokePath)
  check ((noStroke.samplePixel 10 10).g == 1) "moveto-only subpath incorrectly capped"
  let zeroLine ← unwrap (parse (strokePath.replace "M10 10" "M10 10L10 10"))
  check ((zeroLine.samplePixel 10 10).g == 0) "zero-length drawing segment lost round cap"
  let zeroClose ← unwrap (parse (strokePath.replace "M10 10" "M10 10Z"))
  check ((zeroClose.samplePixel 10 10).g == 0) "zero-length closed subpath lost round cap"
  let omittedArc ← unwrap (parse (strokePath.replace "M10 10" "M10 10A8 8 0 0 1 10 10"))
  check ((omittedArc.samplePixel 10 10).g == 1) "omitted coincident arc manufactured a stroke"
  let enormous := parse (path "M0 0Q16 32 32 0Z" "transform='scale(1000000)'")
  check (!enormous.isOk) "over-budget magnified curve silently substituted a chord"
  for malformed in ["M0 0C1 2 3 4","M0 0S1 2","M0 0Q1 2","M0 0T1",
      "M0 0A8 8 0 2 0 4 4","M0 0A8 8 0 0 +1 4 4","M0 0A8 8 0 0 1 4",
      "M0 0A8 8 0 .0 1 4 4","M0 0C1000001 0 1 1 2 2"] do
    check (!(parse (path malformed)).isOk) ("malformed curve accepted: " ++ malformed)
  IO.println "PASS actual Q/C/A analytic pixels, all smooth/relative/repeated commands, flags, radii/degeneracy, stroke caps and screen-aware budget"
#eval run
end NativeSVGCurveTests
