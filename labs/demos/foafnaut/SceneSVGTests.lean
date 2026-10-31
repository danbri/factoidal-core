import SceneSVG
import Font
import SVG

namespace NativeSceneSVGTests
open NativeGraphics
private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def xmlOf (s : Scene) : IO String :=
  match NativeSceneSVG.serialize s with
  | .ok xml => pure xml | .error e => throw (IO.userError e)
private def rgbJSON (c : RGB) : String :=
  "{\"rgb\":[" ++ toString c.r ++ "," ++ toString c.g ++ "," ++ toString c.b ++ "]}"
private def sampleAgreement (s : Scene) (xml : String) (points : List (Nat × Nat)) : IO Unit := do
  for (x,y) in points do
    check (NativeSVG.sample xml 0 0 x.toUInt32 y.toUInt32 == rgbJSON (s.sample x y)) s!"sample mismatch at {x},{y}"

def run : IO Unit := do
  let black : RGB := ⟨0,0,0⟩
  let white : RGB := ⟨255,255,255⟩
  let scene : Scene := {
    width:=32
    height:=24
    background:=⟨23,31,47⟩
    shapes:=[.circle ⟨8,8⟩ 5 ⟨40,210,150⟩,.rectangle ⟨17,4⟩ ⟨9,10⟩ ⟨240,160,90⟩,
      .segment ⟨4,18⟩ ⟨26,18⟩ 5 ⟨120,140,250⟩]}
  let xml ← xmlOf scene
  check (xml.startsWith "<svg xmlns=\"http://www.w3.org/2000/svg\"") "standalone namespace"
  check ((NativeSVG.parse xml).isOk) "primitive scene refused"
  let points := (List.range 24).flatMap fun y => (List.range 32).map fun x => (x,y)
  sampleAgreement scene xml points
  IO.println "PASS circles, rectangles, background and round segment SVG roundtrip"

  for (a,b,width) in [(Point.mk 5 6,Point.mk 24 19,5),(Point.mk 16 12,Point.mk 16 12,7),
      (Point.mk 24 5,Point.mk 4 20,4)] do
    let s : Scene := {width:=32,height:=24,background:=white,shapes:=[.segment a b width black]}
    sampleAgreement s (← xmlOf s) points
  IO.println "PASS diagonal, endpoint and zero-length capsule geometry"
  -- This exact strip-boundary tie exposed roundoff in the old native
  -- projection-distance evaluator. Pin SVG's analytic result separately;
  -- general Float/native/WGSL rounding equivalence is not asserted.
  let tie : Scene := {
    width:=32
    height:=24
    background:=white
    shapes:=[.segment ⟨24,5⟩ ⟨4,20⟩ 3 black]}
  check (NativeSVG.sample (← xmlOf tie) 0 0 7 15 == rgbJSON black) "analytic capsule boundary"
  let caps := "<svg xmlns='http://www.w3.org/2000/svg' width='32' height='24'>" ++
    "<g stroke='black' stroke-width='4' stroke-linecap='round'>" ++
    "<line x1='10' y1='6.5' x2='20' y2='6.5' stroke-linecap='inherit'/>" ++
    "<line x1='10' y1='16.5' x2='20' y2='16.5' stroke-linecap='butt'/></g></svg>"
  check (NativeSVG.sample caps 0 0 8 6 == rgbJSON black) "round cap inheritance"
  check (NativeSVG.sample caps 0 0 8 16 == rgbJSON white) "butt cap override"

  let glyphs : Scene := {
    width:=32
    height:=24
    background:=white
    shapes:=NativeFont.text ⟨1,3⟩ 1 "a:/" black ++ [.glyph ⟨0,0⟩ 0 ⟨31,31,31,31,31,31,31⟩ black]}
  let glyphXML ← xmlOf glyphs
  check ((glyphXML.splitOn "<text").length == 1) "SVG text dependency introduced"
  check ((glyphXML.splitOn "<path").length == 4) "glyphs were not batched into three compound paths"
  sampleAgreement glyphs glyphXML points
  check (match NativeSceneSVG.shapeElements (.glyph ⟨0,0⟩ 1 ⟨0,0,0,0,0,0,0⟩ black) with
    | .ok xs => xs.isEmpty | .error _ => false) "blank glyph paints"
  check ((NativeSceneSVG.shapeElements (.glyph ⟨0,0⟩ 1 ⟨32,0,0,0,0,0,0⟩ black)).isOk == false) "invalid glyph bits accepted"
  IO.println "PASS case-preserving glyph cells without SVG fonts"

  let curves : Scene := {
    width:=32
    height:=24
    background:=white
    shapes:=[.quadratic ⟨1,2⟩ ⟨8,20⟩ ⟨25,4⟩ 2 black,
      .cubic ⟨1,2⟩ ⟨8,20⟩ ⟨16,0⟩ ⟨25,4⟩ 3 black]}
  let curveXML ← xmlOf curves
  check ((curveXML.splitOn "Q 8 20 25 4").length == 2 && (curveXML.splitOn "C 8 20 16 0 25 4").length == 2) "Bezier path semantics flattened"
  check ((NativeSVG.parse curveXML).isOk == false) "native curve support silently invented"
  for shape in [Shape.circle ⟨0,0⟩ 0 black,.rectangle ⟨0,0⟩ ⟨0,5⟩ black,
    .segment ⟨0,0⟩ ⟨3,3⟩ 0 black,.circle ⟨0,0⟩ 1 ⟨256,0,0⟩] do
    check ((NativeSceneSVG.shapeElements shape).isOk == false) "unrepresentable native shape silently accepted"
  check ((NativeSceneSVG.serialize {width:=0,height:=4,background:=white,shapes:=[]}).isOk == false) "empty viewport accepted"
  let large : Scene := {
    width:=32
    height:=24
    background:=white
    shapes:=List.replicate 12288 (.circle ⟨4,4⟩ 1 black)}
  check ((NativeSVG.parse (← xmlOf large)).isOk == false) "consumer primitive capacity silently raised"
  IO.println "PASS explicit curve, degenerate-input and consumer-capacity boundaries"
  IO.println "4 SceneSVG native test groups passed; no GPU/browser result"

#eval run
end NativeSceneSVGTests
