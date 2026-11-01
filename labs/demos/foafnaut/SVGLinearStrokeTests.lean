import SVG
import SVGStroke
namespace NativeSVGLinearStrokeTests
open NativeSVG NativeSVGPath NativeSVGStroke
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def wrap (body : String) := "<svg xmlns='http://www.w3.org/2000/svg' width='100' height='100'>"++body++"</svg>"
private def sample (body : String) (x y : UInt32) := NativeSVG.sample (wrap body) 0 0 x y
private def black := "{\"rgb\":[0,0,0]}"
private def white := "{\"rgb\":[255,255,255]}"
def run : IO Unit := do
  let vertices := [Point.mk 10 10,Point.mk 30 10,Point.mk 30 30]
  check ((NativeSVGStroke.edges ⟨vertices,false⟩).length==2) "open contour closed by stroke"
  check ((NativeSVGStroke.edges ⟨vertices,true⟩).length==3) "explicit close missing"
  check ((NativeSVGStroke.join ⟨0,0⟩ ⟨10,0⟩ ⟨10,10⟩ 2 4).length==2) "right-angle miter"
  check ((NativeSVGStroke.join ⟨0,0⟩ ⟨10,0⟩ ⟨0,1⟩ 2 4).length==1) "acute miter must bevel"
  check ((NativeSVGStroke.join ⟨0,0⟩ ⟨10,0⟩ ⟨0,0⟩ 2 4).isEmpty) "reversal fabricated join"
  let openPath := "<path d='M10 10H30V30' fill='none' stroke='black' stroke-width='4'/>"
  let closedPath := "<path d='M10 10H30V30Z' fill='none' stroke='black' stroke-width='4'/>"
  check (sample openPath 20 20==white && sample closedPath 20 20==black) "fill closure leaked into stroke"
  check (sample openPath 31 8==black) "outer miter triangle not rendered"
  let triangle := "<polyline points='10,10 30,10 30,30' fill='none' stroke='black' stroke-width='4'/>"
  check (sample triangle 20 20==white && sample triangle 31 8==black) "polyline closure or join"
  let multi := "<path d='M10 20H50 M10 40H50' fill='none' stroke='black' stroke-width='4' pathLength='8' stroke-dasharray='1 1'/>"
  check (sample multi 15 20==black && sample multi 25 20==white && sample multi 15 40==black && sample multi 25 40==white) "total calibration and subpath phase reset"
  let round := "<path d='M20 20L20 20 M50 20H70' fill='none' stroke='black' stroke-width='8' stroke-linecap='round'/>"
  check (sample round 20 20==black && sample round 47 20==black) "zero-length and open round caps"
  let alpha := "<path d='M10 30H80 M30 10V80' fill='none' stroke='red' stroke-width='10' stroke-opacity='.5' opacity='.5'/>"
  check (sample alpha 30 30=="{\"rgb\":[255,191,191]}") "subpaths composited independently"
  let transformed := "<path d='M0 0H10V10' transform='translate(20 20) scale(2)' fill='none' stroke='black' stroke-width='4'/>"
  check (sample transformed 42 18==black && sample transformed 30 30==white) "path-tail transform offset"
  let polygon := "<polygon points='20,20 60,20 60,40 20,40' fill='none' stroke='black' stroke-width='6' stroke-dasharray='20 10'/>"
  let path := "<path d='M20 20H60V40H20Z' fill='none' stroke='black' stroke-width='6' stroke-dasharray='20 10'/>"
  for (x,y) in [(20,20),(35,20),(45,20),(60,30),(30,40),(20,35),(18,18)] do
    check (sample polygon x y == sample path x y) "polygon/path union mismatch"
  for file in ["pathlength-001.svg","pathlength-001-ref.svg","pathlength-004a.svg","pathlength-004-ref.svg"] do
    let xml ← IO.FS.readFile ("../../tests/external/svg/upstream/svg/shapes/reftests/"++file)
    check ((NativeSVG.parse xml 800 600).isOk) ("official linear fixture refused: "++file)
  IO.println "PASS linear stroke closure, caps, joins, miter fallback, phase, pathLength, opacity, offsets and official admission"
end NativeSVGLinearStrokeTests
#eval NativeSVGLinearStrokeTests.run
