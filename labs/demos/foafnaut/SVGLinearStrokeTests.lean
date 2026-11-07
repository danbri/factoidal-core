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
  let .ok diagonal := NativeSVGStroke.retain [⟨[⟨0,0⟩,⟨1,1⟩,⟨2,2⟩,⟨3,3⟩],false⟩] [] 0 2 .round
    | throw (IO.userError "diagonal stroke refused")
  check (diagonal.any (fun p => match p with | .disk c _ => c.x==3 && c.y==3 | _ => false)) "Float subtraction lost terminal round cap"
  check ((diagonal.filter (fun p => match p with | .disk c _ => c.x==0 && c.y==0 | _ => false)).length==1) "terminal cap duplicated at start"
  check ((NativeSVGStroke.join ⟨0,0⟩ ⟨10,0⟩ ⟨10,10⟩ 2 4 .bevel).length==1) "bevel join is one triangle"
  check ((NativeSVGStroke.join ⟨0,0⟩ ⟨10,0⟩ ⟨10,10⟩ 2 4 .round).length==1) "round join is one disk"
  check ((NativeSVGStroke.join ⟨0,0⟩ ⟨10,0⟩ ⟨0,0⟩ 2 4 .round).length==1) "round join lost at a reversal"
  let corner (extra : String) := s!"<path d='M10 40H40V10' fill='none' stroke='black' stroke-width='10' {extra}/>"
  check (sample (corner "") 43 43==black && sample (corner "stroke-linejoin='miter'") 43 43==black) "miter join tip"
  check (sample (corner "stroke-linejoin='bevel'") 43 43==white && sample (corner "stroke-linejoin='bevel'") 41 41==black) "bevel join edge"
  check (sample (corner "stroke-linejoin='round'") 43 42==black && sample (corner "stroke-linejoin='bevel'") 43 42==white) "round join passes the bevel edge"
  check (sample (corner "stroke-linejoin='round'") 44 44==white) "round join stops at its radius"
  let acute (extra : String) := s!"<path d='M10 50L60 50L10 44' fill='none' stroke='black' stroke-width='4' {extra}/>"
  check (sample (acute "") 75 51==white) "default miterlimit 4 must bevel at ratio 16.8"
  check (sample (acute "stroke-miterlimit='20'") 75 51==black) "miterlimit 20 keeps the tip"
  check (sample (acute "stroke-miterlimit='16'") 75 51==white) "miterlimit 16 is below the ratio 16.8"
  check (sample ("<g stroke-linejoin='bevel' stroke-miterlimit='20'>"++corner ""++"</g>") 43 43==white) "join inherits from a group"
  check ((NativeSVG.parse (wrap (corner "stroke-miterlimit='.5'")) 100 100).isOk==false) "miterlimit below 1 admitted"
  check ((NativeSVG.parse (wrap (corner "stroke-linejoin='arcs'")) 100 100).isOk==false) "unknown join admitted"
  let ends (extra : String) := s!"<path d='M20 20H40' fill='none' stroke='black' stroke-width='10' {extra}/>"
  check (sample (ends "") 17 20==white) "butt cap passes its end"
  check (sample (ends "stroke-linecap='square'") 17 20==black && sample (ends "stroke-linecap='square'") 15 15==black) "square cap corner"
  check (sample (ends "stroke-linecap='square'") 46 20==white) "square cap passes half the width"
  check (sample (ends "stroke-linecap='round'") 17 20==black && sample (ends "stroke-linecap='round'") 15 15==white) "round cap has no corner"
  let dot (cap : String) := s!"<path d='M50 50L50 50' fill='none' stroke='black' stroke-width='10' stroke-linecap='{cap}'/>"
  check (sample (dot "butt") 50 50==white && sample (dot "square") 46 46==black && sample (dot "square") 56 50==white) "zero-length subpath caps"
  let dashes := "<path d='M10 10H60' fill='none' stroke='black' stroke-width='4' stroke-dasharray='10 10' stroke-linecap='square'/>"
  check (sample dashes 21 10==black && sample dashes 25 10==white && sample dashes 29 10==black) "square caps on each dash"
  check (sample "<rect x='20' y='20' width='20' height='20' fill='none' stroke='black' stroke-width='10' stroke-linejoin='bevel'/>" 15 15==white) "rectangle bevel corner"
  check (sample "<polygon points='20,20 40,20 40,40 20,40' fill='none' stroke='black' stroke-width='10' stroke-linejoin='round'/>" 42 42==black) "polygon round corner"
  check (sample "<line x1='20' y1='20' x2='40' y2='20' stroke='black' stroke-width='10' stroke-linecap='square'/>" 15 15==black) "line square cap"
  let ring (shape : String) := s!"<{shape} fill='none' stroke='black' stroke-width='6' stroke-dasharray='20 1000'/>"
  for shape in ["circle cx='50' cy='50' r='30'","ellipse cx='50' cy='50' rx='30' ry='30'"] do
    check (sample (ring shape) 79 53==black) "dashed outline starts at 3 o'clock"
    check (sample (ring shape) 79 46==white) "dashed outline goes towards 6 o'clock"
    check (sample (ring shape) 20 50==white) "dash reaches the far side"
  let spaced := "<circle cx='50' cy='50' r='30' fill='none' stroke='black' stroke-width='6' stroke-dasharray='10 10' stroke-linecap='round'/>"
  check (sample spaced 79 52==black) "round caps on a dashed circle"
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
  IO.println "PASS linear stroke closure, caps, joins, miterlimit, phase, pathLength, opacity, offsets and official admission"
end NativeSVGLinearStrokeTests
#eval NativeSVGLinearStrokeTests.run
