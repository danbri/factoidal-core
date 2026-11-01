import SVG
import SVGDash
namespace NativeSVGDashTests
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def wrap (body : String) := "<svg xmlns='http://www.w3.org/2000/svg' width='100' height='100'>"++body++"</svg>"
private def sample (body : String) (x y : UInt32) := NativeSVG.sample (wrap body) 0 0 x y
private def black := "{\"rgb\":[0,0,0]}"
private def white := "{\"rgb\":[255,255,255]}"
def run : IO Unit := do
  let odd ← match NativeSVGDash.normalize [2,3,4] with | .ok a => pure a | .error e => throw (IO.userError e)
  check (odd == [2,3,4,2,3,4]) "odd array duplication"
  check ((NativeSVGDash.normalize [0,0]).toOption == some []) "zero sum solid"
  check (!(NativeSVGDash.normalize [1,-1]).isOk) "negative dash admitted"
  check (!(NativeSVGDash.normalize [1.0e308,1.0e308]).isOk) "nonfinite period admitted"
  check (!(NativeSVGDash.normalize [1.0e308]).isOk) "odd expansion nonfinite period admitted"
  check (!(NativeSVGDash.intervals [0.000000001,0.000000001] 1000000 10).isOk) "unreliable phase accepted"
  let spans ← match NativeSVGDash.intervals [10,10] (-5) 30 with | .ok a => pure a | .error e => throw (IO.userError e)
  check (spans.length==2 && spans[0]!.first==5 && spans[0]!.last==15 && spans[1]!.first==25) "negative offset phase"
  let line := "<line x1='10' y1='20' x2='90' y2='20' stroke='black' stroke-width='6' stroke-dasharray='10 10'/>"
  check (sample line 15 20 == black && sample line 25 20 == white && sample line 35 20 == black) "line dash positions"
  let shifted := "<line x1='10' y1='20' x2='90' y2='20' stroke='black' stroke-width='6' stroke-dasharray='10 10' stroke-dashoffset='-5'/>"
  check (sample shifted 11 20 == white && sample shifted 16 20 == black) "negative offset pixels"
  let rect := "<rect x='20' y='20' width='40' height='20' fill='none' stroke='black' stroke-width='10' stroke-dasharray='60 20'/>"
  check (sample rect 63 17 == black) "dash crossing corner miter"
  check (sample rect 63 43 == white) "butt endpoint must not gain corner join"
  let seam := "<rect x='20' y='20' width='40' height='20' fill='none' stroke='black' stroke-width='10' stroke-dasharray='70 10'/>"
  check (sample seam 17 17 == black) "closed seam join"
  let dot := "<line x1='20' y1='20' x2='80' y2='20' stroke='black' stroke-width='8' stroke-linecap='round' stroke-dasharray='0 10'/>"
  check (sample dot 21 21 == black && sample dot 25 20 == white) "zero-length round dashes"
  let alpha := "<line x1='20' y1='20' x2='80' y2='20' stroke='red' stroke-width='10' stroke-linecap='round' stroke-dasharray='2 2' stroke-opacity='0.5' opacity='0.5'/>"
  check (sample alpha 23 20 == "{\"rgb\":[255,191,191]}") "overlapping caps composited more than once"
  let zero := "<line x1='20' y1='20' x2='20' y2='20' stroke='black' stroke-width='8' stroke-linecap='round' stroke-dasharray='4 4'/>"
  check (sample zero 21 21 == black) "zero-length line round cap"
  for file in ["percentage.svg", "percentage-attribute.svg"] do
    let xml ← IO.FS.readFile ("../../tests/external/svg/upstream/svg/painting/reftests/"++file)
    check ((NativeSVG.parse xml 800 600).isOk) ("unchanged fixture refused: "++file)
  IO.println "PASS SVG dash intervals, phase, corners, caps, opacity and unchanged percentage fixture admission"
end NativeSVGDashTests
#eval NativeSVGDashTests.run
