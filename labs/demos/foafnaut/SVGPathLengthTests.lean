import SVG
namespace NativeSVGPathLengthTests
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def wrap (body : String) := "<svg xmlns='http://www.w3.org/2000/svg' width='100' height='100'>"++body++"</svg>"
private def line (attrs : String) := wrap ("<line x1='10' y1='20' x2='90' y2='20' stroke='black' stroke-width='6' "++attrs++"/>")
private def same (a b label : String) : IO Unit := do
  check ((NativeSVG.parse a).isOk && (NativeSVG.parse b).isOk) (label++" admission")
  check (NativeSVG.compile a 0 0 == NativeSVG.compile b 0 0) (label++" artifact equality")
def run : IO Unit := do
  same (line "pathLength='8' stroke-dasharray='1 1' stroke-dashoffset='-.5'")
    (line "stroke-dasharray='10 10' stroke-dashoffset='-5'") "line units and signed offset"
  same (line "pathLength='10' stroke-dasharray='10% 1' stroke-dashoffset='5%'")
    (line "stroke-dasharray='10 8' stroke-dashoffset='5'") "mixed percentages exempt"
  same (line "pathLength='10' stroke-dasharray='1 10% 2'")
    (line "stroke-dasharray='8 10 16'") "odd mixed pattern"
  same (line "pathLength='1' stroke-dasharray='10% 20%' stroke-dashoffset='-5%'")
    (line "stroke-dasharray='10% 20%' stroke-dashoffset='-5%'") "all percentage calibration exemption"
  same (line "pathLength='8' stroke-dasharray='1px 1px'")
    (line "stroke-dasharray='10 10'") "px calibration"
  let rect := fun attrs => wrap ("<rect x='20' y='20' width='40' height='20' fill='none' stroke='black' stroke-width='6' "++attrs++"/>")
  same (rect "pathLength='12' stroke-dasharray='2 1'")
    (rect "stroke-dasharray='20 10'") "rectangle perimeter calibration"
  same (wrap "<g stroke-dasharray='10% 1' stroke-dashoffset='5%'><line x1='10' y1='20' x2='90' y2='20' stroke='black' stroke-width='6' pathLength='10'/></g>")
    (line "stroke-dasharray='10 8' stroke-dashoffset='5'") "inherited unit provenance"
  same (line "pathLength='0'") (line "") "zero author length irrelevant to solid stroke"
  same (line "pathLength='0' stroke-dasharray='10% 20%' stroke-dashoffset='5%'")
    (line "stroke-dasharray='10% 20%' stroke-dashoffset='5%'") "zero author with percentage-only distances"
  for attrs in ["pathLength='-1'", "pathLength='1px'", "pathLength='10%'", "pathLength='NaN'", "pathLength='0' stroke-dasharray='1 1'"] do
    check (!(NativeSVG.parse (line attrs)).isOk) ("invalid/out-of-profile admitted: "++attrs)
  let xml ← IO.FS.readFile "../../tests/external/svg/upstream/svg/shapes/reftests/pathlength-001.svg"
  check ((NativeSVG.parse xml 800 600).isOk) "unchanged official rectangle pathLength fixture"
  IO.println "PASS SVG pathLength calibration, percentage exemption, inheritance, refusal boundaries and official rect admission"
end NativeSVGPathLengthTests
#eval NativeSVGPathLengthTests.run
