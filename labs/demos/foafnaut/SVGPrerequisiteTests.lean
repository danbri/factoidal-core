import SVG
namespace NativeSVGPrerequisiteTests
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def wrap (body : String) := "<svg xmlns='http://www.w3.org/2000/svg' xmlns:h='http://www.w3.org/1999/xhtml' width='32' height='32'>" ++ body ++ "</svg>"
private def green := "{\"rgb\":[0,128,0]}"
private def white := "{\"rgb\":[255,255,255]}"
def run : IO Unit := do
  check (NativeSVG.sample (wrap "<h:link rel='match' href='reference.svg'/><rect width='20' height='20' fill='green'/>") 0 0 5 5 == green) "reftest metadata changes paint"
  check (NativeSVG.sample (wrap "<metadata><rect width='32' height='32' fill='red'/><private xmlns='urn:metadata'>opaque</private></metadata>") 0 0 5 5 == white) "metadata descendants painted"
  check (!(NativeSVG.parse (wrap "<h:link rel='stylesheet' href='x.css'/>" )).isOk) "active stylesheet silently ignored"
  check (NativeSVG.sample (wrap "<rect width='20' height='20' fill='green'/><rect width='20' height='20' fill='url(#missing)'/>") 0 0 5 5 == green) "missing server without fallback paints"
  check (NativeSVG.sample (wrap "<rect width='20' height='20' fill='url(#missing) green'/>") 0 0 5 5 == green) "missing server fallback"
  check (NativeSVG.sample (wrap "<g fill='url(#missing) currentColor' color='red'><rect width='20' height='20' color='green'/></g>") 0 0 5 5 == green) "fallback currentColor resolved too early"
  for body in ["<rect id='present' width='2' height='2'/><rect width='20' height='20' fill='url(#present) green'/>",
      "<rect width='20' height='20' fill='url(other.svg#missing) green'/>",
      "<rect width='20' height='20' fill='url(#missing) green red'/>"] do
    check (!(NativeSVG.parse (wrap body)).isOk) "unsupported reference silently treated as missing"
  for name in ["fallback-001.svg","fallback-002.svg"] do
    let xml ← IO.FS.readFile ("../../tests/external/svg/upstream/svg/painting/reftests/" ++ name)
    check ((NativeSVG.parse xml 800 600).isOk) ("unchanged upstream refused: " ++ name)
    check (NativeSVG.sample xml 800 600 5 5 == green) ("upstream green paint: " ++ name)
    check (NativeSVG.sample xml 800 600 101 5 == white) ("upstream outside paint: " ++ name)
  IO.println "PASS SVG metadata, symbolic paint fallback and explicit reference refusals"
end NativeSVGPrerequisiteTests

#eval NativeSVGPrerequisiteTests.run
