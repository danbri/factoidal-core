import SVG
namespace NativeSVGCSSIntegrationTests
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def wrap (body : String) := "<svg xmlns='http://www.w3.org/2000/svg' width='100' height='100'>"++body++"</svg>"
private def sample (body : String) := NativeSVG.sample (wrap body) 0 0 5 5
private def green := "{\"rgb\":[0,128,0]}"
private def red := "{\"rgb\":[255,0,0]}"
def run : IO Unit := do
  check (sample "<style>rect { fill: green }</style><rect width='20' height='20' fill='red'/>" == green) "stylesheet must beat presentation"
  check (sample "<style>rect { fill: red }</style><rect width='20' height='20' style='fill: green'/>" == green) "inline must beat stylesheet"
  check (sample "<style>rect {fill: red} rect {fill: green}</style><rect width='20' height='20'/>" == green) "source order"
  check (sample "<rect width='20' height='20'/><style>rect {fill:green}</style>" == green) "late stylesheet"
  check (sample "<style>g {fill:green}</style><g><rect width='20' height='20'/></g>" == green) "inherited CSS fill"
  check (sample "<g fill='green'><rect width='20' height='20' style='fill:inherit'/></g>" == green) "inline inherit"
  check (sample "<style type='text/css' media='all'><![CDATA[rect {fill:red}]]></style><rect width='20' height='20'/>" == red) "type/media/CDATA"
  check (sample "<rect width='20' height='20' style='fill:red;opacity:1'/>" == red) "shape CSS opacity"
  for body in ["<style media='screen'>rect {fill:red}</style>","<style type='text/plain'>rect {fill:red}</style>","<style>rect {fill:red !important}</style>","<style>rect {fill:invalid;fill:green}</style>","<g style='opacity:0.5'><rect width='20' height='20'/></g>"] do
    check (!(NativeSVG.parse (wrap body)).isOk) "unsupported CSS silently admitted"
  for file in ["percentage.svg", "percentage-attribute.svg"] do
    let xml ← IO.FS.readFile ("../../tests/external/svg/upstream/svg/painting/reftests/"++file)
    match NativeSVG.parse xml 800 600 with
    | .ok _ => pure ()
    | .error e => throw (IO.userError ("unchanged percentage fixture refused: "++e))
  IO.println "PASS SVG CSS cascade, inheritance, type/media/refusal boundaries; unchanged WPT percentage fixture admission"
end NativeSVGCSSIntegrationTests
#eval NativeSVGCSSIntegrationTests.run
