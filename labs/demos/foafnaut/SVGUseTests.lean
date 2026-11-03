import SVG
import L4Factoidal.JSON.Parser
namespace NativeSVGUseTests
open NativeSVG L4Factoidal.JSON
private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def unwrap (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error message => throw (IO.userError message)
private def wrap (body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink' width='64' height='64'>" ++ body ++ "</svg>"
private def rendering (xml : String) (documentURL : Option String := none) : IO Json := do
  let scene ← unwrap (parse (wrap xml) 0 0 documentURL)
  let json ← unwrap scene.artifact
  let .object fields ← unwrap ((parseJson json).mapError (fun _ => "artifact JSON parse")) | throw (IO.userError "artifact object")
  -- Retained instance groups differ; preserve EVERY rendering field.
  pure (.object (fields.filter (fun (key,_) => key != "tree")))
private def equivalent (actual expected label : String) : IO Unit := do
  check ((← rendering actual) == (← rendering expected)) label
private def expectRect (body : String) (x0 y0 x1 y1 : Nat) (label : String) : IO Unit := do
  let scene ← unwrap (parse (wrap body))
  let coordinates := (List.range 32).flatMap fun y => (List.range 40).map fun x => (x,y)
  for ((x,y),color) in coordinates.zip (scene.samplePixels coordinates) do
    let inside := x0 <= x && x < x1 && y0 <= y && y < y1
    check (color.r == 1 && color.g == (if inside then 0 else 1) && color.b == color.g)
      s!"{label}: pixel {x},{y}"

def run : IO Unit := do
  equivalent "<defs><filter id='unused'><unsupported/></filter><rect width='60' height='60'/></defs><symbol><rect width='60' height='60'/></symbol>" "" "definition containers painted"
  equivalent "<defs fill='green'><rect id='r' width='8' height='8' fill='blue'/></defs><use href='#r' fill='red'/>"
    "<rect width='8' height='8' fill='blue'/>" "target specified style overwritten by use"
  equivalent "<defs fill='blue'><g id='r'><rect width='8' height='8' fill='currentColor'/></g></defs><use href='#r' color='red'/>"
    "<rect width='8' height='8' fill='red'/>" "instance did not inherit host currentColor"
  equivalent "<defs><rect id='r' width='8' height='8'/></defs><use href='#r' x='5' y='3' transform='scale(2)'/>"
    "<g transform='scale(2) translate(5 3)'><rect width='8' height='8'/></g>" "use transform/x/y order"
  equivalent "<defs><rect id='r' width='8' height='8' fill='red'/></defs><use href='#r'/><rect x='4' width='8' height='8' fill='blue'/><use href='#r' x='8'/>"
    "<rect width='8' height='8' fill='red'/><rect x='4' width='8' height='8' fill='blue'/><g transform='translate(8)'><rect width='8' height='8' fill='red'/></g>" "instance painter order"
  equivalent "<defs><rect id='r' width='8' height='8' fill='red'/><rect id='r' width='8' height='8' fill='blue'/></defs><use id='r' href='#r'/>"
    "<rect width='8' height='8' fill='red'/>" "duplicate ID order or false same-ID cycle"
  equivalent "<rect width='8' height='8' fill='red'/><use href='#missing'/><use href='#%GG'/><use href='#%FF'/>"
    "<rect width='8' height='8' fill='red'/>" "missing/invalid reference damaged document"
  equivalent "<defs><rect id='α' width='8' height='8' fill='red'/></defs><use href='#%CE%B1'/>"
    "<rect width='8' height='8' fill='red'/>" "percent UTF-8 fragment"
  equivalent "<defs><rect id='r' width='8' height='8'/></defs><use href='' xlink:href='#r'/>" "" "empty href precedence"
  equivalent "<defs><rect id='r' width='8' height='8'/></defs><use xlink:href='#r'/>"
    "<rect width='8' height='8'/>" "legacy xlink fallback"
  equivalent "<metadata><f:item xmlns:f='urn:metadata' id='r'/></metadata><defs><rect id='r' width='8' height='8'/></defs><use href='#r'/>"
    "" "foreign first duplicate ID target selected later SVG target"
  equivalent "<defs><g id='a'><rect width='4' height='4' fill='red'/><use href='#b'/></g><g id='b'><rect x='4' width='4' height='4' fill='blue'/><use href='#a'/></g></defs><use href='#a'/>"
    "<rect width='4' height='4' fill='red'/><rect x='4' width='4' height='4' fill='blue'/>" "indirect cycle removed valid paint or recurred"
  equivalent "<g id='a'><rect width='4' height='4'/><use href='#a'/></g>"
    "<rect width='4' height='4'/>" "ancestor cycle"
  equivalent "<defs><rect id='r' width='4' height='4'/></defs><use href='#r'/><use href='#r' x='8'/>"
    "<rect width='4' height='4'/><g transform='translate(8)'><rect width='4' height='4'/></g>" "sibling instances share active cycle stack"
  expectRect "<defs><symbol id='s' width='8' height='8' viewBox='0 0 5 5' preserveAspectRatio='none'><rect x='-1' y='-1' width='7' height='7' fill='red'/></symbol></defs><use href='#s' x='12' y='8' width='20' height='10'/>"
    12 8 32 18 "symbol viewBox and viewport frames/use overrides"
  expectRect "<svg x='10' y='10' width='5' height='5'><rect width='10' height='10' fill='red'/></svg>"
    10 10 15 15 "nested default clip"
  expectRect "<svg x='10' y='10' width='5' height='5' overflow='visible'><rect width='10' height='10' fill='red'/></svg>"
    10 10 20 20 "nested visible overflow"
  expectRect "<defs><symbol id='s' width='10' height='10' style='width:20px;height:20px'><rect width='40' height='40' fill='red'/></symbol></defs><use href='#s' width='5' height='5' style='width:30px;height:30px'/>"
    0 0 5 5 "SVGWG2026 ignored CSS dimensions"
  equivalent "<defs><symbol id='s' viewBox='0 0 0 5'><rect width='4' height='4'/></symbol></defs><use href='#s'/>" "" "zero symbol viewBox painted"
  equivalent "<rect xmlns:i='urn:inkscape' i:label='metadata' xml:lang='en' width='8' height='8'/>"
    "<rect width='8' height='8'/>" "foreign metadata altered paint"
  let external := parse (wrap "<defs><rect id='r' width='8' height='8'/></defs><use href='other.svg#r'/>")
  check (!external.isOk) "external resources silently treated as missing IDs"
  let url := some "https://example.test/a/doc.svg"
  let target := "<defs><rect id='r' width='8' height='8' fill='red'/></defs>"
  for href in ["https://example.test/a/doc.svg#r","./sub/../doc.svg#r"] do
    check ((← rendering (target ++ "<use href='" ++ href ++ "'/>") url) ==
      (← rendering "<rect width='8' height='8' fill='red'/>")) "same-document URL resolution"
  check ((← rendering (target ++ "<g xml:base='sub/'><use href='../doc.svg#r'/></g>") url) ==
    (← rendering "<rect width='8' height='8' fill='red'/>")) "inherited xml:base resolution"
  check ((← rendering (target ++ "<defs xml:base='deep/sub/'><g id='t'><use href='../../doc.svg#r'/></g></defs><g xml:base='other/'><use href='../doc.svg#t'/></g>") url) ==
    (← rendering "<rect width='8' height='8' fill='red'/>")) "clone reference did not preserve original source base"
  let externalBase := parse (wrap (target ++ "<g xml:base='https://other.test/'><use href='#r'/></g>")) 0 0 url
  check (!externalBase.isOk) "xml:base external URL silently resolved as local fragment"
  equivalent "<defs><rect id='a+b' width='8' height='8'/></defs><use href='#a+b'/>"
    "<rect width='8' height='8'/>" "fragment plus incorrectly decoded as form space"
  equivalent "<defs><rect id='%20' width='8' height='8'/></defs><use href='#%2520'/>"
    "<rect width='8' height='8'/>" "fragment percent encoding decoded more than once"
  IO.println "PASS defs/use/symbol refs, duplicate identity, cycles, inheritance, transforms, painter order and viewport clipping"
#eval run
end NativeSVGUseTests
