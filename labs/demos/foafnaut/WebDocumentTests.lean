import WebDocument

open L4Factoidal
private def json (fields : List (String × JSON.Json)) : JSON.Json := .object fields
private def resource (id : Nat) (source : String) : JSON.Json :=
  json [("nodeId",.number (toString id)),("source",.string source)]
private def withSheets (dom : DOM.Dom) (sources : List String)
    (fields : List (String × JSON.Json) := []) : JSON.Json :=
  let ids := (dom.treeOrder 0).toList.filter fun id => DOM.Dom.isHtmlElement (dom.get id) "link"
  json (("resources",.array ((ids.zip sources).map fun (id,source) => resource id source))::fields)
private def size (html : String) (sources : List String) : Option Float := do
  let dom := DOM.parseHtmlDocument html
  let rules ← (WebDocument.rules dom (withSheets dom sources)).toOption
  let styles ← (Rendering.CSS.computeAll dom rules).toOption
  let id ← dom.getElementById 0 "target"
  return (← styles[id]?).fontSize
private def sheetSource := "<style>p{font-size:10px}</style><link rel=stylesheet href=one.css><style>p{font-size:30px}</style><p id=target>A</p>"
-- Embedded/external sheets share document source order, rather than grouping
-- fetched sheets at the beginning or end of the cascade.
#guard size sheetSource ["p{font-size:20px}"] == some 30
#guard size "<style>p{font-size:10px}</style><link rel=stylesheet href=one.css><p id=target>A</p>" ["p{font-size:20px}"] == some 20
#guard size "<link rel=stylesheet href=one.css><style>p{font-size:30px}</style><p id=target style='font-size:40px'>A</p>" ["p{font-size:20px!important}"] == some 20
#guard size "<link rel=stylesheet href=one.css><p id=target style='font-size:40px!important'>A</p>" ["p{font-size:20px!important}"] == some 40
#guard size "<link rel=stylesheet href=one.css><link rel=stylesheet href=two.css><p id=target>A</p>" ["p{font-size:20px}","p{font-size:24px}"] == some 24

private def externalDOM := DOM.parseHtmlDocument "<link rel=stylesheet href=one.css><p>A</p>"
private def linkId := ((externalDOM.treeOrder 0).find? fun id => DOM.Dom.isHtmlElement (externalDOM.get id) "link").getD 0
#guard (WebDocument.rules externalDOM (json [])).toOption.isNone
#guard (WebDocument.rules externalDOM (json [("resources",.array [resource linkId "p{}",resource linkId "p{}"])])).toOption.isNone
#guard (WebDocument.rules externalDOM (json [("resources",.string "bad")])).toOption.isNone
#guard size "<link rel=stylesheet href=one.css disabled><p id=target>A</p>" [] == some 16
#guard size "<style media=print>p{font-size:90px}</style><p id=target>A</p>" [] == some 16
#guard size "<style media=print>p{display:grid;unknown-print-property:unsupported}</style><p id=target>A</p>" [] == some 16
#guard size "<style media='screen and (min-width:1px)'>p{font-size:90px}</style><p id=target>A</p>" [] == none
#guard size "<link rel=stylesheet href=one.css type=text/plain><p id=target>A</p>" [] == some 16


private def urlDOM := DOM.parseHtmlDocument "<base href='./assets/'><base href='https://ignored.test/'><link rel=stylesheet href='../css/main.css'><script src='./scripts/app.js'></script><p>A</p>"
private def inspected := (WebDocument.inspect urlDOM "https://example.test/a/page.html").toOption.getD (.object [])
#guard inspected.field? "baseURL" == some (.string "https://example.test/a/assets/")
#guard match inspected.field? "stylesheets" with
  | some (.array [sheet]) => sheet.field? "url" == some (.string "https://example.test/a/css/main.css")
  | _ => false
#guard match inspected.field? "scripts" with
  | some (.array [script]) => script.field? "url" == some (.string "https://example.test/a/assets/scripts/app.js")
  | _ => false

-- The scripting snapshot is the authoritative MIME classifier. Legacy classic
-- types survive inspection; data blocks remain inert; padded modules refuse.
private def ecmaInspection := WebDocument.inspect
  (DOM.parseHtmlDocument "<script type=' text/ecmascript '>classic()</script><script type='application/json'>{}</script>")
  "https://example.test/"
#guard match ecmaInspection with
  | .ok value => match value.field? "scripts" with
    | some (.array [script]) => script.field? "kind" == some (.string "classic") &&
        script.field? "source" == some (.string "classic()")
    | _ => false
  | .error _ => false
#guard (WebDocument.inspect (DOM.parseHtmlDocument "<script type=' module '>export{}</script>") "https://example.test/").toOption.isNone
#guard (WebDocument.run "<script type=' module '>export{}</script>" (json [("op",.string "inspect")]) 1 1).toOption.isNone

private def dynamicHTML := "<link rel=stylesheet href=font.css><p id=target>stale</p><span>office</span>"
private def dynamicDOM := DOM.parseHtmlDocument dynamicHTML
private def target := (dynamicDOM.getElementById 0 "target").getD 0
private def command : JSON.Json := json [("op",.string "setTextContent"),("nodeId",.number (toString target)),("value",.string "November2026 café edited")]
private def dynamicOptions (op : String) (fontData : String := "") :=
  withSheets dynamicDOM ["body{font-family:Arial;font-size:20px;line-height:28px;background:white;color:black}span{font-size:28px}"]
    [("op",.string op),("commands",.array [command]),("fontData",.string fontData)]
private def requested : Option (List (String × Nat × String)) := do
  let dom ← (WebDocument.prepareDOM dynamicHTML (dynamicOptions "fontRequests")).toOption
  let rules ← (WebDocument.rules dom (dynamicOptions "fontRequests")).toOption
  let requests ← (WebRenderFontRequests.collectDOMWithRules dom rules).toOption
  return requests.toList.map fun request => (request.family,request.pixelSize,request.text)
#guard requested == some [("Arial",20," "),("Arial",20,"November2026"),("Arial",20,"café"),("Arial",20,"edited"),("Arial",28,"office")]
#guard (WebDocument.run dynamicHTML (dynamicOptions "fontRequests") 420 100).toOption.isSome
#guard (WebDocument.run dynamicHTML (dynamicOptions "render") 420 100).toOption.isNone
#guard (WebDocument.run dynamicHTML (json [("op",.string "fontRequests"),("resources",.array [resource 1048576 "p{}"])]) 420 100).toOption.isNone
#guard (WebDocument.run "<p>A</p>" (json [("resources",.string "bad")]) 420 100).toOption.isNone


/-- Optional runtime evidence uses actual HarfBuzz/FreeType records generated
from the requests above. It does not replace the pure cascade/request guards. -/
def main (args : List String) : IO UInt32 := do
  let [fontDataPath] := args | throw (IO.userError "usage: WebDocumentTests.lean ACTUAL_FONT_DATA.json")
  let data ← IO.FS.readFile fontDataPath
  let .ok output := WebDocument.run dynamicHTML (dynamicOptions "render" data) 420 100
    | throw (IO.userError "actual font document render failed")
  let .ok value := JSON.parseJson output | throw (IO.userError "invalid rendered document JSON")
  let some metadata := value.field? "webRender" | throw (IO.userError "render metadata missing")
  let some (.array runs) := metadata.field? "glyphRuns" | throw (IO.userError "glyph runs missing")
  let texts := runs.filterMap fun run => match run.field? "text" with | some (.string text) => some text | _ => none
  if !["November2026","café","edited","office"].all texts.contains || texts.contains "stale" then
    throw (IO.userError "DOM command text did not reach actual font render")
  IO.println "PASS document command → supplied CSS → dynamic font requests → actual font scene"
  return 0

#print axioms WebDocument.run
#print axioms WebDocument.compile
