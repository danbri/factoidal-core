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

-- XML pages with an XSLT stylesheet: discovery, engine choice, HTML output.
private def xmlPage := "<?xml version=\"1.0\"?><?xml-stylesheet type=\"text/xsl\" href=\"a.xsl\"?><r><t>Hi</t></r>"
private def xslt (version body : String) : String :=
  s!"<xsl:stylesheet version=\"{version}\" xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\"><xsl:template match=\"/\">{body}</xsl:template></xsl:stylesheet>"
private def page (version : String) : Option (String × String) :=
  (WebXslt.transform xmlPage (xslt version "<html><head><title/></head><body><div/><br/><p><xsl:value-of select=\"r/t\"/></p></body></html>") "file:///p.xml" "file:///a.xsl").toOption
#guard (WebXslt.stylesheetHref xmlPage).toOption == some (some "a.xsl")
#guard (WebXslt.stylesheetHref "<!doctype html><p>&lt;?xml-stylesheet?&gt; <?xml-stylesheet href=a?></p>").toOption == some none
#guard (WebXslt.stylesheetHref "<p>plain</p>").toOption == some none
#guard (WebXslt.stylesheetHref "<?xml version=\"1.0\"?><r/>").toOption == some none
#guard (WebXslt.stylesheetHref "<?xml version=\"1.0\"?><?xml-stylesheet type=\"text/css\" href=\"a.css\"?><r/>").toOption.isNone
#guard (WebXslt.stylesheetHref "<?xml version=\"1.0\"?><?xml-stylesheet type=\"text/xsl\" href=\"#s\"?><r/>").toOption.isNone
#guard (WebXslt.stylesheetHref "<?xml version=\"1.0\"?><?xml-stylesheet type='text/xsl' href='a.xsl'?><r>").toOption.isNone
#guard WebXslt.pseudoAttrs "type='text/xsl' href=\"a b.xsl\"" == [("type","text/xsl"),("href","a b.xsl")]
#guard WebXslt.expandEmptyTags "<title/><br/><a b=\"/>\"/><!-- <i/> --><p>x</p>" == "<title></title><br/><a b=\"/>\"></a><!-- <i/> --><p>x</p>"
#guard (page "1.0").map (·.2) == some "xslt-1.0"
#guard (page "3.0").map (·.2) == some "xslt-4 (version 3.0)"
#guard (page "4.0").map (·.2) == some "xslt-4 (version 4.0)"
#guard ["1.0","3.0","4.0"].all fun version => match page version with
  | some (text,_) => (text.splitOn "<p>Hi</p>").length == 2
  | none => false
#guard (page "1.0").map (fun p => (p.1.splitOn "<title></title>").length) == some 2
#guard (page "9.0").isNone
#guard (WebXslt.transform xmlPage "<notxslt version=\"1.0\"/>" "u" "s").toOption.isNone
#guard (WebXslt.transform xmlPage "<broken" "u" "s").toOption.isNone
#guard match WebXslt.transform xmlPage "<xsl:stylesheet version=\"1.0\" xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\"><xsl:output method=\"text\"/><xsl:template match=\"/\">a&lt;b</xsl:template></xsl:stylesheet>" "u" "s" with
  | .ok (text,_) => text == "<!doctype html><pre>a&lt;b</pre>"
  | _ => false
-- A stylesheet can reach no other document: both engines stop with a refusal
-- or an empty result, never with file content.
#guard (WebXslt.transform xmlPage (xslt "1.0" "<xsl:copy-of select=\"document('/etc/passwd')\"/>") "u" "s").toOption.all (fun r => (r.1.splitOn "root:").length == 1)
#guard (WebXslt.transform xmlPage (xslt "3.0" "<xsl:copy-of select=\"unparsed-text('/etc/passwd')\"/>") "u" "s").toOption.isNone

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
#guard WebDocument.documentTitle (L4Factoidal.DOM.parseHtmlDocument "<title>  Two\n  words </title>") == "Two words"
#guard WebDocument.documentTitle (L4Factoidal.DOM.parseHtmlDocument "<p>none</p>") == ""

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
#guard (WebDocument.run dynamicHTML (dynamicOptions "render") 420 100).toOption.isSome
#guard (WebDocument.run dynamicHTML (json [("op",.string "fontRequests"),("resources",.array [resource 1048576 "p{}"])]) 420 100).toOption.isNone
#guard (WebDocument.run "<p>A</p>" (json [("resources",.string "bad")]) 420 100).toOption.isNone

-- Both shaping requests and rendering accept the same text scale: at least 50, no maximum.
private def textScaleOptions (percent : JSON.Json) (op : String := "render") :=
  json [("op",.string op),("textScalePercent",percent)]
#guard (WebDocument.run "<p>A</p>" (textScaleOptions (.number "150")) 200 100).toOption.isSome
#guard (WebDocument.run "<p>A</p>" (textScaleOptions (.number "49")) 200 100).toOption.isNone
#guard (WebDocument.run "<p>A</p>" (textScaleOptions (.number "251")) 200 100).toOption.isSome
#guard (WebDocument.run "<p>A</p>" (textScaleOptions (.number "2000")) 200 100).toOption.isSome
#guard (WebDocument.run "<p>A</p>" (textScaleOptions (.number "100000")) 200 100).toOption.isSome
#guard (WebDocument.run "<p>A</p>" (textScaleOptions (.number "150.5")) 200 100).toOption.isNone
#guard (WebDocument.run "<p>A</p>" (textScaleOptions (.string "150")) 200 100).toOption.isNone
#guard (WebDocument.run "<p>A</p>" (textScaleOptions (.number "49") "fontRequests") 200 100).toOption.isNone

-- Selection and window commands: the host sends only numbers and positions.
private def textOf (selection : JSON.Json) (html : String := "<p>Hello big world</p><p>Next</p>") : Option String := do
  let output ← (WebDocument.run html (json [("op",.string "selectedText"),("selection",selection)]) 400 200).toOption
  let (value,_) ← (JSON.parseJsonText output).toOption
  match value.field? "text" with | some (.string text) => some text | _ => none
#guard textOf (.string "all") == some "Hello big world\nNext"
#guard textOf (.string "all") (html := "<p>one <b>two</b> three</p>") == some "one two three"
#guard textOf (.array [.number "0",.number "0",.number "0",.number "0"]) == some ""
#guard (textOf (.array [.number "0",.number "0"])).isNone
#guard (WebDocument.run "<p>A</p>" (json [("selection",.string "all")]) 200 100).toOption.isSome
private def primitives (request : JSON.Json) : Option JSON.Json := do
  let output ← (WebDocument.run "<p>A</p>" request 200 100).toOption
  let (value,_) ← (JSON.parseJsonText output).toOption
  value.field? "primitiveCount"
#guard primitives (json []) != primitives (json [("selection",.string "all")])
private def menu (number : Nat) (percent : Nat := 100) : Option String :=
  (WebDocument.run "" (json [("op",.string "command"),("command",.number (toString number)),("textScalePercent",.number (toString percent))]) 1 1).toOption
#guard menu 1 == some "{\"action\":\"zoomIn\",\"textScalePercent\":110}"
#guard menu 2 == some "{\"action\":\"zoomOut\",\"textScalePercent\":90}"
#guard menu 3 200 == some "{\"action\":\"zoomReset\",\"textScalePercent\":150}"
#guard menu 4 == some "{\"action\":\"copy\",\"textScalePercent\":100}"
#guard menu 6 == some "{\"action\":\"back\",\"textScalePercent\":100}"
private def pages : JSON.Json := json [("entries",.array [.string "a",.string "b"]),("index",.number "1")]
private def historyField (request : List (String × JSON.Json)) (key : String) : Option JSON.Json := do
  let output ← (WebDocument.run "" (json request) 1 1).toOption
  let (value,_) ← (JSON.parseJsonText output).toOption
  value.field? key
private def historyCommand (number : Nat) : List (String × JSON.Json) :=
  [("op",.string "command"),("command",.number (toString number)),("history",pages)]
#guard historyField (historyCommand 6) "url" == some (.string "a")
#guard historyField (historyCommand 7) "url" == some .null
#guard historyField (historyCommand 8) "url" == some (.string "b")
#guard historyField (historyCommand 6) "canForward" == some (.bool true)
#guard historyField [("op",.string "historyPush"),("history",pages),("url",.string "c")] "canBack" == some (.bool true)
#guard (WebDocument.run "" (json [("op",.string "historyPush"),("url",.string "c"),
  ("history",json [("entries",.array []),("index",.number "3")])]) 1 1).toOption.isNone
#guard historyField [("op",.string "keyCommand"),("platform",.string "other"),("modifier",.string "alt"),("key",.string "ArrowLeft")] "command" == some (.number "6")
#guard menu 1 250 == some "{\"action\":\"zoomIn\",\"textScalePercent\":275}"
#guard menu 1 2000 == some "{\"action\":\"zoomIn\",\"textScalePercent\":2200}"
#guard menu 99 == some "{\"action\":\"none\",\"textScalePercent\":100}"
private def up (fx : String) : Option String :=
  (WebDocument.run "" (json [("op",.string "pointerUp"),("selection",.array [.number "10",.number "10",.number fx,.number "10"])]) 1 1).toOption
#guard up "11" == some "{\"action\":\"click\"}"
#guard up "40" == some "{\"action\":\"select\"}"

-- The kept layout: a render that takes it answers as one that lays out again.
#guard WebDocument.layoutRequest (json [("shell",json [("scroll",.number "40")]),("url",.string "u"),
  ("selection",.string "all"),("textScalePercent",.number "150"),("live",.bool true)]) ==
  json [("url",.string "u"),("textScalePercent",.number "150")]
private def keptPage : String := "<style>p{margin:0}</style>" ++ String.join ((List.range 40).map fun i => s!"<p>Line {i} of the page</p>")
private def frame (scroll : Nat) (extra : List (String × JSON.Json) := []) (percent := "150") : JSON.Json :=
  json ([("shell",json [("tabs",.array [json [("title",.string "t")]]),("active",.number "0"),("address",.string "a"),
    ("cursor",.number "0"),("scroll",.number (toString scroll))]),("textScalePercent",.number percent),("binary",.bool true)] ++ extra)
private def frames : List (String × JSON.Json × Nat) :=
  [(keptPage,frame 0,300),(keptPage,frame 40,300),(keptPage,frame 80 [("selection",.string "all")],300),
   (keptPage,frame 80 [("op",.string "selectedText"),("selection",.array [.number "0",.number "0",.number "300",.number "90"])],300),
   (keptPage,frame 80,280),(keptPage,frame 80 [] "165",280),
   (keptPage ++ "<p>more</p>",frame 80,280),(keptPage,frame 0 [("checks",.bool false)],280),(keptPage,frame 0,280)]
#guard frames.all fun (html,request,width) =>
  let kept := WebDocument.run html request width 200
  let fresh := WebDocument.runUncached html request width 200
  kept.toOption.isSome && kept.toOption == fresh.toOption
#guard (WebDocument.run keptPage (frame 0 [("checks",.bool false)]) 280 200).toOption.any (·.contains "\"checks\":[]")

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

-- SVG `image` in a document: `inspect` names what the host fetches, by key and URL, and
-- `render` takes the bytes. No bytes and a reference outside HTTP stay refusals.
private def imagePage := "<svg xmlns='http://www.w3.org/2000/svg' width='20' height='20'><image href='a.png' width='20' height='20'/></svg>"
private def imageBytes := "iVBORw0KGgoAAAANSUhEUgAAAAIAAAACCAYAAABytg0kAAAAFElEQVR4nGP4z8DwHwwZGP6DCAYAP9IF+9wCo9QAAAAASUVORK5CYII="
private def contains (text part : String) : Bool := (text.splitOn part).length > 1
#guard contains (WebDocument.compile imagePage "{\"op\":\"inspect\",\"url\":\"https://e.test/p/\"}" 40 40)
  "\"images\":[{\"key\":\"https://e.test/p/a.png\",\"url\":\"https://e.test/p/a.png\"}]"
#guard contains (WebDocument.compile imagePage "{\"op\":\"render\",\"url\":\"https://e.test/p/\"}" 40 40)
  "image resource not supplied: https://e.test/p/a.png"
#guard !contains (WebDocument.compile imagePage ("{\"op\":\"render\",\"url\":\"https://e.test/p/\",\"images\":[{\"key\":\"https://e.test/p/a.png\",\"base64\":\"" ++ imageBytes ++ "\"}]}") 40 40) "\"error\""
#guard contains (WebDocument.compile imagePage "{\"op\":\"render\",\"url\":\"https://e.test/p/\",\"images\":[{\"key\":\"https://e.test/p/a.png\",\"base64\":\"aGk=\"}]}" 40 40)
  "image is not PNG or JPEG"
#guard contains (WebDocument.compile imagePage "{\"op\":\"render\",\"url\":\"https://e.test/p/\",\"images\":3}" 40 40) "document images must be an array"
