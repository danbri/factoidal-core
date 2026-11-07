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
private def historyField' (request : List (String × JSON.Json)) (key : String) : Option JSON.Json := do
  let output ← (WebDocument.run "" (json request) 1 1).toOption
  let (value,_) ← (JSON.parseJsonText output).toOption
  value.field? key
private def menu (number : Nat) (percent : Nat := 100) : Option String :=
  (WebDocument.run "" (json [("op",.string "command"),("command",.number (toString number)),("textScalePercent",.number (toString percent))]) 1 1).toOption
#guard menu 1 == some "{\"action\":\"zoomIn\",\"textScalePercent\":110}"
#guard menu 2 == some "{\"action\":\"zoomOut\",\"textScalePercent\":90}"
#guard menu 3 200 == some "{\"action\":\"zoomReset\",\"textScalePercent\":150}"
#guard menu 4 == some "{\"action\":\"copy\",\"target\":\"page\",\"textScalePercent\":100}"
-- Edit commands act on the address bar when it has the focus; paste always does (issue 1268).
private def focusedMenu (number : Nat) : Option JSON.Json :=
  historyField' [("op",.string "command"),("command",.number (toString number)),("textScalePercent",.number "100"),("focused",.bool true)] "target"
#guard focusedMenu 5 == some (.string "address") && focusedMenu 15 == some (.string "address") && focusedMenu 1 == none
#guard (menu 14).map (fun t => decide ((t.splitOn "address").length > 1)) == some true
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
-- Tab, scroll, stop and find commands (issue 1268): Lean answers the tab and the scroll.
private def counted (command : Nat) (more : List (String × JSON.Json)) : List (String × JSON.Json) :=
  [("op",.string "command"),("command",.number (toString command)),("textScalePercent",.number "100")] ++ more
#guard historyField (counted 29 [("tabs",.number "4"),("active",.number "1")]) "tab" == some (.number "3")
#guard historyField (counted 31 [("tabs",.number "4"),("active",.number "0")]) "tab" == some (.number "3")
#guard historyField (counted 33 [("scroll",.number "100"),("view",.number "500"),("scrollLimit",.number "2000"),("scale",.number "2")]) "scrollTo" == some (.number "500")
#guard historyField (counted 38 [("scroll",.number "100"),("view",.number "500"),("scrollLimit",.number "2000"),("scale",.number "2")]) "scrollTo" == some (.number "0")
#guard historyField (counted 39 []) "action" == some (.string "stop") && historyField (counted 20 []) "action" == some (.string "reopenTab")
#guard (historyField (counted 32 []) "refused").isSome && (historyField (counted 33 []) "refused").isNone
#guard historyField [("op",.string "pageKey"),("key",.number "49"),("modifiers",.number "1")] "command" == some (.number "34")
#guard historyField [("op",.string "pageKey"),("key",.number "0"),("modifiers",.number "0")] "command" == some .null
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

/-! Layers (issue 1268). The CPU sampler of the composite of the two layers must
give the colour of one frame at the same scroll, at every point tried, for scrolls
inside a band that was made at another scroll. -/
private def layerShell (scroll : Nat) : WebShell.Shell := {tabs := #[{title := "t"}],address := "a",scroll}
private def sameAsFrame (html : String) (width height frameScroll : Nat) (scrolls : List Nat) : Bool :=
  let top := WebShell.height (layerShell 0) width
  let view := max 1 (height-top)
  let b := WebDocument.band frameScroll view
  match WebDocument.layOut ⟨html,WebDocument.layoutRequest (json []),width,height,top,none⟩ with
  | .error _ => false
  | .ok laid =>
    match WebRenderSVG.toScene (WebDocument.pageLayer laid.scene [] b) with
    | .error _ => false
    | .ok page => scrolls.all fun scroll =>
      match WebRenderSVG.toScene (WebShell.compose (layerShell scroll) laid.scene width height),
          WebRenderSVG.toScene (WebDocument.chromeLayer (layerShell scroll) laid.scene width) with
      | .ok full,.ok chrome =>
        let points := (List.range ((height+12)/13)).flatMap fun row => [41,150,width-2].map (·,row*13)
        let offset := scroll-b.top
        let pagePoints := (points.filter (·.2 ≥ top)).map fun (x,y) => (x,y-top+offset)
        let chromePoints := points.filter (·.2 < top)
        let want := full.samplePixels (chromePoints ++ points.filter (·.2 ≥ top))
        let got := chrome.samplePixels chromePoints ++ page.samplePixels pagePoints
        b.fits view scroll && want.length == got.length &&
          (want.zip got).all fun (a,c) => a.r == c.r && a.g == c.g && a.b == c.b
      | _,_ => false
#guard sameAsFrame keptPage 300 200 100 [60,137]
#guard sameAsFrame keptPage 300 200 700 [733]
-- The band holds the view, and a layered render answers both layers in band rows.
#guard WebDocument.band 100 161 == ⟨0,1185⟩
#guard WebDocument.band 700 161 == ⟨188,1185⟩
#guard WebDocument.band 0 4096 == ⟨0,4096⟩
#guard (WebDocument.run keptPage (frame 80 [("layers",.bool true),("checks",.bool false)]) 300 200).toOption.any fun text =>
  match JSON.parseJson text with
  | .ok value => (value.field? "layers").bind (·.field? "bandTop") == some (.number "0") &&
      (value.field? "page").bind (·.field? "height") == some (.number "1185") &&
      (value.field? "chrome").bind (·.field? "height") == some (.number "39")
  | .error _ => false
#guard (WebDocument.run keptPage (frame 80 [("layers",.bool true)]) 300 200).toOption ==
  (WebDocument.runUncached keptPage (frame 80 [("layers",.bool true)]) 300 200).toOption

/-! Press acknowledgement and element state (issue 1268). -/
private def pressAnswer (fields : List (String × JSON.Json)) : Option JSON.Json :=
  (WebDocument.run "" (json (("op",.string "press")::fields)) 1 1).toOption.bind fun text => (JSON.parseJson text).toOption
private def pressShell := json [("tabs",.array [json [("title",.string "t")]]),("canBack",.bool true)]
-- A chrome button: its control and its box. A press on the address bar darkens nothing.
#guard (pressAnswer [("shell",pressShell),("width",.number "1000"),("x",.number "70"),("y",.number "40")]).map (·.toString) ==
  some "{\"control\":\"reload\",\"rects\":[[64,30,28,28]]}"
#guard ((pressAnswer [("shell",pressShell),("width",.number "1000"),("x",.number "400"),("y",.number "40")]).bind (·.field? "rects")) == some (.array [])
-- A link: every region of the same anchor, in source rows (page-layer row + top 65).
private def pressLinks := JSON.Json.array [.array [.number "7",.string "u",.number "10",.number "105",.number "30",.number "14"],
  .array [.number "7",.string "u",.number "0",.number "121",.number "12",.number "14"],
  .array [.number "8",.string "v",.number "50",.number "105",.number "30",.number "14"]]
#guard (pressAnswer [("shell",pressShell),("width",.number "1000"),("x",.number "20"),("y",.number "70"),("row",.number "105"),("links",pressLinks)]).map (·.toString) ==
  some "{\"control\":null,\"sourceNode\":7,\"href\":\"u\",\"rects\":[[10,170,30,14],[0,186,12,14]]}"
#guard ((pressAnswer [("shell",pressShell),("width",.number "1000"),("x",.number "200"),("y",.number "70"),("row",.number "105"),("links",pressLinks)]).bind (·.field? "sourceNode")) == some .null
-- The composite darkens the source pixel of a rectangle, at any offset in the band.
#guard WebDocument.inRects [(10,170,30,14)] 20 (WebDocument.sourceRow 65 100 75)
#guard !WebDocument.inRects [(10,170,30,14)] 20 (WebDocument.sourceRow 65 120 75)
#guard WebDocument.compositePress (· + 100) (fun _ _ => 1) (fun _ _ => 2) 65 100 [(10,170,30,14)] 20 75 == 102
#guard WebDocument.compositePress (· + 100) (fun _ _ => 1) (fun _ _ => 2) 65 100 [(64,30,28,28)] 70 40 == 101
#guard WebDocument.compositePress (· + 100) (fun _ _ => 1) (fun _ _ => 2) 65 100 [(64,30,28,28)] 10 40 == 1
#guard (WebDocument.compositeShader.splitOn s!"array<vec4u,{WebDocument.maxPressRects+2}>").length == 2
-- `active`, `hover` and `visited` are layout fields: the kept layout and a fresh one agree,
-- and an active link is drawn otherwise than an idle one.
private def linkPage := "<p><a href='https://x.test/a'>Go there</a> <a href='b'>B</a></p>"
private def anchorId : Nat :=
  let dom := DOM.parseHtmlDocument linkPage
  ((dom.treeOrder 0).find? fun id => DOM.Dom.isHtmlElement (dom.get id) "a").getD 0
private def stateFrames : List JSON.Json :=
  [frame 0, frame 0 [("active",.number (toString anchorId))], frame 0 [("hover",.number (toString anchorId))],
   frame 0 [("visited",.array [.string "https://x.test/a"])], frame 0 [("active",.number "99999")]]
#guard stateFrames.all fun request =>
  let kept := WebDocument.run linkPage request 300 200
  kept.toOption.isSome && kept.toOption == (WebDocument.runUncached linkPage request 300 200).toOption
#guard (WebDocument.run linkPage (frame 0 [("active",.number (toString anchorId))]) 300 200).toOption !=
  (WebDocument.run linkPage (frame 0) 300 200).toOption
#guard (WebDocument.run linkPage (frame 0 [("visited",.array [.string "https://x.test/a"])]) 300 200).toOption !=
  (WebDocument.run linkPage (frame 0) 300 200).toOption
-- An id outside the document is no element: the frame is the idle one.
#guard (WebDocument.run linkPage (frame 0 [("active",.number "99999")]) 300 200).toOption ==
  (WebDocument.run linkPage (frame 0) 300 200).toOption
-- The layers answer says whether an author rule names `:hover`.
private def hoverRulesOf (html : String) : Option JSON.Json :=
  (WebDocument.run html (frame 0 [("layers",.bool true),("checks",.bool false)]) 300 200).toOption.bind fun text =>
    (JSON.parseJson text).toOption.bind (·.field? "layers") |>.bind (·.field? "hoverRules")
#guard hoverRulesOf linkPage == some (.bool false)
#guard hoverRulesOf ("<style>a:hover{color:red}</style>" ++ linkPage) == some (.bool true)

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
  "image is not PNG, JPEG or GIF"
#guard contains (WebDocument.compile imagePage "{\"op\":\"render\",\"url\":\"https://e.test/p/\",\"images\":3}" 40 40) "document images must be an array"

-- HTML `img` (issue 1268): the host fetches it as an SVG image; with the bytes it is a box
-- of its decoded size (2 by 2 here) or of its attributes, with none its description.
private def imgPage := "<p><img src='a.png' alt='pic'>after</p>"
private def withPng := "\"images\":[{\"key\":\"https://e.test/p/a.png\",\"base64\":\"" ++ imageBytes ++ "\"}]"
private def renderImg (page more : String) : String :=
  WebDocument.compile page ("{\"op\":\"render\",\"url\":\"https://e.test/p/\"" ++ more ++ "}") 200 60
#guard contains (WebDocument.compile imgPage "{\"op\":\"inspect\",\"url\":\"https://e.test/p/\"}" 40 40)
  "\"images\":[{\"key\":\"https://e.test/p/a.png\",\"url\":\"https://e.test/p/a.png\"}]"
#guard contains (renderImg imgPage "") "\"text\":\"[pic]after\"" || contains (renderImg imgPage "") "\"text\":\"[pic]\""
#guard !contains (renderImg imgPage ("," ++ withPng)) "[pic]" && !contains (renderImg imgPage ("," ++ withPng)) "\"error\""
#guard !contains (renderImg "<p><img src='a.png' alt='pic' width='40' height='20'></p>" ("," ++ withPng)) "[pic]"
-- With a size and no bytes the box stays, empty, as in the common browsers.
#guard !contains (renderImg "<p><img src='a.png' alt='pic' width='40' height='20'></p>" "") "[pic]"
#guard Rendering.Layout.dimensionValue "40" == some 40 && Rendering.Layout.dimensionValue " 12.5px" == some 12.5
#guard Rendering.Layout.dimensionValue "50%" == none && Rendering.Layout.dimensionValue "auto" == none

-- The tab icon (HTML §4.6.7.8): a scalable icon first, then the smallest at least 32
-- device pixels, the last of equal ones; ICO is skipped (issue 1282); with no icon link,
-- an apple-touch-icon; with none, no icon and no `/favicon.ico`.
private def iconOf (head : String) : Option String :=
  let dom := DOM.parseHtmlDocument s!"<html><head>{head}</head><body></body></html>"
  WebDocument.iconURL dom "https://e.test/p/"
#guard iconOf "<link rel='shortcut icon' href='a.png'><link rel=icon href='b.svg'><link rel=icon href='c.png'>" == some "https://e.test/p/b.svg"
#guard iconOf "<link rel=icon sizes='16x16' href='s.png'><link rel=icon sizes='64x64' href='l.png'><link rel=icon sizes='32x32' href='m.png'>" == some "https://e.test/p/m.png"
#guard iconOf "<link rel=icon href='a.png'><link rel=ICON href='b.png'>" == some "https://e.test/p/b.png"
#guard iconOf "<link rel=icon href='a.ico'><link rel=icon type='image/x-icon' href='b'>" == none
#guard iconOf "<link rel=apple-touch-icon href='t.png'>" == some "https://e.test/p/t.png"
#guard iconOf "<link rel=apple-touch-icon href='t.png'><link rel=icon href='i.png'>" == some "https://e.test/p/i.png"
#guard iconOf "<link rel=stylesheet href='a.css'>" == none
#guard contains (WebDocument.compile "<link rel=icon href='i.svg'>" "{\"op\":\"inspect\",\"url\":\"https://e.test/p/\"}" 40 40) "\"icon\":\"https://e.test/p/i.svg\""
private def prepared (base64 : String) : String :=
  WebDocument.compile "" ("{\"op\":\"iconPrepare\",\"scale\":1,\"base64\":\"" ++ base64 ++ "\"}") 1 1
#guard contains (prepared imageBytes) "\"kind\":\"bitmap\",\"width\":2,\"height\":2"
-- <svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 4 4'><rect width='4' height='4'/></svg>
#guard contains (prepared "PHN2ZyB4bWxucz0naHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmcnIHZpZXdCb3g9JzAgMCA0IDQnPjxyZWN0IHdpZHRoPSc0JyBoZWlnaHQ9JzQnLz48L3N2Zz4=") "\"kind\":\"svg\""
#guard contains (prepared "aGk=") "not PNG, JPEG or GIF"
-- A large bitmap is fitted to 16 device pixels a side, keeping its ratio.
#guard (WebDocument.fitBitmap {width := 64,height := 32,rgba := NativeImage.zeroBytes (64*32*4)} 16).width == 16
#guard (WebDocument.fitBitmap {width := 64,height := 32,rgba := NativeImage.zeroBytes (64*32*4)} 16).height == 8
#guard (WebDocument.fitBitmap {width := 64,height := 32,rgba := NativeImage.zeroBytes (64*32*4)} 16).rgba.size == 16*8*4

/-! The FOAF graph page with no SVG text (issue 1268). `WebGraph.directScene` builds the
scene from the model; these differential guards (not a proof) check that it is the scene
of the SVG text of `NativeSceneSVG.serialize`: the same artifact (every primitive, in the
same order, its storage floats, its tiles and the tree), and the same document render
through `graphModel` as through the page text. -/
private def foafTurtle := "@prefix foaf: <http://xmlns.com/foaf/0.1/> .\n@prefix ex: <https://example.org/friends/> .\nex:alice a foaf:Person ; foaf:name \"Alice\" ; foaf:knows ex:bob, ex:carol .\nex:bob a foaf:Person ; foaf:name \"Bob\" ; foaf:knows ex:carol .\nex:carol a foaf:Person ; foaf:name \"Carol\" .\n"
private def foafModels : List NativeFoafNaut.Model :=
  match FoafGraph.fromTurtle foafTurtle none NativeFoafNaut.graphLimits with
  | .ok graph =>
    let m := NativeFoafNaut.initial graph 400 300
    [m, (NativeFoafNaut.update m 2 120 90).1, (NativeFoafNaut.update m 7 500 0).1]
  | .error _ => []
private def sameSceneAsText (m : NativeFoafNaut.Model) : Bool :=
  match NativeSceneSVG.serialize m.scene with
  | .error _ => false
  | .ok svg =>
    match NativeSVG.parse svg 400 300, WebGraph.directScene m.scene 400 300 with
    | .ok parsed, .ok direct =>
      parsed.artifact false false false == direct.artifact false false false &&
        parsed.compiled.length == direct.compiled.length
    | _, _ => false
#guard foafModels.length == 3
#guard foafModels.all sameSceneAsText
private def graphRequest (m : Option NativeFoafNaut.Model) : JSON.Json :=
  .object ([("op",.string "render"),("url",.string "foafnaut:graph"),("checks",.bool false)] ++
    (match m with | some m => [("graphModel",.string m.encode)] | none => []))
#guard foafModels.all fun m =>
  match WebGraph.page m.encode with
  | .ok html => WebDocument.runUncached html (graphRequest none) 400 300 ==
      WebDocument.runUncached "" (graphRequest (some m)) 400 300 &&
      (WebDocument.runUncached "" (graphRequest (some m)) 400 300).isOk
  | .error _ => false

/-! The inspector tree is in a render answer only when the request asks for it
(`tree:true`, issue 1268). Without it the answer has `"tree":null` and is otherwise the
same, for one frame and for layers. -/
private def treeRequest (tree : Option Bool) (layers : Bool) : JSON.Json :=
  .object ([("op",.string "render"),("url",.string "https://e.test/"),("checks",.bool false)] ++
    (if layers then [("layers",.bool true),("shell",.object [("scroll",.number "0")])] else []) ++
    ((tree.map fun t => [("tree",.bool t)]).getD []))
private def treeAnswer (tree : Option Bool) (layers : Bool) : String :=
  (WebDocument.runUncached "<p>A <b>B</b></p><svg width='20' height='20'><g><rect width='9' height='9'/></g></svg>"
    (treeRequest tree layers) 200 100).toOption.getD ""
private def dropField (key : String) : JSON.Json → JSON.Json
  | .object fields => .object (fields.filter (·.1 != key))
  | other => other
/-- The answer with no `tree` field, at the top and in each layer. -/
private def dropTree (j : JSON.Json) : JSON.Json :=
  match dropField "tree" j with
  | .object fields => .object (fields.map fun (k,v) => (k,dropField "tree" v))
  | other => other
private def sameButTree (a b : String) : Bool :=
  match JSON.parseJsonText a, JSON.parseJsonText b with
  | .ok (x,_), .ok (y,_) => dropTree x == dropTree y
  | _, _ => false
#guard [false,true].all fun layers =>
  contains (treeAnswer none layers) "\"tree\":null" &&
  treeAnswer none layers == treeAnswer (some false) layers &&
  !contains (treeAnswer (some true) layers) "\"tree\":null" &&
  contains (treeAnswer (some true) layers) "\"tree\":[" &&
  sameButTree (treeAnswer none layers) (treeAnswer (some true) layers)

/-! Answers with sections (issue 1268). Differential guards, not a proof: the head with
each section put back as the Base64 text and the decimal tiles is the text answer of
the same request with `binary:true`, for one frame and for layers. -/
private def wordsOf (b : ByteArray) : List JSON.Json :=
  (List.range (b.size/4)).map fun i =>
    .number (toString (b[4*i]!.toNat + 256*b[4*i+1]!.toNat + 65536*b[4*i+2]!.toNat + 16777216*b[4*i+3]!.toNat))
private def fillOne (sections : Array ByteArray) : JSON.Json → JSON.Json
  | .object fields => .object (fields.map fun (k,v) => match k, v with
      | "dataSection", .number n => ("dataBase64",.string (NativeSVG.base64Bytes (sections.getD n.toNat! .empty)))
      | "tilesSection", .number n => ("tiles",.array (wordsOf (sections.getD n.toNat! .empty)))
      | _, _ => (k,v))
  | other => other
private def fillSections (sections : Array ByteArray) (j : JSON.Json) : JSON.Json :=
  match fillOne sections j with
  | .object fields => .object (fields.map fun (k,v) => (k,fillOne sections v))
  | other => other
private def sectionPage := "<p>A <b>B</b> and more text to wrap</p><svg width='120' height='60'><g><rect width='90' height='9'/><circle cx='30' cy='30' r='20' fill='red'/></g></svg>"
private def sectionRequest (layers : Bool) : JSON.Json :=
  .object ([("op",.string "render"),("url",.string "https://e.test/"),("binary",.bool true),("checks",.bool false)] ++
    (if layers then [("layers",.bool true),("shell",.object [("scroll",.number "0")])] else []))
private def sameAsText (layers : Bool) : Bool :=
  match WebDocument.answerWith WebDocument.layOut true sectionPage (sectionRequest layers) 200 100,
      WebDocument.runUncached sectionPage (sectionRequest layers) 200 100 with
  | .ok (head,sections), .ok text =>
    match JSON.parseJsonText head, JSON.parseJsonText text with
    | .ok (h,_), .ok (t,_) => sections.size == (if layers then 4 else 2) && fillSections sections h == t &&
        !contains head "dataBase64"
    | _, _ => false
  | _, _ => false
#guard sameAsText false
#guard sameAsText true
-- Other answers have no section.
#guard (WebDocument.answerWith WebDocument.layOut true "" (json [("op",.string "shellSubmit"),("address",.string "a")]) 1 1).toOption.map (·.2.size) == some 0
-- The layout of `packAnswer`.
#guard (WebDocument.packAnswer "{}" #[⟨#[1,2,3,4,5]⟩]).data.toList ==
  [28,0,0,0, 4,0,0,0, 1,0,0,0, 5,0,0,0, 123,125,32,32, 1,2,3,4,5,0,0,0]
-- The address edit op: the edit state and the text for the clipboard (issue 1268).
private def shellEdit (action text : String) (shell : JSON.Json) : Option JSON.Json := do
  let output ← (WebDocument.run "" (json [("op",.string "shellEdit"),("action",.string action),("text",.string text),("shell",shell)]) 1 1).toOption
  return (← (JSON.parseJsonText output).toOption).1
#guard ((shellEdit "focus" "https://x.org/" (json [])).bind (·.field? "anchor")) == some (.number "0")
#guard ((shellEdit "copy" "" (json [("address",.string "abc"),("cursor",.number "3"),("anchor",.number "1")])).bind (·.field? "clipboard")) == some (.string "bc")
#guard ((shellEdit "cut" "" (json [("address",.string "abc"),("cursor",.number "3"),("anchor",.number "1")])).bind (·.field? "address")) == some (.string "a")
#guard ((shellEdit "copy" "" (json [("address",.string "abc"),("cursor",.number "3")])).bind (·.field? "clipboard")) == some .null
#guard (WebDocument.run "" (json [("op",.string "keyTable"),("platform",.string "mac")]) 1 1).toOption.map (fun t => decide ((t.splitOn "\"p\"").length > 1)) == some true

-- XHTML (HTML §14): a `.xht` URL is read as XML, so a style sheet in a CDATA section
-- applies (the WPT reference ref-filled-green-100px-square.xht has one).
private def xhtmlSource := "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\n<html xmlns=\"http://www.w3.org/1999/xhtml\"><head><style type=\"text/css\"><![CDATA[\n div { width: 100px }\n ]]></style></head><body><div id=\"target\">a</div></body></html>"
private def xhtmlWidth (url : String) : Option String := do
  let request := json [("url",.string url)]
  let dom ← (WebDocument.prepareDOM xhtmlSource request).toOption
  let rules ← (WebDocument.rules dom request).toOption
  let styles ← (Rendering.CSS.computeAll dom rules).toOption
  let id ← dom.getElementById 0 "target"
  return reprStr (← styles[id]?).width
#guard xhtmlWidth "https://example.test/a.xht" == some (reprStr (Rendering.CSS.Length.px 100))
#guard xhtmlWidth "https://example.test/a.XHTML?x=1#y" == some (reprStr (Rendering.CSS.Length.px 100))
-- The same text as HTML: the CDATA markers are text in the style element, the rule is lost.
#guard xhtmlWidth "https://example.test/a.html" == some (reprStr Rendering.CSS.Length.auto)
-- Not well-formed XML is refused, as an XML user agent shows a parse error.
#guard (WebDocument.prepareDOM "<html xmlns=\"http://www.w3.org/1999/xhtml\"><p></html>" (json [("url",.string "a.xht")])).toOption.isNone
