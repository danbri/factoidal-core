import WebRenderFontRequests
import WebRenderScript
import WebXslt
import L4Factoidal.Syntax.IriResolve
import WebSelection
import WebHistory
import WebShell

/-! Browser document transaction. Lean discovers resources, applies DOM commands,
orders supplied CSS, collects font requests and renders the resulting arena.
Hosts fetch bytes and execute the separately bounded JavaScript engine. -/
namespace WebDocument
open L4Factoidal

private def str (j : JSON.Json) (key : String) (fallback : String := "") : String :=
  match j.field? key with | some (.string s) => s | _ => fallback
private def attr (n : DOM.Node) (key : String) := Rendering.CSS.attrValue n key
private def stylesheet (n : DOM.Node) : Bool :=
  DOM.Dom.isHtmlElement n "link" &&
    (((attr n "rel").toLower.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " ").splitOn " ").contains "stylesheet"

private def activeSheet (n : DOM.Node) : Except String Bool := do
  if Rendering.CSS.hasAttribute n "disabled" || !["","text/css"].contains (attr n "type") then return false
  if (attr n "media").toLower == "print" then return false
  if !["","all","screen"].contains (attr n "media").toLower then throw "unsupported stylesheet media condition"
  return true

private def validateResources (dom : DOM.Dom) (request : JSON.Json) : Except String Unit := do
  let .array resources := (request.field? "resources").getD (.array []) | throw "document resources must be an array"
  if resources.length > 64 then throw "document resource limit exceeded"
  let mut ids : List Nat := []
  let mut bytes := 0
  for resource in resources do
    let .object fields := resource | throw "document resource must be an object"
    if (fields.map Prod.fst).eraseDups.length != fields.length then throw "duplicate resource field"
    let some (.number raw) := resource.field? "nodeId" | throw "resource nodeId required"
    let some id := raw.toNat? | throw "resource nodeId must be natural"
    let some node := dom.nodes[id]? | throw "unknown resource nodeId"
    if ids.contains id then throw "duplicate resource nodeId"
    if !(dom.treeOrder 0).contains id || !(stylesheet node || DOM.Dom.isHtmlElement node "script") then
      throw "resource is not a connected stylesheet or script"
    let some (.string source) := resource.field? "source" | throw "resource source must be a string"
    if source.utf8ByteSize > 1048576 then throw "resource exceeds1MiB"
    bytes := bytes+source.utf8ByteSize
    if bytes > 4194304 then throw "resources exceed4MiB"
    ids := id::ids

def prepareDOM (html : String) (request : JSON.Json) : Except String DOM.Dom := do
  if html.utf8ByteSize > 1048576 then throw "document HTML exceeds 1MiB"
  WebRenderScript.applyCommands (DOM.parseHtmlDocument html)
    ((request.field? "commands").getD (.array []))

def baseURL (dom : DOM.Dom) (url : String) : String := Id.run do
  for id in dom.treeOrder 0 do
    let n := dom.get id
    if DOM.Dom.isHtmlElement n "base" && Rendering.CSS.hasAttribute n "href" then
      return Syntax.resolveIri url (attr n "href")
  return url

/-- The text of the first HTML `title` element, with white space collapsed. -/
def documentTitle (dom : DOM.Dom) : String := Id.run do
  for id in dom.treeOrder 0 do
    let n := dom.get id
    if DOM.Dom.isHtmlElement n "title" then
      let text := n.kids.foldl (fun acc kid =>
        let child := dom.get kid
        if child.type == .text then acc ++ child.data else acc) ""
      let spaced := text.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " "
      return " ".intercalate ((spaced.splitOn " ").filter (· != ""))
  return ""

private def supplied (request : JSON.Json) (id : Nat) : Except String String := do
  let .array resources := (request.field? "resources").getD (.array [])
    | throw "document resources must be an array"
  if resources.length > 64 then throw "document resource limit exceeded"
  let foundResources := resources.filter (fun r => r.field? "nodeId" == some (.number (toString id)))
  let [resource] := foundResources | throw s!"stylesheet resource missing or duplicated for node {id}"
  let some (.string source) := resource.field? "source" | throw "stylesheet source must be a string"
  if source.utf8ByteSize > 1048576 then throw "stylesheet exceeds 1MiB"
  return source

def rules (dom : DOM.Dom) (request : JSON.Json) : Except String (List Rendering.CSS.Rule) := do
  -- Preserve the existing SVG/HTML stylesheet boundary validation. This copy
  -- removes only the external-fetch refusal; it is never used for layout.
  let validation := {dom with nodes := dom.nodes.map (fun n =>
    if stylesheet n then {n with attrs := n.attrs.filter (fun a => a.lname != "href")} else n)}
  WebRender.validateStyleBoundaries validation
  let mut sheets : List String := []
  let mut bytes := 0
  for id in dom.treeOrder 0 do
    let n := dom.get id
    let source ← if DOM.Dom.isHtmlElement n "style" then do
        if ← activeSheet n then pure ((dom.textContent id).getD "") else pure ""
      else if stylesheet n && Rendering.CSS.hasAttribute n "href" then do
        if ← activeSheet n then supplied request id else pure ""
      else pure ""
    bytes := bytes+source.utf8ByteSize
    if bytes > 2097152 then throw "document stylesheets exceed 2MiB"
    sheets := source::sheets
  Rendering.CSS.parse (String.intercalate "\n" sheets.reverse)

/-- Script MIME classification has one owner: the Lean scripting snapshot.
All callers use its normalized kind, including whitespace/case and legacy
classic JavaScript MIME types. Modules stay an explicit profile refusal. -/
private def classicScripts (snapshot : JSON.Json) : Except String (List JSON.Json) := do
  let scripts := match snapshot.field? "scripts" with
    | some (.array scripts) => scripts
    | _ => []
  if scripts.any (fun script => str script "kind" == "module") then
    throw "unsupported JavaScript module script"
  return scripts.filter (fun script => str script "kind" == "classic")

def inspect (dom : DOM.Dom) (url : String) : Except String JSON.Json := do
  let base := baseURL dom url
  let snapshot := WebRenderScript.snapshot dom
  let mut sheets : List JSON.Json := []
  for id in dom.treeOrder 0 do
    let n := dom.get id
    if stylesheet n && Rendering.CSS.hasAttribute n "href" && (← activeSheet n) then
      sheets := .object [("nodeId",.number (toString id)),("href",.string (attr n "href")),
        ("url",.string (Syntax.resolveIri base (attr n "href")))]::sheets
  let scripts ← classicScripts snapshot
  let scripts := scripts.map fun script =>
    match script with
    | .object fields => .object (fields ++ [("url",.string (Syntax.resolveIri base (str script "src")))])
    | other => other
  return .object [("nodes",(snapshot.field? "nodes").getD (.array [])),
    ("scripts",.array scripts),("stylesheets",.array sheets.reverse),("baseURL",.string base),("title",.string (documentTitle dom))]

private def float (j : JSON.Json) : Except String Float :=
  match j with
  | .number lexical => Rendering.CSS.number lexical
  | _ => throw "selection point must be a number"

private def points (j : JSON.Json) : Except String (Float × Float × Float × Float) := do
  let .array [ax,ay,fx,fy] := j | throw "selection must be all or four numbers"
  return (← float ax,← float ay,← float fx,← float fy)

private def selection (request : JSON.Json) : Except String (Option WebSelection.Selection) :=
  match request.field? "selection" with
  | none => pure none
  | some (.string "all") => pure (some .all)
  | some value => do
    let (ax,ay,fx,fy) ← points value
    pure (some (.span ax ay fx fy))

private def scalePercent (request : JSON.Json) : Except String Nat := do
  let percent ← match request.field? "textScalePercent" with
    | none => pure 100
    | some (.number n) => match n.toNat? with
      | some value => pure value
      | none => throw "textScalePercent must be an integer"
    | _ => throw "textScalePercent must be an integer"
  if percent < 50 || percent > 250 then throw "textScalePercent must be 50 to 250"
  return percent

private def history (request : JSON.Json) : Except String WebHistory.History := do
  let some value := request.field? "history" | throw "history required"
  let some (.array rawEntries) := value.field? "entries" | throw "history entries required"
  let some (.number rawIndex) := value.field? "index" | throw "history index required"
  let some index := rawIndex.toNat? | throw "history index must be natural"
  let entries ← rawEntries.mapM fun | .string url => pure url | _ => throw "history entry must be a URL"
  if entries.length > WebHistory.maxEntries || (index >= entries.length && index != 0) then throw "history out of range"
  return {entries:=entries.toArray,index}

private def historyFields (h : WebHistory.History) (url : Option String) : List (String × JSON.Json) :=
  [("history",.object [("entries",.array (h.entries.toList.map .string)),("index",.number (toString h.index))]),
   ("url",match url with | some value => .string value | none => .null),
   ("canBack",.bool h.canBack),("canForward",.bool h.canForward)]

/-- Input decisions need no document, so they do not parse one. -/
private def inputOp (op : String) (request : JSON.Json) : Except String (Option String) := do
  if op == "command" then
    let some (.number raw) := request.field? "command" | throw "command number required"
    let some command := raw.toNat? | throw "command must be natural"
    let percent ← scalePercent request
    let fields := [("action",JSON.Json.string (WebSelection.commandName command)),
      ("textScalePercent",.number (toString (WebSelection.commandPercent command percent)))]
    if (request.field? "history").isNone then return some (JSON.Json.object fields).toString
    let (next,url) := WebHistory.apply command (← history request)
    return some (JSON.Json.object (fields ++ historyFields next url)).toString
  if op == "historyPush" then
    let some (.string url) := request.field? "url" | throw "history URL required"
    let next := (← history request).push url
    return some (JSON.Json.object (historyFields next next.current)).toString
  if op == "keyCommand" then
    let answer := WebHistory.keyCommand (str request "platform" "") (str request "modifier" "") (str request "key" "")
    return some (JSON.Json.object [("command",match answer with
      | some value => .number (toString value) | none => .null)]).toString
  if op == "shellHit" then
    let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
    let some (.number x) := request.field? "x" | throw "x required"
    let some (.number y) := request.field? "y" | throw "y required"
    let some (.number width) := request.field? "width" | throw "width required"
    return some (JSON.Json.object [("control",match WebShell.hit shell (width.toNat?.getD 1) (x.toNat?.getD 0) (y.toNat?.getD 0) with
      | some name => .string name | none => .null)]).toString
  if op == "shellText" then
    return some (WebShell.Shell.ofJson ((request.field? "shell").getD .null) |>.typed (str request "text")).editJson.toString
  if op == "shellKey" then
    let some (.number code) := request.field? "key" | throw "key required"
    return some (WebShell.Shell.ofJson ((request.field? "shell").getD .null) |>.key (code.toNat?.getD 0)).editJson.toString
  if op == "shellSubmit" then return some (WebShell.submit (str request "address")).json.toString
  if op == "sourcePage" then
    return some (JSON.Json.object [("source",.string (WebShell.sourcePage (str request "kind") (str request "url") (str request "source")))]).toString
  if op == "shellLink" then return some (WebShell.link (str request "href")).json.toString
  if op == "pointerUp" then
    let (ax,ay,fx,fy) ← points ((request.field? "selection").getD .null)
    return some (JSON.Json.object [("action",.string (if WebSelection.isClick ax ay fx fy then "click" else "select"))]).toString
  return none

/-- A long page must not fill the GPU buffer with text nobody can see. Glyphs carry
their place in a transform; those far above or below the window are left out.
Every other paint stays, since a rectangle can be as tall as the page. -/
private def inWindow (top bottom : Float) : Rendering.Node → Bool
  | .paint p =>
    let t := p.primitive.transform
    (t.a == 1 && t.f == 0) || (top <= t.f && t.f <= bottom)
  | _ => true

def run (html : String) (request : JSON.Json) (width height : Nat) : Except String String := do
  let .object fields := request | throw "document request must be an object"
  if (fields.map Prod.fst).eraseDups.length != fields.length then throw "duplicate document request field"
  if str request "op" == "xmlStylesheet" then
    let url := match ← WebXslt.stylesheetHref html with
      | some href => JSON.Json.string (Syntax.resolveIri (str request "url") href)
      | none => .null
    return (JSON.Json.object [("url",url)]).toString
  if str request "op" == "xslt" then
    let (source,engine) ← WebXslt.transform html (str request "stylesheet") (str request "url") (str request "stylesheetURL")
    return (JSON.Json.object [("source",.string source),("engine",.string engine)]).toString
  if let some answer ← inputOp (str request "op" "render") request then return answer
  let dom ← prepareDOM html request
  validateResources dom request
  let _ ← classicScripts (WebRenderScript.snapshot dom)
  let op := str request "op" "render"
  if op == "inspect" then return (← inspect dom (str request "url")).toString
  let textScale := Float.ofNat (← scalePercent request) / 100
  let rules ← rules dom request
  if op == "fontRequests" then
    return WebRenderFontRequests.requestsJSON (← WebRenderFontRequests.collectDOMWithRules dom rules textScale)
  if op != "render" && op != "selectedText" then throw "unknown document operation"
  if width == 0 || height == 0 || width > 4096 || height > 4096 then throw "unsupported document viewport"
  let fontData := str request "fontData"
  if !fontData.isEmpty then
    let _ ← WebRenderFontRequests.collectDOMWithRules dom rules textScale
  let face ← if fontData.isEmpty then pure none else
    some <$> Rendering.FontProvider.Face.decode fontData
  let font := match face with | some f => Rendering.Layout.FontProfile.ofFace f | none => WebRender.asciiFont
  let url := baseURL dom (str request "url")
  let embedding ← WebRender.makeEmbedding dom (if url.isEmpty then none else some url)
  let shell := (request.field? "shell").map WebShell.Shell.ofJson
  let top := (shell.map (fun value => WebShell.height value width)).getD 0
  -- A window shorter than the chrome still lays out, on one row.
  let (scene,boxes) ← Rendering.Layout.render dom rules font embedding width (max 1 (height-top)) textScale
  -- Pointer positions are in window coordinates; the page starts below the chrome.
  let moved := Float.ofNat top-Float.ofNat ((shell.map (·.scroll)).getD 0)
  let chosen := (← selection request).map (fun value => WebSelection.shift value moved)
  let items := WebSelection.cells scene.glyphRuns
  if op == "selectedText" then
    return (JSON.Json.object [("text",.string (match chosen with
      | some value => WebSelection.text items value
      | none => ""))]).toString
  let marks := match chosen with
    | some value => WebSelection.highlight items value
    | none => []
  let scrolled := Float.ofNat ((shell.map (·.scroll)).getD 0)
  let near := scene.tree.filter (inWindow (scrolled-512) (scrolled+Float.ofNat height+512))
  let page := {scene with tree := near ++ marks}
  WebRender.artifact (match shell with
    | some value => WebShell.compose value page width height
    | none => page) boxes face

@[export web_document_compile]
def compile (html request : String) (width height : UInt32) : String :=
  if request.utf8ByteSize > 20971520 then WebRender.errorJSON "document request exceeds20MiB"
  else match JSON.parseJsonText request with
  | .error _ => WebRender.errorJSON "invalid document request JSON"
  | .ok (j,pos) =>
    if !(request.toList.drop pos).all Char.isWhitespace then WebRender.errorJSON "trailing document request data"
    else match run html j width.toNat height.toNat with
      | .ok value => value | .error message => WebRender.errorJSON message
end WebDocument
