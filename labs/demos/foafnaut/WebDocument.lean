import WebRenderFontRequests
import L4Factoidal.DOM.OfXml
import WebRenderScript
import WebXslt
import L4Factoidal.Syntax.IriResolve
import WebSelection
import WebHistory
import WebShell
import WebGesture
import WebPrint
import WebGraph
import WebEventLoop
import WebWasm
import WebState
import WebSparql
import WebScripts
import L4Factoidal.Rendering.SfntProfile
import L4Factoidal.FrameCost.Band
import L4Factoidal.FrameCost.Lru
import L4Factoidal.Rendering.ComputedValues
import WebRepaint
import L4Factoidal.WHATWG.Encoding.Sniff
import WebHit

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

/-- The media type of a request: "print" when the host prints, else "screen". -/
def medium (request : JSON.Json) : String := if str request "media" == "print" then "print" else "screen"

private def activeSheet (medium : String) (n : DOM.Node) : Except String Bool := do
  if Rendering.CSS.hasAttribute n "disabled" || !["","text/css"].contains (attr n "type") then return false
  let media := (attr n "media").toLower
  if media == "" || media == "all" || media == medium then return true
  if media == "print" || media == "screen" then return false
  throw "unsupported stylesheet media condition"

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

/-- Limit on the images of one request, and on their base64 text. -/
private def maxDocumentImages : Nat := 64
private def maxImageText : Nat := 8388608

/-- Bytes the host fetched for `image` elements: `{key,base64}` records, where `key`
    is a key that `inspect` gave. The bytes stay opaque until `NativeImage.decode`. -/
def suppliedImages (request : JSON.Json) : Except String (List (String × ByteArray)) := do
  let .array images := (request.field? "images").getD (.array []) | throw "document images must be an array"
  if images.length > maxDocumentImages then throw s!"document images exceed {maxDocumentImages}"
  let mut text := 0
  let mut found : List (String × ByteArray) := []
  for image in images do
    let some (.string key) := image.field? "key" | throw "image key must be a string"
    let some (.string data) := image.field? "base64" | throw "image base64 must be a string"
    text := text+data.utf8ByteSize
    if text > maxImageText then throw s!"document images exceed {maxImageText} characters of base64"
    found := (key,← NativeImage.base64 data.toUTF8 0)::found
  return found

/-- SVG `image` and HTML `img` references that the host must fetch, by key and URL,
in document order. A page with more than `maxDocumentImages` gets the first ones;
the others show their alt text. -/
private def imageRequests (dom : DOM.Dom) (base : String) : Except String (List JSON.Json) := do
  let svgKeys ← if dom.nodes.any (fun node => node.type == .element && node.ns == some DOM.svgNS) then do
      let (_,tree) ← WebRender.documentNamespaceTree dom
      pure (NativeSVG.imageKeys tree (some base))
    else pure []
  let htmlKeys := (WebRender.htmlImageKeys dom (some base)).map (·.2)
  let keys := ((svgKeys ++ htmlKeys).eraseDups.filter (!·.toLower.startsWith "data:")).take maxDocumentImages
  return keys.map fun key => .object [("key",.string key),("url",.string key)]

/-- The document tree: the XML syntax of HTML for a `.xht` or `.xhtml` URL (HTML §14,
`DOM.parseXmlDocument`), else the HTML syntax (HTML §13). -/
def prepareDOM (html : String) (request : JSON.Json) : Except String DOM.Dom := do
  if html.utf8ByteSize > 1048576 then throw "document HTML exceeds 1MiB"
  let dom ← if DOM.isXhtmlPath (str request "url") then DOM.parseXmlDocument html
    else pure (DOM.parseHtmlDocument html)
  WebRenderScript.applyCommands dom
    ((request.field? "commands").getD (.array []))

def baseURL (dom : DOM.Dom) (url : String) : String := Id.run do
  for id in dom.treeOrder 0 do
    let n := dom.get id
    if DOM.Dom.isHtmlElement n "base" && Rendering.CSS.hasAttribute n "href" then
      return Syntax.resolveIri url (attr n "href")
  return url

/-! ### The icon of a page (HTML §4.6.7.8, link type "icon") -/

/-- The ASCII-lowercase tokens of an attribute (HTML §2.3.8, space-separated tokens). -/
private def tokens (value : String) : List String :=
  ((value.toLower.replace "\t" " ").replace "\n" " " |>.replace "\r" " " |>.replace "\x0c" " ").splitOn " " |>.filter (· != "")

/-- The path of a URL with no query or fragment, lowercase. -/
private def pathOf (url : String) : String :=
  (((url.splitOn "#").headD "").splitOn "?").headD "" |>.toLower

/-- An icon the engine can not decode: ICO, https://github.com/danbri/factoidal/issues/1282 -/
def iconUnsupported (url type : String) : Bool :=
  type.toLower == "image/x-icon" || type.toLower == "image/vnd.microsoft.icon" || (pathOf url).endsWith ".ico"

/-- How well an icon fits a tab of `target` device pixels; less is better. A scalable
icon fits any size; then the smallest at least `target`; then the largest; then an
icon with no `sizes`. -/
def iconRank (url type sizes : String) (target : Nat) : Nat × Nat :=
  let words := tokens sizes
  if type.toLower == "image/svg+xml" || (pathOf url).endsWith ".svg" || words.contains "any" then (0,0) else
  let sides := words.filterMap fun w => match w.splitOn "x" with
    | [a,b] => match a.toNat?, b.toNat? with | some x, some y => some (max x y) | _, _ => none
    | _ => none
  match (sides.filter (· >= target)).min?, sides.max? with
  | some s, _ => (1,s)
  | none, some s => (2,100000-min s 100000)
  | none, none => (3,0)

/-- The URL of the icon for a tab of `target` device pixels, resolved against `base`.
Of the links whose `rel` has the token "icon" and that the engine can decode, the best
by `iconRank`, the last in tree order of equal ones (HTML §4.6.7.8). With none, an
`apple-touch-icon` the same way. No link gives no icon: `/favicon.ico` is not tried. -/
def iconURL (dom : DOM.Dom) (base : String) (target : Nat := 32) : Option String := Id.run do
  let mut best : Option ((Nat × Nat) × String) := none
  let mut touch : Option ((Nat × Nat) × String) := none
  for id in dom.treeOrder 0 do
    let n := dom.get id
    if !DOM.Dom.isHtmlElement n "link" then continue
    let href := (attr n "href").trimAscii.toString
    if href.isEmpty then continue
    let url := Syntax.resolveIri base href
    let type := attr n "type"
    if iconUnsupported url type then continue
    let rank := iconRank url type (attr n "sizes") target
    let better := fun (held : Option ((Nat × Nat) × String)) => match held with
      | none => true
      | some (r,_) => rank.1 < r.1 || (rank.1 == r.1 && rank.2 <= r.2)
    let rel := tokens (attr n "rel")
    if rel.contains "icon" && better best then best := some (rank,url)
    else if (rel.contains "apple-touch-icon" || rel.contains "apple-touch-icon-precomposed") && better touch then
      touch := some (rank,url)
  return (best.orElse fun _ => touch).map (·.2)

/-- Limit on the bytes of an icon. -/
def maxIconBytes : Nat := 65536

/-- An image `side` pixels at most each way, from `b`: each pixel the mean of the
pixels it covers, with colour weighted by opacity. An image that fits is kept. -/
def fitBitmap (b : Rendering.Bitmap) (side : Nat) : Rendering.Bitmap := Id.run do
  if b.width <= side && b.height <= side then return b
  let large := max b.width b.height
  let w := max 1 (b.width*side/large)
  let h := max 1 (b.height*side/large)
  let mut out := ByteArray.emptyWithCapacity (w*h*4)
  for y in [0:h] do
    for x in [0:w] do
      let x0 := x*b.width/w
      let x1 := max (x0+1) ((x+1)*b.width/w)
      let y0 := y*b.height/h
      let y1 := max (y0+1) ((y+1)*b.height/h)
      let mut r := 0
      let mut g := 0
      let mut bl := 0
      let mut a := 0
      for sy in [y0:y1] do
        for sx in [x0:x1] do
          let i := (sy*b.width+sx)*4
          let alpha := (b.rgba.get! (i+3)).toNat
          r := r+(b.rgba.get! i).toNat*alpha
          g := g+(b.rgba.get! (i+1)).toNat*alpha
          bl := bl+(b.rgba.get! (i+2)).toNat*alpha
          a := a+alpha
      let count := (x1-x0)*(y1-y0)
      let colour := fun (sum : Nat) => if a == 0 then 0 else (sum/a).toUInt8
      out := out.push (colour r) |>.push (colour g) |>.push (colour bl) |>.push (a/count).toUInt8
  return {width := w,height := h,rgba := out}

/-- The tab icon from the bytes of an icon resource, for a screen of `scale` device
pixels to the point: SVG text as it is, after a check that the SVG profile draws it at
16 points; PNG, JPEG and GIF (its first frame) decoded and fitted to 16 points. -/
def iconPrepare (bytes : ByteArray) (scale : Nat) : Except String JSON.Json := do
  if bytes.size > maxIconBytes then throw s!"icon exceeds {maxIconBytes} bytes"
  let side := 16*max 1 scale
  let text := (String.fromUTF8? bytes).getD ""
  let head := text.trimAsciiStart.toString
  if head.startsWith "<" then
    let _ ← NativeSVG.parse head side side
    return .object [("kind",.string "svg"),("source",.string head)]
  let b := fitBitmap (← NativeImage.decode bytes) side
  return .object [("kind",.string "bitmap"),("width",.number (toString b.width)),("height",.number (toString b.height)),
    ("rgba",.string (NativeSVG.base64Bytes b.rgba))]

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
        if ← activeSheet (medium request) n then pure ((dom.textContent id).getD "") else pure ""
      else if stylesheet n && Rendering.CSS.hasAttribute n "href" then do
        if ← activeSheet (medium request) n then supplied request id else pure ""
      else pure ""
    bytes := bytes+source.utf8ByteSize
    if bytes > 2097152 then throw "document stylesheets exceed 2MiB"
    sheets := source::sheets
  Rendering.CSS.parseFor (medium request) (String.intercalate "\n" sheets.reverse)

/-- Script MIME classification has one owner: the Lean scripting snapshot.
All callers use its normalized kind, including whitespace/case and legacy
classic JavaScript MIME types. Modules stay an explicit profile refusal. -/
private def classicScripts (scripts : List JSON.Json) : Except String (List JSON.Json) := do
  if scripts.any (fun script => str script "kind" == "module") then
    throw "unsupported JavaScript module script"
  return scripts.filter (fun script => str script "kind" == "classic")

def inspect (dom : DOM.Dom) (url : String) : Except String JSON.Json := do
  let base := baseURL dom url
  let snapshot := WebRenderScript.snapshot dom
  let mut sheets : List JSON.Json := []
  for id in dom.treeOrder 0 do
    let n := dom.get id
    -- The host fetches the sheets of the screen and of print: it prints the page it shows.
    if stylesheet n && Rendering.CSS.hasAttribute n "href" && ((← activeSheet "screen" n) || (← activeSheet "print" n)) then
      sheets := .object [("nodeId",.number (toString id)),("href",.string (attr n "href")),
        ("url",.string (Syntax.resolveIri base (attr n "href")))]::sheets
  let scripts ← classicScripts (WebRenderScript.scriptRecords dom)
  let scripts := scripts.map fun script =>
    match script with
    | .object fields => .object (fields ++ [("url",.string (Syntax.resolveIri base (str script "src")))])
    | other => other
  return .object [("nodes",(snapshot.field? "nodes").getD (.array [])),
    ("scripts",.array scripts),("stylesheets",.array sheets.reverse),("images",.array (← imageRequests dom base)),
    ("baseURL",.string base),("title",.string (documentTitle dom)),
    ("icon",match iconURL dom base with | some url => .string url | none => .null)]

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
  if percent < WebSelection.minPercent then throw s!"textScalePercent must be at least {WebSelection.minPercent}"
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

/-! ### Press acknowledgement (issue 1268)

On a pointer press the host asks `press` (a small call on the main thread). Lean
answers what is pressed (a chrome control, or the link under the pointer) and the
rectangles that the composite darkens (`compositePress`) until a Lean frame that
includes the press is presented. Rectangles are in source rows: chrome rows
`0 .. top`, then page-layer rows moved down by `top`, so a scroll in the band moves
them with the page. -/

/-- The most rectangles one press darkens: `compositeShader` has room for this many. -/
def maxPressRects : Nat := 8

private def natField (j : JSON.Json) (key : String) : Nat :=
  match j.field? key with | some (.number n) => n.toNat?.getD 0 | _ => 0

/-- The link regions of the frame on screen, decoded once: a press, a hover and a click
on the same frame send the same text. One slot, by string equality. -/
initialize keptLinksRef : IO.Ref (Option (String × List Rendering.LinkRegion)) ← IO.mkRef none

set_option compiler.extract_closed false in
private unsafe def decodeLinksImpl (text : String) : Except String (List Rendering.LinkRegion) :=
  unsafeBaseIO do
    if let some (kept,regions) ← keptLinksRef.get then
      if kept == text then return .ok regions
    let made := Rendering.Links.decode text
    if let .ok regions := made then keptLinksRef.set (some (text,regions))
    return made

/-- `Links.decode`; the engine gives the regions of the last text again when the text is equal. -/
@[implemented_by decodeLinksImpl]
def decodeLinks (text : String) : Except String (List Rendering.LinkRegion) := Rendering.Links.decode text

/-- `Links.pick` over `decodeLinks` (the C shim's `web_render_hit`). -/
@[export web_render_pick_link_kept]
def pickKept (regions : String) (width height : UInt32) (x y : Float) : String :=
  if !x.isFinite || !y.isFinite || x < 0 || y < 0 ||
    x >= Float.ofNat width.toNat || y >= Float.ofNat height.toNat then "null"
  else match decodeLinks regions with
    | .error message => "{\"error\":" ++ "\"" ++ JSON.escapeString message ++ "\"" ++ "}"
    | .ok regions => Rendering.Links.targetJSON (Rendering.hitLink regions x y)

theorem pickKept_eq (regions : String) (width height : UInt32) (x y : Float) :
    pickKept regions width height x y = Rendering.Links.pick regions width height x y := by
  unfold pickKept Rendering.Links.pick decodeLinks; rfl

/-- The answer to `press`: `control` for a chrome control; `sourceNode` and `href` for a
link of the page layer (`linksText` or `links`, in band rows, as the frame answered them, picked at
`(x,row)`); `rects` for the composite. -/
def press (request : JSON.Json) : Except String String := do
  let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
  let width := natField request "width"
  let x := natField request "x"
  let y := natField request "y"
  let top := WebShell.height shell width
  let rect := fun (r : Nat × Nat × Nat × Nat) =>
    JSON.Json.array [.number (toString r.1),.number (toString r.2.1),.number (toString r.2.2.1),.number (toString r.2.2.2)]
  match WebShell.hit shell width x y with
  | some control =>
    let rects := (WebShell.pressBox shell width control).toList
    return (JSON.Json.object [("control",.string control),("rects",.array (rects.map rect))]).toString
  | none =>
    -- `linksText`: the regions as the frame gave them, decoded once per frame (`decodeLinks`);
    -- `links`: the same as a JSON array, decoded on each call (older hosts).
    let regions ← match request.field? "linksText",request.field? "links" with
      | some (.string text),_ => decodeLinks text
      | _,some (.array items) => Rendering.Links.decode (JSON.Json.array items).toString
      | _,_ => pure []
    -- `row`: the page-layer row under the pointer, as the host converts it for `hit`.
    let row := Float.ofNat (natField request "row")
    match Rendering.hitLink regions (Float.ofNat x) row with
    | none => return (JSON.Json.object [("control",.null),("sourceNode",.null),("rects",.array [])]).toString
    | some target =>
      let same := (regions.filter (·.sourceNode == target.sourceNode)).take maxPressRects
      let rects := same.map fun r =>
        let left := r.x.floor.toUInt32.toNat
        let upper := (max r.y.floor 0).toUInt32.toNat
        (left,upper+top,(r.x+r.width).ceil.toUInt32.toNat-left,(r.y+r.height).ceil.toUInt32.toNat-upper)
      return (JSON.Json.object [("control",.null),("sourceNode",.number (toString target.sourceNode)),
        ("href",.string target.href),("rects",.array (rects.map rect))]).toString

/-- `zoomUnit`: the screen's device pixels for each CSS pixel, in percent; 100 if absent. -/
private def zoomUnit (request : JSON.Json) : Nat :=
  match request.field? "zoomUnit" with
  | some (.number n) => match n.toNat? with | some u => if u = 0 then 100 else u | none => 100
  | _ => 100

/-- The text size of the settings page (`foafnaut:zoom/up`, `/down`, `/reset`, `/150`): from
`zoom` (absent or empty: no change), `textScalePercent` and `zoomUnit`, the zoom to use and
the text size the reader sees, with the default, the range and the step as zooms on this
screen. A `zoom` that is not a size is refused and changes nothing. -/
def textZoomAnswer (request : JSON.Json) : Except String String := do
  let percent ← scalePercent request
  let unit := zoomUnit request
  let argument := match request.field? "zoom" with | some (.string a) => a | _ => ""
  let ask := WebSelection.ZoomAsk.parse argument
  let next := match ask with | some a => WebSelection.textZoom a percent unit | none => percent
  let n := fun (k : Nat) => JSON.Json.number (toString k)
  let refused := if ask.isNone && !argument.isEmpty then [("refused",JSON.Json.string s!"not a text size: {argument}")] else []
  return (JSON.Json.object ([("textScalePercent",n next),("shown",n (WebSelection.shownPercent next unit)),
    ("default",n (WebSelection.unitPercent WebSelection.defaultPercent unit)),
    ("min",n (WebSelection.unitPercent WebSelection.minPercent unit)),("max",n (WebSelection.unitPercent WebSelection.maxShown unit)),
    ("step",n WebSelection.textStep)] ++ refused)).toString

/-- Input decisions need no document, so they do not parse one. -/
private def inputOp (op : String) (request : JSON.Json) : Except String (Option String) := do
  if op == "textZoom" then return some (← textZoomAnswer request)
  if op == "command" then
    let some (.number raw) := request.field? "command" | throw "command number required"
    let some command := raw.toNat? | throw "command must be natural"
    let percent ← scalePercent request
    let action := WebSelection.commandName command
    -- An edit command acts on the address bar when it has the focus; paste always does,
    -- since the bar is the only text field. Else it acts on the page (issue 1268).
    let focused := request.field? "focused" == some (.bool true)
    let target := if WebShell.addressCommands.contains action && (focused || action == "paste") then "address" else "page"
    let nat := fun (name : String) => match request.field? name with
      | some (.number n) => n.toNat?.getD 0 | _ => 0
    -- A tab command answers the tab to show, from `tabs` and `active`; a scroll command the
    -- scroll, from `scroll`, `view`, `scrollLimit` and `scale` (issue 1268).
    let tab := match WebHistory.tabTarget command (nat "active") (nat "tabs") with
      | some i => [("tab",JSON.Json.number (toString i))] | none => []
    let scrollTo := match WebHistory.scrollTarget command (nat "scroll") (nat "view") (nat "scrollLimit") (80*max 1 (nat "scale")) with
      | some n => [("scrollTo",JSON.Json.number (toString n))] | none => []
    let refused := if command == WebHistory.findCommand
      then [("refused",JSON.Json.string "find in page is not implemented: https://github.com/danbri/factoidal/issues/1280")] else []
    let fields := [("action",JSON.Json.string action)] ++
      (if WebShell.addressCommands.contains action then [("target",JSON.Json.string target)] else []) ++
      [("textScalePercent",.number (toString (WebSelection.commandPercent command percent (zoomUnit request))))] ++ tab ++ scrollTo ++ refused
    if (request.field? "history").isNone then return some (JSON.Json.object fields).toString
    let (next,url) := WebHistory.apply command (← history request)
    return some (JSON.Json.object (fields ++ historyFields next url)).toString
  if op == "historyPush" then
    let some (.string url) := request.field? "url" | throw "history URL required"
    let next := (← history request).push url
    return some (JSON.Json.object (historyFields next next.current)).toString
  -- The page script setting (WebRenderScript.plan): what a setting means for a page, on a host.
  if op == "scriptSetting" then
    let some value := WebRenderScript.setting? (str request "setting") | throw "unknown page script engine"
    return some (JSON.Json.object [("setting",.string value),("name",.string (WebRenderScript.engineName value))]).toString
  if op == "scriptPlan" then
    let scripts := match request.field? "scripts" with | some (.number n) => n.toNat?.getD 0 | _ => 0
    return some (WebRenderScript.plan (str request "setting") scripts (str request "host" "native")
      (str request "unavailable") (str request "failure")).json.toString
  if op == "scriptChoices" then
    return some (JSON.Json.object [("html",.string (WebRenderScript.choicesHTML (str request "setting") (str request "host" "native")))]).toString
  -- The tab icon from the bytes of an icon resource (`iconPrepare`).
  if op == "iconPrepare" then
    let some (.string data) := request.field? "base64" | throw "icon base64 required"
    if data.utf8ByteSize > 4*maxIconBytes/3+4 then throw s!"icon exceeds {maxIconBytes} bytes"
    let scale := match request.field? "scale" with | some (.number n) => n.toNat?.getD 1 | _ => 1
    return some (← iconPrepare (← NativeImage.base64 data.toUTF8 0) scale).toString
  -- A key that the macOS menu did not take, as the window library sends it.
  if op == "pageKey" then
    let some (.number code) := request.field? "key" | throw "key required"
    let bits := match request.field? "modifiers" with | some (.number m) => m.toNat?.getD 0 | _ => 0
    return some (JSON.Json.object [("command",match WebHistory.pageKey (code.toNat?.getD 0) bits with
      | some value => .number (toString value) | none => .null)]).toString
  if op == "keyCommand" then
    let answer := WebHistory.keyCommand (str request "platform" "") (str request "modifier" "") (str request "key" "")
    return some (JSON.Json.object [("command",match answer with
      | some value => .number (toString value) | none => .null)]).toString
  if op == "shellHit" then
    let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
    let some (.number x) := request.field? "x" | throw "x required"
    let some (.number y) := request.field? "y" | throw "y required"
    let some (.number width) := request.field? "width" | throw "width required"
    let control := WebShell.hit shell (width.toNat?.getD 1) (x.toNat?.getD 0) (y.toNat?.getD 0)
    -- `how` (tap, hold or context) and `touch`: whether this press opens the address menu.
    return some (JSON.Json.object [("control",match control with
      | some name => .string name | none => .null),
      ("menu",.bool (WebShell.opensMenu control (str request "how" "tap") (request.field? "touch" == some (.bool true))))]).toString
  -- The address menu's action table (WebShell.menuActions): the buttons in CSS px and the
  -- text Copy writes. Empty with the menu closed; an engine without the op has no menu.
  if op == "shellActions" then
    let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
    return some (JSON.Json.object [("actions",.array ((WebShell.menuActions shell (natField request "width")).map (·.json)))]).toString
  if op == "press" then return some (← press request)
  -- The pointer for a point of the window (issue 1268): the chrome's control, else the page.
  -- On the page a click acts over a person of the graph `model`, or over a link of
  -- `links` (the regions of the frame on screen, as for picking) at page row `pageY`.
  if op == "pointerCursor" then
    let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
    let some (.number x) := request.field? "x" | throw "x required"
    let some (.number y) := request.field? "y" | throw "y required"
    let some (.number width) := request.field? "width" | throw "width required"
    let x := x.toInt?.getD (-1)
    let y := y.toInt?.getD (-1)
    let control := if x < 0 || y < 0 then none else WebShell.hit shell (width.toNat?.getD 1) x.toNat y.toNat
    let onPage := control.isNone && x >= 0 && y >= 0 &&
      match request.field? "model", request.field? "links", request.field? "pageY" with
      | some (.string _), _, _ => WebGraph.acts request x y
      | _, some (.string links), some (.number pageY) =>
        match L4Factoidal.Rendering.Links.decode links, pageY.toInt? with
        | .ok regions, some row => row >= 0 && (Rendering.hitLink regions (Float.ofInt x) (Float.ofInt row)).isSome
        | _, _ => false
      | _, _, _ => false
    return some (JSON.Json.object [("cursor",.string (WebShell.pointer shell control onPage).name)]).toString
  if op == "shellText" then
    return some (WebShell.Shell.ofJson ((request.field? "shell").getD .null) |>.typed (str request "text")).editJson.toString
  if op == "shellKey" then
    let some (.number code) := request.field? "key" | throw "key required"
    let modifiers := match request.field? "modifiers" with | some (.number m) => m.toNat?.getD 0 | _ => 0
    return some (WebShell.Shell.ofJson ((request.field? "shell").getD .null) |>.key (code.toNat?.getD 0) modifiers).editJson.toString
  -- Select all, copy, cut, paste (`text` is the clipboard), undo, redo, and focus (`text`
  -- is the page address). The answer is the edit state and the text for the clipboard.
  if op == "shellEdit" then
    let (next,copied) := (WebShell.Shell.ofJson ((request.field? "shell").getD .null)).edit (str request "action") (str request "text")
    let .object fields := next.editJson | throw "edit state"
    -- Paste and go answers the address to go to in `go`, not for the clipboard.
    let key := if str request "action" == "pasteGo" then "go" else "clipboard"
    return some (JSON.Json.object (fields ++ [(key,match copied with | some t => .string t | none => .null)])).toString
  -- The key table for a host with no menu, which must decide at once which keys it keeps.
  if op == "keyTable" then
    let platform := str request "platform" "other"
    return some (JSON.Json.array ((WebHistory.keyTable.filter (·.1 == platform)).map fun (_,m,k,c) =>
      .object [("modifier",.string m),("key",.string k),("command",.number (toString c))])).toString
  if op == "shellSubmit" then return some (WebShell.submit (str request "address")).json.toString
  if let some answer ← WebGraph.op op request then return some answer
  if let some answer ← WebEventLoop.op op request then return some answer
  if op == "sourcePage" then
    return some (JSON.Json.object [("source",.string (WebShell.sourcePage (str request "kind") (str request "url") (str request "source")))]).toString
  if op == "shellLink" then return some (WebShell.link (str request "href")).json.toString
  -- Where a link or an address goes (WebRoute; owner, 2026-11-08): the final action, which
  -- the hosts do with no URL test of their own. `origin` is the site the browser loads
  -- pages from ("" for every site), `pages` its folder of pages, `files` whether it reads
  -- local files, `base` the address of the page the link is on.
  if op == "shellRoute" then
    let site : WebRoute.Site := {origin := str request "origin",pages := str request "pages",files := request.field? "files" == some (.bool true)}
    let route := match request.field? "address" with
      | some (.string address) => WebShell.routeAddress site (str request "base") address
      | _ => WebRoute.route site (str request "base") (str request "href")
    return some (WebShell.routeJson route).toString
  -- Back and forward swipes (WebGesture): `action` info, touch or wheel.
  if let some answer ← WebGesture.op op request then return some answer
  -- WebAssembly run by Lean's own engine, WasmVM (WebWasm; issue 1244).
  if let some answer ← WebWasm.op op request then return some answer
  -- Bookmarks, history, settings and tabs as LWS resources (WebState; browser_state_test.ts).
  if let some answer ← WebState.op op request then return some answer
  -- The SPARQL planner drawn as live debug (WebSparql; owner, 2026-11-08).
  if let some answer ← WebSparql.op op request then return some answer
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

/-- A glyph far from the window: a paint with a source node whose transform puts it
above `top` or below `bottom`. Glyphs carry their place in their transform; other paint
in a group (an embedded SVG's shapes) may not, so it stays. -/
private def farGlyph (top bottom : Float) : Rendering.Node → Bool
  | .paint p => p.source.isSome && !inWindow top bottom (.paint p)
  | _ => false

/-- A translation with no scale, rotation or skew: the layout's table cells and rows,
moved blocks and inline-blocks (`Layout.translate`). -/
private def isTranslation (t : Rendering.Transform) : Bool :=
  t.a == 1 && t.b == 0 && t.c == 0 && t.d == 1

mutual
/-- A node with the glyphs far from the window `top .. bottom` left out of each group
or clip that only translates, in its own rows: the window moved up by its translation. -/
private def nearInside (top bottom : Float) : Rendering.Node → Rendering.Node
  | .group id t children =>
    if isTranslation t then .group id t (nearNested (top-t.f) (bottom-t.f) children) else .group id t children
  | .clipped id t clip children =>
    if isTranslation t then .clipped id t clip (nearNested (top-t.f) (bottom-t.f) children)
    else .clipped id t clip children
  | node => node
private def nearNested (top bottom : Float) : List Rendering.Node → List Rendering.Node
  | [] => []
  | node :: rest =>
    if farGlyph top bottom node then nearNested top bottom rest
    else nearInside top bottom node :: nearNested top bottom rest
end

/-- The nodes of a page near the window `top .. bottom`. At the top level a paint goes
by `inWindow`; inside a group or clip that only translates (the layout puts table
cells, table rows, moved blocks and inline-blocks in one) each glyph goes by its place
in the group's rows. Before, every group stayed whole, so a page of tables kept the
glyphs of the whole page in each frame and band, and a tall page at a large text zoom
passed `NativeSVG.maxDataFloats`. Any other group stays whole. -/
def nearNodes (top bottom : Float) (nodes : List Rendering.Node) : List Rendering.Node :=
  (nodes.filter (inWindow top bottom)).map (nearInside top bottom)

/-! ### Two layers: the chrome and a band of the page (issue 1268)

With `layers:true` and a shell, a render answers two artifacts. The chrome layer
holds window rows `0 .. top`. The page layer holds the page rows `band.top ..
band.top+band.height`: the page moved up by `band.top`. The host draws each layer
once into its own texture. Each present then copies, with `composite`: window row
`y < top` from chrome row `y`, and window row `y ≥ top` from page row
`y-top+offset`, with `offset = scroll-band.top`. A scroll whose view stays in the
band changes only `offset`, so it needs no Lean call. -/

-- The band, its keep range and the composite are `FrameCost.Band`, the definitions that
-- the cost theorems (`L4Factoidal.FrameCost.Theorems`, section `Ratchet`) are about.
export L4Factoidal.FrameCost (bandMargin refreshMargin maxLayerRows Band band composite
  composite_eq_frame band_fits band_height_le keep_fits composite_row_lt)

/-- The largest scroll: the view of `view` rows then ends at the last page row
`content` (issue 1270 report: the host took the chrome as 60 rows and stopped 5 rows
short at scale 1, 10 at scale 2). -/
def scrollLimit (content view : Nat) : Nat := content-view

/-- At the largest scroll, the last page row is in the view. -/
theorem scrollLimit_reaches (content view : Nat) : content ≤ scrollLimit content view+view := by
  simp only [scrollLimit]; omega
/-- A page shorter than the view does not scroll. -/
theorem scrollLimit_short (content view : Nat) (short : content ≤ view) : scrollLimit content view = 0 := by
  simp only [scrollLimit]; omega

/-- The source row of window row `y`: the chrome row, or the page-layer row moved down
by `top`. Press rectangles (`press`) are in these rows. -/
def sourceRow (top offset y : Nat) : Nat := if y < top then y else y-top+offset+top

/-- `(x,row)` is in one of the rectangles `(x,y,w,h)`. -/
def inRects (rects : List (Nat × Nat × Nat × Nat)) (x row : Nat) : Bool :=
  rects.any fun (rx,ry,rw,rh) => rx ≤ x && x < rx+rw && ry ≤ row && row < ry+rh

/-- The composite with a press acknowledgement: `tint` applied where a press rectangle
covers the source pixel. -/
def compositePress {α : Type} (tint : α → α) (chrome page : Nat → Nat → α) (top offset : Nat)
    (rects : List (Nat × Nat × Nat × Nat)) (x y : Nat) : α :=
  let c := composite chrome page top offset x y
  if inRects rects x (sourceRow top offset y) then tint c else c

/-- With no press rectangle the composite is unchanged: `composite_eq_frame` still holds. -/
theorem compositePress_nil {α : Type} (tint : α → α) (chrome page : Nat → Nat → α) (top offset x y : Nat) :
    compositePress tint chrome page top offset [] x y = composite chrome page top offset x y := by
  simp [compositePress,inRects]

/-- A page rectangle moves with the page: at any offset, the window pixel that shows
page-layer row `r` is darkened exactly when `(x, r+top)` is in a rectangle. -/
theorem sourceRow_page (top offset y : Nat) (below : top ≤ y) :
    sourceRow top offset y = (y-top+offset)+top := by
  unfold sourceRow; split <;> omega

/-- The press darkening: three quarters of each colour channel, alpha kept. -/
def pressShade : Float := 0.75

/-- The WGSL of `compositePress`: binding 0 the chrome texture, 1 the page texture,
2 ten words-of-four: `place[0]` is `top`, `offset`, the page layer height and the
rectangle count (at most `maxPressRects`); `place[1..8]` the rectangles `(x,y,w,h)`
in source rows. A row past the page layer is white, as the scene shader paints
outside its viewport. -/
def compositeShader : String :=
  "@group(0) @binding(0) var chrome:texture_2d<f32>;\n" ++
  "@group(0) @binding(1) var page:texture_2d<f32>;\n" ++
  s!"@group(0) @binding(2) var<uniform> place:array<vec4u,{maxPressRects+2}>;\n" ++
  "@vertex fn vertex(@builtin(vertex_index) i:u32)->@builtin(position) vec4f {" ++
  "let vertices=array<vec2f,3>(vec2f(-1,-1),vec2f(3,-1),vec2f(-1,3));return vec4f(vertices[i],0,1);}\n" ++
  "fn pressed(x:u32,row:u32)->bool {" ++
  s!"for(var i=1u;i<=min(place[0].w,{maxPressRects}u);i++)\{let r=place[i];" ++
  "if(x>=r.x&&x<r.x+r.z&&row>=r.y&&row<r.y+r.w){return true;}}return false;}\n" ++
  "@fragment fn fragment(@builtin(position) pixel:vec4f)->@location(0) vec4f {" ++
  "let x=u32(pixel.x);let y=u32(pixel.y);let top=place[0].x;var c:vec4f;var source=y;" ++
  "if(y<top){c=textureLoad(chrome,vec2u(x,y),0);}" ++
  "else{let row=y-top+place[0].y;source=row+top;" ++
  "if(row>=place[0].z){c=vec4f(1.0);}else{c=textureLoad(page,vec2u(x,row),0);}}" ++
  s!"if(pressed(x,source))\{c=vec4f(c.rgb*{pressShade},c.a);}" ++
  "return c;}\n"

/-- The page layer of a band: the page moved up by `b.top`, with the glyphs within
`bandMargin` of the band. `extra` (the selection) is not filtered. -/
def pageLayer (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band) : Rendering.Scene :=
  let lift := Float.ofNat b.top
  let keep := nearNodes (lift-Float.ofNat bandMargin) (lift+Float.ofNat (b.height+bandMargin)) page.tree
  {page with
    height := b.height
    mapping := {page.mapping with viewportHeight := Float.ofNat b.height}
    tree := [.group none ⟨1,0,0,1,0,-lift⟩ (keep ++ extra)]
    links := Rendering.moveLinks (· - lift) page.links}

/-- The page layer keeps every link of the page, moved up by the band's top and nothing
else (`LinkTheorems.moveLinks_getElem`, `LinkTheorems.hitLink_band`; issue 1268). -/
theorem pageLayer_links (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band) :
    (pageLayer page extra b).links = Rendering.moveLinks (· - Float.ofNat b.top) page.links := rfl

/-- The chrome layer: window rows `0 .. WebShell.height`. -/
def chromeLayer (shell : WebShell.Shell) (page : Rendering.Scene) (width : Nat) : Rendering.Scene :=
  let top := max 1 (WebShell.height shell width)
  {page with
    height := top
    mapping := {page.mapping with viewportHeight := Float.ofNat top}
    tree := WebShell.nodes shell width
    glyphRuns := #[]
    links := #[]}

/-- The chrome top the band of a folding chrome is made for: the folded strip, the
smallest the chrome gets (`WebShell.strip_le_height`). -/
def bandTop (shell : WebShell.Shell) (width : Nat) : Nat :=
  WebShell.height {shell with collapse := 100} width

/-- The chrome layer alone, for a change of `collapse` (op `chromeLayer`): its scene is the
chrome's nodes, rows `0 .. top`. No layout and no page. -/
def chromeScene (shell : WebShell.Shell) (width : Nat) : Rendering.Scene :=
  let top := max 1 (WebShell.height shell width)
  {width,height := top,mapping := {viewportWidth := Float.ofNat width,viewportHeight := Float.ofNat top},
   tree := WebShell.nodes shell width}

/-- The blit of a page GPU canvas (docs/designissues/2026-11-08-page-gpu.md) into the page
layer: the canvas texture scaled to the canvas box `r` (x, y, width, height in layer
pixels), over white. The host draws it with the scissor `clip` of `canvasRects`. -/
def canvasBlitShader : String :=
  "@group(0) @binding(0) var src:texture_2d<f32>;\n" ++
  "@group(0) @binding(1) var<uniform> r:vec4f;\n" ++
  "@vertex fn vertex(@builtin(vertex_index) i:u32)->@builtin(position) vec4f {" ++
  "let v=array<vec2f,3>(vec2f(-1,-1),vec2f(3,-1),vec2f(-1,3));return vec4f(v[min(i,2u)],0,1);}\n" ++
  "@fragment fn fragment(@builtin(position) p:vec4f)->@location(0) vec4f {" ++
  "let size=vec2f(textureDimensions(src));let uv=(p.xy-r.xy)/max(r.zw,vec2f(1.0));" ++
  "let t=vec2u(clamp(uv*size,vec2f(0.0),size-vec2f(1.0)));let c=textureLoad(src,t,0);" ++
  "return vec4f(c.rgb*c.a+vec3f(1.0-c.a),1.0);}\n"

/-- The `canvas` elements of the page with their layout boxes (the largest box of each). -/
def canvasBoxes (dom : DOM.Dom) (boxes : Array Rendering.Layout.Box) : List Rendering.Layout.Box :=
  boxes.foldl (init := []) fun acc b =>
    if b.source < dom.size && (dom.get b.source).type == .element && (dom.get b.source).lname == "canvas" then
      match acc.find? (·.source == b.source) with
      | some a => if a.width * a.height ≥ b.width * b.height then acc else b :: acc.filter (·.source != b.source)
      | none => b :: acc
    else acc

/-- Each canvas box in the page layer of band `b`: its rectangle (layer pixels) and the
part of it inside the layer (`clip`), for the host's blit. Boxes outside are left out. -/
def canvasRects (cs : List Rendering.Layout.Box) (b : Band) (width : Nat) : JSON.Json :=
  let number := fun (n : Int) => JSON.Json.number (toString n)
  .array (cs.reverse.filterMap fun c =>
    let x := c.x.round.toInt64.toInt
    let y := c.y.round.toInt64.toInt - Int.ofNat b.top
    let w := c.width.round.toInt64.toInt
    let h := c.height.round.toInt64.toInt
    let x0 := max 0 x
    let y0 := max 0 y
    let x1 := min (Int.ofNat width) (x + w)
    let y1 := min (Int.ofNat b.height) (y + h)
    if w ≤ 0 || h ≤ 0 || x1 ≤ x0 || y1 ≤ y0 then none else
    some (.object [("node",number c.source),("rect",.array [number x,number y,number w,number h]),
      ("clip",.array [number x0,number y0,number (x1-x0),number (y1-y0)])]))

/-- A page layer answer that the engine keeps, with every input it was made from. -/
structure KeptPage where
  page : Rendering.Scene
  extra : List Rendering.Node
  band : Band
  boxes : Array Rendering.Layout.Box
  face : Option Rendering.FontProvider.Face
  live : Bool
  form : NativeSVG.DataForm
  checks : Bool
  tree : Bool
  answer : String × Array ByteArray

/-- Page layer answers kept: the last two, for a chrome change and back. -/
def keptPageSlots : Nat := 2

initialize keptPageRef : IO.Ref (List KeptPage) ← IO.mkRef []
/-- Page layers made, and page layers given again from `keptPageRef`. -/
initialize pageWorkRef : IO.Ref (Nat × Nat) ← IO.mkRef (0,0)

private def formSame : NativeSVG.DataForm → NativeSVG.DataForm → Bool
  | .decimal,.decimal => true
  | .base64,.base64 => true
  | .sections a,.sections b => a == b
  | .sectionsCpu a,.sectionsCpu b => a == b
  | _,_ => false

/- The kept answer is used only when the scene, the boxes, the face and the extra nodes
are the same objects as those it was made from (`ptrEq`; the entry holds them, so their
addresses are not used again while it is kept) and the band and flags are equal. So it is
the answer that `artifactWith` gives again for these inputs. -/
set_option compiler.extract_closed false in
private unsafe def pageArtifactImpl (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) (live : Bool)
    (form : NativeSVG.DataForm) (checks tree : Bool) : Except String (String × Array ByteArray) :=
  unsafeBaseIO do
    let same := fun (k : KeptPage) => ptrEq k.page page && ptrEq k.boxes boxes && ptrEq k.face face &&
      ptrEq k.extra extra && k.band == b && k.live == live && formSame k.form form && k.checks == checks && k.tree == tree
    let kept ← keptPageRef.get
    match kept.find? same with
    | some k =>
      pageWorkRef.modify fun (m,g) => (m,g+1)
      return .ok k.answer
    | none =>
      let made := WebRender.artifactWith (pageLayer page extra b) boxes face live form checks tree
      if let .ok answer := made then
        keptPageRef.set ((⟨page,extra,b,boxes,face,live,form,checks,tree,answer⟩ :: kept).take keptPageSlots)
        pageWorkRef.modify fun (m,g) => (m+1,g)
      return made

/-- The page layer of a layers answer. Its value is `artifactWith` of the band of the page;
the engine gives a kept answer again when the inputs are the same objects (a frame whose
only change is in the chrome: loading, the address, a pressed chrome control, the menu). -/
@[implemented_by pageArtifactImpl]
def pageArtifact (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) (live : Bool)
    (form : NativeSVG.DataForm) (checks tree : Bool) : Except String (String × Array ByteArray) :=
  WebRender.artifactWith (pageLayer page extra b) boxes face live form checks tree

theorem pageArtifact_eq (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) (live : Bool)
    (form : NativeSVG.DataForm) (checks tree : Bool) :
    pageArtifact page extra b boxes face live form checks tree =
      WebRender.artifactWith (pageLayer page extra b) boxes face live form checks tree := rfl

/-- The answer to a render with `layers:true`. -/
def layersJSON (shell : WebShell.Shell) (page : Rendering.Scene) (extra : List Rendering.Node)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face)
    (width height : Nat) (live : Bool) (form : NativeSVG.DataForm) (checks tree : Bool) (hoverRules : Bool := false)
    (canvases : List Rendering.Layout.Box := []) :
    Except String (String × Array ByteArray) := do
  let top := WebShell.height shell width
  -- A chrome that may fold: the band covers the view under the strip, the most it shows,
  -- so a change of `collapse` keeps the band and only the chrome layer is drawn again.
  let view := max 1 (height-(if shell.collapsible then bandTop shell width else top))
  let b := band shell.scroll view
  let (pageText,pageSections) ← pageArtifact page extra b boxes face live form checks tree
  let (chromeText,chromeSections) ←
    WebRender.artifactWith (chromeLayer shell page width) #[] face live form.next checks tree
  let number := fun (n : Nat) => JSON.Json.number (toString n)
  let place := JSON.Json.object ([("top",number top),("view",number view),("bandTop",number b.top),
    ("bandHeight",number b.height),("keepFrom",number b.keepFrom),("keepTo",number (b.keepTo view)),
    ("composite",.string compositeShader),("hoverRules",.bool hoverRules),
    ("scrollLimit",number (scrollLimit (WebPrint.contentHeight boxes) view))] ++
    (if canvases.isEmpty then [] else [("canvases",canvasRects canvases b width),("canvasBlit",.string canvasBlitShader)]))
  return ("{\"layers\":" ++ place.toString ++ ",\"page\":" ++ pageText ++ ",\"chrome\":" ++ chromeText ++ "}",
    pageSections ++ chromeSections)

/-- The fonts the engine holds between calls, so that a scroll does not read them
again. The first is the primary font; the others draw the characters it lacks, in
order (`SfntProfile.wordIn`). The memo holds words shaped with this list. -/
structure HeldFont where
  fonts : Array Rendering.SfntProfile.Font
  memo : Rendering.SfntProfile.Memo

/-- The family and SHA-256 of each held font, in order: the font part of `LayoutKey`. -/
def HeldFont.names (held : HeldFont) : List (String × String) :=
  held.fonts.toList.map fun f => (f.family,f.sha256)

initialize heldFontRef : IO.Ref (Option HeldFont) ← IO.mkRef none

-- Without this the read does not depend on its argument, so it would run once and be kept.
set_option compiler.extract_closed false in
private unsafe def heldFontImpl (_ : JSON.Json) : Option HeldFont := unsafeBaseIO heldFontRef.get
private unsafe def keepFontImpl (held : HeldFont) (_ : JSON.Json) : HeldFont :=
  unsafeBaseIO (do heldFontRef.set (some held); return held)
private unsafe def keepWordsImpl (words : Rendering.SfntProfile.Memo) (_ : JSON.Json) : Rendering.SfntProfile.Memo :=
  unsafeBaseIO (do heldFontRef.modify (·.map ({· with memo := words})); return words)
/-- These read and change the held font. The request argument keeps each call in place,
and each returns what it kept so that the caller uses the result and the call stays. -/
@[implemented_by heldFontImpl, noinline] private opaque heldFont (request : JSON.Json) : Option HeldFont
@[implemented_by keepFontImpl, noinline] private opaque keepFont (held : HeldFont) (_ : JSON.Json) : HeldFont := held
@[implemented_by keepWordsImpl, noinline] private opaque keepWords (words : Rendering.SfntProfile.Memo) (request : JSON.Json) : Rendering.SfntProfile.Memo

/-- Most fonts that the engine holds at once. -/
def maxHeldFonts : Nat := 64

/-- Read the bytes of a font file once. Later renders use it until another load
changes the list. With `fallback`, the font goes at the end of the held list (a font
with the same SHA-256 is not added twice); otherwise it replaces the list. Either
way the word memo starts again, as words may now draw differently. `request` only
keeps the call in place (see `keepFont`). -/
private def loadFontBytes (bytes : ByteArray) (family sha256 : String) (fallback : Bool) (request : JSON.Json) :
    Except String String := do
  let font ← Rendering.SfntProfile.Font.read bytes family sha256
  let fonts := match fallback,heldFont request with
    | true,some held => if held.fonts.any (·.sha256 == sha256) then held.fonts else held.fonts.push font
    | _,_ => #[font]
  if fonts.size > maxHeldFonts then throw "font file: more than 64 fonts held"
  let held := keepFont ⟨fonts,{}⟩ request
  return (JSON.Json.object [("family",.string font.family),("glyphs",.number (toString font.face.numGlyphs)),
    ("fonts",.number (toString held.fonts.size))]).toString

/-- The `fontLoad` op: the font file as Base64 in the JSON request. This is the text
reference path; `fontLoadBin` takes the same file as bytes. -/
private def loadFont (request : JSON.Json) : Except String String := do
  let some bytes := Rendering.SfntProfile.decodeBase64 (str request "fontBase64") | throw "font file: invalid base64"
  loadFontBytes bytes (str request "fontFamily" "font") (str request "fontSha256" "unnamed")
    (request.field? "fallback" == some (.bool true)) request

/-- `fontLoad` with the font file as bytes, with no Base64 and no JSON around it.
A host copies the file into engine memory, so a font is not limited by the call stack,
which holds string arguments in Wasm. `fallback` is 1 to add the font to the held
list, 0 to replace the list. The answer is the `fontLoad` answer. -/
@[export web_document_font_load_bin]
def fontLoadBin (bytes : ByteArray) (family sha256 : String) (fallback : UInt32) : String :=
  let request := JSON.Json.object [("op",.string "fontLoad"),("fontFamily",.string family),
    ("fontSha256",.string sha256),("fontBytes",.number (toString bytes.size)),("fallback",.bool (fallback != 0))]
  -- The guest module of page scripts comes the same way, as bytes (WebScripts).
  let loaded := if family == "guest:quickjs" || family == "guest:quickjs-aot" then WebScripts.loadModuleBytes family bytes request
    else loadFontBytes bytes family sha256 (fallback != 0) request
  match loaded with
  | .ok value => value | .error message => WebRender.errorJSON message

/-! ### Held images (issues 1268, 1274 and 1292)

The host sends each image once, by key (the URL that `inspect` gave) and SHA-256, with
`imageLoad` (Base64 in JSON) or `web_document_image_load_bin` (bytes). Lean holds it;
a render names the images in `heldImages`, `[{key,sha256}]`, so the bytes of a render
request do not grow with the images (`frame_work_test.ts` counts them). `imageInfo`
says that the engine has these ops: a host calls none of them before it asks. -/

/-- An image the engine holds: the key `inspect` gave, its SHA-256 as the host said,
and its bytes, opaque until `NativeImage.decode`. -/
structure HeldImage where
  key : String
  sha256 : String
  bytes : ByteArray

/-- Most images, and most bytes of images, that the engine holds; the oldest go first. -/
def maxHeldImages : Nat := 64
def maxHeldImageBytes : Nat := 33554432

initialize heldImagesRef : IO.Ref (List HeldImage) ← IO.mkRef []

set_option compiler.extract_closed false in
private unsafe def heldImagesImpl (_ : JSON.Json) : List HeldImage := unsafeBaseIO heldImagesRef.get
private unsafe def keepImagesImpl (images : List HeldImage) (_ : JSON.Json) : List HeldImage :=
  unsafeBaseIO (do heldImagesRef.set images; return images)
/-- These read and change the held images, as `heldFont` and `keepFont` do. -/
@[implemented_by heldImagesImpl, noinline] private opaque heldImages (request : JSON.Json) : List HeldImage
@[implemented_by keepImagesImpl, noinline] private opaque keepImages (images : List HeldImage) (request : JSON.Json) : List HeldImage := images

/-- Hold `bytes` as the image `key` with `sha256`, first; drop another image of the same
key, then the oldest past the limits. -/
private def loadImageBytes (bytes : ByteArray) (key sha256 : String) (request : JSON.Json) : Except String String := do
  if key.isEmpty || sha256.isEmpty then throw "image key and sha256 required"
  if bytes.size > maxHeldImageBytes then throw s!"image exceeds {maxHeldImageBytes} bytes"
  let others := (heldImages request).filter (·.key != key)
  let (kept,_) := others.foldl (fun (acc : List HeldImage × Nat) image =>
    if acc.1.length+1 < maxHeldImages && acc.2+image.bytes.size ≤ maxHeldImageBytes then (acc.1 ++ [image],acc.2+image.bytes.size)
    else acc) ([],bytes.size)
  let held := keepImages (⟨key,sha256,bytes⟩ :: kept) request
  let number := fun (n : Nat) => JSON.Json.number (toString n)
  return (JSON.Json.object [("key",.string key),("sha256",.string sha256),("bytes",number bytes.size),
    ("held",number held.length)]).toString

/-- `imageLoad`: the image as Base64 in the JSON request. -/
private def loadImage (request : JSON.Json) : Except String String := do
  let bytes ← NativeImage.base64 (str request "imageBase64").toUTF8 0
  loadImageBytes bytes (str request "key") (str request "sha256") request

/-- A page's bytes as its text (HTML §13.2.3 encoding sniffing, then the Encoding
Standard's decoder: `WHATWG.Encoding.Sniff.decodeDocumentFast`), given the transport
layer's `Content-Type` value or a bare charset label ("" for none). The answer is the
encoding's name, a line feed, then the text. The hosts call this where a page's bytes
become text, so a document declared in a legacy encoding is read in it and
`document.characterSet` is its name. -/
@[export web_document_decode_bin]
def decodeBin (bytes : ByteArray) (contentType : String) : String :=
  let label := if contentType.isEmpty then none
    else (L4Factoidal.WHATWG.Encoding.Sniff.extractFromMeta contentType).orElse fun _ =>
      if contentType.contains ';' || contentType.contains '/' then none else some contentType
  let (e, text) := L4Factoidal.WHATWG.Encoding.Sniff.decodeDocumentFast bytes label
  e.name ++ "\n" ++ text

/-- `imageLoad` with the image as bytes, with no Base64 and no JSON around it. -/
@[export web_document_image_load_bin]
def imageLoadBin (bytes : ByteArray) (key sha256 : String) : String :=
  let request := JSON.Json.object [("op",.string "imageLoad"),("key",.string key),("sha256",.string sha256),
    ("imageBytes",.number (toString bytes.size))]
  match loadImageBytes bytes key sha256 request with
  | .ok value => value | .error message => WebRender.errorJSON message

/-- The images a render names (`heldImages`), as key and SHA-256. -/
def namedImages (request : JSON.Json) : Except String (List (String × String)) := do
  let .array items := (request.field? "heldImages").getD (.array []) | throw "heldImages must be an array"
  if items.length > maxHeldImages then throw s!"heldImages exceed {maxHeldImages}"
  items.mapM fun item => do
    let some (.string key) := item.field? "key" | throw "held image key must be a string"
    let some (.string sha) := item.field? "sha256" | throw "held image sha256 must be a string"
    pure (key,sha)

/-- The named images that the engine holds: the image part of `LayoutKey`. A named
image that is not held is left out (the page shows its alt text), and the key says so. -/
def heldNamed (request : JSON.Json) (names : List (String × String)) : List (String × String) :=
  let held := heldImages request
  names.filter fun (key,sha) => held.any fun image => image.key == key && image.sha256 == sha

/-- The bytes of the held images of a key. -/
private def heldBytes (request : JSON.Json) (names : List (String × String)) : List (String × ByteArray) :=
  let held := heldImages request
  names.filterMap fun (key,sha) => (held.find? fun image => image.key == key && image.sha256 == sha).map (key,·.bytes)

/-- What Canvas 2D draws with (L4Factoidal.PageCanvas): the fonts the engine holds, the SVG
path parser (`new Path2D(d)`), and the held images by key, decoded by Lean when a page
draws one (the canvas keeps it decoded). -/
def canvasEnv (request : JSON.Json) : L4Factoidal.PageCanvas.Env :=
  { fonts := ((heldFont request).map (·.fonts)).getD #[],
    svgPath := fun d => (NativeSVGPath.parse NativeSVG.number d).toOption,
    image := fun key => ((heldImages request).find? (·.key == key)).bind fun img =>
      match NativeImage.decode img.bytes with
      | .ok b => some (L4Factoidal.PageCanvas.Bitmap.ofStraight b.width b.height b.rgba)
      | .error _ => none }

/-- The request fields that a render reads before its layout ends. `shell` gives only
the height of the chrome, which the key holds as `top`; `selection`, `live`, `binary`,
`checks`, `tree`, `op` and the scroll act after layout. `hover` and `active` are not
here: the pointer state is painted (`WebRepaint`), and is in the key, as `pointer`,
only for a frame whose pointer styles change geometry. -/
def layoutFields : List String := ["commands","resources","images","heldImages","url","fontData","textScalePercent","graphModel",
  "visited","media"]

/-- The request with only `layoutFields`, in that order. -/
def layoutRequest (request : JSON.Json) : JSON.Json :=
  .object (layoutFields.filterMap fun key => (request.field? key).map (key,·))

/-- Everything that a render reads before its layout ends. The held fonts are named by
family and SHA-256, all of them in order: `layOut` reads the fonts that `fontLoad`
holds, and only `fontLoad` changes them. A fallback font added after a render gives
a new key, so the kept layout of the old list is not used. -/
structure LayoutKey where
  html : String
  request : JSON.Json
  width : Nat
  height : Nat
  /-- Height of the browser chrome above the page. -/
  top : Nat
  /-- The held fonts by family and SHA-256, in order (`HeldFont.names`); empty when
  none is held. The layout depends on every one of them, not only the first. -/
  fonts : List (String × String)
  /-- The held images that `heldImages` names and the engine holds, by key and SHA-256. -/
  held : List (String × String) := []
  /-- The hover and active nodes, for a layout with them (a pointer style that changes
  geometry); `(none,none)` for the layout that every pointer state is painted on. -/
  pointer : Option Nat × Option Nat := (none,none)
  deriving DecidableEq

/-- A laid-out document: the scene before the window, the selection and the chrome. -/
structure Laid where
  scene : Rendering.Scene
  boxes : Array Rendering.Layout.Box
  face : Option Rendering.FontProvider.Face
  /-- An author rule names `:hover`: a pointer move over the page can change the frame. -/
  hoverRules : Bool := false
  /-- What a pointer state is painted with (`restyle`): the document, its rules, the
  text scale, the element state of the layout, and its computed styles, made at the
  first repaint and kept. -/
  dom : DOM.Dom := default
  rules : List Rendering.CSS.Rule := []
  textScale : Float := 1
  state : Rendering.CSS.ElementState := {}
  styles : Thunk (Except String (Array Rendering.CSS.Computed)) := Thunk.pure (.ok #[])

/-- The element state of a request (Selectors 4 §9): `hover` and `active` are node ids
of the page (a link's `sourceNode`); `visited` lists URLs of the session history. A
hyperlink is visited when its `href`, resolved against the document base URL, is one
of them. An id outside the document is no element. -/
def elementState (dom : DOM.Dom) (base : String) (request : JSON.Json) : Except String Rendering.CSS.ElementState := do
  let node := fun (key : String) => match request.field? key with
    | some (.number n) => n.toNat?.bind fun id => if id < dom.size then some id else none
    | _ => none
  let urls ← match request.field? "visited" with
    | none => pure []
    | some (.array items) => items.mapM fun | .string u => pure u | _ => throw "visited entries must be URLs"
    | some _ => throw "visited must be an array"
  if urls.length > WebHistory.maxEntries then throw "visited exceeds the history bound"
  let visited := if urls.isEmpty then [] else (dom.treeOrder 0).toList.filter fun id =>
    let n := dom.get id
    Rendering.CSS.isHyperlink n && urls.contains (Syntax.resolveIri base (attr n "href"))
  return {hover := node "hover", active := node "active", visited}

/-- The hover and active nodes a request names. -/
def requestPointer (request : JSON.Json) : Option Nat × Option Nat :=
  let node := fun (key : String) => match request.field? key with
    | some (.number n) => n.toNat?
    | _ => none
  (node "hover",node "active")

/-- A pointer state on the element state of the document: an id outside it is no element. -/
def withPointer (dom : DOM.Dom) (state : Rendering.CSS.ElementState) (pointer : Option Nat × Option Nat) :
    Rendering.CSS.ElementState :=
  let inside := fun (id : Option Nat) => id.bind fun n => if n < dom.size then some n else none
  {state with hover := inside pointer.1, active := inside pointer.2}

/-- `layOut` after the parse: the layout of the arena `dom`, `width` by `rows` CSS pixels.
A script session's layout reads (`measure`) lay its arena out here, with no parse. -/
def layOutDOM (request : JSON.Json) (graph : Option NativeFoafNaut.Model) (dom : DOM.Dom) (width rows : Nat)
    (held : List (String × String)) (pointer : Option Nat × Option Nat) : Except String Laid := do
  validateResources dom request
  let _ ← classicScripts (WebRenderScript.scriptRecords dom)
  let textScale := Float.ofNat (← scalePercent request) / 100
  let rules ← rules dom request
  if width == 0 || rows == 0 || width > 4096 || rows > 4096 then throw "unsupported document viewport"
  let fontData := str request "fontData"
  if !fontData.isEmpty then
    let _ ← WebRenderFontRequests.collectDOMWithRules dom rules textScale
  let face ← if fontData.isEmpty then pure none else
    some <$> Rendering.FontProvider.Face.decode fontData
  -- A font loaded by the fontLoad op: Lean shapes the words and takes the outlines.
  let loaded := heldFont request
  let memo := loaded.map fun held => Rendering.SfntProfile.remember held.fonts held.memo (Rendering.SfntProfile.wordsOf dom)
  let font ← match loaded,memo with
    | some held,some words =>
      Rendering.SfntProfile.profile held.fonts (keepWords words request)
    | _,_ => pure (match face with | some f => Rendering.Layout.FontProfile.ofFace f | none => WebRender.asciiFont)
  let url := baseURL dom (str request "url")
  -- SVG text is drawn with the fonts of the HTML text.
  let svgFonts := (loaded.map (·.fonts)).getD #[]
  let images := (← suppliedImages request) ++ heldBytes request held
  let (embedding,pictures) ← match graph with
    | some m => pure (WebGraph.embedding m,Rendering.Layout.noPictures)
    | none => WebRender.makeReplaced dom (if url.isEmpty then none else some url) images svgFonts
  -- A window shorter than the chrome still lays out, on one row.
  let state := withPointer dom (← elementState dom url request) pointer
  let (scene,boxes) ← Rendering.Layout.render dom rules font embedding width rows textScale state pictures
  let hoverRules := rules.any fun rule => rule.selectors.any fun sel => sel.parts.any (·.pseudo.contains .hover)
  let laid : Laid := {scene := scene,boxes := boxes,face := face,hoverRules := hoverRules}
  return {laid with dom := dom}
    |> fun l => {l with rules := rules}
    |> fun l => {l with textScale := textScale}
    |> fun l => {l with state := state}
    |> fun l => {l with styles := Thunk.mk fun _ => Rendering.CSS.computeAll dom rules textScale state}

/-- Parse, script check, cascade and layout of a render. It reads only the key: the
request it reads is `key.request`, which has only `layoutFields`. With `graphModel`
(the FOAF graph page) the document is `WebGraph.skeleton` of the model, not `key.html`,
and the picture comes from the model with no SVG text (`WebGraph.embedding`). -/
def layOut (key : LayoutKey) : Except String Laid := do
  let request := key.request
  let graph ← match request.field? "graphModel" with
    | none => pure none
    | some (.string wire) => match NativeFoafNaut.Model.decode wire with
      | some m => pure (some m)
      | none => throw "invalid FOAF graph model"
    | some _ => throw "graphModel must be a string"
  let dom ← prepareDOM (match graph with | some m => WebGraph.skeleton m | none => key.html) request
  if key.width == 0 || key.height == 0 || key.width > 4096 || key.height > 4096 then throw "unsupported document viewport"
  layOutDOM request graph dom key.width (max 1 (key.height-key.top)) key.held key.pointer

/-! ### Layout reads of page scripts

A script that reads a size (`clientWidth`, `getBoundingClientRect`, `getBBox`) gets it
from this engine's layout of its arena as it stands (`WasmVM.Hosts.Page.Reads`): laid out
when a read first asks, once until the DOM or the viewport changes, as a browser forces
a layout. The layout is that of a render with the session's `layout` request. -/

/-- The answer of a layout read: op 17 "x y w h left top width height" (the border box
in the page, then the client box: inside the borders; zero for an SVG element inside an
`svg`, which has no CSS box, CSSOM View §6); op 18 an SVG element's bounding box in its
user space, "x y w h" (`WebHit.boundsOf`). -/
def readAnswer (l : Laid) (node op : Nat) : Option String :=
  let line := fun (xs : List Float) => " ".intercalate (xs.map Rendering.FloatFormat.format)
  let box := l.boxes.foldl (init := (none : Option WebHit.Bounds)) fun acc b =>
    if b.source != node then acc else
    let r : WebHit.Bounds := (b.x,b.y,b.x+b.width,b.y+b.height)
    some ((acc.map (·.union r)).getD r)
  match op with
  | 17 =>
    match box with
    | some (x0,y0,x1,y1) =>
      let e : Rendering.CSS.Edges := match l.styles.get with
        | .ok styles => (styles[node]?.map (·.borderEdges)).getD {}
        | .error _ => {}
      some (line [x0,y0,x1-x0,y1-y0,e.left,e.top,max 0 (x1-x0-e.left-e.right),max 0 (y1-y0-e.top-e.bottom)])
    | none => match (WebHit.boundsOf l.dom l.scene node).1 with
      | some (x0,y0,x1,y1) => some (line [x0,y0,x1-x0,y1-y0,0,0,0,0])
      | none => some "0 0 0 0 0 0 0 0"
  | 18 => match (WebHit.boundsOf l.dom l.scene node).2 with
    | some (x0,y0,x1,y1) => some (line [x0,y0,x1-x0,y1-y0])
    | none => some "0 0 0 0"
  -- 21: the used width and height of the node's content box (CSSOM §9.1 resolved values
  -- of `width` and `height`), "" when the node has no box
  | 21 => match box, l.styles.get with
    | some (x0,y0,x1,y1), .ok styles =>
      let s := styles[node]?.getD {}
      let b := s.borderEdges
      some (line [max 0 (x1-x0-b.left-b.right-s.padding.left-s.padding.right),
                  max 0 (y1-y0-b.top-b.bottom-s.padding.top-s.padding.bottom)])
    | _, _ => some ""
  | _ => none

/-- The layout reads of a script session (`Page.Measure`) with the render request
`request` (its `layoutFields`): the arena laid out `width` by `height` (`layOutDOM`)
when a read first asks, then the answers from that one layout. -/
def measure (request : JSON.Json) : WasmVM.Hosts.Page.Measure := fun dom width height =>
  let request := layoutRequest request
  let held := heldNamed request ((namedImages request).toOption.getD [])
  let laid : Thunk (Except String Laid) := Thunk.mk fun _ => layOutDOM request none dom width height held (none,none)
  -- `getComputedStyle` (op 20) reads the cascade alone: no layout for it
  let styled : Thunk (Except String (Array Rendering.CSS.Computed)) := Thunk.mk fun _ => do
    let textScale := Float.ofNat (← scalePercent request) / 100
    let rules ← rules dom request
    let state := withPointer dom (← elementState dom (baseURL dom (str request "url")) request) (none,none)
    Rendering.CSS.computeAll dom rules textScale state
  fun node op => if op == 20 || op ≥ 200 then
      match styled.get with
      -- CSSOM §9 getComputedStyle: an element that is not connected to the page's
      -- document has no computed style (the declaration is empty)
      | .ok styles => if node < dom.size && (dom.get node).type == .element && dom.root node == 0 then
          let c := styles[node]?.getD {}
          some (if op == 20 then Rendering.ComputedValues.text c
            else (((Rendering.ComputedValues.values c)[op - 200]?).map (·.2)).getD "")
        else some ""
      | .error _ => none
    else match laid.get with
    | .ok l => readAnswer l node op
    | .error _ => none

/-! ### The layouts of the last keys, kept

A scroll, a selection or a pointer move sends the same document, width, height,
chrome height, text scale and font again. `run` then takes a kept layout and does
not parse, cascade or lay out again. The engine keeps the layouts of its last
`FrameCost.layoutSlots` keys (four) of one document in a `FrameCost.Lru` (a layout of
another document drops them, so memory holds one page's layouts), the memo that the frame cost
model keeps with its values left out, so that a hover on and off, or a zoom step and
back, lays out once (`FrameCost.layout_once_per_distinct_key`). `lookupLayout` states
what `run` does with the memo, and `lookupLayout_eq` shows the answer is `layOut key`
for any memo so made (`FrameCost.Lru.lookup_eq`). -/

open L4Factoidal.FrameCost

/-- A memo is valid when each value is the layout of its key. `keepLayout` makes only
such entries. -/
def ValidEntry (memo : Lru LayoutKey Laid) : Prop := Lru.Valid layOut memo

def lookupLayout (memo : Lru LayoutKey Laid) (key : LayoutKey) : Except String Laid :=
  Lru.lookup layOut memo key

theorem lookupLayout_eq (memo : Lru LayoutKey Laid) (valid : ValidEntry memo) (key : LayoutKey) :
    lookupLayout memo key = layOut key :=
  Lru.lookup_eq layOut memo valid key

/-- The memo that a render leaves is valid. -/
theorem stored_valid (memo : Lru LayoutKey Laid) (valid : ValidEntry memo) (key : LayoutKey) (laid : Laid)
    (made : layOut key = .ok laid) : ValidEntry (Lru.putIn LayoutKey.html layoutSlots memo key laid) :=
  Lru.putIn_valid LayoutKey.html layOut layoutSlots memo valid key laid made

/-- The frame cost model's cache hit is this memo's: leaving out the values keeps
`find?`'s answer and commutes with the scoped put (`FrameCost.Session.kept` is
`Lru.erase` of it, scoped by page as this memo is by document). -/
theorem model_hit (memo : Lru LayoutKey Laid) (key : LayoutKey) :
    (Lru.find? (Lru.erase memo) key).isSome = (Lru.find? memo key).isSome :=
  Lru.find?_erase memo key
theorem model_put (memo : Lru LayoutKey Laid) (key : LayoutKey) (laid : Laid) :
    Lru.erase (Lru.putIn LayoutKey.html layoutSlots memo key laid) = Lru.putIn LayoutKey.html layoutSlots (Lru.erase memo) key () :=
  Lru.erase_putIn LayoutKey.html layoutSlots memo key laid

/-! The layout key leaves the scroll and the pointer out (`FrameCost.apply_scroll_key`,
`FrameCost.apply_hover_key` state the same of the model's key). -/

/-- Neither the shell, which holds the scroll, nor the hover and active nodes are
fields of the layout request. -/
theorem pointer_not_layout_field : "shell" ∉ layoutFields ∧ "hover" ∉ layoutFields ∧ "active" ∉ layoutFields := by
  decide

/-- Two requests that agree on the layout fields have the same layout request: a request
that differs only in its shell (and so its scroll), hover or active has the same key. -/
theorem layoutRequest_congr (a b : JSON.Json) (agree : ∀ k ∈ layoutFields, a.field? k = b.field? k) :
    layoutRequest a = layoutRequest b := by
  have same : ∀ l : List String, (∀ k ∈ l, a.field? k = b.field? k) →
      l.filterMap (fun key => (a.field? key).map (key,·)) = l.filterMap (fun key => (b.field? key).map (key,·)) := by
    intro l h
    induction l with
    | nil => rfl
    | cons k r ih =>
      simp only [List.filterMap_cons,h k (List.mem_cons_self ..),ih (fun x m => h x (List.mem_cons_of_mem _ m))]
  unfold layoutRequest
  rw [same _ agree]

/-- The chrome height that the layout key holds: the full chrome, whatever its fold. -/
def layoutTop (shell : Option WebShell.Shell) (width : Nat) : Nat :=
  (shell.map (fun value => WebShell.fullHeight value width)).getD 0

/-- A folding step makes no layout (owner, 2026-11-08): the key's chrome height does not
read `collapse` (nor the scroll), and `layoutRequest_congr` says the shell is no layout
field, so two requests that differ only in their shell's fold have the same key. -/
theorem layoutTop_collapse (shell : WebShell.Shell) (collapse scroll width : Nat) :
    layoutTop (some {shell with collapse,scroll}) width = layoutTop (some shell) width := rfl

/-- With the classic UI (`collapse = 0`) the key holds the chrome on screen, as before. -/
theorem layoutTop_classic (shell : WebShell.Shell) (width : Nat) (classic : shell.collapse = 0) :
    layoutTop (some shell) width = WebShell.height shell width :=
  (WebShell.height_classic shell width classic).symm

/-- The chrome height, which the key holds as `top`, does not read the scroll. -/
theorem shell_height_scroll (shell : WebShell.Shell) (scroll width : Nat) :
    WebShell.height {shell with scroll} width = WebShell.height shell width := rfl

/-- Frame work the engine did since it started (or since `frameWork` with `reset`):
layouts, kept layouts used, and pointer states painted on a kept layout. -/
initialize frameWorkRef : IO.Ref (Nat × Nat × Nat) ← IO.mkRef (0,0,0)

initialize layoutRef : IO.Ref (Lru LayoutKey Laid) ← IO.mkRef []

/-- Pointer states painted on a kept layout (`:hover`, `:active`), kept apart from the
layouts so that they do not push a layout out: a press, a hover and a loading frame under
the pointer then give the same layout object again, and the page layer that
`pageArtifact` keeps for it. -/
def paintedSlots : Nat := 2
initialize paintedRef : IO.Ref (Lru LayoutKey Laid) ← IO.mkRef []

set_option compiler.extract_closed false in
private unsafe def keptLayoutImpl (key : LayoutKey) : Option Laid :=
  unsafeBaseIO do
    let memo ← layoutRef.get
    match Lru.find? memo key with
    | some laid =>
      layoutRef.set (Lru.putIn LayoutKey.html layoutSlots memo key laid)
      frameWorkRef.modify fun (l,k,r) => (l,k+1,r)
      return some laid
    | none => return none
private unsafe def keepLayoutImpl (key : LayoutKey) (laid : Laid) : Laid :=
  unsafeBaseIO do
    layoutRef.modify (Lru.putIn LayoutKey.html layoutSlots · key laid)
    frameWorkRef.modify fun (l,k,r) => (l+1,k,r)
    return laid
private unsafe def countRepaintImpl (laid : Laid) : Laid :=
  unsafeBaseIO (do frameWorkRef.modify (fun (l,k,r) => (l,k,r+1)); return laid)
set_option compiler.extract_closed false in
private unsafe def frameWorkImpl (reset : Bool) : Nat × Nat × Nat :=
  unsafeBaseIO do
    let work ← frameWorkRef.get
    if reset then frameWorkRef.set (0,0,0)
    return work
/-- These read and change the memo (a hit moves its entry first, as `Lru.put`), and
count the work, as `heldFont` and `keepFont` do for the font. -/
@[implemented_by keptLayoutImpl, noinline] private opaque keptLayout (key : LayoutKey) : Option Laid
@[implemented_by keepLayoutImpl, noinline] private opaque keepLayout (key : LayoutKey) (laid : Laid) : Laid := laid
@[implemented_by countRepaintImpl, noinline] private opaque countRepaint (laid : Laid) : Laid := laid
@[implemented_by frameWorkImpl, noinline] private opaque frameWork (reset : Bool) : Nat × Nat × Nat
set_option compiler.extract_closed false in
private unsafe def pageWorkImpl (reset : Bool) : Nat × Nat :=
  unsafeBaseIO do
    let work ← pageWorkRef.get
    if reset then pageWorkRef.set (0,0)
    return work
/-- Page layers made and page layers kept (`pageArtifact`), as `frameWork` counts layouts. -/
@[implemented_by pageWorkImpl, noinline] private opaque pageWork (reset : Bool) : Nat × Nat

/-- `lookupLayout` over the kept memo. -/
private def cachedLayOut (key : LayoutKey) : Except String Laid :=
  match keptLayout key with
  | some laid => .ok laid
  | none => keepLayout key <$> layOut key

/-- The pointer state of `pointer` painted on a layout with none (`WebRepaint`): the
layout with the new colours, or none when a style of that state changes geometry. -/
def restyle (base : Laid) (pointer : Option Nat × Option Nat) : Option Laid := do
  let .ok old := base.styles.get | none
  let .ok new := Rendering.CSS.computeAll base.dom base.rules base.textScale (withPointer base.dom base.state pointer) | none
  let scene ← WebRepaint.recolor base.dom old new base.scene
  return {base with scene,state := withPointer base.dom base.state pointer,styles := Thunk.pure (.ok new)}

/-- The layout of a frame from a source of layouts: with no pointer state, the layout of
the key; with one, the layout with no pointer state, restyled, or, when a style of the
state changes geometry (or that layout fails), the layout of the key with the pointer in it. -/
def frameWith (laidOut : LayoutKey → Except String Laid) (key : LayoutKey) (painted : Laid → Laid := id) :
    Except String Laid :=
  if key.pointer == (none,none) then laidOut key else
  match laidOut {key with pointer := (none,none)} with
  | .ok base =>
    match restyle base key.pointer with
    | some laid => .ok (painted laid)
    | none => laidOut key
  | .error _ => laidOut key

/-- What `WebDocumentTests.lean` checks on pages with pointer styles: a restyled layout
is the layout with the pointer state. -/
def RestyleSound : Prop :=
  ∀ key base laid, layOut {key with pointer := (none,none)} = .ok base → restyle base key.pointer = some laid →
    layOut key = .ok laid

/-- With a valid memo and a sound restyle, a frame is the layout of its key: the cost
cut (no layout for a colour-only hover) gives the picture of the expensive path. The
engine passes `countRepaint` as `painted`, which counts and gives back its argument,
as `keepLayout` does for `lookupLayout`. -/
theorem frameWith_eq (memo : Lru LayoutKey Laid) (valid : ValidEntry memo) (sound : RestyleSound) (key : LayoutKey) :
    frameWith (lookupLayout memo) key = layOut key := by
  unfold frameWith
  simp only [lookupLayout_eq memo valid]
  split
  · rfl
  · cases hb : layOut {key with pointer := (none,none)} with
    | error e => rfl
    | ok base =>
      simp only
      cases hr : restyle base key.pointer with
      | none => rfl
      | some laid => exact (sound key base laid hb hr).symm

set_option compiler.extract_closed false in
private unsafe def keptPaintedImpl (key : LayoutKey) : Option Laid :=
  unsafeBaseIO do
    match Lru.find? (← paintedRef.get) key with
    | some laid =>
      paintedRef.modify (Lru.putIn LayoutKey.html paintedSlots · key laid)
      frameWorkRef.modify fun (l,k,r) => (l,k+1,r)
      return some laid
    | none => return none
private unsafe def keepPaintedImpl (key : LayoutKey) (laid : Laid) : Laid :=
  unsafeBaseIO do
    paintedRef.modify (Lru.putIn LayoutKey.html paintedSlots · key laid)
    return laid
/-- A frame with a pointer state that the engine painted before, and keeping one. The
entries are values of `frameWith cachedLayOut` for their keys. -/
@[implemented_by keptPaintedImpl, noinline] private opaque keptPainted (key : LayoutKey) : Option Laid
@[implemented_by keepPaintedImpl, noinline] private opaque keepPainted (key : LayoutKey) (laid : Laid) : Laid := laid

/-- `frameWith` over the kept memo: what a render uses. A key with a pointer state is
looked up in the painted memo first. -/
private def cachedFrame (key : LayoutKey) : Except String Laid :=
  if key.pointer == (none,none) then frameWith cachedLayOut key countRepaint else
  match keptPainted key with
  | some laid => .ok laid
  | none => keepPainted key <$> frameWith cachedLayOut key countRepaint

/-- `cpu:true`: each scene of a bytes answer also carries its CPU pixels. -/
private def cpuPixels (request : JSON.Json) : Bool := request.field? "cpu" == some (.bool true)

/-- A document request, with `laidOut` as the layout of a render. `run` passes the
kept layout; `runUncached` passes `layOut`, so that tests compare the two. With
`bytes`, a render answer names its storage floats and tile words as sections
(`DataForm.sections`) and gives their bytes; other answers have no section. -/
def answerWith (laidOut : LayoutKey → Except String Laid) (bytes : Bool) (html : String) (request : JSON.Json)
    (width height : Nat) : Except String (String × Array ByteArray) := do
  let .object fields := request | throw "document request must be an object"
  if (fields.map Prod.fst).eraseDups.length != fields.length then throw "duplicate document request field"
  if str request "op" == "fontLoad" then return (← loadFont request,#[])
  if str request "op" == "imageLoad" then return (← loadImage request,#[])
  -- The ops of held images and frame work: a host asks this before it calls them (issue 1274).
  if str request "op" == "imageInfo" then
    let number := fun (n : Nat) => JSON.Json.number (toString n)
    return ((JSON.Json.object [("engine",.string "heldImages"),
      ("ops",.array (["imageLoad","imageLoadBin","imageDrop","frameWork"].map .string)),
      ("maxImages",number maxHeldImages),("maxBytes",number maxHeldImageBytes),
      ("held",number (heldImages request).length),("layoutSlots",number layoutSlots)]).toString,#[])
  -- The folding chrome (owner, 2026-11-08). A host asks `shellInfo` before it sends a shell
  -- with `collapse` or calls `chromeLayer`: an older engine answers "unknown document
  -- operation" and the host keeps the classic chrome (issue 1274). `full` and `strip` are
  -- the chrome's rows unfolded and folded, for the `width` and `shell` of the request.
  -- The CPU raster (docs/designissues/2026-11-08-cpu-render-backend.md): a host with no
  -- GPU asks this once. An engine without it answers "unknown document operation", and
  -- such a host shows no page. With `cpu:true` on a bytes call, each scene of the answer
  -- also names `pixelsSection`: its RGBA bytes, row by row, drawn by `SVGRaster`.
  if str request "op" == "cpuInfo" then
    return ((JSON.Json.object [("engine",.string "cpu"),("pixels",.string "rgba8"),
      ("ops",.array ([.string "render",.string "chromeLayer"]))]).toString,#[])
  if str request "op" == "shellInfo" then
    let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
    let w := natField request "width"
    let number := fun (n : Nat) => JSON.Json.number (toString n)
    return ((JSON.Json.object [("collapse",.bool true),("ops",.array [.string "chromeLayer"]),
      ("full",number (WebShell.fullHeight shell w)),("strip",number (bandTop shell w))]).toString,#[])
  -- The chrome layer alone at the shell's fold, `width` wide: no layout, no page band.
  if str request "op" == "chromeLayer" then
    let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
    let live := request.field? "live" == some (.bool true)
    let form : NativeSVG.DataForm := if bytes then (if cpuPixels request then .sectionsCpu 0 else .sections 0)
      else if request.field? "binary" == some (.bool true) then .base64 else .decimal
    let checks := request.field? "checks" != some (.bool false)
    let scene := chromeScene shell width
    let (text,sections) ← WebRender.artifactWith scene #[] none live form checks false
    return ("{\"top\":" ++ toString scene.height ++ ",\"chrome\":" ++ text ++ "}",sections)
  if str request "op" == "imageDrop" then
    let held := keepImages [] request
    return ((JSON.Json.object [("held",.number (toString held.length))]).toString,#[])
  -- Layouts done, kept layouts used and pointer states painted with no layout.
  if str request "op" == "frameWork" then
    let reset := request.field? "reset" == some (.bool true)
    let (layouts,kept,repaints) := frameWork reset
    let (pagesMade,pagesKept) := pageWork reset
    let number := fun (n : Nat) => JSON.Json.number (toString n)
    return ((JSON.Json.object [("layouts",number layouts),("kept",number kept),("repaints",number repaints),
      ("layoutSlots",number layoutSlots),("pagesMade",number pagesMade),("pagesKept",number pagesKept)]).toString,#[])
  if str request "op" == "xmlStylesheet" then
    let url := match ← WebXslt.stylesheetHref html with
      | some href => JSON.Json.string (Syntax.resolveIri (str request "url") href)
      | none => .null
    return ((JSON.Json.object [("url",url)]).toString,#[])
  if str request "op" == "xslt" then
    let (source,engine) ← WebXslt.transform html (str request "stylesheet") (str request "url") (str request "stylesheetURL")
    return ((JSON.Json.object [("source",.string source),("engine",.string engine)]).toString,#[])
  if let some answer ← inputOp (str request "op" "render") request then return (answer,#[])
  -- Page scripts run by Lean: QuickJS in WasmVM on the page's arena (WebScripts).
  if let some answer ← WebScripts.opSections (str request "op" "render") html request (fun r => some (measure r))
      (fun _ => canvasEnv request) then return answer
  let op := str request "op" "render"
  if op != "render" && op != "selectedText" && op != "printLayout" && op != "nodeAt" then
    let dom ← prepareDOM html request
    validateResources dom request
    let _ ← classicScripts (WebRenderScript.scriptRecords dom)
    if op == "inspect" then return ((← inspect dom (str request "url")).toString,#[])
    let textScale := Float.ofNat (← scalePercent request) / 100
    let rules ← rules dom request
    if op == "droppedCSS" then
      return ((JSON.Json.object [("dropped",.array ((Rendering.CSS.droppedDeclarations dom rules).toList.map .string))]).toString,#[])
    if op == "fontRequests" then
      return (WebRenderFontRequests.requestsJSON (← WebRenderFontRequests.collectDOMWithRules dom rules textScale),#[])
    throw "unknown document operation"
  let shell := (request.field? "shell").map WebShell.Shell.ofJson
  -- `top` is the chrome on screen; the layout reads the full chrome (`layoutTop`), so a
  -- folding chrome lays nothing out again.
  let top := (shell.map (fun value => WebShell.height value width)).getD 0
  let fonts := ((heldFont request).map HeldFont.names).getD []
  let key : LayoutKey := ⟨html,layoutRequest request,width,height,layoutTop shell width,fonts,
    heldNamed request (← namedImages request),requestPointer request⟩
  let laid ← laidOut key
  let scene := laid.scene
  let boxes := laid.boxes
  let face := laid.face
  -- Printing (issue 1268): the host lays the document out at the paper width, with
  -- `media:"print"`, and `height` the rows of one page. The answer is the pages.
  if op == "printLayout" then
    let dom ← prepareDOM html request
    let sheet ← rules dom request
    let styles ← Rendering.CSS.computeAll dom sheet
    let content := WebPrint.contentHeight boxes
    let pages := WebPrint.paginate (WebPrint.pieces dom sheet styles boxes) content height
    let number := fun (n : Nat) => JSON.Json.number (toString n)
    return ((JSON.Json.object [("contentHeight",number content),
      ("pages",.array (pages.map fun (top,rows) => .array [number top,number rows]))]).toString,#[])
  -- Pointer positions are in window coordinates; the page starts below the chrome.
  let moved := Float.ofNat top-Float.ofNat ((shell.map (·.scroll)).getD 0)
  let chosen := (← selection request).map (fun value => WebSelection.shift value moved)
  -- The node under a window point (`x`, `y`), for the pointer events that page scripts
  -- receive: the smallest layout box that holds the point, in page rows (`y` below the
  -- chrome, plus the scroll), and inside an embedded `svg` the shape under the point
  -- (WebHit). The answer has the event's coordinates. Lean's DOM, not the host, then
  -- dispatches the events (WebScripts).
  if op == "nodeAt" then
    return ((WebHit.nodeAtAnswer laid.dom scene boxes (Float.ofNat (natField request "x"))
      (Float.ofNat (natField request "y")) (Float.ofNat top) (Float.ofNat ((shell.map (·.scroll)).getD 0))).toString,#[])
  let items := WebSelection.cells scene.glyphRuns
  if op == "selectedText" then
    return ((JSON.Json.object [("text",.string (match chosen with
      | some value => WebSelection.text items value
      | none => ""))]).toString,#[])
  let marks := match chosen with
    | some value => WebSelection.highlight items value
    | none => []
  let live := request.field? "live" == some (.bool true)
  let binary := request.field? "binary" == some (.bool true)
  let form : NativeSVG.DataForm :=
    if bytes then (if cpuPixels request then .sectionsCpu 0 else .sections 0) else if binary then .base64 else .decimal
  let checks := request.field? "checks" != some (.bool false)
  -- The inspector tree only when the request asks (`tree:true`); no frame host reads it.
  let tree := request.field? "tree" == some (.bool true)
  -- One printed page: the rows `top .. top+rows` of the document at the top of the
  -- image, and white below them. No chrome and no selection.
  if let some (.array [.number rawTop,.number rawRows]) := request.field? "printPage" then
    let top := rawTop.toNat?.getD 0
    let rows := min height (rawRows.toNat?.getD height)
    let page := pageLayer scene [] ⟨top,height⟩
    let page := {page with tree := page.tree ++ (if rows < height then [WebPrint.cover width rows (height-rows)] else [])}
    return ← WebRender.artifactWith page boxes face live form checks tree
  if let some value := shell then
    if request.field? "layers" == some (.bool true) then
      return ← layersJSON value scene marks boxes face width height live form checks tree laid.hoverRules
        (canvasBoxes laid.dom boxes)
  let scrolled := Float.ofNat ((shell.map (·.scroll)).getD 0)
  let near := nearNodes (scrolled-512) (scrolled+Float.ofNat height+512) scene.tree
  let page := {scene with tree := near ++ marks}
  WebRender.artifactWith (match shell with
    | some value => WebShell.compose value page width height
    | none => page) boxes face live form checks tree

/-- The JSON text answer: storage floats in Base64 (`binary:true`) or decimal. -/
def runWith (laidOut : LayoutKey → Except String Laid) (html : String) (request : JSON.Json) (width height : Nat) :
    Except String String :=
  Prod.fst <$> answerWith laidOut false html request width height

def run := runWith cachedFrame
def runUncached := runWith layOut

/-- The request text as JSON, with the bounds of `compile`. -/
private def parseRequest (request : String) : Except String JSON.Json :=
  if request.utf8ByteSize > 20971520 then .error "document request exceeds20MiB"
  else match JSON.parseJsonText request with
  | .error _ => .error "invalid document request JSON"
  | .ok (j,pos) =>
    if !(request.toList.drop pos).all Char.isWhitespace then .error "trailing document request data"
    else .ok j

@[inline] private def pushU32 (bytes : ByteArray) (n : Nat) : ByteArray :=
  let w := n.toUInt32
  bytes.push w.toUInt8 |>.push (w >>> 8).toUInt8 |>.push (w >>> 16).toUInt8 |>.push (w >>> 24).toUInt8

/-- The bytes of an answer with sections. Each count is uint32 little-endian: the
total length, the head length `h`, the section count `n`, the length of each section;
then the head (UTF-8 JSON, with spaces to a multiple of 4 bytes, so `h` is that
multiple); then each section, with zero bytes to a multiple of 4. Every section
starts at a multiple of 4 bytes, so the host can view it as 32-bit words. -/
def packAnswer (head : String) (sections : Array ByteArray) : ByteArray := Id.run do
  let pad := fun (n : Nat) => (4 - n % 4) % 4
  let headBytes := head.toUTF8
  let headSize := headBytes.size + pad headBytes.size
  let total := 12 + 4*sections.size + headSize + sections.foldl (fun t s => t + s.size + pad s.size) 0
  let mut out := ByteArray.emptyWithCapacity total
  out := pushU32 (pushU32 (pushU32 out total) headSize) sections.size
  for s in sections do out := pushU32 out s.size
  out := out ++ headBytes
  for _ in [0:pad headBytes.size] do out := out.push 32
  for s in sections do
    out := out ++ s
    for _ in [0:pad s.size] do out := out.push 0
  return out

/-- A render answer with no Base64 (issue 1268): the JSON head, and the storage floats
and tile words as raw sections (`packAnswer`). The head is the `compile` answer with
`"dataSection":k` in place of `"dataBase64"` and `"tilesSection":k+1` in place of
`"tiles"`; other answers have no section. -/
@[export web_document_compile_bin]
def compileBin (html request : String) (width height : UInt32) : ByteArray :=
  match parseRequest request >>= fun j => answerWith cachedFrame true html j width.toNat height.toNat with
  | .ok (head,sections) => packAnswer head sections
  | .error message => packAnswer (WebRender.errorJSON message) #[]

@[export web_document_compile]
def compile (html request : String) (width height : UInt32) : String :=
  match parseRequest request >>= fun j => run html j width.toNat height.toNat with
  | .ok value => value | .error message => WebRender.errorJSON message
end WebDocument
