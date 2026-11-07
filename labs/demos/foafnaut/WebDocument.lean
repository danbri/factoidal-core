import WebRenderFontRequests
import WebRenderScript
import WebXslt
import L4Factoidal.Syntax.IriResolve
import WebSelection
import WebHistory
import WebShell
import WebGraph
import L4Factoidal.Rendering.SfntProfile

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

/-- `image` references that the host must fetch, by key and URL. -/
private def imageRequests (dom : DOM.Dom) (base : String) : Except String (List JSON.Json) := do
  if !(dom.nodes.any (fun node => node.type == .element && node.ns == some DOM.svgNS)) then return []
  let (_,tree) ← WebRender.documentNamespaceTree dom
  let keys := (NativeSVG.imageKeys tree (some base)).filter (!·.toLower.startsWith "data:")
  if keys.length > maxDocumentImages then throw s!"document images exceed {maxDocumentImages}"
  return keys.map fun key => .object [("key",.string key),("url",.string key)]

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
    if stylesheet n && Rendering.CSS.hasAttribute n "href" && (← activeSheet n) then
      sheets := .object [("nodeId",.number (toString id)),("href",.string (attr n "href")),
        ("url",.string (Syntax.resolveIri base (attr n "href")))]::sheets
  let scripts ← classicScripts (WebRenderScript.scriptRecords dom)
  let scripts := scripts.map fun script =>
    match script with
    | .object fields => .object (fields ++ [("url",.string (Syntax.resolveIri base (str script "src")))])
    | other => other
  return .object [("nodes",(snapshot.field? "nodes").getD (.array [])),
    ("scripts",.array scripts),("stylesheets",.array sheets.reverse),("images",.array (← imageRequests dom base)),
    ("baseURL",.string base),("title",.string (documentTitle dom))]

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
    return some (WebShell.Shell.ofJson ((request.field? "shell").getD .null) |>.key (code.toNat?.getD 0)).editJson.toString
  if op == "shellSubmit" then return some (WebShell.submit (str request "address")).json.toString
  if let some answer ← WebGraph.op op request then return some answer
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

/-! ### Two layers: the chrome and a band of the page (issue 1268)

With `layers:true` and a shell, a render answers two artifacts. The chrome layer
holds window rows `0 .. top`. The page layer holds the page rows `band.top ..
band.top+band.height`: the page moved up by `band.top`. The host draws each layer
once into its own texture. Each present then copies, with `composite`: window row
`y < top` from chrome row `y`, and window row `y ≥ top` from page row
`y-top+offset`, with `offset = scroll-band.top`. A scroll whose view stays in the
band changes only `offset`, so it needs no Lean call. -/

/-- Page rows that a page layer keeps above and below the view. -/
def bandMargin : Nat := 512
/-- When the view comes this near to an edge of the band that the page goes on
past, the host asks for a new band. -/
def refreshMargin : Nat := 128
/-- A layer is at most this many rows: the texture side that the hosts ask for. -/
def maxLayerRows : Nat := 4096

/-- The page rows of a page layer: from page row `top`, `height` rows. -/
structure Band where
  top : Nat
  height : Nat
  deriving Repr, DecidableEq

/-- The band around a view of `view` rows from page row `scroll`. -/
def band (scroll view : Nat) : Band :=
  let margin := min bandMargin ((maxLayerRows-view)/2)
  ⟨scroll-min scroll margin,view+2*margin⟩

/-- True when a view of `view` rows from page row `scroll` is in the band. -/
def Band.fits (b : Band) (view scroll : Nat) : Bool := b.top ≤ scroll && scroll+view ≤ b.top+b.height
/-- The scroll positions that the host shows from this band with no new one. -/
def Band.keepFrom (b : Band) : Nat := if b.top = 0 then 0 else b.top+refreshMargin
def Band.keepTo (b : Band) (view : Nat) : Nat := b.top+b.height-view-refreshMargin

theorem band_fits (scroll view : Nat) : (band scroll view).fits view scroll = true := by
  dsimp only [band,Band.fits]
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true (by omega),decide_eq_true (by omega)⟩

theorem band_height_le (scroll view : Nat) (small : view ≤ maxLayerRows) :
    (band scroll view).height ≤ maxLayerRows := by
  simp only [band,maxLayerRows,bandMargin] at *
  omega

/-- Every scroll that the host keeps is in the band. -/
theorem keep_fits (b : Band) (view scroll : Nat) (tall : view ≤ b.height)
    (low : b.keepFrom ≤ scroll) (high : scroll ≤ b.keepTo view) : b.fits view scroll = true := by
  simp only [Band.keepFrom,Band.keepTo,Band.fits,Bool.and_eq_true,decide_eq_true_eq] at *
  split at low <;> omega

/-- What the composite shader writes at window pixel `(x,y)`: `compositeShader`
states the same in WGSL. -/
def composite {α : Type} (chrome page : Nat → Nat → α) (top offset x y : Nat) : α :=
  if y < top then chrome x y else page x (y-top+offset)

/-- The composite is the window. Let `image` be the page drawn in page rows and let
the page layer be that image from row `b.top`. Then the composite at offset
`scroll-b.top` is the chrome over rows `0 .. top`, and below it the page from row
`scroll`: the frame that one render at `scroll` describes. The GPU part, that
drawing the page moved up by `b.top` gives `image` moved up by `b.top`, is checked
by pixel hashes (`scroll_layers_test.ts`), not proved here. -/
theorem composite_eq_frame {α : Type} (image chrome : Nat → Nat → α) (b : Band) (top scroll x y : Nat)
    (inside : b.top ≤ scroll) :
    composite chrome (fun x row => image x (row+b.top)) top (scroll-b.top) x y =
      if y < top then chrome x y else image x (y-top+scroll) := by
  unfold composite
  split
  · rfl
  · next above =>
    dsimp only
    rw [show y-top+(scroll-b.top)+b.top = y-top+scroll by omega]

/-- The composite reads only rows of the page layer, for a view in the band. -/
theorem composite_row_lt (b : Band) (top view scroll y : Nat) (fits : b.fits view scroll = true)
    (below : top ≤ y) (within : y < top+view) : y-top+(scroll-b.top) < b.height := by
  simp only [Band.fits,Bool.and_eq_true,decide_eq_true_eq] at fits
  omega

/-- The WGSL of `composite`: binding 0 the chrome texture, 1 the page texture,
2 the words `top`, `offset` and the page layer height. A row past the page layer
is white, as the scene shader paints outside its viewport. -/
def compositeShader : String :=
  "@group(0) @binding(0) var chrome:texture_2d<f32>;\n" ++
  "@group(0) @binding(1) var page:texture_2d<f32>;\n" ++
  "@group(0) @binding(2) var<uniform> place:vec4u;\n" ++
  "@vertex fn vertex(@builtin(vertex_index) i:u32)->@builtin(position) vec4f {" ++
  "let vertices=array<vec2f,3>(vec2f(-1,-1),vec2f(3,-1),vec2f(-1,3));return vec4f(vertices[i],0,1);}\n" ++
  "@fragment fn fragment(@builtin(position) pixel:vec4f)->@location(0) vec4f {" ++
  "let x=u32(pixel.x);let y=u32(pixel.y);" ++
  "if(y<place.x){return textureLoad(chrome,vec2u(x,y),0);}" ++
  "let row=y-place.x+place.y;if(row>=place.z){return vec4f(1.0);}" ++
  "return textureLoad(page,vec2u(x,row),0);}\n"

/-- The page layer of a band: the page moved up by `b.top`, with the glyphs within
`bandMargin` of the band. `extra` (the selection) is not filtered. -/
def pageLayer (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band) : Rendering.Scene :=
  let lift := Float.ofNat b.top
  let keep := page.tree.filter (inWindow (lift-Float.ofNat bandMargin) (lift+Float.ofNat (b.height+bandMargin)))
  {page with
    height := b.height
    mapping := {page.mapping with viewportHeight := Float.ofNat b.height}
    tree := [.group none ⟨1,0,0,1,0,-lift⟩ (keep ++ extra)]
    links := page.links.map (fun link => {link with y := link.y-lift})}

/-- The chrome layer: window rows `0 .. WebShell.height`. -/
def chromeLayer (shell : WebShell.Shell) (page : Rendering.Scene) (width : Nat) : Rendering.Scene :=
  let top := max 1 (WebShell.height shell width)
  {page with
    height := top
    mapping := {page.mapping with viewportHeight := Float.ofNat top}
    tree := WebShell.nodes shell width
    glyphRuns := #[]
    links := #[]}

/-- The answer to a render with `layers:true`. -/
def layersJSON (shell : WebShell.Shell) (page : Rendering.Scene) (extra : List Rendering.Node)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face)
    (width height : Nat) (live : Bool) (form : NativeSVG.DataForm) (checks tree : Bool) :
    Except String (String × Array ByteArray) := do
  let top := WebShell.height shell width
  let view := max 1 (height-top)
  let b := band shell.scroll view
  let (pageText,pageSections) ← WebRender.artifactWith (pageLayer page extra b) boxes face live form checks tree
  let (chromeText,chromeSections) ←
    WebRender.artifactWith (chromeLayer shell page width) #[] face live form.next checks tree
  let number := fun (n : Nat) => JSON.Json.number (toString n)
  let place := JSON.Json.object [("top",number top),("view",number view),("bandTop",number b.top),
    ("bandHeight",number b.height),("keepFrom",number b.keepFrom),("keepTo",number (b.keepTo view)),
    ("composite",.string compositeShader)]
  return ("{\"layers\":" ++ place.toString ++ ",\"page\":" ++ pageText ++ ",\"chrome\":" ++ chromeText ++ "}",
    pageSections ++ chromeSections)

/-- The font the engine holds between calls, so that a scroll does not read it again. -/
structure HeldFont where
  font : Rendering.SfntProfile.Font
  memo : Rendering.SfntProfile.Memo

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

/-- Read the bytes of a font file once. Later renders use it until another replaces it.
`request` only keeps the call in place (see `keepFont`). -/
private def loadFontBytes (bytes : ByteArray) (family sha256 : String) (request : JSON.Json) : Except String String := do
  let font ← Rendering.SfntProfile.Font.read bytes family sha256
  let held := keepFont ⟨font,{}⟩ request
  return (JSON.Json.object [("family",.string held.font.family),("glyphs",.number (toString held.font.face.numGlyphs))]).toString

/-- The `fontLoad` op: the font file as Base64 in the JSON request. This is the text
reference path; `fontLoadBin` takes the same file as bytes. -/
private def loadFont (request : JSON.Json) : Except String String := do
  let some bytes := Rendering.SfntProfile.decodeBase64 (str request "fontBase64") | throw "font file: invalid base64"
  loadFontBytes bytes (str request "fontFamily" "font") (str request "fontSha256" "unnamed") request

/-- `fontLoad` with the font file as bytes, with no Base64 and no JSON around it.
A host copies the file into engine memory, so a font is not limited by the call stack,
which holds string arguments in Wasm. The answer is the `fontLoad` answer. -/
@[export web_document_font_load_bin]
def fontLoadBin (bytes : ByteArray) (family sha256 : String) : String :=
  let request := JSON.Json.object [("op",.string "fontLoad"),("fontFamily",.string family),
    ("fontSha256",.string sha256),("fontBytes",.number (toString bytes.size))]
  match loadFontBytes bytes family sha256 request with
  | .ok value => value | .error message => WebRender.errorJSON message

/-- The request fields that a render reads before its layout ends. `shell` gives only
the height of the chrome, which the key holds as `top`; `selection`, `live`, `binary`,
`checks`, `tree`, `op` and the scroll act after layout. -/
def layoutFields : List String := ["commands","resources","images","url","fontData","textScalePercent","graphModel"]

/-- The request with only `layoutFields`, in that order. -/
def layoutRequest (request : JSON.Json) : JSON.Json :=
  .object (layoutFields.filterMap fun key => (request.field? key).map (key,·))

/-- Everything that a render reads before its layout ends. The held font is named by
its family and SHA-256: `layOut` reads the font that `fontLoad` holds, and only
`fontLoad` replaces it. -/
structure LayoutKey where
  html : String
  request : JSON.Json
  width : Nat
  height : Nat
  /-- Height of the browser chrome above the page. -/
  top : Nat
  font : Option (String × String)
  deriving DecidableEq

/-- A laid-out document: the scene before the window, the selection and the chrome. -/
structure Laid where
  scene : Rendering.Scene
  boxes : Array Rendering.Layout.Box
  face : Option Rendering.FontProvider.Face

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
  validateResources dom request
  let _ ← classicScripts (WebRenderScript.scriptRecords dom)
  let textScale := Float.ofNat (← scalePercent request) / 100
  let rules ← rules dom request
  if key.width == 0 || key.height == 0 || key.width > 4096 || key.height > 4096 then throw "unsupported document viewport"
  let fontData := str request "fontData"
  if !fontData.isEmpty then
    let _ ← WebRenderFontRequests.collectDOMWithRules dom rules textScale
  let face ← if fontData.isEmpty then pure none else
    some <$> Rendering.FontProvider.Face.decode fontData
  -- A font loaded by the fontLoad op: Lean shapes the words and takes the outlines.
  let loaded := heldFont request
  let memo := loaded.map fun held => Rendering.SfntProfile.remember held.font held.memo (Rendering.SfntProfile.wordsOf dom)
  let font ← match loaded,memo with
    | some held,some words =>
      Rendering.SfntProfile.profile held.font (keepWords words request)
    | _,_ => pure (match face with | some f => Rendering.Layout.FontProfile.ofFace f | none => WebRender.asciiFont)
  let url := baseURL dom (str request "url")
  let embedding ← match graph with
    | some m => pure (WebGraph.embedding m)
    | none => WebRender.makeEmbedding dom (if url.isEmpty then none else some url) (← suppliedImages request)
  -- A window shorter than the chrome still lays out, on one row.
  let (scene,boxes) ← Rendering.Layout.render dom rules font embedding key.width (max 1 (key.height-key.top)) textScale
  return {scene := scene,boxes := boxes,face := face}

/-! ### The layout of the last render, kept

A scroll, a selection or a pointer move sends the same document, width, height,
chrome height, text scale and font again. `run` then takes the kept layout and does
not parse, cascade or lay out again. The cache holds one entry, `(key, layOut key)`
when that was a success. `lookupLayout` states what `run` does with it, and
`lookupLayout_eq` shows the answer is `layOut key` for any entry so made. -/

/-- An entry is valid when its value is the layout of its key. `keepLayout` makes
only such entries. -/
def ValidEntry (entry : Option (LayoutKey × Laid)) : Prop :=
  ∀ key laid, entry = some (key,laid) → layOut key = .ok laid

def lookupLayout (entry : Option (LayoutKey × Laid)) (key : LayoutKey) : Except String Laid :=
  match entry with
  | some (kept,laid) => if kept = key then .ok laid else layOut key
  | none => layOut key

theorem lookupLayout_eq (entry : Option (LayoutKey × Laid)) (valid : ValidEntry entry) (key : LayoutKey) :
    lookupLayout entry key = layOut key := by
  unfold lookupLayout
  match entry, valid with
  | none, _ => rfl
  | some (kept,laid), valid =>
    simp only
    split
    · next same => subst same; exact (valid kept laid rfl).symm
    · rfl

/-- The entry that a render leaves is valid. -/
theorem stored_valid (key : LayoutKey) (laid : Laid) (made : layOut key = .ok laid) :
    ValidEntry (some (key,laid)) := by
  intro k l same
  cases same
  exact made

initialize layoutRef : IO.Ref (Option (LayoutKey × Laid)) ← IO.mkRef none

set_option compiler.extract_closed false in
private unsafe def keptLayoutImpl (key : LayoutKey) : Option Laid :=
  unsafeBaseIO do
    match ← layoutRef.get with
    | some (kept,laid) => return if kept == key then some laid else none
    | none => return none
private unsafe def keepLayoutImpl (key : LayoutKey) (laid : Laid) : Laid :=
  unsafeBaseIO (do layoutRef.set (some (key,laid)); return laid)
/-- These read and set the kept layout, as `heldFont` and `keepFont` do for the font. -/
@[implemented_by keptLayoutImpl, noinline] private opaque keptLayout (key : LayoutKey) : Option Laid
@[implemented_by keepLayoutImpl, noinline] private opaque keepLayout (key : LayoutKey) (laid : Laid) : Laid := laid

/-- `lookupLayout` over the kept entry. -/
private def cachedLayOut (key : LayoutKey) : Except String Laid :=
  match keptLayout key with
  | some laid => .ok laid
  | none => keepLayout key <$> layOut key

/-- A document request, with `laidOut` as the layout of a render. `run` passes the
kept layout; `runUncached` passes `layOut`, so that tests compare the two. With
`bytes`, a render answer names its storage floats and tile words as sections
(`DataForm.sections`) and gives their bytes; other answers have no section. -/
def answerWith (laidOut : LayoutKey → Except String Laid) (bytes : Bool) (html : String) (request : JSON.Json)
    (width height : Nat) : Except String (String × Array ByteArray) := do
  let .object fields := request | throw "document request must be an object"
  if (fields.map Prod.fst).eraseDups.length != fields.length then throw "duplicate document request field"
  if str request "op" == "fontLoad" then return (← loadFont request,#[])
  if str request "op" == "xmlStylesheet" then
    let url := match ← WebXslt.stylesheetHref html with
      | some href => JSON.Json.string (Syntax.resolveIri (str request "url") href)
      | none => .null
    return ((JSON.Json.object [("url",url)]).toString,#[])
  if str request "op" == "xslt" then
    let (source,engine) ← WebXslt.transform html (str request "stylesheet") (str request "url") (str request "stylesheetURL")
    return ((JSON.Json.object [("source",.string source),("engine",.string engine)]).toString,#[])
  if let some answer ← inputOp (str request "op" "render") request then return (answer,#[])
  let op := str request "op" "render"
  if op != "render" && op != "selectedText" then
    let dom ← prepareDOM html request
    validateResources dom request
    let _ ← classicScripts (WebRenderScript.scriptRecords dom)
    if op == "inspect" then return ((← inspect dom (str request "url")).toString,#[])
    let textScale := Float.ofNat (← scalePercent request) / 100
    let rules ← rules dom request
    if op == "fontRequests" then
      return (WebRenderFontRequests.requestsJSON (← WebRenderFontRequests.collectDOMWithRules dom rules textScale),#[])
    throw "unknown document operation"
  let shell := (request.field? "shell").map WebShell.Shell.ofJson
  let top := (shell.map (fun value => WebShell.height value width)).getD 0
  let font := (heldFont request).map fun held => (held.font.family,held.font.sha256)
  let key : LayoutKey := ⟨html,layoutRequest request,width,height,top,font⟩
  let laid ← laidOut key
  let scene := laid.scene
  let boxes := laid.boxes
  let face := laid.face
  -- Pointer positions are in window coordinates; the page starts below the chrome.
  let moved := Float.ofNat top-Float.ofNat ((shell.map (·.scroll)).getD 0)
  let chosen := (← selection request).map (fun value => WebSelection.shift value moved)
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
  let form : NativeSVG.DataForm := if bytes then .sections 0 else if binary then .base64 else .decimal
  let checks := request.field? "checks" != some (.bool false)
  -- The inspector tree only when the request asks (`tree:true`); no frame host reads it.
  let tree := request.field? "tree" == some (.bool true)
  if let some value := shell then
    if request.field? "layers" == some (.bool true) then
      return ← layersJSON value scene marks boxes face width height live form checks tree
  let scrolled := Float.ofNat ((shell.map (·.scroll)).getD 0)
  let near := scene.tree.filter (inWindow (scrolled-512) (scrolled+Float.ofNat height+512))
  let page := {scene with tree := near ++ marks}
  WebRender.artifactWith (match shell with
    | some value => WebShell.compose value page width height
    | none => page) boxes face live form checks tree

/-- The JSON text answer: storage floats in Base64 (`binary:true`) or decimal. -/
def runWith (laidOut : LayoutKey → Except String Laid) (html : String) (request : JSON.Json) (width height : Nat) :
    Except String String :=
  Prod.fst <$> answerWith laidOut false html request width height

def run := runWith cachedLayOut
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
  match parseRequest request >>= fun j => answerWith cachedLayOut true html j width.toNat height.toNat with
  | .ok (head,sections) => packAnswer head sections
  | .error message => packAnswer (WebRender.errorJSON message) #[]

@[export web_document_compile]
def compile (html request : String) (width height : UInt32) : String :=
  match parseRequest request >>= fun j => run html j width.toNat height.toNat with
  | .ok value => value | .error message => WebRender.errorJSON message
end WebDocument
