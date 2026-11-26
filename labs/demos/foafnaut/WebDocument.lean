import WebRenderFontRequests
import L4Factoidal.Epub
import L4Factoidal.DOM.OfXml
import WebRenderScript
import WebXslt
import L4Factoidal.Syntax.IriResolve
import WebSelection
import WebHistory
import WebShell
import WebGesture
import WebPrint
import WebAbout
import WebGraph
import WebEventLoop
import WebHostContract
import WebWasm
import WebState
import WebSparql
import WebScripts
import L4Factoidal.Net.Subresource
import L4Factoidal.Prim.Bytes
import L4Factoidal.Rendering.SfntProfile
import L4Factoidal.FrameCost.Band
import L4Factoidal.FrameCost.Lru
import L4Factoidal.Rendering.ComputedValues
import L4Factoidal.Rendering.ComputedGeneric
import L4Factoidal.Rendering.GridResolved
import WebRepaint
import L4Factoidal.WHATWG.Encoding.Sniff
import WebHit
import WebAccept
import WebConsole
import WebPaint
import L4Factoidal.Rendering.FontFaceRule
import L4Factoidal.Rendering.ImportTree
import L4Factoidal.HTML.AccessibleTree

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

/-- The media environment of a layout (`MediaQuery.Env`): the media type, and the viewport
in CSS px, `width` by `rows` device pixels at the text scale `percent` (a text scale of 200%
on a 1600 px wide window is an 800 px wide viewport, as a page zoom of 200% is). Pages are
drawn in light colours: `prefers-color-scheme: dark` does not hold. -/
def mediaEnv (medium : String) (width rows percent : Nat) : Rendering.MediaQuery.Env :=
  WasmVM.Hosts.Page.mediaEnvOf medium width rows percent

/-- Kind: seam theorem (media queries). Says: the media environment the layout reads its
sheets in is the one `matchMedia` evaluates a query in (`Hosts.Page.mediaAnswer`): one maker
for both. Does not say: that the two are given the same viewport and zoom (the session's
`layout` request and viewport are the host's; `host_parity_test.ts` checks a page where
`matchMedia` and an `@media` block must agree). -/
theorem mediaEnv_eq (medium : String) (width rows percent : Nat) :
    mediaEnv medium width rows percent = WasmVM.Hosts.Page.mediaEnvOf medium width rows percent := rfl

private def sheetTyped (n : DOM.Node) : Bool :=
  !Rendering.CSS.hasAttribute n "disabled" && ["","text/css"].contains (attr n "type")

/-- Where a sheet is, for a diagnostic. -/
private def sheetWhere (n : DOM.Node) (id : Nat) : String :=
  let tag := if DOM.Dom.isHtmlElement n "style" then "style" else "link"
  let href := attr n "href"
  let media := attr n "media"
  s!"<{tag}> node {id}" ++ (if href.isEmpty then "" else " href=\"" ++ href ++ "\"") ++
    (if media.isEmpty then "" else " media=\"" ++ media ++ "\"")

private def mediaRefusal : String := "unsupported stylesheet media condition"

/-- Whether a `style` or stylesheet `link` applies in `env`. A `media` attribute that
`MediaQuery` can not read is a skip point. -/
private def activeSheetIn (m : WebAccept.Mode) (env : Rendering.MediaQuery.Env) (n : DOM.Node) (id : Nat) :
    Except String (Bool × List WebAccept.Diagnostic) :=
  if !sheetTyped n then .ok (false,[]) else
  match Rendering.MediaQuery.holds env (attr n "media") with
  | some b => .ok (b,[])
  | none => WebAccept.skip m .mediaCondition (sheetWhere n id) mediaRefusal false

/-- Whether the host fetches a stylesheet `link`: its `media` can hold on a screen or on
paper at some viewport size. -/
private def fetchSheetIn (m : WebAccept.Mode) (n : DOM.Node) (id : Nat) : Except String (Bool × List WebAccept.Diagnostic) :=
  if !sheetTyped n then .ok (false,[]) else
  match Rendering.MediaQuery.parse (attr n "media") with
  | some qs => .ok (qs.isEmpty || qs.any (fun q => q.negated ||
      Rendering.MediaQuery.typeMatches {medium := "screen"} q.type || Rendering.MediaQuery.typeMatches {medium := "print"} q.type),[])
  | none => WebAccept.skip m .mediaCondition (sheetWhere n id) mediaRefusal false

/-- The request's scripting: `scripting:false` when the host runs no page scripts. Only a
liberal request carries it. -/
def scripting (request : JSON.Json) : Bool := request.field? "scripting" != some (.bool false)

/-- The reason the host gives for a stylesheet it could not fetch (`resourceFailures`). -/
private def failure (request : JSON.Json) (id : Nat) : Option String :=
  match request.field? "resourceFailures" with
  | some (.array fs) => (fs.find? fun f => f.field? "nodeId" == some (.number (toString id))).map fun f =>
      str f "reason" "not fetched"
  | _ => none
/-- A supplied resource whose node is no longer a connected style sheet link or script is
left out (true) or refuses the request (false). It is left out when the request carries
commands of the page's scripts: the host fetched the sheet for the tree as it was, and a
script then removed the link, or changed its `rel`. With no commands the tree is the one
the host was told of, and such a resource is the host's error. Before 2026-11-14 it refused
the request in both cases, so a page whose script removed a linked sheet was not drawn. -/
def staleResourceLeftOut (request : JSON.Json) : Bool :=
  match request.field? "commands" with
  | some (.array (_ :: _)) => true
  | _ => false

/-- Kind: property. Says: a request with no script commands keeps the refusal of a resource
for a node that is no style sheet or script, as before. Does not say: anything of the
resource's source (the other checks of `validateResources` hold in both cases). -/
theorem staleResourceLeftOut_no_commands (request : JSON.Json) (h : request.field? "commands" = none) :
    staleResourceLeftOut request = false := by
  simp [staleResourceLeftOut, h]

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
    if !(dom.treeOrder 0).contains id || !(stylesheet node || WebRenderScript.isScriptElement node) then
      if staleResourceLeftOut request then continue
      throw "resource is not a connected stylesheet or script"
    let some (.string source) := resource.field? "source" | throw "resource source must be a string"
    if source.utf8ByteSize > WebRender.maxSourceBytes then throw "resource exceeds 16 MiB"
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

/-- The tree of `html` in the XML syntax (`xhtml`) or the HTML syntax. -/
def parseFresh (html : String) (xhtml : Bool) : Except String DOM.Dom :=
  if xhtml then DOM.parseXmlDocument html else pure (DOM.parseHtmlDocument html)

/-! ### Work kept between layouts (issue 390)

Every layout of a page (a relayout at another width, a pointer state that changes
geometry) parsed its source again: 13 to 30 ms of a relayout of Wikipedia or gov.uk; and
read its sheets and decoded its images again (realperf). The engine keeps the last two
trees by their source, the last eight sheets by their text, and the last two image
stores (`WebRender.StoresKept`) in `Kept`, a field of its state. A layout looks them up
there, and gives back what it made (`Made`), which the engine adds (`Kept.add`). -/

/-- A style sheet's text, read (`CSS.parseRaw`). -/
abbrev RawSheet := Except String (List Rendering.CSS.RawRule)

structure Kept where
  parsed : Array (String × Bool × Except String DOM.Dom) := #[]
  sheets : Array (String × RawSheet) := #[]
  stores : WebRender.StoresKept := #[]
  /-- Words of SVG text (`NativeSVGText.wordIn`). -/
  words : NativeSVGText.Words := {}

/-- What one operation made that `Kept` did not have. -/
structure Made where
  parsed : Option (String × Bool × Except String DOM.Dom) := none
  sheet : Option (String × RawSheet) := none
  store : Option WebRender.StoreEntry := none
  words : NativeSVGText.Words := {}

/-- `a` then the entries of `b` that `a` lacks (the first operation's wins). -/
def Made.merge (a b : Made) : Made :=
  {parsed := a.parsed.orElse fun _ => b.parsed,sheet := a.sheet.orElse fun _ => b.sheet,
   store := a.store.orElse fun _ => b.store,words := b.words.fold (fun m k v => m.insert k v) a.words}

/-- `xs` with `x` last, at most `n`. -/
def keepLast {α : Type} (n : Nat) (xs : Array α) : Option α → Array α
  | some x => (if xs.size ≥ n then xs.extract 1 xs.size else xs).push x
  | none => xs

/-- `kept` with `made`: the last two trees, the last eight sheets, the last two stores. -/
def Kept.add (kept : Kept) (made : Made) : Kept :=
  let last := @keepLast
  {parsed := last 2 kept.parsed made.parsed,sheets := last 8 kept.sheets made.sheet,
   stores := match made.store with | some s => WebRender.keepStore kept.stores s | none => kept.stores,
   words := if made.words.isEmpty then kept.words
     else if kept.words.size + made.words.size > NativeSVGText.keptWordsLimit then made.words
     else made.words.fold (fun m k v => m.insert k v) kept.words}

/-- The tree of `html`: the kept one, or `parseFresh`, which is also given back. -/
def parseIn (kept : Kept) (html : String) (xhtml : Bool) : Except String DOM.Dom × Made :=
  match kept.parsed.find? (fun (h,x,_) => x == xhtml && h == html) with
  | some (_,_,d) => (d,{})
  | none => let d := parseFresh html xhtml; (d,{parsed := some (html,xhtml,d)})

/-- The rules of a sheet's text: the kept ones, or `CSS.parseRaw`, also given back. -/
def sheetIn (kept : Kept) (source : String) : RawSheet × Made :=
  match kept.sheets.find? (·.1 == source) with
  | some (_,r) => (r,{})
  | none => let r := Rendering.CSS.parseRaw source; (r,{sheet := some (source,r)})

/-- A table is valid when each entry is what it keeps: the parse of its source, the
rules of its text, the image store of its keys and bytes. -/
def Kept.Valid (kept : Kept) : Prop :=
  (∀ e ∈ kept.parsed, e.2.2 = parseFresh e.1 e.2.1) ∧ (∀ e ∈ kept.sheets, e.2 = Rendering.CSS.parseRaw e.1) ∧
  WebRender.StoresValid kept.stores

/-- Refinement: from a valid table, `parseIn` gives `parseFresh`. -/
theorem parseIn_eq (kept : Kept) (valid : kept.Valid) (html : String) (xhtml : Bool) :
    (parseIn kept html xhtml).1 = parseFresh html xhtml := by
  unfold parseIn
  split
  · next _ h' x d h =>
    have mem := Array.mem_of_find?_eq_some h
    have sat := Array.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at sat
    have v := valid.1 _ mem
    simp only at v
    rw [v, sat.1, sat.2]
  · rfl

/-- Refinement: from a valid table, `sheetIn` gives `CSS.parseRaw`. -/
theorem sheetIn_eq (kept : Kept) (valid : kept.Valid) (source : String) :
    (sheetIn kept source).1 = Rendering.CSS.parseRaw source := by
  unfold sheetIn
  split
  · next _ s raw h =>
    have mem := Array.mem_of_find?_eq_some h
    have sat := Array.find?_some h
    simp only [beq_iff_eq] at sat
    have v := valid.2.1 _ mem
    simp only at v
    rw [v, sat]
  · rfl

/-! Words that miss the font memo (`SfntProfile.profile`) were also shaped again by each
layout (realperf). `shapeKept` is `SfntProfile.shapeFresh`; its implementation keeps
what it made, by `SfntProfile.fontsKey`, text, size and direction (at most 16,384, then
the table starts again). It is called from inside `Rendering.Layout`, so it is not yet
a field of the engine's state (issue 390). With a `primary` font it is
`SfntProfile.shapeFreshWith primary` (the words of web fonts and of the serif face, drawn
in the primary font's units), else `SfntProfile.shapeFresh`. -/
initialize shapedKept : IO.Ref (Std.HashMap (String × String × Nat × Option Bool) (Except String Rendering.FontProvider.Word)) ← IO.mkRef {}

private unsafe def shapeKeptImpl (key : String) (primary : Option Rendering.SfntProfile.Font)
    (fonts : Array Rendering.SfntProfile.Font) (text : String) (px : Nat)
    (rtl : Option Bool) : Except String Rendering.FontProvider.Word :=
  unsafeBaseIO do
    let k := (key,text,px,rtl)
    if let some w := (← shapedKept.get)[k]? then return w
    let w := match primary with
      | some p => Rendering.SfntProfile.shapeFreshWith p fonts text px rtl
      | none => Rendering.SfntProfile.shapeFresh fonts text px rtl
    shapedKept.modify fun m => (if m.size ≥ 16384 then {} else m).insert k w
    return w

/-- `SfntProfile.shapeFresh fonts` (with `primary`, `SfntProfile.shapeFreshWith primary fonts`),
kept; `key` names `primary` and `fonts` (`SfntProfile.fontsKey`), and no other pair. -/
@[implemented_by shapeKeptImpl, noinline]
def shapeKept (_key : String) (primary : Option Rendering.SfntProfile.Font) (fonts : Array Rendering.SfntProfile.Font)
    (text : String) (px : Nat) (rtl : Option Bool) : Except String Rendering.FontProvider.Word :=
  match primary with
  | some p => Rendering.SfntProfile.shapeFreshWith p fonts text px rtl
  | none => Rendering.SfntProfile.shapeFresh fonts text px rtl

/-- The document tree: the XML syntax for a `.xht`, `.xhtml` or `.svg` URL (HTML §14,
`DOM.parseXmlDocument`, `DOM.isXmlPath`), else the HTML syntax (HTML §13). -/
def prepareDOMIn (kept : Kept) (html : String) (request : JSON.Json) : Except String (DOM.Dom × Made) := do
  if html.utf8ByteSize > WebRender.maxSourceBytes then throw "document HTML exceeds 16 MiB"
  let (dom,made) := parseIn kept html (DOM.xmlSyntax (str request "url") (str request "syntax"))
  return (← WebRenderScript.applyCommands (← dom) ((request.field? "commands").getD (.array [])),made)

/-- `prepareDOMIn` with nothing kept. -/
def prepareDOM (html : String) (request : JSON.Json) : Except String DOM.Dom :=
  Prod.fst <$> prepareDOMIn {} html request

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

/-- The supplied source of a stylesheet `link`, none when the host supplied none. -/
private def supplied (request : JSON.Json) (id : Nat) : Except String (Option String) := do
  let .array resources := (request.field? "resources").getD (.array [])
    | throw "document resources must be an array"
  if resources.length > 64 then throw "document resource limit exceeded"
  let foundResources := resources.filter (fun r => r.field? "nodeId" == some (.number (toString id)))
  match foundResources with
  | [] => return none
  | [resource] =>
    let some (.string source) := resource.field? "source" | throw "stylesheet source must be a string"
    if source.utf8ByteSize > WebRender.maxSourceBytes then throw "stylesheet exceeds 16 MiB"
    return some source
  | _ => throw s!"stylesheet resource missing or duplicated for node {id}"

/-- The URL a supplied stylesheet came from (its `url`), for the URLs in it. -/
private def suppliedURL (request : JSON.Json) (id : Nat) : Option String := do
  let .array resources := (request.field? "resources").getD (.array []) | none
  let r ← resources.find? (fun r => r.field? "nodeId" == some (.number (toString id)))
  match r.field? "url" with
  | some (.string u) => some u
  | _ => none

/-! ### `@import` (CSS Cascade 5 §6.1)

The engine names the sheets a page's sheets import (`inspect`, `imports`), a host fetches
them and gives them back in every layout request (`imported`: `{url, source}` records), and
`sheetsIn` reads each in place: before the sheet that imports it, under the import's layer,
`supports()` condition and media (`wrapImport`), by the walk of `Rendering.ImportTree`
(each URL once, 64 sheets, 8 deep). A page with no `imported` field does none of this. -/

/-- The imported sheets a host supplies: at most 256, 4 MiB of text in all. -/
def importedSheets (request : JSON.Json) : Except String (List (String × String)) := do
  let .array items := (request.field? "imported").getD (.array []) | throw "imported must be an array"
  if items.length > 256 then throw "imported style sheets exceed 256"
  let mut out : List (String × String) := []
  let mut bytes := 0
  for item in items do
    let some (.string url) := item.field? "url" | throw "imported style sheet url must be a string"
    let some (.string source) := item.field? "source" | throw "imported style sheet source must be a string"
    bytes := bytes+source.utf8ByteSize
    if bytes > 4194304 then throw "imported style sheets exceed 4 MiB"
    out := (url,source)::out
  return out.reverse

/-- The text of an imported sheet under the conditions of its `@import` rule: in an `@layer`
block for `layer` or `layer(name)`, in an `@supports` block for `supports(...)`, in an
`@media` block for a media query list. A rule with none of them leaves the text as it is. -/
def wrapImport (i : Rendering.SheetReader.Import) (text : String) : String :=
  let text := match i.layer with
    | some name => "@layer " ++ name ++ " {\n" ++ text ++ "\n}"
    | none => text
  let text := match i.supports with
    | some c =>
      let low := c.toLower
      let condition := if c.startsWith "(" || low.startsWith "not " || low.startsWith "selector(" then c else "(" ++ c ++ ")"
      "@supports " ++ condition ++ " {\n" ++ text ++ "\n}"
    | none => text
  if i.media == "" then text else "@media " ++ i.media ++ " {\n" ++ text ++ "\n}"

/-- Kind: property. Says: an `@import` with no layer, no `supports()` and no media gives the
imported text as it is. Does not say: that the wrapped forms mean what CSS says (the sheet
reader reads them: tested). -/
theorem wrapImport_plain (i : Rendering.SheetReader.Import) (text : String)
    (hl : i.layer = none) (hs : i.supports = none) (hm : i.media = "") : wrapImport i text = text := by
  simp [wrapImport, hl, hs, hm]

/-- The imports of a sheet's text, for `Rendering.ImportTree`. A text with no `@import` in
it is not read for them. -/
def importEdges (text : String) : List Rendering.ImportTree.Edge :=
  if (text.toLower.splitOn "@import").length < 2 then [] else
  (Rendering.SheetReader.imports text).map fun i => { url := i.url, wrap := wrapImport i }

/-- The document's sheets in `env`, in tree order, each with the URL its own URLs resolve
against (the document's base for a `style` element, the sheet's URL for a supplied one,
CSS Values 4 §4.5.1), with the skip points of mode `m`: a `media` that can not be read, a
stylesheet the host could not fetch, and sheets past 8 MiB. -/
def sheetsIn (m : WebAccept.Mode) (dom : DOM.Dom) (request : JSON.Json) (env : Rendering.MediaQuery.Env) :
    Except String (List (String × String) × List WebAccept.Diagnostic) := do
  let given ← importedSheets request
  -- The same source order governs both HTML and inline SVG author rules.
  let base := baseURL dom (str request "url")
  let mut sheets : List (String × String) := []
  let mut bytes := 0
  let mut ds : List WebAccept.Diagnostic := []
  for id in dom.treeOrder 0 do
    let n := dom.get id
    let inline := DOM.Dom.isHtmlElement n "style" ||
      (n.type == .element && n.ns == some DOM.svgNS && n.lname == "style")
    if !inline && !(stylesheet n && Rendering.CSS.hasAttribute n "href") then continue
    let (active,d) ← activeSheetIn m env n id
    ds := ds ++ d
    if !active then continue
    let mut source := ""
    if inline then source := (dom.textContent id).getD ""
    else
      match failure request id with
      | some reason =>
        let (_,d) ← WebAccept.skip m .stylesheetMissing (sheetWhere n id) s!"stylesheet not loaded: {reason}" ()
        ds := ds ++ d
      | none => match ← supplied request id with
        | some text => source := text
        | none =>
          let (_,d) ← WebAccept.skip m .stylesheetMissing (sheetWhere n id)
            s!"stylesheet resource missing or duplicated for node {id}" ()
          ds := ds ++ d
    -- the engine's own limit on the text of the sheets (`maxSheetBytes`): a sheet past it is
    -- left out whole and reported, so the engine never has to cut a sheet (issue 865)
    if bytes+source.utf8ByteSize > Rendering.CSS.maxSheetBytes then
      let (_,d) ← WebAccept.skip m .stylesheetBytes (sheetWhere n id) "document stylesheets exceed 8 MiB" ()
      ds := ds ++ d
      continue
    bytes := bytes+source.utf8ByteSize
    let from_ := if inline then base else (suppliedURL request id).getD base
    -- the sheets it imports that the host gave, before it, within the same bound of bytes
    if !given.isEmpty then
      for (u,t) in Rendering.ImportTree.sheetsOf importEdges Syntax.resolveIri (fun url => given.lookup url) from_ source do
        if bytes+t.utf8ByteSize ≤ Rendering.CSS.maxSheetBytes then
          bytes := bytes+t.utf8ByteSize
          sheets := (u,t)::sheets
        else
          -- reported as for a sheet of the document (issue 865); before, it was left out silently
          let (_,d) ← WebAccept.skip m .stylesheetBytes s!"@import {u}" "document stylesheets exceed 8 MiB" ()
          ds := ds ++ d
    sheets := (from_,source)::sheets
  return (sheets.reverse,ds)

/-! ### Background images (CSS Backgrounds 3 §3.3, issue 704)

A `url(...)` in a `background` or `background-image` declaration is resolved against the URL of
the sheet it is in (CSS Values 4 §4.5), or of the document for a `style` element or attribute,
when the sheets are read (`backgroundUrlsAbsolute`), so the cascade holds absolute URLs. The
host fetches them as it fetches images: `inspect` lists them (`backgroundImages`) once it has
the sheets (its second call, with `resources`). After the cascade each element's image is
looked up in the supplied images and decoded (`attachBackgrounds`). -/

/-- The argument of a `url(` whose text follows: its URL, and the text after its `)`. -/
private def urlArg (p : String) : Option (String × String) :=
  let cs := p.toList.dropWhile Char.isWhitespace
  match cs with
  | [] => none
  | q :: more =>
    if q == '"' || q == '\'' then
      let inner := more.takeWhile (· != q)
      if inner.length == more.length then none else
      match (more.drop (inner.length+1)).dropWhile Char.isWhitespace with
      | ')' :: rest => some (String.ofList inner,String.ofList rest)
      | _ => none
    else
      let inner := cs.takeWhile (· != ')')
      if inner.length == cs.length then none else
      some (String.ofList (inner.reverse.dropWhile Char.isWhitespace).reverse,String.ofList (cs.drop (inner.length+1)))

/-- Whether the declaration that the text after `t` is in names a background property,
`border-image` (CSS Backgrounds 3 §6) or `content` (a `url()` there is an image too, CSS Content 3 §2.1): the
text after the last `{` or `;` of `t` mentions `background`, or `t` has neither and the
declaration before it did (`prev`). -/
private def inBackground (prev : Bool) (t : String) : Bool :=
  let cs := t.toLower.toList
  let tail := (cs.reverse.takeWhile (fun c => c != '{' && c != ';' && c != '}')).reverse
  let mentions := fun (l : List Char) => ((String.ofList l).splitOn "background").length > 1 ||
    ((String.ofList l).splitOn "content").length > 1 || ((String.ofList l).splitOn "border-image").length > 1
  if tail.length < cs.length then mentions tail else prev || mentions cs

private def resolveBackgroundUrl (base u : String) : String :=
  if base.isEmpty || u.toLower.startsWith "data:" then u else Syntax.resolveIri base u

/-- Resolve background URLs against `base` while preserving fragment-only URLs as local
references (CSS Values 4 §4.5.1.1). -/
def backgroundUrlsAbsolute (base text : String) : String := Id.run do
  let pieces := text.splitOn "url("
  if pieces.length < 2 then return text
  let mut out := pieces.head!
  let mut st := inBackground false pieces.head!
  for p in pieces.tail do
    match urlArg p with
    | some (u,rest) =>
      if st && !u.isEmpty && !u.startsWith "#" && !u.contains '"' then
        out := out ++ "url(\"" ++ resolveBackgroundUrl base u ++ "\")" ++ rest
      else out := out ++ "url(" ++ p
      st := inBackground st rest
    | none =>
      out := out ++ "url(" ++ p
      st := inBackground st p
  return out

/-- The absolute URLs of background declarations that can identify image resources. -/
def backgroundUrlsOf (base text : String) : List String := Id.run do
  let pieces := text.splitOn "url("
  if pieces.length < 2 then return []
  let mut out : List String := []
  let mut st := inBackground false pieces.head!
  for p in pieces.tail do
    match urlArg p with
    | some (u,rest) =>
      if st && !u.isEmpty && !u.startsWith "#" then out := resolveBackgroundUrl base u :: out
      st := inBackground st rest
    | none => st := inBackground st p
  return out.reverse

#guard backgroundUrlsAbsolute "https://a.test/css/s.css" "p{background:url(i.png) no-repeat} q{content:url(x.png)}" ==
  "p{background:url(\"https://a.test/css/i.png\") no-repeat} q{content:url(\"https://a.test/css/x.png\")}"
#guard backgroundUrlsAbsolute "https://a.test/css/s.css" "li+li:before{content:url(\"/stylesheets/star.svg\")}" ==
  "li+li:before{content:url(\"https://a.test/stylesheets/star.svg\")}"
#guard backgroundUrlsOf "https://a.test/css/s.css" "a::after{content:\" \" url('../i/x.png') \"!\"}" == ["https://a.test/i/x.png"]
#guard backgroundUrlsAbsolute "https://a.test/s.css" "a{content:url(#frag)}" == "a{content:url(#frag)}"
#guard backgroundUrlsOf "https://a.test/" "div { color: red; background-image: url('a b.png'), url(c.png) }" ==
  ["https://a.test/a b.png","https://a.test/c.png"]
#guard backgroundUrlsOf "https://a.test/s.css" "div { border-image: url(\"stripes.png\") 0 35 0 0 repeat }" == ["https://a.test/stripes.png"]
#guard backgroundUrlsAbsolute "https://a.test/css/s.css" "div{border-image-source:url(b.png)}" ==
  "div{border-image-source:url(\"https://a.test/css/b.png\")}"
#guard backgroundUrlsOf "https://a.test/" "div { list-style: url(m.png) }" == []
#guard backgroundUrlsAbsolute "https://a.test/s.css" "p{background:url(#a),url('#b')}" ==
  "p{background:url(#a),url('#b')}"
#guard backgroundUrlsOf "https://a.test/s.css" "p{background:url(#a),url('icons.svg#b')}" ==
  ["https://a.test/icons.svg#b"]

/-- The document with each `style` attribute's background URLs absolute against `base`. -/
def styleAttributesAbsolute (dom : DOM.Dom) (base : String) : DOM.Dom :=
  if !dom.nodes.any (fun n => n.attrs.any (fun a => a.lname == "style" && (a.value.splitOn "url(").length > 1)) then dom
  else {dom with nodes := dom.nodes.map fun n =>
    if n.attrs.any (fun a => a.lname == "style" && (a.value.splitOn "url(").length > 1) then
      {n with attrs := n.attrs.map fun a => if a.lname == "style" then {a with value := backgroundUrlsAbsolute base a.value} else a}
    else n}

/-- Most background images that a page has fetched. -/
private def maxBackgroundImages : Nat := 64

/-- The text of a document's sheets, read as one. -/
def sheetSource (sheets : List (String × String)) : String := String.intercalate "\n" (sheets.map (·.2))

/-- The rules of sheets in `env`: `CSS.parseIn env`, with the sheets read once (`sheetIn`). -/
def rulesOfSheets (kept : Kept) (env : Rendering.MediaQuery.Env) (sheets : List (String × String)) :
    Except String (List Rendering.CSS.Rule × Made) := do
  -- background URLs absolute against each sheet's own URL, before the sheets are joined
  let (raw,made) := sheetIn kept (sheetSource (sheets.map fun (b,t) => (b,backgroundUrlsAbsolute b t)))
  return (Rendering.CSS.parseInRaw env (← raw),made)

/-- The rules of the document's sheets in `env` (`sheetsIn`). -/
def rulesIn (kept : Kept) (m : WebAccept.Mode) (dom : DOM.Dom) (request : JSON.Json) (env : Rendering.MediaQuery.Env) :
    Except String ((List Rendering.CSS.Rule × Made) × List WebAccept.Diagnostic) := do
  let (sheets,ds) ← sheetsIn m dom request env
  return (← rulesOfSheets kept env sheets,ds)

/-- The rules of a request, in its mode (`WebAccept.accept`), and the sheet it read that
`kept` did not have. `env` is the media environment; with none given, the media type of
the request and no viewport. -/
def rulesWith (kept : Kept) (dom : DOM.Dom) (request : JSON.Json) (env : Rendering.MediaQuery.Env := {medium := medium request}) :
    Except String (List Rendering.CSS.Rule × Made) :=
  (WebAccept.accept (WebAccept.mode request) fun m => rulesIn kept m dom request env).map (·.1)

/-- `rulesWith` with nothing kept. -/
def rules (dom : DOM.Dom) (request : JSON.Json) (env : Rendering.MediaQuery.Env := {medium := medium request}) :
    Except String (List Rendering.CSS.Rule) :=
  Prod.fst <$> rulesWith {} dom request env

/-- The `@font-face` rules of sheets (CSS Fonts 4 §4), URLs resolved. Pages with no
`@font-face` pay one substring search of their sheets. -/
def facesOf (env : Rendering.MediaQuery.Env) (sheets : List (String × String)) : Array Rendering.FontFaceRule.Face :=
  if !sheets.any (fun (_,src) => (src.splitOn "@font-face").length > 1 || (src.toLower.splitOn "@font-face").length > 1) then #[]
  else Rendering.FontFaceRule.ofSheets env.medium Syntax.resolveIri sheets

/-- The resource limit on `@font-face` rules (`FontFaceRule.maxFaces`), when `faces` (of
`facesOf`) is at it: the number of rules the sheets have. Issue 865. -/
def faceLimits (env : Rendering.MediaQuery.Env) (sheets : List (String × String))
    (faces : Array Rendering.FontFaceRule.Face) : List WebAccept.LimitHit :=
  if faces.size < Rendering.FontFaceRule.maxFaces then [] else
  let blocks := sheets.foldl (fun n (_,src) => n + (Rendering.CSS.fontFaceBlocks env.medium src).length) 0
  WebAccept.LimitHit.check "maxFaces" Rendering.FontFaceRule.maxFaces blocks "@font-face rules"

/-- The resource limits of the declarations of `rules` (issue 865), each reported once with the
largest number asked and the number of declarations:
`Content.maxPieces` (a `content` value with more parts is dropped),
`CssVars.maxValueBytes` (a custom property, or a value with `var()` replaced, longer than the limit
is invalid at computed-value time) and `CssVars.maxFallbacks` (`var()` fallbacks nested that deep).
The custom properties are resolved as one flat environment (every rule's, the last winning), so a
value that grows through references is found where its references are found. A declaration of a
`style` attribute is not looked at. -/
def declarationLimits (rules : List Rendering.CSS.Rule) : List WebAccept.LimitHit := Id.run do
  let decls := rules.flatMap (·.declarations)
  let mentioning := decls.filter fun d => Rendering.CssVars.mentions d.value
  let mut pieces := 0
  let mut piecesCount := 0
  for d in decls do
    if d.property == "content" then
      let n := Rendering.CSS.Content.piecesWanted d.value
      if n > Rendering.CSS.Content.maxPieces then
        piecesCount := piecesCount + 1
        pieces := max pieces n
  let mut bytes := 0
  let mut bytesCount := 0
  let mut levels := 0
  let mut levelsCount := 0
  if !mentioning.isEmpty || decls.any (·.property.startsWith "--") then
    let own := decls.filterMap fun d => if d.property.startsWith "--" then some (d.property,d.value) else none
    let vars := Rendering.CssVars.resolve {} own
    for d in decls do
      if d.property.startsWith "--" && d.value.utf8ByteSize > Rendering.CssVars.maxValueBytes then
        bytesCount := bytesCount + 1
        bytes := max bytes d.value.utf8ByteSize
      else if Rendering.CssVars.mentions d.value then
        let reached := (Rendering.CssVars.substituteR vars.find Rendering.CssVars.maxFallbacks d.value).2
        if reached > Rendering.CssVars.maxValueBytes then
          bytesCount := bytesCount + 1
          bytes := max bytes reached
        let deep := Rendering.CssVars.fallbackLevels d.value
        if deep > Rendering.CssVars.maxFallbacks then
          levelsCount := levelsCount + 1
          levels := max levels deep
  return WebAccept.LimitHit.check "maxPieces" Rendering.CSS.Content.maxPieces pieces s!"{piecesCount} content values with too many parts"
    ++ WebAccept.LimitHit.check "maxValueBytes" Rendering.CssVars.maxValueBytes bytes s!"{bytesCount} custom property values longer than the limit"
    ++ WebAccept.LimitHit.check "maxFallbacks" Rendering.CssVars.maxFallbacks levels s!"{levelsCount} values with var() fallbacks nested too deep"

/-- The resource limit on the tracks of a grid axis (`Grid.maxTracks`): an axis with more fixed
tracks than that (a `repeat(n, …)` counts `n` times) has the rest cut. One report, with the most
tracks asked and the number of axes. An automatic repetition is not counted
(`TrackList.tracksWanted`). Issue 865. -/
def gridLimits (styles : Array Rendering.CSS.Computed) : List WebAccept.LimitHit := Id.run do
  let mut most := 0
  let mut count := 0
  for st in styles do
    if st.grid.templateColumns.entries.isEmpty && st.grid.templateRows.entries.isEmpty then continue
    for list in [st.grid.templateColumns, st.grid.templateRows] do
      let n := list.tracksWanted
      if n > Rendering.Grid.maxTracks then
        count := count + 1
        most := max most n
  return WebAccept.LimitHit.check "maxTracks" Rendering.Grid.maxTracks most s!"{count} grid track lists"

/-- The `@font-face` rules of the document's sheets, in the request's mode. -/
def fontFaces (dom : DOM.Dom) (request : JSON.Json) (env : Rendering.MediaQuery.Env := {medium := medium request}) :
    Except String (Array Rendering.FontFaceRule.Face) :=
  (WebAccept.accept (WebAccept.mode request) fun m => sheetsIn m dom request env).map (facesOf env ·.1)

/-- The faces of a page that a host fetches, one answer a face: those its rules name
(`declared`, `FontFaceRule.declaredFaces`) and those its text uses now (`used`). `used` is
asked only when some face is not named by a rule: it needs the computed style of every
element, a cascade of the whole page (0.5 to 1.6 s of the load of a large page), and when
every face is named its answer changes nothing. A page that `used` would refuse is then not
refused here; its layout says why. -/
def facesFetched (declared : Array Bool) (used : Unit → Except String (Array Bool)) : Except String (Array Bool) :=
  if declared.all id then pure declared else
    (used ()).map fun u => u.mapIdx fun i x => x || declared.getD i false

/-- Kind: cost. Says: when the page's rules name every one of its faces, the faces to
fetch are answered without asking which the text uses: no cascade is made for the
`fontFaces` question. Does not say: how many faces a page has (the reader bounds them). -/
theorem facesFetched_declared (declared : Array Bool) (used : Unit → Except String (Array Bool))
    (h : declared.all id = true) : facesFetched declared used = pure declared := by
  unfold facesFetched
  rw [if_pos h]

/-- The rules of the `style` elements of each connected shadow tree (CSS Scoping 1 §3.1),
each rule with that shadow root as its scope. A text the engine keeps (`sheetIn`) is not read
again; a new one is read on each layout and not kept (the engine's `Made` holds one sheet,
the document's). -/
def shadowRulesIn (kept : Kept) (dom : DOM.Dom) (env : Rendering.MediaQuery.Env) : List Rendering.CSS.Rule := Id.run do
  let mut out : List Rendering.CSS.Rule := []
  for sr in [0:dom.size] do
    if dom.isShadowRoot sr && dom.connected sr then
      let mut sheets : List String := []
      for id in dom.treeOrder sr do
        if DOM.Dom.isHtmlElement (dom.get id) "style" then
          match activeSheetIn .liberal env (dom.get id) id with
          | .ok (true,_) => sheets := ((dom.textContent id).getD "") :: sheets
          | _ => pure ()
      if !sheets.isEmpty then
        let rules := ((sheetIn kept (String.intercalate "\n" sheets.reverse)).1).toOption.getD []
        out := out ++ (Rendering.CSS.parseInRaw env rules).map fun r => {r with scope := some sr}
  return out

/-- A page with a shadow host is laid out on its flat tree, with its node tree for
selectors, and with the rules of its shadow trees (CSS Scoping 1). A page with none takes
none of this (`DOM.Dom.flat_eq_of_noShadow`, `CSS.computeFor_none`). -/
def flatView (kept : Kept) (dom : DOM.Dom) (env : Rendering.MediaQuery.Env) (rules : List Rendering.CSS.Rule) :
    DOM.Dom × List Rendering.CSS.Rule × Option Rendering.CSS.TreeScope :=
  if dom.hasShadow then (dom.flat, rules ++ shadowRulesIn kept dom env, some (Rendering.CSS.TreeScope.of dom))
  else (dom, rules, none)

/-- Script MIME classification has one owner: the Lean scripting snapshot.
All callers use its normalized kind, including whitespace/case and legacy
classic JavaScript MIME types. The host fetches the `src` of the classic scripts; module
scripts and their imports are fetched by the script session (`LeanJSModules`, CORS mode).
With `scripting` off, every page script, classic or module, is a skip point. -/
private def classicScriptsIn (m : WebAccept.Mode) (scripting : Bool) (scripts : List JSON.Json) :
    Except String (List JSON.Json × List WebAccept.Diagnostic) := do
  let classic := scripts.filter (fun script => str script "kind" == "classic")
  let modules := scripts.filter (fun script => str script "kind" == "module")
  if !scripting && !(classic.isEmpty && modules.isEmpty) then
    let (_,d) ← WebAccept.skip m .scriptsOff s!"{classic.length + modules.length} page scripts"
      "page scripts are off in this browser; this page is refused" ()
    return ([],d)
  return (classic,[])

/-- The classic scripts of a request, in its mode. -/
private def classicScripts (request : JSON.Json) (scripts : List JSON.Json) : Except String (List JSON.Json) :=
  (WebAccept.accept (WebAccept.mode request) fun m => classicScriptsIn m (scripting request) scripts).map (·.1)

/-- Whether an element of the page has an attribute with no namespace whose name is `on` and
one or more letters: the names of the event handler content attributes (HTML §8.1.8.1). -/
def hasHandlerAttributes (dom : DOM.Dom) : Bool :=
  (dom.treeOrder 0).any fun id =>
    let n := dom.get id
    n.type == .element && n.attrs.any fun a =>
      a.ns.isNone && a.lname.length > 2 && a.lname.startsWith "on" && (a.lname.drop 2).all Char.isAlpha

def inspectIn (m : WebAccept.Mode) (dom : DOM.Dom) (url : String) (scripting : Bool) :
    Except String (JSON.Json × List WebAccept.Diagnostic) := do
  let base := baseURL dom url
  let snapshot := WebRenderScript.snapshot dom
  let mut sheets : List JSON.Json := []
  let mut ds : List WebAccept.Diagnostic := []
  for id in dom.treeOrder 0 do
    let n := dom.get id
    -- The host fetches the sheets of the screen and of print: it prints the page it shows.
    if stylesheet n && Rendering.CSS.hasAttribute n "href" then
      let (fetch,d) ← fetchSheetIn m n id
      ds := ds ++ d
      if fetch then
        sheets := .object [("nodeId",.number (toString id)),("href",.string (attr n "href")),
          ("url",.string (Syntax.resolveIri base (attr n "href")))]::sheets
  let records := WebRenderScript.scriptRecords dom
  let (scripts,d) ← classicScriptsIn m scripting records
  -- Module scripts: the script session fetches them (`LeanJSModules`), so they are not in
  -- `scripts`; their count tells the host to start a session at load (issue 1161: a page whose
  -- only script was a module ran it only after the first press).
  let modules := if scripting then (records.filter (fun s => str s "kind" == "module")).length else 0
  let scripts := scripts.map fun script =>
    match script with
    | .object fields => .object (fields ++ [("url",.string (Syntax.resolveIri base (str script "src")))])
    | other => other
  return (.object [("nodes",(snapshot.field? "nodes").getD (.array [])),
    ("scripts",.array scripts),("modules",.number (toString modules)),
    -- An event handler content attribute (HTML §8.1.8.1) is page script too: `<body onload>`
    -- runs with no script element, so the host starts a script session for it.
    ("handlers",.bool (scripting && hasHandlerAttributes dom)),
    ("stylesheets",.array sheets.reverse),("images",.array (← imageRequests dom base)),
    ("baseURL",.string base),("title",.string (documentTitle dom)),
    ("icon",match iconURL dom base with | some url => .string url | none => .null)],ds ++ d)

/-- The URLs of the sheets that the page's sheets import, at any depth through the sheets
the request gives (`imported`), and that it does not give: what a host fetches next
(`imports` of `inspect`). The page's sheets are its `style` elements and the linked sheets
the request supplies. At most `ImportTree.maxSheets`. -/
def importsLacking (dom : DOM.Dom) (url : String) (request : JSON.Json) : List String :=
  match importedSheets request with
  | .error _ => []
  | .ok given =>
    let base := baseURL dom url
    let texts : List (String × String) := (dom.treeOrder 0).toList.filterMap fun id =>
      let n := dom.get id
      if DOM.Dom.isHtmlElement n "style" then some (base,(dom.textContent id).getD "")
      else if stylesheet n && Rendering.CSS.hasAttribute n "href" then
        match supplied request id with
        | .ok (some text) => some ((suppliedURL request id).getD base,text)
        | _ => none
      else none
    (texts.flatMap fun (from_,text) =>
      Rendering.ImportTree.lackingOf importEdges Syntax.resolveIri (fun u => given.lookup u) from_ text).eraseDups.take
        Rendering.ImportTree.maxSheets

/-- The background images of a page that a host fetches (`backgroundImages` of `inspect`):
the background URLs of its `style` elements, of its `style` attributes, and of the linked and
imported sheets the request gives, each against its own base; at most
`maxBackgroundImages`, `data:` URLs left out (the engine decodes those itself). -/
def backgroundImageRequests (dom : DOM.Dom) (url : String) (request : JSON.Json) : List String :=
  let base := baseURL dom url
  let given := (importedSheets request).toOption.getD []
  let texts : List (String × String) := (dom.treeOrder 0).toList.flatMap fun id =>
    let n := dom.get id
    let own := match n.attrs.find? (·.lname == "style") with
      | some a => [(base,a.value)]
      | none => []
    if DOM.Dom.isHtmlElement n "style" then (base,(dom.textContent id).getD "") :: own
    else if stylesheet n && Rendering.CSS.hasAttribute n "href" then
      match supplied request id with
      | .ok (some text) => ((suppliedURL request id).getD base,text) :: own
      | _ => own
    else own
  ((texts ++ given).flatMap fun (b,t) => backgroundUrlsOf b t).eraseDups.filter
    (!·.toLower.startsWith "data:") |>.take maxBackgroundImages

/-- What the host fetches for a page, in the mode of `request`. In liberal mode the answer
has `diagnostics`, the skips (`WebAccept.Diagnostic.json`), when there are any. With sheets
that import others, `imports`: the URLs of the imported sheets the request does not give.
With background images in its sheets or styles, `backgroundImages` (`{key,url}`). -/
def inspect (dom : DOM.Dom) (url : String) (request : JSON.Json := .object []) : Except String JSON.Json := do
  let (answer,ds) ← WebAccept.accept (WebAccept.mode request) fun m => inspectIn m dom url (scripting request)
  let lacking := importsLacking dom url request
  let backgrounds := backgroundImageRequests dom url request
  let more : List (String × JSON.Json) :=
    (if lacking.isEmpty then [] else [("imports",.array (lacking.map fun u => .object [("url",.string u)]))]) ++
    (if backgrounds.isEmpty then [] else [("backgroundImages",.array (backgrounds.map fun u => .object [("key",.string u),("url",.string u)]))]) ++
    (if ds.isEmpty then [] else [("diagnostics",WebAccept.diagnosticsJSON ds)])
  match answer with
  | .object fields => return .object (fields ++ more)
  | _ => return answer

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
    -- `selectionClicks`: the click count of the press (issue 1031): 2 whole words, 3 lines.
    let clicks := match request.field? "selectionClicks" with | some (.number n) => n.toNat?.getD 0 | _ => 0
    pure (some (WebSelection.Selection.ofClicks clicks ax ay fx fy))

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
on the same frame send the same text. One slot (`Engine.links`), by string equality:
`Links.decode text`, with the regions of the last text again when the text is equal. -/
def decodeKept (kept : Option (String × List Rendering.LinkRegion)) (text : String) :
    Option (String × List Rendering.LinkRegion) × Except String (List Rendering.LinkRegion) :=
  match kept with
  | some (k,regions) => if k == text then (kept,.ok regions) else fresh
  | none => fresh
where fresh := match Rendering.Links.decode text with
  | .ok regions => (some (text,regions),.ok regions)
  | .error e => (kept,.error e)

/-- A slot is valid when its regions are the decoding of its text. -/
def LinksValid (kept : Option (String × List Rendering.LinkRegion)) : Prop :=
  ∀ k r, kept = some (k,r) → Rendering.Links.decode k = .ok r

/-- Refinement: from a valid slot, `decodeKept` answers `Links.decode text`. -/
theorem decodeKept_eq (kept : Option (String × List Rendering.LinkRegion)) (valid : LinksValid kept) (text : String) :
    (decodeKept kept text).2 = Rendering.Links.decode text := by
  unfold decodeKept decodeKept.fresh
  rcases kept with _ | ⟨k,regions⟩
  · simp only; split <;> simp_all
  · simp only
    split
    · next h => have := valid k regions rfl; simp_all
    · split <;> simp_all

/-- Invariant: the slot `decodeKept` leaves is valid. -/
theorem decodeKept_valid (kept : Option (String × List Rendering.LinkRegion)) (valid : LinksValid kept) (text : String) :
    LinksValid (decodeKept kept text).1 := by
  unfold decodeKept decodeKept.fresh
  rcases kept with _ | ⟨k,regions⟩
  · simp only; split
    · next h => intro a b e; simp_all
    · exact valid
  · simp only
    split
    · exact valid
    · split
      · next h => intro a b e; simp_all
      · exact valid

/-- `Links.pick` over the engine's kept regions (the C shim's `web_render_hit`). -/
def pickIn (links : Option (String × List Rendering.LinkRegion)) (regions : String) (width height : UInt32) (x y : Float) :
    Option (String × List Rendering.LinkRegion) × String :=
  if !x.isFinite || !y.isFinite || x < 0 || y < 0 ||
    x >= Float.ofNat width.toNat || y >= Float.ofNat height.toNat then (links,"null")
  else match decodeKept links regions with
    | (links,.error message) => (links,"{\"error\":" ++ "\"" ++ JSON.escapeString message ++ "\"" ++ "}")
    | (links,.ok regions) => (links,Rendering.Links.targetJSON (Rendering.hitLink regions x y))

/-- Refinement: from a valid slot, `pickIn` answers `Links.pick`. -/
theorem pickIn_eq (links : Option (String × List Rendering.LinkRegion)) (valid : LinksValid links)
    (regions : String) (width height : UInt32) (x y : Float) :
    (pickIn links regions width height x y).2 = Rendering.Links.pick regions width height x y := by
  have h := decodeKept_eq links valid regions
  unfold pickIn Rendering.Links.pick
  split
  · rfl
  · revert h; cases decodeKept links regions with
    | mk l r => cases r <;> intro h <;> simp only at h <;> rw [← h] <;> rfl

/-- The answer to `press`: `control` for a chrome control; `sourceNode` and `href` for a
link of the page layer (`linksText` or `links`, in band rows, as the frame answered them, picked at
`(x,row)`); `rects` for the composite. -/
def press (decode : String → Except String (List Rendering.LinkRegion)) (request : JSON.Json) : Except String String := do
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
    -- `linksText`: the regions as the frame gave them, decoded once per frame (`decodeKept`);
    -- `links`: the same as a JSON array, decoded on each call (older hosts).
    let regions ← match request.field? "linksText",request.field? "links" with
      | some (.string text),_ => decode text
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

/-- `zoomUnit`: the screen's device pixels for each CSS pixel, in percent; 100 if absent.
A render request with it lays the page out in CSS pixels and draws it at this ratio
(`layOut`, section "Device pixels"). -/
def zoomUnit (request : JSON.Json) : Nat :=
  match request.field? "zoomUnit" with
  | some (.number n) => match n.toNat? with | some u => if u = 0 then 100 else u | none => 100
  | _ => 100

/-! ### Device pixels (dprfix, 2026-11-09)

A window of `width` device pixels on a screen of `unit`/100 device pixels for each CSS
pixel (`zoomUnit`; 200 on a Retina Mac, 300 on a phone) is `width*100/unit` CSS pixels
wide. Layout happens in CSS pixels: lengths, percentages and media queries all see the
CSS viewport, and the text zoom `textScalePercent` (device pixels of text for each CSS
pixel) is `percent/unit` of CSS text. The scene is then drawn at the ratio: one uniform
scale over the page (`Laid.toDevice`), applied once, after layout, so every length, text,
border and image grows together and the rasterizer draws the vectors at device
resolution. At `unit` 100 none of this runs: the layout and its answer are those of
before. Before, the Hub laid out in device pixels and scaled only the text, so on a 2x
screen a 16px margin drew as 8 CSS px and a 760px column as 380. -/

/-- The text scale of a layout in CSS pixels: the zoom over the screen's ratio, and at
least the 50% that `computeAll` takes. At `unit` 100 it is the zoom, as before. -/
def cssTextScale (percent unit : Nat) : Float :=
  if unit == 100 then Float.ofNat percent / 100
  else max 0.5 (Float.ofNat percent / Float.ofNat (max 1 unit))

/-- What layout reads of a window: its CSS width, its CSS rows and the zoom of the media
environment (`mediaEnv`), from the window in device pixels, the zoom and the ratio. -/
def layoutInputs (width rows percent unit : Nat) : Nat × Nat × Nat :=
  (width*100/unit,rows*100/unit,percent*100/unit)

/-- Layout does not depend on the device pixel ratio: a window `k` times as many device
pixels on each side, at `k` times the zoom (the same text size to the reader) on a
screen `k` times as dense, is laid out exactly as the 1x window is. -/
theorem layoutInputs_ratio (width rows percent k : Nat) (hk : 0 < k) :
    layoutInputs (width*k) (rows*k) (percent*k) (100*k) = (width,rows,percent) := by
  have cancel : ∀ n : Nat, n*k*100/(100*k) = n := fun n => by
    rw [show n*k*100 = n*(100*k) by rw [Nat.mul_assoc, Nat.mul_comm k 100]]
    exact Nat.mul_div_cancel n (by omega)
  simp only [layoutInputs, cancel]

/-- At `unit` 100 the inputs are the device sizes and the zoom: the layout of before. -/
theorem layoutInputs_unit (width rows percent : Nat) :
    layoutInputs width rows percent 100 = (width,rows,percent) := by
  simp [layoutInputs]

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
private def inputOp {M : Type → Type} [Monad M] [WebWasm.Machine M] (op : String) (request : JSON.Json) : ExceptT String M (Option String) := do
  if op == "textZoom" then return some (← textZoomAnswer request)
  -- The console tab (WebConsole): the page of the entries the host kept for a tab.
  if op == "consolePage" then return some (WebConsole.answer request)
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
    let fields := [("action",JSON.Json.string action)] ++
      (if WebShell.addressCommands.contains action then [("target",JSON.Json.string target)] else []) ++
      [("textScalePercent",.number (toString (WebSelection.commandPercent command percent (zoomUnit request))))] ++ tab ++ scrollTo
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
  -- The default encoding of pages that declare none (WebState.encodingSetting, the
  -- settings page section).
  if op == "encodingSetting" then
    return some (JSON.Json.object [("setting",.string (WebState.encodingSetting (str request "setting")))]).toString
  if op == "encodingChoices" then
    return some (JSON.Json.object [("html",.string (WebState.encodingChoicesHTML (str request "setting") (str request "locale")))]).toString
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
  -- about:foafnaut (WebAbout): the engine writes the page from its own build facts; `host`
  -- is what the desktop program reports ({rows: [[label, value]...], version, commit}),
  -- shown as such. `engineBuild`: the facts, the --version line, and the line that says
  -- when the host's record disagrees.
  if op == "aboutPage" || op == "engineBuild" then
    let h := (request.field? "host").getD .null
    let text := fun (j : JSON.Json) (key : String) => match j.field? key with
      | some (.string v) => some v | _ => none
    let rows : List (String × String) := match h.field? "rows" with
      | some (.array items) => (items.take 32).filterMap fun item => match item with
        | .array [.string k,.string v] => some (k,v) | _ => none
      | _ => []
    let host : WebAbout.Host := {rows,version := text h "version",commit := text h "commit"}
    let e := WebAbout.engine
    if op == "aboutPage" then
      return some (JSON.Json.object [("source",.string (WebAbout.page e host))]).toString
    return some (JSON.Json.object ([("version",.string e.version),("commit",.string e.commit),("builtAt",.string e.builtAt),
      ("dirty",.bool e.dirty),("release",.bool e.release),("line",.string (WebAbout.versionLine e))] ++
      (match WebAbout.mismatch e host with | some m => [("mismatch",.string m)] | none => []))).toString
  -- A key or typed text in the find field (WebShell.findEdit): the text after it and the step.
  if op == "findEdit" then
    let typed := match request.field? "text" with | some (.string t) => some t | _ => none
    let code := match request.field? "key" with | some (.number c) => c.toNat?.getD 0 | _ => 0
    let modifiers := match request.field? "modifiers" with | some (.number m) => m.toNat?.getD 0 | _ => 0
    let (query,step) := WebShell.findEdit (str request "query") typed code modifiers
    return some (JSON.Json.object [("query",.string query),("step",.string step.name)]).toString
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
  -- The context menu of a press on the page (issue 1031; WebShell.openContext): `link` is the
  -- address of the link under the press in the frame on screen (null: none), `selection`
  -- whether the page has a selection. The answer is the edit state with the menu open.
  if op == "shellContext" then
    let link := match request.field? "link" with | some (.string h) => if h.isEmpty then none else some h | _ => none
    let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
    return some (shell.openContext link (request.field? "selection" == some (.bool true))).editJson.toString
  -- The key table for a host with no menu, which must decide at once which keys it keeps.
  if op == "keyTable" then
    let platform := str request "platform" "other"
    return some (JSON.Json.array ((WebHistory.keyTable.filter (·.1 == platform)).map fun (_,m,k,c) =>
      .object [("modifier",.string m),("key",.string k),("command",.number (toString c))])).toString
  -- What a press does by its button and modifiers (issue 1031): follow, a tab, or the menu.
  if op == "linkGesture" then
    let num (k : String) : Nat := match request.field? k with | some (.number n) => n.toNat?.getD 0 | _ => 0
    return some (JSON.Json.object [("gesture",.string (WebShell.linkGesture (str request "platform" "other") (num "button") (num "modifiers")))]).toString
  if op == "shellSubmit" then return some (WebShell.submit (str request "address")).json.toString
  -- Where the keyboard focus goes when a page commits (issue 1077): "page" or "address".
  if op == "shellCommitFocus" then
    let flag (k : String) : Bool := match request.field? k with | some (.bool b) => b | _ => false
    return some (JSON.Json.object [("focus",.string (WebShell.focusOnCommit (str request "url") (flag "newTab")
      (flag "focused") (flag "typed")))]).toString
  if let some answer ← WebGraph.op op request then return some answer
  if let some answer ← WebEventLoop.op op request then return some answer
  -- Boundary traces of host shells checked against the host contract (WebHostContract).
  if let some answer := WebHostContract.op op request then return some answer
  if op == "sourcePage" then
    return some (JSON.Json.object [("source",.string (WebShell.sourcePage (str request "kind") (str request "url") (str request "source")))]).toString
  if op == "shellLink" then return some (WebShell.link (str request "href")).json.toString
  -- Where a link or an address goes (WebRoute; owner, 2026-11-08): the final action, which
  -- the hosts do with no URL test of their own. `origin` is the site the browser loads
  -- pages from ("" for every site), `pages` its folder of pages, `files` whether it reads
  -- local files, `base` the address of the page the link is on.
  -- `outside` is the address whose Outside page the tab shows ("" for any other page), so a
  -- link to it is that page's button; `search` is the search engine chosen in Settings.
  if op == "shellRoute" then
    let site : WebRoute.Site := {origin := str request "origin",pages := str request "pages",files := (request.field? "files" == some (.bool true)),outside := str request "outside"}
    let route := match request.field? "address" with
      | some (.string address) => WebShell.routeAddress {site with outside := ""} (str request "base") address (str request "search")
      | _ => WebRoute.routeAddress site (str request "base") (str request "href")
    return some (WebShell.routeJson route).toString
  -- Words typed in the address bar (owner, 2026-11-16: no default search engine). The page
  -- `foafnaut:search/WORDS`, from the stored `resources` and the open `tabs` the host passes:
  -- no request is made to show it.
  if op == "searchPage" then
    let words := WebRoute.decodeQuery (str request "argument")
    let tabs := match request.field? "tabs" with
      | some (.array items) => items.filterMap fun t =>
          let url := str t "url"; let title := str t "title"
          if !url.isEmpty && WebState.matchesWords words url title then some ("Open tab", url, title) else none
      | _ => []
    let found := tabs.take WebState.maxFound ++ WebState.searchFoundOf words request
    let stateOn := request.field? "state" == some (.bool true)
    return some (JSON.Json.object [("title",.string (words ++ " (search)")),
      ("source",.string (WebShell.searchPage words found stateOn (str request "search")))]).toString
  if op == "searchChoices" then
    return some (JSON.Json.object [("html",.string (WebShell.searchChoicesHTML (str request "setting")))]).toString
  if op == "searchSetting" then
    let setting := WebRoute.searchSetting (str request "setting")
    return some (JSON.Json.object [("setting",.string setting),("name",.string (WebRoute.searchName setting))]).toString
  if op == "outsidePage" then
    return some (JSON.Json.object [("title",.string "Another site"),
      ("source",.string (WebShell.outsidePage (str request "url") (request.field? "hub" == some (.bool true)) (request.field? "textnaut" == some (.bool true))))]).toString
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
    -- A double or triple click (`clicks`, issue 1031) selects: it is not a click on a link.
    let clicks := match request.field? "clicks" with | some (.number n) => n.toNat?.getD 0 | _ => 0
    let click := WebSelection.isClick ax ay fx fy && WebSelection.granularity clicks == .character
    return some (JSON.Json.object [("action",.string (if click then "click" else "select"))]).toString
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
def nearNodesFlat (top bottom : Float) (nodes : List Rendering.Node) : List Rendering.Node :=
  (nodes.filter (inWindow top bottom)).map (nearInside top bottom)

/-- A uniform scale by more than 0, not 1, with no other part: the one group of a page laid
out in CSS pixels and drawn in device pixels (`Laid.toDevice`). -/
private def isUniformScale (t : Rendering.Transform) : Bool :=
  t.a == t.d && t.a > 0 && t.a != 1 && t.b == 0 && t.c == 0 && t.e == 0 && t.f == 0

/-- `nearNodesFlat`; a page drawn at a device pixel ratio (one top-level group that scales
by `k`) is the same group with its nodes near the window in its own rows, `top/k ..
bottom/k`: the glyphs it keeps are those it keeps at ratio 1. -/
def nearNodes (top bottom : Float) (nodes : List Rendering.Node) : List Rendering.Node :=
  match nodes with
  | [.group id t children] =>
    if isUniformScale t then [.group id t (nearNodesFlat (top/t.a) (bottom/t.a) children)]
    else nearNodesFlat top bottom nodes
  | _ => nearNodesFlat top bottom nodes

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

/-- Kind: equality. Says: the layout text of a page layer (`WebRender.layoutJSON`) is the head
of the page's boxes, glyph runs and face, the same for every band `b`, then the tail of the
layer's links. So the engine may keep the head of one band and write only the tail for
another band of the same layout (`pageArtifactImpl`). Does not say: that the engine keeps it. -/
theorem pageLayer_layoutJSON (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) :
    WebRender.layoutJSON (pageLayer page extra b) boxes face =
      WebRender.layoutHead boxes page.glyphRuns face ++ WebRender.layoutTail (pageLayer page extra b).links :=
  WebRender.layoutJSON_of_head _ _ _ _ rfl

/-- The page layer keeps every link of the page, moved up by the band's top and nothing
else (`LinkTheorems.moveLinks_getElem`, `LinkTheorems.hitLink_band`; issue 1268). -/
theorem pageLayer_links (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band) :
    (pageLayer page extra b).links = Rendering.moveLinks (· - Float.ofNat b.top) page.links := rfl

/-- The chrome layer: window rows `0 .. WebShell.height`. -/
def chromeLayer (shell : WebShell.Shell) (page : Rendering.Scene) (width : Nat)
    (addressFont : WebShell.AddressFont := {}) : Rendering.Scene :=
  let top := max 1 (WebShell.height shell width)
  {page with
    height := top
    mapping := {page.mapping with viewportHeight := Float.ofNat top}
    tree := WebShell.nodes shell width addressFont
    glyphRuns := #[]
    links := #[]}

/-- The chrome top the band of a folding chrome is made for: the folded strip, the
smallest the chrome gets (`WebShell.strip_le_height`). -/
def bandTop (shell : WebShell.Shell) (width : Nat) : Nat :=
  WebShell.height {shell with collapse := 100} width

/-- The chrome layer alone, for a change of `collapse` (op `chromeLayer`): its scene is the
chrome's nodes, rows `0 .. top`. No layout and no page. -/
def chromeScene (shell : WebShell.Shell) (width : Nat)
    (addressFont : WebShell.AddressFont := {}) : Rendering.Scene :=
  let top := max 1 (WebShell.height shell width)
  {width,height := top,mapping := {viewportWidth := Float.ofNat width,viewportHeight := Float.ofNat top},
   tree := WebShell.nodes shell width addressFont}

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
  /-- The compile of the band's primitives, for the next frame (`WebPaint.retainedAnswer`). -/
  retained : Option WebPaint.RetainedLayer := none
  /-- `layoutJSON` of this frame: the next frame with the same layout gives it again. -/
  layoutText : String := ""
  /-- The number that `damage.id` answers: a host that drew answer `id` can draw a later
  answer with `damage.base = id` by its damage rectangles alone. -/
  id : Nat := 0
  /-- `WebRender.layoutHead` of this frame's boxes, glyph runs and face: the part of
  `layoutText` that every band of the layout shares (`WebRender.layoutJSON_of_head`); empty
  when not made. -/
  layoutHead : String := ""
  /-- Made with the boxes, glyph runs and links left out of the text (`layoutSections`). -/
  layoutOff : Bool := false

/-- Page layer answers kept: the last two, for a chrome change and back. -/
def keptPageSlots : Nat := 2

/-- The page layer answers an engine keeps (`pageArtifact`), a field of `Engine`, so each
engine session has its own (docs/designissues/2026-11-26-foafnaut-engine-sessions.md, D2;
before, three `initialize` cells of the process). -/
structure KeptPages where
  /-- The last `keptPageSlots` answers, newest first. -/
  pages : List KeptPage := []
  /-- Page layers made and given again; then primitives compiled again, kept and moved with
  their geometry kept by the retained compile (op `frameWork`). -/
  work : Nat × Nat × Nat × Nat × Nat := (0,0,0,0,0)
  /-- The last number given to `damage.id`. -/
  lastId : Nat := 0

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
private unsafe def pageArtifactImpl (kp : KeptPages) (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) (live : Bool)
    (form : NativeSVG.DataForm) (checks tree : Bool) (retainOn : Bool := true) (layoutOff : Bool := false) :
    KeptPages × Except String (String × Array ByteArray) := Id.run do
    let same := fun (k : KeptPage) => ptrEq k.page page && ptrEq k.boxes boxes && ptrEq k.face face &&
      ptrEq k.extra extra && k.band == b && k.live == live && formSame k.form form && k.checks == checks && k.tree == tree &&
      (retainOn || k.retained.isNone) && k.layoutOff == layoutOff
    let kept := kp.pages
    match kept.find? same with
    | some k =>
      return ({kp with work := let (m,g,x) := kp.work; (m,g+1,x)},.ok k.answer)
    | none =>
      let layer := pageLayer page extra b
      -- The retained compile only for a frame host's answer: sections, no probes, no tree.
      -- `pageArtifact` (the reference) stays the plain path, that `partial_frame_test.ts`
      -- compares this with.
      let previous : Option KeptPage := kept.find? fun (k : KeptPage) => k.band == b && k.live == live && formSame k.form form && k.checks == checks && k.tree == tree && k.retained.isSome &&
        k.layoutOff == layoutOff
      match form,checks,tree,retainOn with
      | .sections first,false,false,true =>
        let layoutText := previous.bind fun k =>
          if ptrEq k.boxes boxes && ptrEq k.face face && ptrEq k.page.links page.links && ptrEq k.page.glyphRuns page.glyphRuns then
            some k.layoutText else none
        -- Another band of the same layout: the head of its layout text is this one's
        -- (the layer's glyph runs are the page's, and the
        -- head reads no link: `pageLayer_layoutJSON`); only the links, moved for the band,
        -- are written again.
        let (layoutText,head) := if layoutOff then (WebRender.layoutHeadOnly face,"") else match layoutText with
          | some text => (text,(previous.map fun (k : KeptPage) => k.layoutHead).getD "")
          | none =>
            let head := match kept.find? fun (k : KeptPage) => !k.layoutHead.isEmpty && ptrEq k.boxes boxes && ptrEq k.face face &&
                ptrEq k.page.glyphRuns page.glyphRuns with
              | some k => k.layoutHead
              | none => WebRender.layoutHead boxes page.glyphRuns face
            (head ++ WebRender.layoutTail layer.links,head)
        -- A layout makes every primitive a new object: the address test first, then the
        -- values (`WebPaint.samePrimitive`, proved to hold only of equal primitives; bitmaps
        -- by address, as the paint table keeps one per image).
        let bitmaps := fun (x y : Rendering.Bitmap) => ptrEq x y
        let reuseLeaf := fun (a b : WebPaint.LeafKey) =>
          if (ptrEq a.primitive b.primitive || WebPaint.samePrimitive bitmaps a.primitive b.primitive) && a.sameContext b then NativeSVG.Reuse.same
          else if (ptrEq a.primitive.geometry b.primitive.geometry || decide (a.primitive.geometry = b.primitive.geometry)) &&
              (ptrEq a.primitive.style b.primitive.style || WebPaint.sameStyle bitmaps a.primitive.style b.primitive.style) then a.movedOf b
          else NativeSVG.Reuse.different
        match WebPaint.retainedAnswer reuseLeaf (previous.bind (·.retained)) layer boxes face first (some layoutText) with
        | .error e => return (kp,.error e)
        | .ok (retained,damage,value,sections,layout,recompiled,moved) =>
          let id := kp.lastId+1
          let number := fun (n : Nat) => toString n
          let damageText := "{\"id\":" ++ number id ++ ",\"base\":" ++
            (match previous.bind (·.retained),damage with
             | some _,some _ => number ((previous.map fun (k : KeptPage) => k.id).getD 0)
             | _,_ => "null") ++ ",\"rects\":" ++
            (match damage with | some rects => NativeSVG.damageJSON rects | none => "null") ++ "}"
          let value := (value.dropEnd 1).toString ++ ",\"damage\":" ++ damageText ++ "}"
          let answer := (value,sections)
          let pages := (((⟨page,extra,b,boxes,face,live,form,checks,tree,answer,some retained,layout,id,head,layoutOff⟩ : KeptPage) :: kept).take keptPageSlots)
          let (m,g,a,r,c) := kp.work
          return ({pages,work := (m+1,g,a+recompiled,r+(retained.items.size-recompiled-moved),c+moved),lastId := id},.ok answer)
      | _,_,_,_ =>
        let made := WebRender.artifactWith (WebPaint.cull layer) boxes face live form checks tree layoutOff
        match made with
        | .ok answer =>
          let work := let (m,g,x) := kp.work; (m+1,g,x)
          return ({kp with pages := (⟨page,extra,b,boxes,face,live,form,checks,tree,answer,none,"",0,"",layoutOff⟩ :: kept).take keptPageSlots, work},made)
        | .error _ => return (kp,made)

/-- The page layer of a layers answer. Its value is `artifactWith` of the band of the page,
with its curves off the band made lines (`WebPaint.cull`: the same pixels, fewer edges for a
zoomed group);
the engine gives a kept answer again when the inputs are the same objects (a frame whose
only change is in the chrome: loading, the address, a pressed chrome control, the menu).
The kept answers are the engine's own (`kp`, `Engine.pages`); the reference body keeps none. -/
@[implemented_by pageArtifactImpl]
def pageArtifact (kp : KeptPages) (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) (live : Bool)
    (form : NativeSVG.DataForm) (checks tree : Bool) (_retainOn : Bool := true) (layoutOff : Bool := false) :
    KeptPages × Except String (String × Array ByteArray) :=
  (kp,WebRender.artifactWith (WebPaint.cull (pageLayer page extra b)) boxes face live form checks tree layoutOff)

/-- Kind: equality. Says: the answer of `pageArtifact` (its reference body) is `artifactWith` of
the culled page layer, whatever the kept answers. Does not say: what the implementation keeps. -/
theorem pageArtifact_eq (kp : KeptPages) (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) (live : Bool)
    (form : NativeSVG.DataForm) (checks tree retainOn layoutOff : Bool) :
    (pageArtifact kp page extra b boxes face live form checks tree retainOn layoutOff).2 =
      WebRender.artifactWith (WebPaint.cull (pageLayer page extra b)) boxes face live form checks tree layoutOff := rfl

/-- A data form as numbers, for the keys of kept answers. -/
def formCode : NativeSVG.DataForm → Nat × Nat
  | .decimal => (0,0)
  | .base64 => (1,0)
  | .sections k => (2,k)
  | .sectionsCpu k => (3,k)

/-- The mapping, bit for bit. -/
def mappingBits (m : Rendering.Mapping) : List UInt64 :=
  [m.sx.toBits,m.sy.toBits,m.tx.toBits,m.ty.toBits,m.minX.toBits,m.minY.toBits,m.viewportWidth.toBits,m.viewportHeight.toBits]

/-- What the chrome layer answer (`chromeArtifact`) reads: the shell; the window width; of the
page, only its width and mapping (`chromeLayer` replaces the rest); the held fonts, whose
monospace face gives the address font (`Holds.fontNames` names it with its SHA-256); of the
face, only what the layout header writes (`WebRender.layoutHeader`); and the flags. Issue
https://github.com/danbri/factoidal-core/issues/1124, stage A. -/
structure ChromeKey where
  shell : WebShell.Shell
  width : Nat
  pageWidth : Nat
  mapping : List UInt64
  fonts : List (String × String)
  face : Option (String × Nat × String × String × UInt64)
  live : Bool
  form : Nat × Nat
  checks : Bool
  tree : Bool
  deriving BEq

/-- The fields of a face that the layout header writes. -/
def faceHeader (face : Option Rendering.FontProvider.Face) : Option (String × Nat × String × String × UInt64) :=
  face.map fun f => (f.fontSha256,f.faceIndex,f.family,f.style,f.unitsPerEm.toBits)

/-- What an answer with no layers (`plainArtifact`) reads, for a scene that is the layout's own
(`Laid.scene`, no paint values) and no marks: the layout's number (`Laid.serial`: the engine
gives each layout and each painted pointer state its own number, so the number names the
scene, the boxes and the face), the shell, the sizes, the held fonts (the address font) and
the flags. -/
structure PlainKey where
  serial : Nat
  shell : Option WebShell.Shell
  width : Nat
  height : Nat
  fonts : List (String × String)
  live : Bool
  form : Nat × Nat
  checks : Bool
  tree : Bool
  deriving BEq

/-- The chrome layer of a layers answer. -/
def chromeArtifact (shell : WebShell.Shell) (page : Rendering.Scene) (width : Nat)
    (addressFont : WebShell.AddressFont) (face : Option Rendering.FontProvider.Face) (live : Bool)
    (form : NativeSVG.DataForm) (checks tree : Bool) : Except String (String × Array ByteArray) :=
  WebRender.artifactWith (chromeLayer shell page width addressFont) #[] face live form checks tree

/-- The answer of a render with no layers: the page near the scroll with the marks, under the
chrome when there is a shell. -/
def plainArtifact (scene : Rendering.Scene) (marks : List Rendering.Node) (shell : Option WebShell.Shell)
    (width height : Nat) (addressFont : WebShell.AddressFont) (boxes : Array Rendering.Layout.Box)
    (face : Option Rendering.FontProvider.Face) (live : Bool) (form : NativeSVG.DataForm) (checks tree : Bool) :
    Except String (String × Array ByteArray) :=
  let scrolled := Float.ofNat ((shell.map (·.scroll)).getD 0)
  let near := nearNodes (scrolled-512) (scrolled+Float.ofNat height+512) scene.tree
  let page := {scene with tree := near ++ marks}
  WebRender.artifactWith (WebPaint.cull (match shell with
    | some value => WebShell.compose value page width height addressFont
    | none => page)) boxes face live form checks tree

/-- The `damage.id` that a retained page layer answer ends with (`pageArtifact`: its text ends
`"damage":{"id":N,...}}`); `none` for an answer with no damage (the plain path). The pattern
holds quote marks, which JSON writes escaped inside a string, so only the damage object matches. -/
def pageAnswerId (text : String) : Option Nat :=
  match (text.splitOn "\"damage\":{\"id\":").getLast? with
  | none => none
  | some tail =>
    if tail.length == text.length then none
    else (String.ofList (tail.toList.takeWhile Char.isDigit)).toNat?

#guard pageAnswerId "{\"a\":1,\"damage\":{\"id\":42,\"base\":null,\"rects\":null}}" == some 42
#guard pageAnswerId "{\"a\":\"\\\"damage\\\":{\\\"id\\\":7\"}" == none
#guard pageAnswerId "{\"abi\":1}" == none

/-- Whether the 8 bytes at `p` differ: `ldU64LE` of each (bytes past the end read 0). -/
def wordsDifferRef (old new : ByteArray) (p : USize) : Bool :=
  Prim.Bytes.ldU64LE old p != Prim.Bytes.ldU64LE new p

/-- `wordsDifferRef` with one 8-byte load from each array where the word is inside both
(`Prim.Bytes.ldU64LEIn`, C), by the `USize` window test of `ldU64LE`. Equal to the reference:
`wordsDiffer_eq`. -/
@[inline] def wordsDiffer (old new : ByteArray) (p : USize) : Bool :=
  if h : p < p + 8 ∧ p + 8 ≤ old.usize ∧ p + 8 ≤ new.usize then
    have win : ∀ (d : ByteArray), p + 8 ≤ d.usize → p.toNat + 8 ≤ d.usize.toNat := fun d hd => by
      have a := USize.le_iff_toNat_le.mp hd
      rw [Prim.Bytes.usize_add_small h.1 8 (by rw [Prim.Bytes.usize_eight_toNat]; omega), Prim.Bytes.usize_eight_toNat] at a
      exact a
    Prim.Bytes.ldU64LEIn old p (win old h.2.1) != Prim.Bytes.ldU64LEIn new p (win new h.2.2)
  else wordsDifferRef old new p

theorem wordsDiffer_eq : wordsDiffer = wordsDifferRef := by
  funext old new p
  unfold wordsDiffer
  split
  · simp only [wordsDifferRef, ← Prim.Bytes.ldU64LE_eq_in]
  · rfl

/-- The first word index from `w` (below `words`) whose 8 bytes differ (`differs` at byte
`8*w`), or `words`. `USize` indices: a loop with no allocation. -/
@[specialize] def nextDiffering (differs : ByteArray → ByteArray → USize → Bool) (old new : ByteArray) (words w : USize) : USize :=
  if h : w < words then
    if differs old new (8*w) then w else nextDiffering differs old new words (w+1)
  else words
termination_by words.toNat - w.toNat
decreasing_by have := Prim.Bytes.usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega

/-- The first word index from `w` (below `words`) whose 8 bytes are the same, or `words`. -/
@[specialize] def nextSame (differs : ByteArray → ByteArray → USize → Bool) (old new : ByteArray) (words w : USize) : USize :=
  if h : w < words then
    if differs old new (8*w) then nextSame differs old new words (w+1) else w
  else words
termination_by words.toNat - w.toNat
decreasing_by have := Prim.Bytes.usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega

/-- The ranges of differing words from word `w` on, after `out`; a run of differing words that
starts at most `gap` bytes after the last range ends joins it. One step per run; `fuel` bounds
the steps (each step moves past at least one word, so `words+1` is enough). -/
@[specialize] def wordRanges (differs : ByteArray → ByteArray → USize → Bool) (old new : ByteArray) (words : USize) (gap : Nat) :
    Nat → USize → Array (Nat × Nat) → Array (Nat × Nat)
  | 0, _, out => out
  | fuel+1, w, out =>
    let s := nextDiffering differs old new words w
    if s < words then
      let e := max (s+1) (nextSame differs old new words s)
      let (s,e) := (s.toNat,e.toNat)
      match out.back? with
      | some (o,l) =>
        if 8*s ≤ o+l+gap then wordRanges differs old new words gap fuel e.toUSize (out.pop.push (o,8*e-o))
        else wordRanges differs old new words gap fuel e.toUSize (out.push (8*s,8*(e-s)))
      | none => wordRanges differs old new words gap fuel e.toUSize (out.push (8*s,8*(e-s)))
    else out

/-- The byte ranges `(offset, length)` where `new` differs from `old`, for two arrays of one size
(issue 1124, stage C), with `differs` the test of one 8-byte word: the word ranges
(`wordRanges`), then the last bytes one by one. A run that starts at most `gap` bytes after the
last one ends joins it. Offsets and lengths are multiples of 4 when the size is. -/
@[specialize] def changedRangesWith (differs : ByteArray → ByteArray → USize → Bool) (old new : ByteArray) (gap : Nat := 64) :
    Array (Nat × Nat) := Id.run do
  let size := new.size
  let words := size / 8
  -- Word indices in `USize`: an array's size is below `USize.size`, so `words` is exact.
  let mut out := wordRanges differs old new words.toUSize gap (words+1) 0 #[]
  for i in [8*words:size] do
    if old.get! i != new.get! i then
      let at_ := i - i % 4
      match out.back? with
      | some (o,l) =>
        if at_ ≤ o+l+gap then out := out.pop.push (o,max (o+l) (min size (at_+4))-o)
        else out := out.push (at_,min size (at_+4)-at_)
      | none => out := out.push (at_,min size (at_+4)-at_)
  return out

/-- `changedRangesWith` with the fast word test; the same ranges as with the reference test
(`changedRanges_eq`). -/
def changedRanges (old new : ByteArray) (gap : Nat := 64) : Array (Nat × Nat) :=
  changedRangesWith wordsDiffer old new gap

theorem changedRanges_eq (old new : ByteArray) (gap : Nat) :
    changedRanges old new gap = changedRangesWith wordsDifferRef old new gap := by
  rw [changedRanges, wordsDiffer_eq]

/-- The bytes of `new` in `ranges`, in order: a patch section. -/
def rangeBytes (new : ByteArray) (ranges : Array (Nat × Nat)) : ByteArray :=
  ranges.foldl (fun acc (o,l) => new.copySlice o acc acc.size l) (ByteArray.emptyWithCapacity (ranges.foldl (fun n r => n+r.2) 0))

/-- Applying a patch: `old` with the bytes of `patch` written at `ranges`, in order. The host does
this (`native_html_layout.ts`, `applyPatch`); the tests check that it gives `new`. -/
def applyRanges (old patch : ByteArray) (ranges : Array (Nat × Nat)) : ByteArray :=
  (ranges.foldl (fun (acc,at_) (o,l) => (patch.copySlice at_ acc o l,at_+l)) (old,0)).1

-- The guards run the reference word test (the interpreter has no code for the C load).
#guard let a := ByteArray.mk #[1,2,3,4,5,6,7,8,9,10,11,12]; let b := ByteArray.mk #[1,2,3,4,5,6,7,9,9,10,11,13]
  let r := changedRangesWith wordsDifferRef a b 0
  r == #[(0,12)] && applyRanges a (rangeBytes b r) r == b
#guard let a := ByteArray.mk ((Array.range 200).map (·.toUInt8)); let b := (a.set! 40 0).set! 190 0
  let r := changedRangesWith wordsDifferRef a b 0
  r == #[(40,8),(184,8)] && changedRangesWith wordsDifferRef a b 200 == #[(40,152)] &&
    changedRangesWith wordsDifferRef a a == #[] && applyRanges a (rangeBytes b r) r == b

/-- A patch of one section as JSON: the base answer, the ranges, the full size. -/
def patchJSON (base : Nat) (ranges : Array (Nat × Nat)) (size : Nat) : String :=
  "{\"base\":" ++ toString base ++ ",\"ranges\":[" ++
    ",".intercalate (ranges.toList.map fun (o,l) => "[" ++ toString o ++ "," ++ toString l ++ "]") ++
    "],\"size\":" ++ toString size ++ "}"

/-- The page part of a layers answer for a host that holds the page answer `held` (its
`damage.id`, storage bytes and tile bytes; request field `have`, issue 1124 stage C):
- this frame's answer is `held` itself (`pageAnswerId`): `{"kept":id}` and empty sections;
- the same section sizes and at most half the bytes changed: the answer's text with
  `"dataPatch"` and `"tilesPatch"` (`changedRanges` against `held`), and as sections only the
  changed bytes (`rangeBytes`). `applyRanges` of the held bytes and a patch gives this frame's
  section (`changedRanges_apply` below is the check over test arrays);
- otherwise the answer as it is.
The second result says the page is kept. -/
def pageForHost (text : String) (sections : Array ByteArray) (held : Option (Nat × ByteArray × ByteArray)) :
    (String × Array ByteArray) × Bool :=
  -- `held` first: with nothing held the page text is not read.
  match held with
  | none => ((text,sections),false)
  | some (h,data,tiles) =>
  match pageAnswerId text with
  | none => ((text,sections),false)
  | some id =>
    if h == id then (("{\"kept\":" ++ toString h ++ "}",sections.map fun _ => ByteArray.empty),true)
    else match sections with
      | #[newData,newTiles] =>
        if data.size != newData.size || tiles.size != newTiles.size then ((text,sections),false) else
        let dr := changedRanges data newData
        let tr := changedRanges tiles newTiles
        let changed := (dr ++ tr).foldl (fun n r => n+r.2) 0
        if 2*changed > newData.size+newTiles.size then ((text,sections),false) else
        (((text.dropEnd 1).toString ++ ",\"dataPatch\":" ++ patchJSON h dr newData.size ++
          ",\"tilesPatch\":" ++ patchJSON h tr newTiles.size ++ "}",#[rangeBytes newData dr,rangeBytes newTiles tr]),false)
      | _ => ((text,sections),false)

/-- The view under the chrome and the band of the page layer of a layers answer. A chrome that
may fold: the band covers the view under the strip, the most it shows, so a change of
`collapse` keeps the band and only the chrome layer is drawn again. -/
def layersBand (shell : WebShell.Shell) (width height : Nat) : Nat × Band :=
  let top := WebShell.height shell width
  let view := max 1 (height-(if shell.collapsible then bandTop shell width else top))
  (view,band shell.scroll view)

/-- The answer to a render with `layers:true`, and the page layer answers kept after it
(`pageArtifact`). -/
def layersJSON (kp : KeptPages) (shell : WebShell.Shell) (page : Rendering.Scene) (extra : List Rendering.Node)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face)
    (width height : Nat) (live : Bool) (form : NativeSVG.DataForm) (checks tree : Bool) (hoverRules : Bool := false)
    (canvases : List Rendering.Layout.Box := []) (animating : Bool := false) (animations : Bool := false)
    (retainOn : Bool := true) (splashing : Bool := false) (addressFont : WebShell.AddressFont := {})
    (chrome : Option (String × Array ByteArray) := none)
    (layout : Option (ByteArray × ByteArray) := none) (held : Option (Nat × ByteArray × ByteArray) := none) :
    KeptPages × Except String ((String × Array ByteArray) × Option (Nat × ByteArray × ByteArray)) :=
  let top := WebShell.height shell width
  let (view,b) := layersBand shell width height
  -- `layout`: the boxes, glyph runs and links of this band as sections (`WebRender.layoutSections`,
  -- request field `layoutSections`), given by the caller; the page's text then leaves them out.
  let (kp,pageAnswer) := pageArtifact kp page extra b boxes face live form checks tree retainOn layout.isSome
  let answer : Except String ((String × Array ByteArray) × Option (Nat × ByteArray × ByteArray)) := do
    let (pageText,pageSections) ← pageAnswer
    -- `chrome`: the caller's kept chrome answer for these inputs (`keptChrome`), else made here.
    let (chromeText,chromeSections) ← match chrome with
      | some answer => pure answer
      | none => chromeArtifact shell page width addressFont face live form.next checks tree
    let number := fun (n : Nat) => JSON.Json.number (toString n)
    let place := JSON.Json.object ([("top",number top),("view",number view),("bandTop",number b.top),
      ("bandHeight",number b.height),("keepFrom",number b.keepFrom),("keepTo",number (b.keepTo view)),
      ("composite",.string compositeShader),("hoverRules",.bool hoverRules),("animating",.bool animating),("animations",.bool animations),
      ("splash",.bool splashing),
      ("scrollLimit",number (scrollLimit (WebPrint.contentHeight boxes) view))] ++
      (if canvases.isEmpty then [] else [("canvases",canvasRects canvases b width),("canvasBlit",.string canvasBlitShader)]))
    let first := match form with
      | .sections k | .sectionsCpu k => k
      | _ => 0
    -- `held` (issue 1124, stage C): the page answer the host holds (`pageForHost`). The second
    -- result is this frame's page answer whole (its id and sections), for the engine to keep.
    -- Only for a host with layout sections (the one that sends `have`): `pageAnswerId` reads the
    -- page text, which without them holds the boxes, glyph runs and links (about 400 KB).
    let sent : Option (Nat × ByteArray × ByteArray) := if layout.isNone then none else
      match pageAnswerId pageText,pageSections with
      | some id,#[data,tiles] => some (id,data,tiles)
      | _,_ => none
    let ((pageText,pageSections),keptPage) := pageForHost pageText pageSections held
    match (if keptPage then none else layout) with
    | some (nums,text) =>
      let at_ := first+pageSections.size+chromeSections.size
      return (("{\"layers\":" ++ place.toString ++ ",\"page\":" ++ pageText ++ ",\"chrome\":" ++ chromeText ++
        ",\"layout\":{\"section\":" ++ toString at_ ++ ",\"strings\":" ++ toString (at_+1) ++ "}}",
        pageSections ++ chromeSections ++ #[nums,text]),sent)
    | none =>
      return (("{\"layers\":" ++ place.toString ++ ",\"page\":" ++ pageText ++ ",\"chrome\":" ++ chromeText ++ "}",
        pageSections ++ chromeSections),sent)
  (kp,answer)

/-- The fonts the engine holds between calls, so that a scroll does not read them
again. The first is the primary font; the others draw the characters it lacks, in
order (`SfntProfile.wordIn`). The memo holds words shaped with this list. -/
structure HeldFont where
  fonts : Array Rendering.SfntProfile.Font
  memo : Rendering.SfntProfile.Memo

/-- The family and SHA-256 of each held font, in order: the font part of `LayoutKey`. -/
def HeldFont.names (held : HeldFont) : List (String × String) :=
  held.fonts.toList.map fun f => (f.family,f.sha256)

/-- An image the engine holds: the key `inspect` gave, its SHA-256 as the host said,
and its bytes, opaque until `NativeImage.decode`. -/
structure HeldImage where
  key : String
  sha256 : String
  bytes : ByteArray

/-- The fonts and images the engine holds between calls, which layout reads: a field of
`Engine` (issue 390), passed to layout as a value. `fontLoad` and `imageLoad` change it;
a layout gives back the word memo it grew (`Laid.words`). -/
structure Holds where
  font : Option HeldFont := none
  /-- Web fonts (`@font-face`) by SHA-256, oldest first. -/
  webFonts : Array Rendering.SfntProfile.Font := #[]
  images : List HeldImage := []
  /-- The serif face (`FontFaceRule.genericOf`), when the host gave it (`fontLoad` mode 3,
  `loadSerifFont`). The window and the Hub give it before the first page, so a serif page is
  laid out once (`serifWanted_held`); a layout draws with it only on a page whose cascade has
  serif text (`layOutDOMIn`), so a page with none lays out as with no face held. A host that
  has not given it learns from `Laid.wantsSerif`. -/
  serif : Array Rendering.SfntProfile.Font := #[]
  /-- The monospace face (`FontFaceRule.genericOf`), when the host gave it (`fontLoad` mode 4,
  `loadMonoFont`), held and used as the serif face is: a layout draws with it only on a page
  whose cascade has monospace text, and a host that has not given it learns from
  `Laid.wantsMono`. -/
  mono : Array Rendering.SfntProfile.Font := #[]
  /-- Outlines of the held monospace face for the default address field. -/
  addressFont : WebShell.AddressFont := {}

instance : Inhabited Holds := ⟨{}⟩

/-- Most fonts that the engine holds at once. -/
def maxHeldFonts : Nat := 64

/-! ### Web fonts (CSS Fonts 4 §4, `@font-face`)

The host fetches the faces that `fontFaces` says the page uses and gives each one with
`fontLoad` mode 2 (`web_document_font_load_bin`, `fallback` 2, or `webFont:true` in
JSON). Lean reads the file with the font safety policy (`SfntProfile.Font.read`), and
holds it by SHA-256, apart from the fallback list: a web font draws only the text whose
`font-family` names it. A render names the faces it may use in `webFonts`
(`[{url,sha256}]`, a layout field); the rule that has that URL gives the family and the
`unicode-range`. -/

/-- Most web fonts held at once; the oldest goes first. -/
def maxWebFonts : Nat := 16

/-- Read a web font; the policy refuses it or the store holds it. -/
private def loadWebFont (h : Holds) (bytes : ByteArray) (sha256 : String) : Holds × Except String String :=
  match Rendering.SfntProfile.Font.read bytes "" sha256 with
  | .error e => (h, .error e)
  | .ok font =>
    let held := if h.webFonts.any (·.sha256 == font.sha256) then h.webFonts else
      let more := h.webFonts.push font
      if more.size > maxWebFonts then more.extract 1 more.size else more
    ({h with webFonts := held}, .ok (JSON.Json.object [("webFont",.string sha256),
      ("glyphs",.number (toString font.face.numGlyphs)),("held",.number (toString held.size))]).toString)

/-- Hold the serif face (`fontLoad` mode 3): the policy refuses it or it replaces the one
held. Layouts draw with it the text whose family list resolves to `serif`
(`FontFaceRule.genericOf`). -/
private def loadSerifFont (h : Holds) (bytes : ByteArray) (family sha256 : String) : Holds × Except String String :=
  match Rendering.SfntProfile.Font.read bytes family sha256 with
  | .error e => (h, .error e)
  | .ok font =>
    ({h with serif := #[font]}, .ok (JSON.Json.object [("serif",.string font.family),
      ("glyphs",.number (toString font.face.numGlyphs))]).toString)

private def addressFontOf (font : Rendering.SfntProfile.Font) : WebShell.AddressFont := Id.run do
  let cell := (font.face.glyph font.bytes 'M').toOption
  let advance := (cell.bind fun g => font.face.advances[g]?).getD 0
  if advance == 0 then return {}
  let mut glyphs := #[]
  for cp in [32:127] do
    let paths : Option (List Rendering.Geometry) := do
      let g ← (font.face.glyphCp font.bytes cp).toOption
      if g == 0 then none else
        let commands ← (Rendering.SfntOutline.outline font.bytes font.dir g font.cff).toOption
        (Rendering.FontProvider.outlineGeometry 0 ⟨g,commands⟩).toOption
    glyphs := glyphs.push paths
  return {advance,glyphs}

/-- Hold the monospace face (`fontLoad` mode 4): the policy refuses it or it replaces the one
held. Layouts draw with it the text whose family list resolves to `monospace`
(`FontFaceRule.genericOf`). -/
private def loadMonoFont (h : Holds) (bytes : ByteArray) (family sha256 : String) : Holds × Except String String :=
  match Rendering.SfntProfile.Font.read bytes family sha256 with
  | .error e => (h, .error e)
  | .ok font =>
    ({h with mono := #[font], addressFont := addressFontOf font}, .ok (JSON.Json.object [("mono",.string font.family),
      ("glyphs",.number (toString font.face.numGlyphs))]).toString)

/-- The held fonts that a layout depends on, by family and SHA-256, in order (the `fonts`
of `LayoutKey`): the page fonts (`HeldFont.names`), then the serif face and the monospace
face, if held. -/
def Holds.fontNames (h : Holds) : List (String × String) :=
  (h.font.map HeldFont.names).getD [] ++ h.serif.toList.map (fun f => ("serif:" ++ f.family,f.sha256)) ++
    h.mono.toList.map fun f => ("mono:" ++ f.family,f.sha256)

/-- The web fonts a render names (`webFonts`: `[{url,sha256}]`), as (URL, SHA-256). -/
def namedWebFonts (request : JSON.Json) : List (String × String) :=
  match request.field? "webFonts" with
    | some (.array items) => items.filterMap fun item => match item.field? "url",item.field? "sha256" with
      | some (.string u),some (.string h) => some (u,h)
      | _,_ => none
    | _ => []

/-- A hit when the render names more different web fonts (by SHA-256) than the engine holds
at once (`maxWebFonts`): the oldest are let go, and text in those faces is drawn in a
fallback font (issue 865). -/
def webFontLimits (request : JSON.Json) : List WebAccept.LimitHit :=
  WebAccept.LimitHit.check "maxWebFonts" maxWebFonts ((namedWebFonts request).map (·.2)).eraseDups.length
    "web fonts named by the render"

/-- The faces of `faces` with their held fonts, by the `webFonts` of the request: the
font of the first source URL of each face that the request names with a held SHA-256,
with the rule's family and `unicode-range`. -/
def webFaceFonts (h : Holds) (faces : Array Rendering.FontFaceRule.Face) (request : JSON.Json) :
    Array (Option Rendering.SfntProfile.Font) :=
  let named := namedWebFonts request
  if named.isEmpty then faces.map (fun _ => none) else
  let held := h.webFonts
  faces.map fun face => do
    let sha ← face.sources.findSome? fun u => (named.find? (·.1 == u)).map (·.2)
    let font ← held.find? (·.sha256 == sha)
    let ranges := if face.ranges == [(0,0x10FFFF)] then [] else face.ranges
    some {font with family := face.family, ranges}

/-- The fonts a layout shapes text with: the page font a host holds, and with none held
the page's own web fonts that the engine holds (`own`, in the order of its `@font-face`
rules), each still drawing first the text whose `font-family` names it.

Before, web fonts were used only inside the profile of a held page font: a host that holds
none (the WPT runner) laid every page out in the bitmap face, and a page's own font, though
fetched, checked and held, measured nothing (nine letters of `font: 10px/1 Ahem` were
77.14px wide, not 90px). With its own fonts as its fonts, text that names no web font is
drawn in the first of them that has its letters, where a host with a page font draws it in
that font; the bitmap face and a font file do not mix in one layout. A page with no web
font, and any page in a host that holds a font, is laid out as before. -/
def pageFonts (held : Option HeldFont) (own : Array Rendering.SfntProfile.Font) : Option HeldFont :=
  match held with
  | some h => some h
  | none => if own.isEmpty then none else some ⟨own,{}⟩

/-- Kind: property. Says: a host's page font is the layout's font whatever web fonts the
page has: nothing changes for a host that holds one. -/
theorem pageFonts_held (h : HeldFont) (own : Array Rendering.SfntProfile.Font) : pageFonts (some h) own = some h := rfl

/-- Kind: property. Says: with no page font and no web font held, there is no font: the
layout is in the bitmap face, as before. -/
theorem pageFonts_none (own : Array Rendering.SfntProfile.Font) (h : own.isEmpty = true) : pageFonts none own = none := by
  simp [pageFonts, h]

/-- The web fonts for a `font-family` value (CSS Fonts 4 §5.2): for each family in
order, its selected faces that are held, until a generic or held family. -/
def familyFonts (faces : Array Rendering.FontFaceRule.Face) (fonts : Array (Option Rendering.SfntProfile.Font))
    (held : List String) (value : String) : Array Rendering.SfntProfile.Font := Id.run do
  let mut out : Array Rendering.SfntProfile.Font := #[]
  for family in Rendering.CSS.familyList value do
    for i in Rendering.FontFaceRule.selected faces family do
      if let some (some f) := fonts[i]? then out := out.push f
    if Rendering.FontFaceRule.endsSearch held family then break
  return out

/-- The fonts of a `font-family` value before the held fonts: its web fonts
(`familyFonts`), then the serif face when the value resolves to `serif`, or the monospace face
when it resolves to `monospace` (`FontFaceRule.genericOfValue`), when that face is held. -/
def familyFontsWith (serif mono : Array Rendering.SfntProfile.Font) (faces : Array Rendering.FontFaceRule.Face)
    (fonts : Array (Option Rendering.SfntProfile.Font)) (held : List String) (value : String) :
    Array Rendering.SfntProfile.Font :=
  if serif.isEmpty && mono.isEmpty then familyFonts faces fonts held value
  else match Rendering.FontFaceRule.genericOfValue held value with
    | .serif => familyFonts faces fonts held value ++ serif
    | .monospace => familyFonts faces fonts held value ++ mono
    | .first => familyFonts faces fonts held value

/-- Kind: property. Says: with no serif and no monospace face held, the fonts of every family
value are the web fonts as before: a host that never gives either face lays every page out as
before. -/
theorem familyFontsWith_none (faces : Array Rendering.FontFaceRule.Face)
    (fonts : Array (Option Rendering.SfntProfile.Font)) (held : List String) (value : String) :
    familyFontsWith #[] #[] faces fonts held value = familyFonts faces fonts held value := by
  unfold familyFontsWith
  rfl

/-- Kind: property. Says: a family value that resolves to neither `serif` nor `monospace`
(`sans-serif`, a held or installed sans-serif family first) gets the same fonts whether or not
the faces are held: explicit families are not taken over. -/
theorem familyFontsWith_first (serif mono : Array Rendering.SfntProfile.Font) (faces : Array Rendering.FontFaceRule.Face)
    (fonts : Array (Option Rendering.SfntProfile.Font)) (held : List String) (value : String)
    (h : Rendering.FontFaceRule.genericOfValue held value = .first) :
    familyFontsWith serif mono faces fonts held value = familyFonts faces fonts held value := by
  unfold familyFontsWith
  split
  · rfl
  · rw [h]

/-- Kind: property. Says: a family value that resolves to `serif` draws with the serif face
after its web fonts and before the held fonts, when one is held; the monospace face is not
used for it. -/
theorem familyFontsWith_serif (serif mono : Array Rendering.SfntProfile.Font) (faces : Array Rendering.FontFaceRule.Face)
    (fonts : Array (Option Rendering.SfntProfile.Font)) (held : List String) (value : String)
    (hs : serif.isEmpty = false) (h : Rendering.FontFaceRule.genericOfValue held value = .serif) :
    familyFontsWith serif mono faces fonts held value = familyFonts faces fonts held value ++ serif := by
  unfold familyFontsWith
  rw [if_neg (by simp [hs]), h]

/-- Kind: property. Says: a family value that resolves to `monospace` draws with the monospace
face after its web fonts and before the held fonts, when one is held; the serif face is not
used for it. -/
theorem familyFontsWith_mono (serif mono : Array Rendering.SfntProfile.Font) (faces : Array Rendering.FontFaceRule.Face)
    (fonts : Array (Option Rendering.SfntProfile.Font)) (held : List String) (value : String)
    (hm : mono.isEmpty = false) (h : Rendering.FontFaceRule.genericOfValue held value = .monospace) :
    familyFontsWith serif mono faces fonts held value = familyFonts faces fonts held value ++ mono := by
  unfold familyFontsWith
  rw [if_neg (by simp [hm]), h]

/-- The answers of `f` for `keys`, each computed once, in a hash map (`memoLookup`). The layout
asks for the fonts of a `font-family` value (`familyFontsWith`) for each word and each line, and
each ask read the value again (`CSS.familyList`) and searched the faces: on a long page that was
about a third of the first layout (https://github.com/danbri/factoidal-core/issues/1168).
The table is a value of its own, made once by the caller with `let`: a function
`memoOn f keys : String → α` with the map in its body is compiled as a function of three
arguments, and made the map again at each ask (measured 2026-11-26: the first layout 1.6 times
slower at p50, three pages with no first frame in 240 s). -/
def memoTable {α : Type} (f : String → α) (keys : Array String) : Std.HashMap String α :=
  keys.foldl (fun m k => if m.contains k then m else m.insert k (f k)) {}

/-- `f v` from `table` when it holds `v`, else computed. -/
def memoLookup {α : Type} (f : String → α) (table : Std.HashMap String α) (v : String) : α :=
  match table[v]? with
  | some a => a
  | none => f v

/-- Kind: equivalence. Says: a lookup in `memoTable f keys` is `f`: the layout with the fonts of
each family value computed once is the layout with them computed at each ask.
Does not say: anything of time or memory. -/
theorem memoLookup_memoTable {α : Type} (f : String → α) (keys : Array String) :
    memoLookup f (memoTable f keys) = f := by
  funext v
  unfold memoLookup memoTable
  rw [← Array.foldl_toList]
  have inv : ∀ (l : List String) (m : Std.HashMap String α), (∀ k a, m[k]? = some a → a = f k) →
      ∀ k a, (l.foldl (fun m k => if m.contains k then m else m.insert k (f k)) m)[k]? = some a → a = f k := by
    intro l
    induction l with
    | nil => intro m h; simpa using h
    | cons x xs ih =>
      intro m h
      apply ih
      intro k a hk
      simp only at hk
      split at hk
      · exact h k a hk
      · rw [Std.HashMap.getElem?_insert] at hk
        split at hk
        · rename_i heq; simp at hk heq; subst heq; exact hk.symm
        · exact h k a hk
  have h0 : ∀ k a, (({} : Std.HashMap String α))[k]? = some a → a = f k := by simp
  split
  · rename_i a ha; exact inv _ _ h0 v a ha
  · rfl

#guard memoLookup (fun s => s.length) (memoTable (fun s => s.length) #["ab","c","ab"]) "ab" == 2
#guard memoLookup (fun s => s.length) (memoTable (fun s => s.length) #["ab","c"]) "xyz" == 3

/-- Whether the drawn text of `dom` has a family value that resolves to `g`
(`FontFaceRule.genericOfValue`), by the computed styles of its text nodes: a host that holds
no face for `g` gives it when a layout says so (`Laid.wantsSerif`, `Laid.wantsMono`). Each
distinct value is resolved once; the text of `SfntProfile.unrenderedText` elements is not
drawn. -/
def textWants (g : Rendering.FontFaceRule.Generic) (held : List String) (dom : DOM.Dom) (styles : Array Rendering.CSS.Computed) : Bool := Id.run do
  let mut seen : Std.TreeMap String Unit := {}
  -- Text nodes in a row mostly share their value: the last one is checked first.
  let mut last := "\x00"
  for id in [:dom.size] do
    let n := dom.get id
    if n.type != .text then continue
    let value := (styles[id]?.map (·.fontFamily)).getD ""
    if value == last || n.data.all Char.isWhitespace || seen.contains value then continue
    if Rendering.FontFaceRule.genericOfValue held value == g then
      if !Rendering.SfntProfile.inUnrendered dom id then return true
    else
      seen := seen.insert value ()
      last := value
  return false

/-- `textWants` for the serif face. -/
def textWantsSerif (held : List String) (dom : DOM.Dom) (styles : Array Rendering.CSS.Computed) : Bool :=
  textWants .serif held dom styles

/-- Whether the text of a page's cascade (`Generated.styled`: the tree with its generated
content, and the styles) resolves to `g`, before any layout; false when the cascade refused
(the layout then refuses with it). -/
def madeWants (g : Rendering.FontFaceRule.Generic) (held : List String) (made : Except String (DOM.Dom × Array Rendering.CSS.Computed)) : Bool :=
  match made with
  | .ok (d,styles) => textWants g held (Rendering.Generated.flattenContents d styles) styles
  | .error _ => false

/-- `madeWants` for the serif face. -/
def madeWantsSerif (held : List String) (made : Except String (DOM.Dom × Array Rendering.CSS.Computed)) : Bool :=
  madeWants .serif held made

/-- The layout of `dom` with a cascade already made for it (`made`, from
`Generated.styled`): what `Layout.renderWithStyles` does after its own cascade. -/
def drawMade (dom : DOM.Dom) (made : DOM.Dom × Array Rendering.CSS.Computed) (font : Rendering.Layout.FontProfile)
    (embedding : Rendering.Layout.Embedding) (width rows : Nat) (pictures : Rendering.Layout.Pictures) :
    Except String ((Rendering.Scene × Array Rendering.Layout.Box) × Array Rendering.CSS.Computed) := do
  let drawn ← Rendering.Layout.renderStyled (Rendering.Generated.flattenContents made.1 made.2) made.2 font embedding width rows pictures
  return ((drawn.1,Rendering.Layout.pageBoxes dom.size drawn.2),made.2.extract 0 dom.size)

/-- Kind: correctness of the shared cascade. Says: the layout of a page whose cascade is made
first (`layOutDOMIn`, so that the fonts can know whether the page has serif text) is the
layout `Layout.renderWithStyles` makes with its own cascade: making the cascade before the
fonts changes no layout. -/
theorem renderWithStyles_made (dom : DOM.Dom) (rules : List Rendering.CSS.Rule) (font : Rendering.Layout.FontProfile)
    (embedding : Rendering.Layout.Embedding) (width rows : Nat) (textScale : Float) (state : Rendering.CSS.ElementState)
    (pictures : Rendering.Layout.Pictures) (treeScope : Option Rendering.CSS.TreeScope) :
    Rendering.Layout.renderWithStyles dom rules font embedding width rows textScale state pictures treeScope =
      (Rendering.Generated.styled treeScope dom rules textScale state).bind
        (fun m => drawMade dom m font embedding width rows pictures) := by
  unfold Rendering.Layout.renderWithStyles drawMade
  cases Rendering.Generated.styled treeScope dom rules textScale state <;> rfl

/-- Whether a layout asks the host for a generic face (`Laid.wantsSerif` with the serif face,
`Laid.wantsMono` with the monospace face): only when none is held, a page font is held, and
the page has text in that family (`text`, worked out only then). -/
def serifWanted (serif : Array Rendering.SfntProfile.Font) (loaded : Bool) (text : Unit → Bool) : Bool :=
  serif.isEmpty && loaded && text ()

/-- Kind: property. Says: a layout made with the serif face held never asks for it, so a host
that gives the face before the first layout of a page (run_html.ts, the Hub worker) never
draws that page a second time for it: its first layout is final. -/
theorem serifWanted_held (serif : Array Rendering.SfntProfile.Font) (loaded : Bool) (text : Unit → Bool)
    (h : serif.isEmpty = false) : serifWanted serif loaded text = false := by
  simp [serifWanted, h]

/-- Kind: property. Says: a page with no serif text never asks for the serif face, held or
not: its text never costs a font load. -/
theorem serifWanted_noText (serif : Array Rendering.SfntProfile.Font) (loaded : Bool) (text : Unit → Bool)
    (h : text () = false) : serifWanted serif loaded text = false := by
  simp [serifWanted, h]

/-- Kind: property. Says: the family lookup a layout uses when the page has neither serif nor
monospace text (`layOutDOMIn` passes no face then) gives every family value that resolves to
neither the fonts it gets with the faces held: on such text the faces change nothing. -/
theorem familyFontsWith_noSerif (serif mono : Array Rendering.SfntProfile.Font) (faces : Array Rendering.FontFaceRule.Face)
    (fonts : Array (Option Rendering.SfntProfile.Font)) (held : List String) (value : String)
    (h : Rendering.FontFaceRule.genericOfValue held value = .first) :
    familyFontsWith #[] #[] faces fonts held value = familyFontsWith serif mono faces fonts held value := by
  rw [familyFontsWith_none, familyFontsWith_first serif mono faces fonts held value h]

/-- Kind: property. Says: a page with monospace text and no serif text gets, for every family
value, the fonts it gets with the serif face held too (`layOutDOMIn` passes the serif face only
for a page with serif text): on text that is not serif, holding the serif face changes nothing. -/
theorem familyFontsWith_monoOnly (serif mono : Array Rendering.SfntProfile.Font) (faces : Array Rendering.FontFaceRule.Face)
    (fonts : Array (Option Rendering.SfntProfile.Font)) (held : List String) (value : String)
    (h : Rendering.FontFaceRule.genericOfValue held value ≠ .serif) :
    familyFontsWith #[] mono faces fonts held value = familyFontsWith serif mono faces fonts held value := by
  unfold familyFontsWith
  cases hg : Rendering.FontFaceRule.genericOfValue held value with
  | serif => exact absurd hg h
  | monospace =>
    by_cases hm : mono.isEmpty = true
    · have h0 : mono = #[] := by simpa using hm
      subst h0
      simp
    · simp [hm]
  | first => simp

/-- Read the bytes of a font file once. Later renders use it until another load
changes the list. With `fallback`, the font goes at the end of the held list (a font
with the same SHA-256 is not added twice); otherwise it replaces the list. Either
way the word memo starts again, as words may now draw differently. -/
private def loadFontBytes (h : Holds) (bytes : ByteArray) (family sha256 : String) (fallback : Bool) :
    Holds × Except String String :=
  match Rendering.SfntProfile.Font.read bytes family sha256 with
  | .error e => (h, .error e)
  | .ok font =>
    let fonts := match fallback,h.font with
      | true,some held => if held.fonts.any (·.sha256 == sha256) then held.fonts else held.fonts.push font
      | _,_ => #[font]
    if fonts.size > maxHeldFonts then (h, .error "font file: more than 64 fonts held") else
    ({h with font := some ⟨fonts,{}⟩}, .ok (JSON.Json.object [("family",.string font.family),
      ("glyphs",.number (toString font.face.numGlyphs)),("fonts",.number (toString fonts.size))]).toString)

/-- The `fontLoad` op: the font file as Base64 in the JSON request. This is the text
reference path; `fontLoadBin` takes the same file as bytes. -/
private def loadFont (h : Holds) (request : JSON.Json) : Holds × Except String String :=
  match Rendering.SfntProfile.decodeBase64 (str request "fontBase64") with
  | none => (h, .error "font file: invalid base64")
  | some bytes =>
  if request.field? "webFont" == some (.bool true) then loadWebFont h bytes (str request "fontSha256" "unnamed") else
  if request.field? "serif" == some (.bool true) then loadSerifFont h bytes (str request "fontFamily" "serif") (str request "fontSha256" "unnamed") else
  if request.field? "mono" == some (.bool true) then loadMonoFont h bytes (str request "fontFamily" "monospace") (str request "fontSha256" "unnamed") else
  loadFontBytes h bytes (str request "fontFamily" "font") (str request "fontSha256" "unnamed")
    (request.field? "fallback" == some (.bool true))

/-! ### Held images (issues 1268, 1274 and 1292)

The host sends each image once, by key (the URL that `inspect` gave) and SHA-256, with
`imageLoad` (Base64 in JSON) or `web_document_image_load_bin` (bytes). Lean holds it;
a render names the images in `heldImages`, `[{key,sha256}]`, so the bytes of a render
request do not grow with the images (`frame_work_test.ts` counts them). `imageInfo`
says that the engine has these ops: a host calls none of them before it asks. -/

/-- Most images, and most bytes of images, that the engine holds; the oldest go first.
128: the 64 `img` and SVG images that `inspect` lists (`maxDocumentImages`) and as many
background images. -/
def maxHeldImages : Nat := 128
def maxHeldImageBytes : Nat := 33554432

/-- Hold `bytes` as the image `key` with `sha256`, first; drop another image of the same
key, then the oldest past the limits. -/
private def loadImageBytes (h : Holds) (bytes : ByteArray) (key sha256 : String) : Holds × Except String String :=
  if key.isEmpty || sha256.isEmpty then (h, .error "image key and sha256 required") else
  if bytes.size > maxHeldImageBytes then (h, .error s!"image exceeds {maxHeldImageBytes} bytes") else
  let others := h.images.filter (·.key != key)
  let (kept,_) := others.foldl (fun (acc : List HeldImage × Nat) image =>
    if acc.1.length+1 < maxHeldImages && acc.2+image.bytes.size ≤ maxHeldImageBytes then (acc.1 ++ [image],acc.2+image.bytes.size)
    else acc) ([],bytes.size)
  let held := ⟨key,sha256,bytes⟩ :: kept
  let number := fun (n : Nat) => JSON.Json.number (toString n)
  ({h with images := held}, .ok (JSON.Json.object [("key",.string key),("sha256",.string sha256),("bytes",number bytes.size),
    ("held",number held.length)]).toString)

/-- `imageLoad`: the image as Base64 in the JSON request. -/
private def loadImage (h : Holds) (request : JSON.Json) : Holds × Except String String :=
  match NativeImage.base64 (str request "imageBase64").toUTF8 0 with
  | .error e => (h, .error e)
  | .ok bytes => loadImageBytes h bytes (str request "key") (str request "sha256")

/-- A page's bytes as its text (HTML §13.2.3 encoding sniffing, then the Encoding
Standard's decoder: `WHATWG.Encoding.Sniff.decodeDocumentFast`), given the transport
layer's `Content-Type` value or a bare charset label ("" for none). The answer is the
encoding's name, a line feed, then the text. The hosts call this where a page's bytes
become text, so a document declared in a legacy encoding is read in it and
`document.characterSet` is its name. `fallback` is the user's default for pages that
declare no encoding (`WebState.encodingSetting`; "" is detect) and `locale` the system's
language (a BCP 47 or POSIX tag; "" for none), which `Sniff.localeEncoding` maps by HTML
§13.2.3.2's table. -/
@[export web_document_decode2_bin]
def decodeBinWith (bytes : ByteArray) (contentType fallback locale : String) : String :=
  let label := if contentType.isEmpty then none
    else (L4Factoidal.WHATWG.Encoding.Sniff.extractFromMeta contentType).orElse fun _ =>
      if contentType.contains ';' || contentType.contains '/' then none else some contentType
  let (e, text) := L4Factoidal.WHATWG.Encoding.Sniff.decodeDocumentFast bytes label
    (L4Factoidal.WHATWG.Encoding.Sniff.Fallback.ofSetting fallback) locale
  e.name ++ "\n" ++ text

/-- `decodeBinWith` with the default setting and no locale (an older host). -/
@[export web_document_decode_bin]
def decodeBin (bytes : ByteArray) (contentType : String) : String := decodeBinWith bytes contentType "" ""

/-- The images a render names (`heldImages`), as key and SHA-256: the first
`maxHeldImages`. A name past them is not held, so its image is drawn as missing (alt
text, no background), as for any name not held (`heldNamed`); the page is not refused.
Cost of refusing: from 2026-11-22 the Wikipedia article "United States" (more than 64
images and backgrounds together) was refused whole (issue 831). -/
def namedImages (request : JSON.Json) : Except String (List (String × String)) := do
  let .array items := (request.field? "heldImages").getD (.array []) | throw "heldImages must be an array"
  (items.take maxHeldImages).mapM fun item => do
    let some (.string key) := item.field? "key" | throw "held image key must be a string"
    let some (.string sha) := item.field? "sha256" | throw "held image sha256 must be a string"
    pure (key,sha)

/-- The named images that the engine holds: the image part of `LayoutKey`. A named
image that is not held is left out (the page shows its alt text), and the key says so. -/
def heldNamed (h : Holds) (names : List (String × String)) : List (String × String) :=
  let held := h.images
  names.filter fun (key,sha) => held.any fun image => image.key == key && image.sha256 == sha

/-- The bytes of the held images of a key. -/
private def heldBytes (h : Holds) (names : List (String × String)) : List (String × ByteArray) :=
  let held := h.images
  names.filterMap fun (key,sha) => (held.find? fun image => image.key == key && image.sha256 == sha).map (key,·.bytes)

/-- What Canvas 2D draws with (L4Factoidal.PageCanvas): the fonts the engine holds, the SVG
path parser (`new Path2D(d)`), and the held images by key, decoded by Lean when a page
draws one (the canvas keeps it decoded). -/
def canvasEnv (h : Holds) (opaqueKeys : Std.HashSet String := {}) (opaqueFull : Bool := false)
    (faces : Array Rendering.SfntProfile.Font := #[]) : L4Factoidal.PageCanvas.Env :=
  let fonts := (h.font.map (·.fonts)).getD #[]
  let held := fonts.toList.map (L4Factoidal.PageCanvas.Text.familyKey ·.family)
  { imageOpaque := fun key => opaqueFull || opaqueKeys.contains key,
    fonts,
    -- the faces a family list asks for (issue 1075): the page's `@font-face` faces (`faces`,
    -- `canvasFaceFonts`), then the monospace or the serif face the host gave
    familyFaces := L4Factoidal.PageCanvas.Text.familyFaces faces h.serif h.mono held,
    svgPath := fun d => (NativeSVGPath.parse NativeSVG.number d).toOption,
    image := fun key => (h.images.find? (·.key == key)).bind fun img =>
      match NativeImage.decode img.bytes with
      | .ok b => some (L4Factoidal.PageCanvas.Bitmap.ofStraight b.width b.height b.rgba)
      | .error _ => none,
    decode := fun bytes =>
      match NativeImage.decode bytes with
      | .ok b => some (L4Factoidal.PageCanvas.Bitmap.ofStraight b.width b.height b.rgba)
      | .error _ => none }

/-- The request fields that a render reads before its layout ends. `shell` gives only
the height of the chrome, which the key holds as `top`; `selection`, `live`, `binary`,
`checks`, `tree`, `op` and the scroll act after layout. `hover` and `active` are not
here: the pointer state is painted (`WebRepaint`), and is in the key, as `pointer`,
only for a frame whose pointer styles change geometry. `animated` is the values of the
page's running animations and transitions (`elementState` reads it into the cascade): a
host gives the list of its script session's last turn, so the frame it paints has the
values the page's scripts read. Until 2026-11-14 the field was not in this list, and a
render's layout never saw it: content that fades in from `opacity: 0` stayed invisible. A
page with no animation sends no such field and its key is as before. `partialNote` (`false`:
no "Partial page" note, `layOutDOMIn`) is the WPT reftest runner's; it was missing from this
list on 2026-11-22 and the note stayed in its pictures. -/
def layoutFields : List String := ["commands","resources","images","heldImages","url","syntax","fontData","textScalePercent","graphModel",
  "visited","media","liberal","scripting","resourceFailures","zoomUnit","webFonts","animated","imported","partialNote"]

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
  /-- The node tree of a page with shadow trees, whose `dom` is its flat tree. -/
  treeScope : Option Rendering.CSS.TreeScope := none
  /-- What liberal mode skipped (`WebAccept`); empty in strict mode. -/
  diagnostics : List WebAccept.Diagnostic := []
  /-- The resource limits this layout reached (`WebAccept.LimitHit`), in both modes. -/
  limits : List WebAccept.LimitHit := []
  /-- What a frame paints on this layout with no layout: the `transform` of script
  slots and SVG animations (`WebPaint`). -/
  paint : WebPaint.Plan := {}
  /-- The word memo of the held fonts after this layout (`SfntProfile.remember`), which
  the engine keeps for the next layout (`Holds.font`); none with no held font. -/
  words : Option Rendering.SfntProfile.Memo := none
  /-- The number the engine gave this layout when it made it (`Engine.serial`); 0 for a
  layout the engine does not keep. Two kept layouts with one number are one value. -/
  serial : Nat := 0
  /-- What this layout made that the engine's `Kept` did not have; the engine adds it and
  keeps the layout without it. -/
  made : Made := {}
  /-- Text of the page resolves to `serif` and the engine holds no serif face
  (`textWantsSerif`): the answer says `wantsSerif`, and a host gives the face. -/
  wantsSerif : Bool := false
  /-- Text of the page resolves to `monospace` and the engine holds no monospace face
  (`textWants .monospace`): the answer says `wantsMono`, and a host gives the face. -/
  wantsMono : Bool := false

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
  -- the values of running animations (`Rendering.Animation`; `measure` adds the field)
  let animated := match request.field? "animated" with
    | some (.array items) => items.filterMap fun
      | .array [.number n, .string p, .string v, .bool t] => n.toNat?.map fun id => (id, p, v, t)
      | _ => none
    | _ => []
  return {hover := node "hover", active := node "active", visited, animated}

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

/-- The arena with the children of each node `limit` levels below the root taken out of
the tree, and the number of nodes that lost them. -/
def pruneDeep (dom : DOM.Dom) (limit : Nat) : DOM.Dom × Nat := Id.run do
  let mut d := dom
  let mut cut := 0
  let mut pending : List (Nat × Nat) := [(0,0)]
  for _ in [:dom.size+1] do
    match pending with
    | [] => break
    | (id,depth)::rest =>
      pending := rest
      let n := d.get id
      if depth >= limit && !n.kids.isEmpty then
        d := d.setNode id fun n => {n with kids := #[]}
        cut := cut+1
      else
        pending := n.kids.toList.map (·,depth+1) ++ pending
  return (d,cut)

/-- The note that liberal mode puts at the top of a page it drew with skips: a link to the
console tab (`foafnaut:console`), drawn by this engine as page content. A document with no
`body` gets no note. -/
def partialNote (dom : DOM.Dom) : DOM.Dom := Id.run do
  let some body := (dom.treeOrder 0).find? (fun id => DOM.Dom.isHtmlElement (dom.get id) "body") | return dom
  let doc := (dom.get body).doc
  let style := "display:block;margin:0;padding:6px 12px;background-color:#fff1b8;color:#4a3300;" ++
    "border:2px solid #b08a1e;font-size:14px;line-height:20px;text-decoration:none;text-align:left"
  let attrs : Array DOM.Attr := #[{lname := "href", value := "foafnaut:console"},{lname := "style", value := style}]
  let html := some DOM.htmlNS
  let link : DOM.Node := {type := .element, doc := doc, ns := html, lname := "a", attrs := attrs}
  let text : DOM.Node := {type := .text, doc := doc, data := "Partial page \u2014 see console"}
  let (d,a) := dom.push link
  let (d,t) := d.push text
  let d := d.linkChild a t none
  d.linkChild body a (d.get body).kids[0]?

/-- The inline `svg` roots: SVG `svg` elements whose parent is not SVG, in tree order. -/
def svgRoots (dom : DOM.Dom) : List Nat :=
  (dom.treeOrder 0).toList.filter fun id =>
    let n := dom.get id
    n.type == .element && n.ns == some DOM.svgNS && n.lname == "svg" &&
      (n.parent.map fun p => (dom.get p).ns != some DOM.svgNS).getD false

/-- The refusals of the embedding for the `svg` roots `roots` that a layout drew, each read at
the size of its box. -/
def svgRefusals (embedding : Rendering.Layout.Embedding) (styles : Array Rendering.CSS.Computed)
    (boxes : Array Rendering.Layout.Box) (roots : List Nat) (size : Nat) : List String :=
  let byId := boxes.foldl (fun (a : Array (Option Rendering.Layout.Box)) b => if b.source < a.size then a.set! b.source (some b) else a)
    (Array.replicate size none)
  roots.filterMap fun id => match byId[id]?, styles[id]? with
    | some (some b), some s => match embedding id s b.width b.height with
      | .error e => some e
      | .ok _ => none
    | _, _ => none

/-- The arena with every inline `svg` root (an SVG `svg` element whose parent is not SVG) taken
out of the tree, and how many. -/
def stripSvg (dom : DOM.Dom) : DOM.Dom × Nat :=
  let roots := svgRoots dom
  (roots.foldl DOM.Dom.remove dom,roots.length)

/-- The SVG step of a liberal layout (`layOutDOMIn`): the SVG of the document; when it can not
be read, the document with its `svg` roots taken out (`stripSvg`); when even that can not be
read (the reader reads the whole document tree, where the taken-out roots stay in the arena),
the document with no SVG at all (`WebRender.makeReplacedNoSvg`). Its type has no refusal: in
liberal mode no SVG content refuses the page (`liberalSvg_ok`, `liberalSvg_noSvg`). -/
def liberalSvg (kept : Kept) (dom : DOM.Dom) (documentURL : Option String)
    (images : List (String × ByteArray)) (svgFonts : Array Rendering.SfntProfile.Font)
    (cascade : Option (Array Rendering.CSS.Computed) := none) :
    Rendering.Layout.Embedding × Rendering.Layout.Pictures × DOM.Dom × List WebAccept.Diagnostic ×
      Option WebRender.StoreEntry × NativeSVGText.Words :=
  match WebRender.makeReplacedIn kept.stores kept.words dom documentURL images svgFonts cascade with
  | .ok (e,p,s,w) => (e,p,dom,[],s,w)
  | .error e =>
    let (bare,n) := stripSvg dom
    let skipped : List WebAccept.Diagnostic := [{skip := .svgContent, «where» := s!"{n} inline svg elements", refusal := e}]
    match WebRender.makeReplacedIn kept.stores kept.words bare documentURL images svgFonts with
    | .ok (e',p,s,w) => (e',p,bare,skipped,s,w)
    | .error _ =>
      let (e',p,s,w) := WebRender.makeReplacedNoSvg kept.stores bare documentURL images e
      (e',p,bare,skipped,s,w)

/-- Kind: equivalence. Says: liberal mode is strict mode on a document whose SVG is read: the
same embedding, pictures and document, with no diagnostic. -/
theorem liberalSvg_ok (kept : Kept) (dom : DOM.Dom) (documentURL : Option String)
    (images : List (String × ByteArray)) (svgFonts : Array Rendering.SfntProfile.Font) (e p s w)
    (h : WebRender.makeReplacedIn kept.stores kept.words dom documentURL images svgFonts = .ok (e,p,s,w)) :
    liberalSvg kept dom documentURL images svgFonts = (e,p,dom,[],s,w) := by
  simp [liberalSvg, h]

/-- Kind: safety. Says: when neither the document nor the document with its `svg` roots taken
out can be read, liberal mode lays out the page with an embedding that refuses every `svg` root
with the first refusal (drawn as nothing), and says so in one diagnostic: the page is drawn. -/
theorem liberalSvg_noSvg (kept : Kept) (dom : DOM.Dom) (documentURL : Option String)
    (images : List (String × ByteArray)) (svgFonts : Array Rendering.SfntProfile.Font) (e e2 : String)
    (h1 : WebRender.makeReplacedIn kept.stores kept.words dom documentURL images svgFonts = .error e)
    (h2 : WebRender.makeReplacedIn kept.stores kept.words (stripSvg dom).1 documentURL images svgFonts = .error e2)
    (id : Nat) (st : Rendering.CSS.Computed) (wd ht : Float) :
    (liberalSvg kept dom documentURL images svgFonts).1 id st wd ht = .error e ∧
    (liberalSvg kept dom documentURL images svgFonts).2.2.2.1.map (·.skip) = [.svgContent] := by
  simp [liberalSvg, h1, h2, WebRender.makeReplacedNoSvg]

/-- Background pictures take ids from here up, apart from the ids of the page's `img` and SVG
images (`WebRender.picturesOf`): the paint table keeps one bitmap for each id. -/
def backgroundPictureBase : Nat := 1099511627776

/-- Most SVG background images drawn again at their tile size on one page. -/
def maxVectorRedraws : Nat := 16

/-- An SVG background image shown larger than its picture is drawn again at its tile size
(`WebRender.vectorPictureAt`), for a box whose width and height are lengths in px (content
box sizing): a stretched picture blurs its edges. Tile size by `Layout.backgroundTileSize`
against the padding box; at most `maxVectorRedraws`, each with its own paint-table id. -/
def redrawVectorBackgrounds (images : List (String × ByteArray)) (styles : Array Rendering.CSS.Computed) :
    Array Rendering.CSS.Computed × Nat := Id.run do
  let mut out := styles
  let mut count := 0
  for i in [0:styles.size] do
    let st := styles[i]!
    let some (_,b) := st.backgroundBitmap | continue
    let some (nw,nh,ratio) := st.backgroundNatural | continue
    let some key := st.backgroundImage | continue
    if key.contains '#' then continue
    let some bytes := images.lookup key | continue
    if st.pos.borderBox then continue
    let .px w := st.width | continue
    let .px h := st.height | continue
    let aw := w+st.padding.left+st.padding.right
    let ah := h+st.padding.top+st.padding.bottom
    let (tw,th) := Rendering.Layout.backgroundTileSize st.backgroundSize nw nh ratio aw ah
    if !(tw.isFinite && th.isFinite) || tw < 1 || th < 1 || tw > 4096 || th > 4096 then continue
    let (tw,th) := (tw.round.toUInt32.toNat, th.round.toUInt32.toNat)
    if tw ≤ b.width && th ≤ b.height then continue
    -- past the limit: counted (`vectorRedrawsWanted`), not drawn
    count := count+1
    if count > maxVectorRedraws then continue
    let some bitmap := WebRender.vectorPictureAt bytes tw th | continue
    out := out.set! i {st with backgroundBitmap := some (2*backgroundPictureBase+i,bitmap)}
  -- with the number that wanted drawing again (`maxVectorRedraws` reports past it)
  return (out,count)

/-- The pictures of `img` elements with an SVG image shown larger than its picture, drawn
again at the size they are shown (`Layout.fitScale` of the box and `object-fit`), as SVG
backgrounds are (`redrawVectorBackgrounds`): for a box whose width and height are lengths
in px (content box sizing), at most `maxVectorRedraws`, each with its own paint-table id.
The picture keeps the image's natural size, so it is placed as before. -/
@[noinline] def redrawnPictures (images : List (String × ByteArray)) (keys : List (Nat × String))
    (styles : Array Rendering.CSS.Computed) (pictures : Rendering.Layout.Pictures) :
    Std.TreeMap Nat Rendering.Layout.Picture × Nat := Id.run do
  let mut found : Std.TreeMap Nat Rendering.Layout.Picture := {}
  let mut wanted := 0
  for (id,key) in keys do
    let some picture := pictures id | continue
    -- a fragment (`#view`, `#svgView(...)`) picks a view, which the store's picture has
    if key.contains '#' then continue
    -- the cheap tests first: most pictures are not shown larger than they are held
    let some st := styles[id]? | continue
    if st.pos.borderBox then continue
    let .px w := st.width | continue
    let .px h := st.height | continue
    let (dw,dh) := picture.fittedSize st.objectFit w h
    if !(dw.isFinite && dh.isFinite) || dw < 1 || dh < 1 || dw > 4096 || dh > 4096 then continue
    let (dw,dh) := (dw.round.toUInt32.toNat,dh.round.toUInt32.toNat)
    if dw ≤ picture.bitmap.width && dh ≤ picture.bitmap.height then continue
    let some bytes := images.lookup key | continue
    if !WebRender.looksLikeSVG bytes then continue
    -- past the limit: counted, not drawn
    wanted := wanted+1
    if found.size ≥ maxVectorRedraws then continue
    let some bitmap := WebRender.vectorPictureAt bytes dw dh | continue
    let natural := picture.natural.getD (Rendering.Layout.PictureSize.fromPixels picture.bitmap.width picture.bitmap.height)
    let made : Rendering.Layout.Picture := ⟨3*backgroundPictureBase+id,bitmap,some natural⟩
    found := found.insert id made
  return (found,wanted)

/-- `pictures` with the pictures of `found` in place of theirs. -/
def withPictures (found : Std.TreeMap Nat Rendering.Layout.Picture) (pictures : Rendering.Layout.Pictures) :
    Rendering.Layout.Pictures :=
  if found.isEmpty then pictures
  else fun id => match found.get? id with
    | some p => some p
    | none => pictures id

private def attachBackgroundPicture (picture : Rendering.Layout.Pictures)
    (naturals : List (String × (Option Float × Option Float × Option Float)))
    (id : Nat) (style : Rendering.CSS.Computed) : Rendering.CSS.Computed :=
  match picture id with
  | some pic =>
    let natural := match style.backgroundImage.bind (naturals.lookup ·) with
      | some n => some n
      | none => pic.natural.map fun n => (some n.width,some n.height,n.ratio)
    {style with backgroundBitmap := some (pic.id+backgroundPictureBase,pic.bitmap), backgroundNatural := natural}
  | none => style

/-- Take the already constructed picture map as data. A function of an element id can
be eta-expanded inside the style loop, rebuilding the map for every element. -/
@[noinline] def attachBackgroundPictures (pictures : Std.TreeMap Nat Rendering.Layout.Picture)
    (naturals : List (String × (Option Float × Option Float × Option Float)))
    (styles : Array Rendering.CSS.Computed) : Array Rendering.CSS.Computed :=
  styles.mapIdx (attachBackgroundPicture (fun id => pictures.get? id) naturals)

/-- The decoded picture of each element's `border-image-source`, in the same paint-table ids as
a background of the same URL (one image, one entry). An image that did not decode leaves the
border style to draw (CSS Backgrounds 3 §6.1). -/
@[noinline] def attachBorderPictures (pictures : Std.TreeMap Nat Rendering.Layout.Picture)
    (styles : Array Rendering.CSS.Computed) : Array Rendering.CSS.Computed :=
  styles.mapIdx fun id st =>
    match pictures.get? id with
    | some pic => {st with borderImage := {st.borderImage with bitmap := some (pic.id+backgroundPictureBase,pic.bitmap)}}
    | none => st

theorem attachBackgroundPictures_eq (store : NativeImage.Store) (keys : List (Nat × String))
    (naturals : List (String × (Option Float × Option Float × Option Float)))
    (styles : Array Rendering.CSS.Computed) :
    attachBackgroundPictures (WebRender.picturesMap store keys) naturals styles =
      styles.mapIdx (attachBackgroundPicture (WebRender.picturesOf store keys) naturals) := rfl

#print axioms attachBackgroundPictures_eq

/-- Generated images take paint-table ids from here up (`backgroundPictureBase` and the
ids of redrawn pictures are below). -/
def generatedPictureBase : Nat := 4*backgroundPictureBase

/-- The images of the generated tree `d` (an image of a `content` value, CSS 2.1 §12.2): the
nodes that `Generated.fill` added, in node order, with their URLs. Only ids from `base` up
(the page's own nodes are not generated). -/
def generatedImages (base : Nat) (d : DOM.Dom) : List (Nat × String) := Id.run do
  let mut out : Array (Nat × String) := #[]
  for id in [base:d.size] do
    let n := d.get id
    if n.type == .element && n.lname == Rendering.Generated.imageName then
      let src := Rendering.CSS.attrValue n "src"
      if !src.isEmpty then out := out.push (id,src)
  return out.toList

/-- The cascade with each element's background image decoded from the supplied images (a
`data:` URL from itself), and the store made for them, for the engine to keep. A page with no
background image gives its cascade back as it is. The pictures of the images of `content`
values (`generatedImages`) are decoded in the same store and given by node: the layout lays
each out as a replaced box; an image the host did not give or that did not decode has no
picture and draws nothing (CSS 2.1 §12.2). -/
def attachBackgrounds (stores : WebRender.StoresKept) (images : List (String × ByteArray))
    (base : Nat) (made : Except String (DOM.Dom × Array Rendering.CSS.Computed)) :
    Except String (DOM.Dom × Array Rendering.CSS.Computed) × Option WebRender.StoreEntry × List WebAccept.LimitHit ×
      Std.TreeMap Nat Rendering.Layout.Picture :=
  match made with
  | .error e => (.error e,none,[],{})
  | .ok (d,styles) =>
    let generated := generatedImages base d
    let all := ((styles.toList.filterMap (·.backgroundImage)) ++ (styles.toList.filterMap (·.borderImage.source)) ++
      generated.map (·.2)).eraseDups
    let keys := all.take maxBackgroundImages
    let over := WebAccept.LimitHit.check "maxBackgroundImages" maxBackgroundImages all.length "background images"
    if keys.isEmpty then (.ok (d,styles),none,[],{}) else
    let (store,entry) := WebRender.storeIn stores keys images
    let pictureKeys := styles.toList.zipIdx.filterMap fun (st,i) => st.backgroundImage.map (i,·)
    let borderKeys := styles.toList.zipIdx.filterMap fun (st,i) => st.borderImage.source.map (i,·)
    -- the natural size of each SVG background, read once for each URL (a page can name one
    -- image from many elements); an image URL with a fragment shows a view: its size is the picture's
    let naturals : List (String × (Option Float × Option Float × Option Float)) := keys.filterMap fun k =>
      if k.contains '#' then none else (images.lookup k).bind WebRender.vectorNatural |>.map (k,·)
    let styles := attachBackgroundPictures (WebRender.picturesMap store pictureKeys) naturals styles
    let styles := attachBorderPictures (WebRender.picturesMap store borderKeys) styles
    let (styles,wanted) := redrawVectorBackgrounds images styles
    let pictures := (WebRender.picturesMap store (generated.filter (keys.contains ·.2))).map fun _ p =>
      {p with id := generatedPictureBase+p.id}
    (.ok (d,styles),entry,over ++ WebAccept.LimitHit.check "maxVectorRedraws" maxVectorRedraws wanted "SVG background images shown larger than their pictures",pictures)

private def depthRefusal : String := "unsupported HTML nesting depth (maximum 64)"
/-- `layOutDOM` in mode `m`, with its skip points. A liberal run is made only after a strict
run refused (`WebAccept.accept`), so it puts `partialNote` on the page. -/
def layOutDOMIn (h : Holds) (m : WebAccept.Mode) (request : JSON.Json) (graph : Option NativeFoafNaut.Model) (dom : DOM.Dom)
    (width rows : Nat) (held : List (String × String)) (pointer : Option Nat × Option Nat) (kept : Kept := {}) :
    ExceptT String (StateM Made) (Laid × List WebAccept.Diagnostic) := do
  -- Paint-only changes (WebPaint): script `transform` slots are the identity here, and
  -- animation elements are comments; the frame puts their values on the scene.
  let (dom,slots) := WebPaint.unmark dom
  let (dom,paint) := WebPaint.prepare dom slots
  validateResources dom request
  let (_,d1) ← classicScriptsIn m (scripting request) (WebRenderScript.scriptRecords dom)
  let percent ← scalePercent request
  -- `width` and `rows` are CSS pixels; the zoom is device pixels of text (Device pixels).
  let unit := zoomUnit request
  let textScale := cssTextScale percent unit
  -- One pass over the sheets gives the rules and the `@font-face` faces.
  let env := mediaEnv (medium request) width rows (percent*100/unit)
  let (sheets,d2) ← sheetsIn m dom request env
  let (rules,madeSheet) ← rulesOfSheets kept env sheets
  modify (·.merge madeSheet)
  -- A request with `"partialNote":false` gets no note: the WPT reftest runner compares the page's
  -- own content, and the note is the browser's (it moved each such page down 34 px and failed
  -- 92 of 322 failing SVG reftests, issue 747). The window and the Hub still show it.
  let dom := if m == .liberal && graph.isNone && request.field? "partialNote" != some (.bool false) then partialNote dom else dom
  -- Shadow trees (CSS Scoping 1): the layout is of the flat tree, and the selectors match
  -- on the node tree. A page with no shadow host takes none of this (`flatView`).
  let (dom,rules,treeScope) := flatView kept dom env rules
  if width == 0 || rows == 0 || width > 4096 || rows > 4096 then throw "unsupported document viewport"
  let fontData := str request "fontData"
  if !fontData.isEmpty then
    let _ ← WebRenderFontRequests.collectDOMWithRules dom rules textScale
  let face ← if fontData.isEmpty then pure none else
    some <$> Rendering.FontProvider.Face.decode fontData
  -- A font loaded by the fontLoad op: Lean shapes the words and takes the outlines.
  -- Web fonts (`@font-face`): those the request names and the engine holds.
  let faces := facesOf env sheets
  let faceFonts := webFaceFonts h faces request
  -- With no page font held, the page's own fonts are the fonts of its text (`pageFonts`).
  let loaded := pageFonts h.font (faceFonts.filterMap id)
  -- The words are shaped in tasks (`rememberPar_eq`: the memo of `remember`; issue 1031).
  let memo := loaded.map fun held => Rendering.SfntProfile.rememberPar held.fonts held.memo (Rendering.SfntProfile.wordsOf dom)
  let heldFamilies := ((h.font.map (·.fonts)).getD #[]).toList.map (·.family.toLower)
  let url := baseURL dom (str request "url")
  -- SVG text is drawn with the fonts of the HTML text.
  let svgFonts := (h.font.map (·.fonts)).getD #[] ++ faceFonts.filterMap id
  let images := (← suppliedImages request) ++ heldBytes h held
  -- The SVG of the page is read here. In liberal mode a refusal of it (the SVG reader reads all
  -- inline `svg` roots of the document together) lays the page out with no inline `svg`.
  let documentURL := if url.isEmpty then none else some url
  -- Resolve styles before building the SVG view so both renderers use one cascade.
  let state := withPointer dom (← elementState dom url request) pointer
  let dom := styleAttributesAbsolute dom url
  let made := Rendering.Generated.styled treeScope dom rules textScale state
  let cascade := if (WebRender.documentElement dom).any (fun id =>
    DOM.Dom.isHtmlElement (dom.get id) "html") then made.toOption.map (·.2) else none
  let (embedding,pictures,dom,d0,madeStore,madeWords) ← match graph with
    | some g => pure (WebGraph.embedding g,Rendering.Layout.noPictures,dom,([] : List WebAccept.Diagnostic),none,({} : NativeSVGText.Words))
    | none => match m with
      | .strict => do
        let (e,p,s,w) ← WebRender.makeReplacedIn kept.stores kept.words dom documentURL images svgFonts cascade
        pure (e,p,dom,[],s,w)
      | .liberal => pure (liberalSvg kept dom documentURL images svgFonts cascade)
  modify (·.merge {store := madeStore,words := madeWords})
  -- The liberal fallback may have removed SVG roots and changed selector matches.
  let state ← if d0.isEmpty then pure state else
    pure (withPointer dom (← elementState dom url request) pointer)
  let made := if d0.isEmpty then made else Rendering.Generated.styled treeScope dom rules textScale state
  -- background images decoded into the cascade (issue 704); none on most pages
  let (made,bgStore,bgLimits,generated) := attachBackgrounds kept.stores images dom.size made
  modify (·.merge {store := bgStore})
  -- the images of `content` values lay out as replaced boxes (the pictures of nodes the
  -- cascade added, so none of the document's own)
  let pictures := withPictures generated pictures
  -- With the serif face held, the family lookup goes in only for a page that has serif text;
  -- a page with none lays out as with no face held (`familyFontsWith_first`), with no lookup
  -- for each word. A host that gives the face before the first page (run_html.ts, the Hub)
  -- so lays a serif page out once, with its final face.
  let serifText := !h.serif.isEmpty && loaded.isSome && madeWantsSerif heldFamilies made
  -- The monospace face likewise, for a page whose cascade has monospace text.
  let monoText := !h.mono.isEmpty && loaded.isSome && madeWants .monospace heldFamilies made
  -- The serif face draws the text whose family resolves to `serif` (`familyFontsWith`); the
  -- words of web fonts and of the serif face are kept across layouts, as the others are.
  -- The fonts of each distinct family value of the cascade, once (`memoLookup_memoTable`).
  let familyFontsOf := familyFontsWith (if serifText then h.serif else #[]) (if monoText then h.mono else #[]) faces faceFonts heldFamilies
  let familyTable := if faceFonts.all Option.isNone && !serifText && !monoText then {} else
    memoTable familyFontsOf (match made with | .ok (_,styles) => styles.map (·.fontFamily) | .error _ => #[])
  let font ← match loaded,memo with
    | some held,some words =>
      let heldKey := Rendering.SfntProfile.fontsKey held.fonts
      Rendering.SfntProfile.profile held.fonts words
        (shapeKept heldKey none held.fonts)
        (if faceFonts.all Option.isNone && !serifText && !monoText then fun _ => #[]
         else memoLookup familyFontsOf familyTable)
        (held.fonts[0]?.map fun primary web =>
          shapeKept ("with|" ++ Rendering.SfntProfile.fontsKey web ++ "|" ++ heldKey) (some primary) (web ++ held.fonts))
    | _,_ => pure (match face with | some f => Rendering.Layout.FontProfile.ofFace f | none => WebRender.asciiFont)
  -- The layout with the styles it was made with (`Layout.renderWithStyles`): the one cascade
  -- of a layout also answers the SVG refusals below and `Laid.styles` (each cascaded the
  -- document again before). The page's own tree takes the cascade made above.
  -- SVG images of `img` shown larger than their pictures, drawn again at their size
  -- (a map, made once here: as a function-valued `match`, it was made again for each
  -- picture the layout asked for; see `WebRender.picturesOf`)
  let redrawn : Std.TreeMap Nat Rendering.Layout.Picture × Nat := match made with
    | .ok (_,styles) => redrawnPictures images (WebRender.htmlImageKeys dom documentURL) styles pictures
    | .error _ => ({},0)
  let picturesWanted := redrawn.2
  let pictures := withPictures redrawn.1 pictures
  let limits := faceLimits env sheets faces ++ declarationLimits rules ++ (match made with | .ok (_,styles) => gridLimits styles | .error _ => []) ++ webFontLimits request ++ bgLimits ++ WebAccept.LimitHit.check "maxVectorRedraws" maxVectorRedraws picturesWanted
    "SVG images shown larger than their pictures"
  let draw := fun (d : DOM.Dom) (e : Rendering.Layout.Embedding) => Rendering.Layout.renderWithStyles d rules font e width rows textScale state pictures treeScope
  let drawPage := fun (e : Rendering.Layout.Embedding) => made.bind fun m => drawMade dom m font e width rows pictures
  -- Inline SVG is a skip point, checked so that liberal mode lays the page out once
  -- (2026-11-09: BBC News took three layouts). In the layout: the embedding draws a refused
  -- `svg` as nothing (`quiet`). After it: each `svg` root that was laid out is read again at
  -- its box size, and the refusals become one diagnostic. (An `svg` root with a percentage
  -- height was taken out before the layout until 2026-11-14: layout now sizes it, CSS 2.1 §10.5.)
  let quiet : Rendering.Layout.Embedding := fun id s w h => match embedding id s w h with
    | .ok nodes => .ok nodes
    | .error _ => .ok []
  let (first,used,d3,dom) ← match m with
    | .strict => pure (drawPage embedding,embedding,([] : List WebAccept.Diagnostic),dom)
    | .liberal => do
      let roots := svgRoots dom
      let result := drawPage quiet
      let refused := match result with
        | .ok ((_,boxes),styles) => if roots.isEmpty then [] else svgRefusals embedding styles boxes roots dom.size
        | .error _ => []
      let dRefused : List WebAccept.Diagnostic := match refused with
        | [] => []
        | e :: _ => [{skip := .svgContent, «where» := s!"{refused.length} inline svg elements", refusal := e}]
      pure (result,quiet,dRefused,dom)
  -- Nesting deeper than layout reads is a skip point: liberal mode draws the page with the
  -- content below some depth taken out, the first of these depths that lays out.
  let (scene,boxes,styles,dom,d4) ← match first with
    | .ok ((scene,boxes),styles) => pure (scene,boxes,styles,dom,([] : List WebAccept.Diagnostic))
    | .error e =>
      match m with
      | .strict => throw e
      | .liberal =>
        if e == depthRefusal then
          let tries := [48,40,32,24,16].map (pruneDeep dom)
          match tries.findSome? (fun (d,cut) => match draw d used with | .ok r => some (r,d,cut) | .error _ => none) with
          | some (((scene,boxes),styles),d,cut) =>
            pure (scene,boxes,styles,d,[{skip := .nestingDepth, «where» := s!"{cut} elements", refusal := e}])
          | none => throw e
        else
          -- A layout refusal of inline SVG (an SVG box that layout can not size, as BBC News's
          -- percentage heights): the page with no inline `svg`, when that lays out.
          let (bare,n) := stripSvg dom
          if n == 0 then throw e else
          match draw bare used with
          | .ok ((scene,boxes),styles) => pure (scene,boxes,styles,bare,[{skip := .svgContent, «where» := s!"{n} inline svg elements", refusal := e}])
          | .error _ => throw e
  let hoverRules := rules.any fun rule => rule.selectors.any fun sel =>
    sel.parts.any (·.pseudo.contains .hover) || sel.slotted.any (·.pseudo.contains .hover)
  let laid : Laid := {scene := scene,boxes := boxes,face := face,hoverRules := hoverRules,words := memo}
  -- A page whose text resolves to `serif` while the engine holds no serif face says so; a
  -- host with a page font then gives the face and draws again. Others pay nothing more.
  let wantsSerif := serifWanted h.serif loaded.isSome fun _ => textWantsSerif heldFamilies dom styles
  let wantsMono := serifWanted h.mono loaded.isSome fun _ => textWants .monospace heldFamilies dom styles
  return ({laid with dom := dom}
    |> fun l => {l with rules := rules}
    |> fun l => {l with textScale := textScale}
    |> fun l => {l with state := state}
    |> fun l => {l with treeScope := treeScope}
    |> fun l => {l with styles := Thunk.pure (.ok styles)}
    |> fun l => {l with paint := paint}
    |> fun l => {l with wantsSerif := wantsSerif}
    |> fun l => {l with wantsMono := wantsMono}
    |> fun l => {l with limits := limits},d1 ++ d2 ++ d0 ++ d3 ++ d4)

/-- `layOut` after the parse: the layout of the arena `dom`, `width` by `rows` CSS pixels,
in the mode of the request (`WebAccept.accept`). A script session's layout reads
(`measure`) lay its arena out here, with no parse. -/
def layOutDOM (h : Holds) (request : JSON.Json) (graph : Option NativeFoafNaut.Model) (dom : DOM.Dom) (width rows : Nat)
    (held : List (String × String)) (pointer : Option Nat × Option Nat) (kept : Kept := {}) : Except String Laid := do
  -- `WebAccept.accept`, with what the strict run made kept for the liberal run.
  let run := fun (k : Kept) (m : WebAccept.Mode) => (layOutDOMIn h m request graph dom width rows held pointer k).run.run {}
  let (first,made1) := run kept .strict
  let (result,made) := match WebAccept.strictly first,WebAccept.mode request with
    | .ok a,_ => (Except.ok (a,[]),made1)
    | .error e,.strict => (.error e,made1)
    | .error _,.liberal => let (second,made2) := run (kept.add made1) .liberal; (second,made1.merge made2)
  let (laid,ds) ← result
  return {laid with diagnostics := ds,made}

/-- Liberal mode is a conservative extension of strict mode for layout: when the strict
layout of a request succeeds, the liberal layout is the same, with no diagnostics. Stated
with nothing kept. Does not say: that `layOutDOM` is this `accept`; it gives the liberal
run what the strict run made, and that this changes no layout is not proved. -/
theorem layOut_liberal_conservative (h₀ : Holds) (request : JSON.Json) (graph : Option NativeFoafNaut.Model) (dom : DOM.Dom)
    (width rows : Nat) (held : List (String × String)) (pointer : Option Nat × Option Nat)
    (laid : Laid) (ds : List WebAccept.Diagnostic)
    (h : WebAccept.accept .strict (fun m => Id.run ((layOutDOMIn h₀ m request graph dom width rows held pointer).run.run' {})) = .ok (laid,ds)) :
    WebAccept.accept .liberal (fun m => Id.run ((layOutDOMIn h₀ m request graph dom width rows held pointer).run.run' {})) = .ok (laid,[]) ∧ ds = [] :=
  WebAccept.liberal_conservative _ laid ds h

/-- The same for what the host fetches (`inspect`). -/
theorem inspect_liberal_conservative (dom : DOM.Dom) (url : String) (scripting : Bool) (j : JSON.Json)
    (ds : List WebAccept.Diagnostic)
    (h : WebAccept.accept .strict (fun m => inspectIn m dom url scripting) = .ok (j,ds)) :
    WebAccept.accept .liberal (fun m => inspectIn m dom url scripting) = .ok (j,[]) ∧ ds = [] :=
  WebAccept.liberal_conservative _ j ds h

/-! The scale of a CSS-pixel layout to device pixels (section "Device pixels"): the
scene goes into one group that scales by `k`, so the rasterizer draws each path, glyph
and image at device resolution; the boxes, glyph runs and link regions, which the host
and the selection read as numbers, are multiplied by `k`. -/

/-- The request with no field `key`. -/
def withoutField (key : String) : JSON.Json → JSON.Json
  | .object fields => .object (fields.filter (·.1 != key))
  | j => j

/-- The uniform scale by `k`. -/
def deviceScale (k : Float) : Rendering.Transform := ⟨k,0,0,k,0,0⟩

def boxToDevice (k : Float) (b : Rendering.Layout.Box) : Rendering.Layout.Box :=
  {b with x := b.x*k, y := b.y*k, width := b.width*k, height := b.height*k}

def runToDevice (k : Float) (r : Rendering.GlyphRun) : Rendering.GlyphRun :=
  {r with fontSize := r.fontSize*k,
          glyphs := r.glyphs.map fun g => {g with x := g.x*k, y := g.y*k, advance := g.advance*k}}

def linkToDevice (k : Float) (r : Rendering.LinkRegion) : Rendering.LinkRegion :=
  {r with x := r.x*k, y := r.y*k, width := r.width*k, height := r.height*k}

/-- A scene laid out in CSS pixels, drawn `width` by `rows` device pixels at `k` device
pixels for each CSS pixel. -/
def sceneToDevice (k : Float) (width rows : Nat) (s : Rendering.Scene) : Rendering.Scene :=
  {s with width := width, height := rows,
          mapping := {s.mapping with viewportWidth := Float.ofNat width, viewportHeight := Float.ofNat rows},
          tree := [.group none (deviceScale k) s.tree],
          glyphRuns := s.glyphRuns.map (runToDevice k),
          links := s.links.map (linkToDevice k)}

/-- A layout in CSS pixels at the ratio `unit` (`zoomUnit`), in the device pixels of a
window `width` by `rows`. The document, rules, text scale and styles stay those of the
layout: a pointer state is painted on this scene by colour alone (`restyle`). -/
def Laid.toDevice (l : Laid) (unit width rows : Nat) : Laid :=
  let k := Float.ofNat unit / 100
  {l with scene := sceneToDevice k width rows l.scene, boxes := l.boxes.map (boxToDevice k)}

/-- The scale keeps every link region and box, in order: one for one, scaled. -/
theorem toDevice_sizes (l : Laid) (unit width rows : Nat) :
    (l.toDevice unit width rows).boxes.size = l.boxes.size ∧
    (l.toDevice unit width rows).scene.links.size = l.scene.links.size ∧
    (l.toDevice unit width rows).scene.glyphRuns.size = l.scene.glyphRuns.size := by
  simp [Laid.toDevice, sceneToDevice]

/-- The scale changes no source node, document or rule: what a box, link or run belongs
to is that of the CSS-pixel layout. -/
theorem toDevice_sources (l : Laid) (unit width rows : Nat) :
    (l.toDevice unit width rows).boxes.map (·.source) = l.boxes.map (·.source) ∧
    (l.toDevice unit width rows).scene.links.map (·.sourceNode) = l.scene.links.map (·.sourceNode) ∧
    (l.toDevice unit width rows).dom = l.dom ∧ (l.toDevice unit width rows).rules = l.rules := by
  simp [Laid.toDevice, sceneToDevice, boxToDevice, linkToDevice, Array.map_map, Function.comp_def]

/-- Parse, script check, cascade and layout of a render. It reads only the key: the
request it reads is `key.request`, which has only `layoutFields`. With `graphModel`
(the FOAF graph page) the document is `WebGraph.skeleton` of the model, not `key.html`,
and the picture comes from the model with no SVG text (`WebGraph.embedding`). -/
def layOut (h : Holds) (key : LayoutKey) (kept : Kept := {}) : Except String Laid := do
  let request := key.request
  let graph ← match request.field? "graphModel" with
    | none => pure none
    | some (.string wire) => match NativeFoafNaut.Model.decode wire with
      | some m => pure (some m)
      | none => throw "invalid FOAF graph model"
    | some _ => throw "graphModel must be a string"
  let (dom,madeParse) ← prepareDOMIn kept (match graph with | some m => WebGraph.skeleton m | none => key.html) request
  if key.width == 0 || key.height == 0 || key.width > 4096 || key.height > 4096 then throw "unsupported document viewport"
  let rows := max 1 (key.height-key.top)
  -- Device pixels: a page is laid out in CSS pixels and drawn at the ratio. The graph page
  -- keeps device pixels: its model is drawn at the size of the window (`graphInput`).
  let unit := if graph.isSome then 100 else zoomUnit request
  if unit == 100 then
    let laid ← layOutDOM h (if graph.isSome then withoutField "zoomUnit" request else request) graph dom key.width rows key.held key.pointer kept
    return {laid with made := laid.made.merge madeParse}
  else
    let (cssWidth,cssRows,_) := layoutInputs key.width rows 0 unit
    let laid ← layOutDOM h request graph dom (max 1 cssWidth) (max 1 cssRows) key.held key.pointer kept
    return {laid.toDevice unit key.width rows with made := laid.made.merge madeParse}

/-! ### Layout reads of page scripts

A script that reads a size (`clientWidth`, `getBoundingClientRect`, `getBBox`) gets it
from this engine's layout of its arena as it stands (`WasmVM.Hosts.Page.Reads`): laid out
when a read first asks, once until the DOM or the viewport changes, as a browser forces
a layout. The layout is that of a render with the session's `layout` request. -/

/-- The padding box of node `node`'s laid-out boxes, width and height in CSS pixels (its
border box less its borders, as op 17's client size): the containing block that percentage
insets refer to (`Rendering.ComputedGeneric.insetBase`). `none` when the node has no box. -/
def paddingBoxOf (l : Laid) (node : Nat) : Option (Float × Float) :=
  let box := l.boxes.foldl (init := (none : Option WebHit.Bounds)) fun acc b =>
    if b.source != node then acc else
    let r : WebHit.Bounds := (b.x,b.y,b.x+b.width,b.y+b.height)
    some ((acc.map (·.union r)).getD r)
  box.map fun (x0,y0,x1,y1) =>
    let e : Rendering.CSS.Edges := match l.styles.get with
      | .ok styles => (styles[node]?.map (·.borderEdges)).getD {}
      | .error _ => {}
    (max 0 (x1-x0-e.left-e.right), max 0 (y1-y0-e.top-e.bottom))

/-- The answer of a layout read (op 35, the hit test, is below): op 17 "x y w h left top width height parent ox oy" (the border box
in the page, then the client box: inside the borders, then the offset parent's node
(-1: none) and the box's corner from that parent's padding edge; eight zeros for an SVG
element inside an `svg`, which has no CSS box, CSSOM View §6); op 18 an SVG element's bounding box in its
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
      let styles : Array Rendering.CSS.Computed := match l.styles.get with
        | .ok styles => styles
        | .error _ => #[]
      let e : Rendering.CSS.Edges := (styles[node]?.map (·.borderEdges)).getD {}
      -- CSSOM View §7: the offset parent (`Rendering.Layout.offsetParent`; -1 for none) and
      -- the border box's corner from the padding edge of that parent, or from the page.
      let (parent,ox,oy) : Float × Float × Float := match Rendering.Layout.offsetParent l.dom styles node with
        | none => (-1,x0,y0)
        | some p =>
          match l.boxes.find? (·.source == p) with
          | none => (-1,x0,y0)
          | some b =>
            -- A `body` that is not positioned is the offset parent in name only: the offsets
            -- are from the page, as browsers have them.
            if DOM.Dom.isHtmlElement (l.dom.get p) "body" && !(styles[p]?.map (·.pos.isPositioned)).getD false then
              (Float.ofNat p,x0,y0)
            else
              let pe : Rendering.CSS.Edges := (styles[p]?.map (·.borderEdges)).getD {}
              (Float.ofNat p,x0-b.x-pe.left,y0-b.y-pe.top)
      some (line [x0,y0,x1-x0,y1-y0,e.left,e.top,max 0 (x1-x0-e.left-e.right),max 0 (y1-y0-e.top-e.bottom),parent,ox,oy])
    | none => match (WebHit.boundsOf l.dom l.scene node).1 with
      | some (x0,y0,x1,y1) => some (line [x0,y0,x1-x0,y1-y0,0,0,0,0])
      -- no box (`display: none`, a popover that is not showing, not connected): zeros, no
      -- offset parent, and a twelfth number -1 that says there is no box (the page's
      -- `getClientRects` is then empty, CSSOM View §6.1; WebDriver reads the first four)
      | none => some "0 0 0 0 0 0 0 0 -1 0 0 -1"
  | 18 => match (WebHit.boundsOf l.dom l.scene node).2 with
    | some (x0,y0,x1,y1) => some (line [x0,y0,x1-x0,y1-y0])
    | none => some "0 0 0 0"
  -- 35: `elementFromPoint` and `elementsFromPoint` (CSSOM View §5.1). `node` carries the
  -- point, x × 65536 + y in whole CSS pixels of the page. The answer is the target of a
  -- pointer there (`WebHit.target`: the smallest box that holds the point, and inside an
  -- `svg` the shape whose `pointer-events` takes it) and its ancestor elements, topmost
  -- first, as node numbers; "" when no box holds the point.
  | 35 =>
    let px := (node / 65536).toFloat
    let py := (node % 65536).toFloat
    let styles : Array Rendering.CSS.Computed := match l.styles.get with
      | .ok styles => styles
      | .error _ => #[]
    match WebHit.targetWithStyles l.dom l.scene l.boxes styles px py with
    | some (hit,_) =>
      let chain := Id.run do
        let mut acc : Array Nat := #[hit]
        let mut cur := hit
        for _ in [0:l.dom.size] do
          match (l.dom.get cur).parent with
          | some p =>
            if (l.dom.get p).type == .element then
              acc := acc.push p
              cur := p
            else break
          | none => break
        return acc
      some (" ".intercalate (chain.toList.map toString))
    | none => some ""
  -- 38: `scrollWidth` and `scrollHeight` (CSSOM View §6.1), "w h" in whole CSS pixels
  -- (`Rendering.Layout.scrollSize`): the padding box extended to the boxes inside it; for
  -- the root element, the viewport extended to the whole page. "0 0" with no box.
  | 38 =>
    let style : Rendering.CSS.Computed := match l.styles.get with
      | .ok styles => styles[node]?.getD {}
      | .error _ => {}
    match Rendering.Layout.scrollSize l.dom l.boxes style.borderEdges
        (Float.ofNat l.scene.width) (Float.ofNat l.scene.height) node (Rendering.Layout.scrollAxes style) with
    | some (w,h) => some (line [w,h])
    | none => some "0 0"
  -- 21: the used width and height of the node's content box (CSSOM §9.1 resolved values
  -- of `width` and `height`), "" when the node has no box
  | 21 => match box, l.styles.get with
    | some (x0,y0,x1,y1), .ok styles =>
      -- The stored cascade is before viewport edge resolution. The script layout has
      -- a CSS-pixel scene, so use the same viewport that renderStyled used.
      let s := Rendering.Layout.withViewportEdges (styles[node]?.getD {})
        (Float.ofNat l.scene.width) (Float.ofNat l.scene.height)
      let b := s.borderEdges
      some (line [max 0 (x1-x0-b.left-b.right-s.padding.left-s.padding.right),
                  max 0 (y1-y0-b.top-b.bottom-s.padding.top-s.padding.bottom)])
    | _, _ => some ""
  | _ => none

/-- `document.fonts` (CSS Font Loading 3 §5), `node_query` op 22: the faces of the
page's `@font-face` rules as JSON, each with its family, descriptors and status:
`loaded` when the engine holds its font for this page (`webFonts`), else `unloaded`.
The host loads the faces the text uses before the scripts run, so no face is loading. -/
def fontFacesAnswer (h : Holds) (dom : DOM.Dom) (request : JSON.Json) : String :=
  let faces := (fontFaces dom request).toOption.getD #[]
  let fonts := webFaceFonts h faces request
  let hex := fun (n : Nat) => String.ofList (Nat.toDigits 16 n) |>.toUpper
  let entries := (List.range faces.size).map fun i =>
    let f := faces[i]!
    JSON.Json.object [("family",.string f.family),("style",.string f.style),
      ("weight",.string (if f.weight.1 == f.weight.2 then toString f.weight.1 else s!"{f.weight.1} {f.weight.2}")),
      ("unicodeRange",.string (", ".intercalate (f.ranges.map fun (lo,hi) => if lo == hi then s!"U+{hex lo}" else s!"U+{hex lo}-{hex hi}"))),
      ("status",.string (if (fonts[i]?.bind id).isSome then "loaded" else "unloaded"))]
  (JSON.Json.array entries).toString

/-- The request with the animated values of the page's animations, as the field
`animated` that `elementState` reads: each a node, a longhand, its computed text, and
whether a transition gives it. With none, the request as it is. -/
def withAnimated (request : JSON.Json) (overrides : List Rendering.Animation.Override) : JSON.Json :=
  if overrides.isEmpty then request else
  let field : JSON.Json := .array (overrides.map fun o =>
    .array [.number (toString o.node), .string o.property, .string o.value, .bool o.transition])
  match request with
  | .object fields => .object (fields.filter (·.1 != "animated") ++ [("animated", field)])
  | j => j

/-- The image store of the page whose script session starts with `request`, made ahead of
its first layout (`WebRender.storeAhead`, for the tree and the images of the session's
`layout` request, as `layOutDOMIn` reads them): none when the engine keeps it already, when
the page has no image, and when the page or the request can not be read (the layout says
why). -/
def storeAheadOf (h : Holds) (kept : Kept) (html : String) (request : JSON.Json) :
    Option WebRender.StoreEntry :=
  let layout := layoutRequest ((request.field? "layout").getD (.object []))
  match (parseIn kept html (DOM.xmlSyntax (str layout "url") (str layout "syntax"))).1, suppliedImages layout with
  | .ok dom, .ok supplied =>
    let url := baseURL dom (str layout "url")
    let images := supplied ++ heldBytes h (heldNamed h ((namedImages layout).toOption.getD []))
    WebRender.storeAhead kept.stores dom (if url.isEmpty then none else some url) images
  | _, _ => none

/-- The page's `@font-face` faces that the engine holds, each named by its rule's family
(`webFaceFonts`), from the page and the layout fields of a script session's start: Canvas 2D
text picks them by its family list as the page's text does (issue 1075). -/
def canvasFaceFonts (h : Holds) (kept : Kept) (html : String) (request : JSON.Json) : Array Rendering.SfntProfile.Font :=
  let layout := layoutRequest ((request.field? "layout").getD (.object []))
  if (namedWebFonts layout).isEmpty then #[] else
  match (parseIn kept html (DOM.xmlSyntax (str layout "url") (str layout "syntax"))).1 with
  | .ok dom => (webFaceFonts h ((fontFaces dom layout).toOption.getD #[]) layout).filterMap id
  | .error _ => #[]

/-- `kept` with the store of `storeAheadOf`: the layouts that the scripts' reads ask for
before the first frame then find the store and decode no image. -/
def keepStoreAhead (h : Holds) (kept : Kept) (html : String) (request : JSON.Json) : Kept :=
  match storeAheadOf h kept html request with
  | some store => {kept with stores := WebRender.keepStore kept.stores store}
  | none => kept

/-- Kind: property. Says: making the store ahead changes nothing of what the engine keeps
but its image stores: the parsed trees, the read sheets and the words of SVG text are the
same. Does not say: that the store is found by the next layout (`WebRender.storeAhead`
makes it for the keys and images the layout asks for, `WebRender.storeAhead_made`; that the
two lists compare equal is tested, not proved). -/
theorem keepStoreAhead_rest (h : Holds) (kept : Kept) (html : String) (request : JSON.Json) :
    (keepStoreAhead h kept html request).parsed = kept.parsed ∧
    (keepStoreAhead h kept html request).sheets = kept.sheets ∧
    (keepStoreAhead h kept html request).words = kept.words := by
  unfold keepStoreAhead
  split <;> exact ⟨rfl,rfl,rfl⟩

/-- Partial restyles may only touch a few nodes, while repeated ancestor tests ask
for the same class words repeatedly. Read the keys of each node when first needed. -/
@[noinline] private def memoElementKeys (tree : DOM.Dom) : Array (Thunk Rendering.CSS.ElemKey) :=
  Array.ofFn (n := tree.size) fun i => Thunk.mk fun _ => Rendering.CSS.readKeys tree i.val

private def elementKeyWithMemo (tree : DOM.Dom) (memo : Array (Thunk Rendering.CSS.ElemKey))
    (id : Nat) : Rendering.CSS.ElemKey :=
  match memo[id]? with
  | some found => found.get
  | none => Rendering.CSS.readKeys tree id

private theorem elementKeyWithMemo_eq (tree : DOM.Dom) (id : Nat) :
    elementKeyWithMemo tree (memoElementKeys tree) id = Rendering.CSS.readKeys tree id := by
  by_cases h : id < tree.size <;> simp [elementKeyWithMemo, memoElementKeys, h, Thunk.get]

/-- A matcher of rules for the reads of `measure` (the animation rules of op 28 and op 24, and
the rules of the computed values): the rule buckets and the element keys of the tree, made
once. It is data, passed to the functions that use it: a closure over the tables was
compiled with the tables made again at each call (each element read the keys of the whole
document, n², 64 s in one script turn of a Wikipedia article on 2026-11-15). -/
inductive RuleMatcher where
  | empty
  /-- Partial restyles keep a lazily populated key table for their current arena. -/
  | keysMemo (ix : Rendering.CSS.RuleIndex) (ks : Thunk (Array (Thunk Rendering.CSS.ElemKey)))
      (tree : DOM.Dom) (state : Rendering.CSS.ElementState)
  | plain (ix : Rendering.CSS.RuleIndex) (ks : Rendering.CSS.ElemKeys) (tree : DOM.Dom) (state : Rendering.CSS.ElementState)
  | scoped (ix : Rendering.CSS.ScopedIndex) (ks : Rendering.CSS.ElemKeys) (ts : Rendering.CSS.TreeScope) (state : Rendering.CSS.ElementState)

/-- The tables of `rules` over the flat tree `flat`, or over the tree scope's node tree. -/
def RuleMatcher.make (rules : List Rendering.CSS.Rule) (flat : DOM.Dom)
    (treeScope : Option Rendering.CSS.TreeScope) (state : Rendering.CSS.ElementState) : RuleMatcher :=
  match treeScope with
  | .none => .plain (Rendering.CSS.RuleIndex.build rules) (Rendering.CSS.ElemKeys.of flat) flat state
  | .some ts => .scoped (Rendering.CSS.ScopedIndex.build rules) (Rendering.CSS.ElemKeys.of ts.tree) ts state

/-- The matches of element `id`: a look in the tables. -/
def RuleMatcher.matched : RuleMatcher → Nat → List Rendering.CSS.Match
  | .empty, _ => []
  | .keysMemo ix ks tree state, id => ix.matched (elementKeyWithMemo tree ks.get) tree id state
  | .plain ix ks tree state, id => ix.matched (ks.get tree) tree id state
  | .scoped ix ks ts state, id => ix.matched (ks.get ts.tree) ts id state

/-- The memo returns each element's current-arena keys, including during ancestor matches. -/
theorem RuleMatcher.keysMemo_matched (ix : Rendering.CSS.RuleIndex) (tree : DOM.Dom)
    (state : Rendering.CSS.ElementState) (id : Nat) :
    (RuleMatcher.keysMemo ix (Thunk.mk fun _ => memoElementKeys tree) tree state).matched id =
      ix.matched (Rendering.CSS.readKeys tree) tree id state := by
  change ix.matched (elementKeyWithMemo tree (memoElementKeys tree)) tree id state = _
  rw [show elementKeyWithMemo tree (memoElementKeys tree) = Rendering.CSS.readKeys tree from
    funext (elementKeyWithMemo_eq tree)]

#print axioms RuleMatcher.keysMemo_matched

/-- Kind: equivalence. The tables give the matches of the bucket matcher with the keys read
once, as `CSS.computeAll` and `CSS.computeAllIn` take them: the data form changes when the
work is done, not what an element matches. -/
theorem RuleMatcher.make_matched (rules : List Rendering.CSS.Rule) (flat : DOM.Dom)
    (treeScope : Option Rendering.CSS.TreeScope) (state : Rendering.CSS.ElementState) (id : Nat) :
    (RuleMatcher.make rules flat treeScope state).matched id =
      match treeScope with
      | .none => (Rendering.CSS.RuleIndex.build rules).matched ((Rendering.CSS.ElemKeys.of flat).get flat) flat id state
      | .some ts => (Rendering.CSS.ScopedIndex.build rules).matched ((Rendering.CSS.ElemKeys.of ts.tree).get ts.tree) ts id state := by
  cases treeScope <;> rfl

/-- The matches of every element of a tree of `size` nodes, each made when first asked for (one
thunk a node), with the animated values after them (`CSS.withAnimated`). The matcher is an
argument, made before the call: its tables are made once, whatever the number of elements. -/
@[noinline] def RuleMatcher.memo (m : RuleMatcher) (state : Rendering.CSS.ElementState) (size : Nat) :
    Array (Thunk (List Rendering.CSS.Match)) :=
  let matchesOf := Rendering.CSS.withAnimated state m.matched
  Array.ofFn (n := size) fun i => Thunk.mk fun _ => matchesOf i.val

/-- Kind: equivalence. Says: the memo of an element is the matcher's matches of it, with the
animated values: making them once changes when, not what. -/
theorem RuleMatcher.memo_get (m : RuleMatcher) (state : Rendering.CSS.ElementState) (size i : Nat) (h : i < size) :
    ((m.memo state size)[i]'(by simp [RuleMatcher.memo, h])).get = Rendering.CSS.withAnimated state m.matched i := by
  simp [RuleMatcher.memo, Thunk.get]

/-- A WebDriver label can name these native elements even when the renderer
does not draw their own boxes. Other ways of hiding them still apply. -/
private def nativeUnboxedLabel (dom : DOM.Dom) (id : Nat) : Bool :=
  let n := dom.get id
  let has := Rendering.CSS.hasAttribute n
  !has "popover" && !Rendering.CSS.closedDetailsContent dom id &&
    (DOM.Dom.isHtmlElement n "area" ||
      (DOM.Dom.isHtmlElement n "dialog" && !has "open") ||
      (DOM.Dom.isHtmlElement n "optgroup" &&
        n.parent.any fun p => DOM.Dom.isHtmlElement (dom.get p) "select"))

private def labelRootAllowsUnboxed (view : Rendering.ComputedGeneric.View) (id : Nat) : Bool :=
  let d := view.dom
  let style : HTML.AccessibleRole.NameStyle :=
    { displayed := fun n => ((view.styles[n]?).map (·.display != .none)).getD true }
  nativeUnboxedLabel d id && !HTML.AccessibleRole.hiddenEl d id &&
    !((d.get id).parent.any (HTML.AccessibleRole.hiddenReference d style)) &&
    (Rendering.ComputedGeneric.winning
      ((Rendering.ComputedGeneric.cascadedAll view id "display").filter
        fun (key, _) => !Rendering.ComputedGeneric.uaNormal key)).isNone

/-- The layout reads of a script session (`Page.Measure`) with the render request
`request` (its `layoutFields`): the arena laid out `width` by `rows` (`layOutDOM`)
when a read first asks, then the answers from that one layout. `overrides` are the
values of the page's running animations: the cascade and the layout take them
(`CSS.withAnimated`).

`carry` is what an earlier measure of the page left, with the nodes to style again
(`Page.Measure`): the rules, their buckets and the element state are taken from it, and
the styles are its styles with those subtrees styled again (`CSS.restyleWith`); with
none, the cascade of the document. The second answer is what this measure leaves.

For the animation engine (`Page.animationAccess`), with no layout: 24 the cascaded
animation and transition longhands of a node; 25 the text of the document's sheets; 27
the computed text of "property U+0000 value" in the node's style; 28 the elements whose
rules or `style` attribute declare an animation or a transition, as node numbers; 29 the
computed text of the property named; 26 the declarations of the node's rules and `style`
attribute as one text, or with "names" the longhands they declare, with "rules" the
rules' declarations alone, with "style" the longhands of the `style` attribute. -/
def measure (h : Holds) (request : JSON.Json) (kept : Kept := {}) : WasmVM.Hosts.Page.Measure := fun dom width height overrides carry =>
  let request := withAnimated (layoutRequest request) overrides
  let held := heldNamed h ((namedImages request).toOption.getD [])
  let laid : Thunk (Except String Laid) := Thunk.mk fun _ => layOutDOM h request none dom width height held (none,none) kept
  -- what the cascade reads: the flat tree, the rules, the tree scopes, the element state
  let inputs : Thunk (Except String (DOM.Dom × List Rendering.CSS.Rule × Option Rendering.CSS.TreeScope × Rendering.CSS.ElementState × Float)) :=
    Thunk.mk fun _ =>
      match carry with
      | some (c,_) =>
        -- as the measure before read them (`Page.Carry`: nothing they read was written since),
        -- with the animated values of now
        .ok (dom,c.rules,none,{c.state with animated := overrides.map fun o => (o.node,o.property,o.value,o.transition)},1)
      | none => do
        let percent ← scalePercent request
        let textScale := cssTextScale percent (zoomUnit request)
        -- The media environment of the layout (`layOutDOMIn`), so that the computed values a script
        -- reads are of the rules the page is laid out with: a `@media (min-width: …)` block that
        -- the layout applies holds here too. (It was the media type alone, with no viewport.)
        let env := mediaEnv (medium request) width height (percent*100/zoomUnit request)
        let (rules,_) ← rulesWith kept dom request env
        let state := withPointer dom (← elementState dom (baseURL dom (str request "url")) request) (none,none)
        let (flat,rules,treeScope) := flatView kept dom env rules
        return (flat,rules,treeScope,state,textScale)
  -- 40: the text of the document's style sheets, with no layout: the editing algorithms
  -- (`Hosts.Dom.editOp`, `document.execCommand`) read the styles of nodes from it
  let sheetText : Thunk String := Thunk.mk fun _ =>
    match WebAccept.accept (WebAccept.mode request) fun m => sheetsIn m dom request {medium := medium request} with
    | .ok (sheets,_) => sheetSource sheets
    | .error _ => ""
  -- the rules in their buckets: those of the measure before, or made when first asked for
  let index : Thunk Rendering.CSS.RuleIndex := Thunk.mk fun _ =>
    match carry, inputs.get with
    | some (c,_), _ => c.index
    | none, .ok (_,rules,_,_,_) => Rendering.CSS.RuleIndex.build rules
    | none, .error _ => Rendering.CSS.RuleIndex.build []
  -- `getComputedStyle` (op 20) reads the cascade alone: no layout for it
  -- with the styles: the view of `ComputedGeneric`, for the computed value of a property
  -- outside the layout profile (made when asked for): the flat tree and the rules that match
  -- an element, with the animated values after them (`CSS.withAnimated`), as in `computeFor`
  let styled : Thunk (Except String Rendering.ComputedGeneric.View) := Thunk.mk fun _ => do
    let (flat,rules,treeScope,state,textScale) ← inputs.get
    -- the rule buckets of `computeFor` and the element keys, made once here (`RuleMatcher`)
    let matcher : RuleMatcher := match treeScope with
      | some ts => .scoped (Rendering.CSS.ScopedIndex.build rules) (Rendering.CSS.ElemKeys.of ts.tree) ts state
      | none =>
        match carry with
        -- Initialise the table only when the partial restyle first asks for a key.
        | some _ => .keysMemo index.get (Thunk.mk fun _ => memoElementKeys flat) flat state
        | none => .plain index.get (Rendering.CSS.ElemKeys.of flat) flat state
    let matchesOf := Rendering.CSS.withAnimated state matcher.matched
    -- an element's matches are made once a measure: the property table asks for them
    -- several times for one value (the cascaded value, the flow, the logical partner), and the
    -- animation engine reads several values of one element (one thunk a node; none is forced
    -- for a node nobody asks about)
    let memo : Array (Thunk (List Rendering.CSS.Match)) := matcher.memo state flat.size
    let matchesOf : Nat → List Rendering.CSS.Match := fun id =>
      match memo[id]? with
      | some t => t.get
      | none => matchesOf id
    -- the styles: those of the measure before with the named subtrees styled again
    -- (`CSS.restyleWith`), or the cascade of the document
    let whole := fun (_ : Unit) => Rendering.CSS.computeFor treeScope flat rules textScale state
    let styles ← match carry with
      | some (c,roots) =>
        (match Rendering.CSS.restyleWith matchesOf flat c.styles roots with
          | .ok styles => pure styles
          | .error _ => whole ())
      | none => whole ()
    return { dom := flat, matchesOf := matchesOf, styles := styles,
             viewportW := width, viewportH := height,
             -- the rules of the page, for the styles of pseudo-elements
             rules := rules,
             functions := Thunk.mk fun _ => Rendering.ComputedGeneric.functionsOf sheetText.get,
             -- the containing block of a percentage inset: asked only for one, it lays the page out
             paddingBox := fun p => match laid.get with
               | .ok l => paddingBoxOf l p
               | .error _ => none,
             -- the `@property` registrations of the page's sheets, read when a custom property is asked
             registered := Thunk.mk fun _ =>
               Rendering.ComputedGeneric.registrationsOfDocument dom ++ Rendering.ComputedGeneric.registrationsOf sheetText.get }
  -- the styles of the document of a frame in the same arena (root `r`, not the page's
  -- document): a cascade of its own, the UA sheet and the frame document's `style` elements,
  -- from its root (`CSS.computeAllWith` at `r`). The body of such a document takes the margins
  -- of its container's `marginwidth` and `marginheight` (`CSS.containerMarginHints`), which the
  -- script side brings in `q` as U+0002, the two values and U+0000 between them, then the
  -- container's node. A `style` element applies when its `type` and `media` say so in the
  -- frame's media environment (HTML §4.2.6: "the element's media attribute's value matches
  -- the environment"; Media Queries 4 §4: `width` and `height` are the frame's viewport, the
  -- padding box of its container); a frame document none of whose sheets asks for a media
  -- condition lays nothing out for it.
  let frameView := fun (r node : Nat) (q : String) => (do
    let parts := (q.drop 1).toString.splitOn "\x00"
    let styleIds := (dom.treeOrder r).toList.filter fun id => DOM.Dom.isHtmlElement (dom.get id) "style"
    let asksMedia := styleIds.any fun id =>
      !(Rendering.CSS.attrValue (dom.get id) "media").isEmpty || ((dom.textContent id).getD "").contains '@'
    let env : Rendering.MediaQuery.Env := if !asksMedia then {medium := medium request} else
      let viewport := match q.startsWith "\x02", (parts[2]?).bind String.toNat? with
        | true, some f => (match laid.get with
          | .ok l => paddingBoxOf l f
          | .error _ => none)
        | _, _ => none
      { mediaEnv (medium request) width height 100 with
        width := viewport.map (·.1), height := viewport.map (·.2),
        deviceWidth := some width.toFloat, deviceHeight := some height.toFloat }
    let source := String.intercalate "\n" (styleIds.filterMap fun id =>
      match activeSheetIn .liberal env (dom.get id) id with
      | .ok (true, _) => dom.textContent id
      | _ => none)
    let rules ← Rendering.CSS.parseIn env source
    let ix := Rendering.CSS.RuleIndex.build rules
    let matchesOf : Nat → List Rendering.CSS.Match := fun id => ix.matched (Rendering.CSS.readKeys dom) dom id {}
    let styles ← Rendering.CSS.computeAllWith matchesOf dom 1 r
    let n := dom.get node
    let isBody := DOM.Dom.isHtmlElement n "body" && (n.parent.bind fun p => (dom.get p).parent) == some r
    let styles := match isBody, q.startsWith "\x02", parts with
      | true, true, mw :: mh :: _ => styles.modify node (Rendering.CSS.containerMarginHints mw mh)
      | _, _, _ => styles
    return ({ dom := dom, matchesOf := matchesOf, styles := styles, viewportW := width, viewportH := height } :
      Rendering.ComputedGeneric.View) : Except String Rendering.ComputedGeneric.View)
  -- what this measure leaves for the next (`Page.Carry`): for a page with no shadow tree, at
  -- text scale 1 (with rules that read the `style` attribute too: `Carry.readsStyle`)
  let left : Thunk (Option WasmVM.Hosts.Page.Carry) := Thunk.mk fun _ =>
    match styled.get, inputs.get with
    | .ok view, .ok (_,rules,none,state,textScale) =>
      if textScale == 1 then
        some { index := index.get, rules := rules, state := {state with animated := []}, styles := view.styles,
               -- (the rules are those of the measure before when it left them)
               parentOnly := match carry with
                 | some (c,_) => c.parentOnly
                 | none => Rendering.CSS.attributesReachParentOnly rules,
               readsStyle := match carry with
                 | some (c,_) => c.readsStyle
                 | none => Rendering.CSS.readsStyleAttribute rules,
               hasReads := match carry with
                 | some (c,_) => c.hasReads
                 | none => if Rendering.CSS.attributesReachParentOnly rules then none
                   else Rendering.CSS.hasArgumentReads rules }
      else none
    | _, _ => none
  -- the position of each computed style name, for the reads by name of the animation engine
  let nameIndex : Thunk (Std.HashMap String Nat) := Thunk.mk fun _ => Rendering.Animation.Computed.nameIndex ()
  -- the rules that declare an animation or a transition (none on most pages)
  let animationRules : Thunk (List Rendering.CSS.Rule) := Thunk.mk fun _ =>
    match inputs.get with
    | .ok (_,rules,_,_,_) => Rendering.Animation.Css.animationRules rules
    | .error _ => []
  -- their matches of an element, from rule buckets made once when first asked for (as
  -- `CSS.computeFor` matches: an element tries only the rules of its buckets). The buckets
  -- and the element keys are data in the thunk (`RuleMatcher`), not a function: a thunk
  -- whose value was `fun id => …` was compiled with the keys of the whole document read
  -- again at each call, so op 28 cost n² (64 s in one script turn of a Wikipedia article).
  let matcher : Thunk RuleMatcher := Thunk.mk fun _ =>
    match inputs.get with
    | .ok (flat,_,treeScope,state,_) => RuleMatcher.make animationRules.get flat treeScope state
    | .error _ => .empty
  let matchedOf := fun (node : Nat) => matcher.get.matched node
  let element := fun (node : Nat) => node < dom.size && (dom.get node).type == .element
  -- 22: the device pixel ratio of the layout request (`zoomUnit`/100), with no layout
  -- 23: the `@font-face` faces of the page and the state of each (`document.fonts`)
  let answers : WasmVM.Hosts.Page.Answers := fun node op q => if op == 22 then some (Rendering.FloatFormat.format (Float.ofNat (zoomUnit request) / 100))
    else if op == 23 then some (fontFacesAnswer h dom request)
    else if op == 40 then some sheetText.get
    -- 41: the inputs of the layout's media environment (`mediaEnv`): the media type, the
    -- viewport in CSS pixels and the zoom, with no layout. `matchMedia` evaluates its query
    -- in the environment they make (`Hosts.Page.mediaAnswer`).
    else if op == 41 then
      match scalePercent request with
      | .ok percent => some s!"{medium request} {width} {height} {percent*100/zoomUnit request}"
      | .error _ => none
    else if op == 24 then
      if element node then
        some (Rendering.Animation.Css.cascadedText
          (Rendering.Animation.Css.cascaded (if animationRules.get.isEmpty then [] else matchedOf node)
            (Rendering.CSS.attrValue (dom.get node) "style")))
      else some ""
    else if op == 25 then some sheetText.get
    else if op == 26 then
      match styled.get with
      | .ok view =>
        if element node && dom.connected node then
          -- with "names": the declared longhands; "rules": the declarations of the rules alone;
          -- "style": the longhands of the `style` attribute; else the declarations as one text
          some (if q == "names" then "\x00".intercalate (Rendering.Animation.Computed.declaredNames view node)
            else if q == "rules" then Rendering.Animation.Computed.ruleDeclarationText view node
            else if q == "style" then Rendering.Animation.Computed.styleAttributeText view node
            else Rendering.Animation.Computed.declarationText view node)
        else some ""
      | .error _ => some ""
    else if op == 27 then
      match styled.get, q.splitOn "\x00" with
      | .ok view, [property, value] =>
        if element node then Rendering.Animation.Computed.computeIn nameIndex.get view node property value else none
      | _, _ => none
    else if op == 28 then
      let rules := animationRules.get
      -- the elements of the document's tree only: what left the document animates nothing
      let ids := (dom.treeOrder 0).toList.filter fun id =>
        let n := dom.get id
        n.type == .element &&
          (Rendering.Animation.Css.mentions (Rendering.CSS.attrValue n "style") ||
            (!rules.isEmpty && !(Rendering.Animation.Css.cascaded (matchedOf id) "").isEmpty))
      some (" ".intercalate (ids.map toString))
    else if op == 29 then
      match styled.get with
      | .ok view =>
        if element node && dom.connected node then Rendering.Animation.Computed.valueOf nameIndex.get view node q else none
      | .error _ => none
    -- 42: CSS facts for accessible names. Clipping affects paint, while clipped text
    -- can still give a name. "label-root" also asks whether the direct WebDriver
    -- label target is a native element without its own renderer box.
    else if op == 42 then
      let root := dom.shadowIncludingRoot node
      match (if root != 0 then frameView root node "" else styled.get) with
      | .ok view => (view.styles[node]?).map fun c =>
          if c.display == .none then
            if q == "label-root" && (c.visible || c.clipHidden) && labelRootAllowsUnboxed view node
            then "native-unboxed" else "none"
          else if !c.visible && !c.clipHidden then "hidden"
          else "visible"
      | .error _ => none
    -- grid: the resolved `grid-template-columns` and `grid-template-rows` of a grid container
    -- are its used track sizes (CSS Grid 2 §7.2.6), read from its layout; any other value is
    -- the computed value below
    else if let some r := (if op ≥ 200 then Rendering.Layout.gridResolvedAt
        (fun _ => match laid.get with | .ok l => l.scene.tree | .error _ => []) node (op - 200) else none) then some r
    else if op == 20 || op == 36 || op ≥ 200 then
      let root := dom.shadowIncludingRoot node
      match (if element node && root != 0 && dom.connected node then frameView root node q else styled.get) with
      -- CSSOM §9 getComputedStyle: an element that is not connected to the page's
      -- document has no computed style (the declaration is empty)
      | .ok view => if element node && dom.connected node then
          let c := view.styles[node]?.getD {}
          -- 36: the custom properties that apply to the element (35 is the hit test); 200 + k: the k-th property's value
          some (if op == 20 then Rendering.ComputedValues.text c
            else if op == 36 then Rendering.ComputedGeneric.customNamesText view node
            else Rendering.Animation.Computed.resolvedAt view node (op - 200) fun _ =>
              -- the laid out border box, for a percentage of a box whose size is not a length
              match laid.get with
              | .ok l => (readAnswer l node 17).bind Rendering.Animation.Computed.sizeOfBox
              | .error _ => none)
        else some ""
      | .error _ => none
    else match laid.get with
    | .ok l => readAnswer l node op
    | .error _ => none
  (answers,left)

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

/-- A memo is valid when each value is the layout of its key. `Engine.layOutKept` makes
only such entries. -/
def ValidEntry (h : Holds) (memo : Lru LayoutKey Laid) : Prop := Lru.Valid (layOut h) memo

def lookupLayout (h : Holds) (memo : Lru LayoutKey Laid) (key : LayoutKey) : Except String Laid :=
  Lru.lookup (layOut h) memo key

theorem lookupLayout_eq (h : Holds) (memo : Lru LayoutKey Laid) (valid : ValidEntry h memo) (key : LayoutKey) :
    lookupLayout h memo key = layOut h key :=
  Lru.lookup_eq (layOut h) memo valid key

/-- The memo that a render leaves is valid. -/
theorem stored_valid (h : Holds) (memo : Lru LayoutKey Laid) (valid : ValidEntry h memo) (key : LayoutKey) (laid : Laid)
    (made : layOut h key = .ok laid) : ValidEntry h (Lru.putIn LayoutKey.html layoutSlots memo key laid) :=
  Lru.putIn_valid LayoutKey.html (layOut h) layoutSlots memo valid key laid made

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

/-- Kind: property. Says: the animated values and the imported sheets are layout fields: two
requests that differ in either are two layouts, and a kept layout of one is not used for
the other. -/
theorem animated_imported_layout_fields : "animated" ∈ layoutFields ∧ "imported" ∈ layoutFields := by
  decide

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

/-- Kind: determinism theorem (hosts). Says: two render requests that agree on every layout
field give the same layout of the same source, window, held fonts, held images and pointer
state: nothing else a host puts in a request (its shell and scroll, the operation, the answer
format, checks) reaches the layout. Does not say: that two hosts send requests that agree on
the layout fields (`labs/demos/foafnaut/host_parity_test.ts` checks the hosts), nor that the
bytes a host fetched for a field are the same in both. -/
theorem layOut_agree (h : Holds) (kept : Kept) (html : String) (a b : JSON.Json) (width height top : Nat)
    (fonts held : List (String × String)) (pointer : Option Nat × Option Nat)
    (agree : ∀ k ∈ layoutFields, a.field? k = b.field? k) :
    layOut h ⟨html,layoutRequest a,width,height,top,fonts,held,pointer⟩ kept =
      layOut h ⟨html,layoutRequest b,width,height,top,fonts,held,pointer⟩ kept := by
  rw [layoutRequest_congr a b agree]

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

/-- The key of paint-only values (`WebPaint.state`): equal values give equal keys. -/
def paintKey (values : Std.TreeMap Nat (Rendering.Transform × Option Float)) : String :=
  ";".intercalate (values.toList.map fun (n,(m,o)) => s!"{n}:{m.a},{m.b},{m.c},{m.d},{m.e},{m.f},{o.getD (-1)}")

/-- Pointer states painted on a kept layout (`:hover`, `:active`), kept apart from the
layouts so that they do not push a layout out: a press, a hover and a loading frame under
the pointer then give the same layout object again, and the page layer that
`pageArtifact` keeps for it. -/
def paintedSlots : Nat := 2

/-- The pointer state of `pointer` painted on a layout with none (`WebRepaint`): the
layout with the new colours, or none when a style of that state changes geometry. -/
def restyle (base : Laid) (pointer : Option Nat × Option Nat) : Option Laid := do
  let .ok old := base.styles.get | none
  let .ok new := Rendering.CSS.computeFor base.treeScope base.dom base.rules base.textScale (withPointer base.dom base.state pointer) | none
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
  ∀ h key base laid, layOut h {key with pointer := (none,none)} = .ok base → restyle base key.pointer = some laid →
    layOut h key = .ok laid

/-- With a valid memo and a sound restyle, a frame is the layout of its key: the cost
cut (no layout for a colour-only hover) gives the picture of the expensive path.
`Engine.frame` is this with the counting of `frameWork` added. -/
theorem frameWith_eq (h : Holds) (memo : Lru LayoutKey Laid) (valid : ValidEntry h memo) (sound : RestyleSound)
    (key : LayoutKey) : frameWith (lookupLayout h memo) key = layOut h key := by
  unfold frameWith
  simp only [lookupLayout_eq h memo valid]
  split
  · rfl
  · cases hb : layOut h {key with pointer := (none,none)} with
    | error e => rfl
    | ok base =>
      simp only
      cases hr : restyle base key.pointer with
      | none => rfl
      | some laid => exact (sound h key base laid hb hr).symm

/-! ### The engine's state (issue 390)

What the engine keeps between calls of its C ABI, as a value: the shim holds it and
passes it to each call, which gives back the next one. -/

/-- Page answers the engine keeps for `have` (the frame on screen and a prefetched band). -/
def pagesSentSlots : Nat := 3

/-- The engine's state between calls. -/
structure Engine where
  /-- Held fonts, web fonts and images (`fontLoad`, `imageLoad`). -/
  holds : Holds := {}
  /-- Page scripts: the guest module and the session (`WebScripts`). -/
  scripts : WebScripts.Held := {}
  /-- The layouts of the last keys (`lookupLayout`). -/
  layouts : Lru LayoutKey Laid := []
  /-- Frames with a pointer state painted on a kept layout (`paintedSlots`). -/
  painted : Lru LayoutKey Laid := []
  /-- Layouts done, kept layouts used, pointer states painted on a kept layout, since the
  start or the last `frameWork` with `reset`. -/
  frameWork : Nat × Nat × Nat := (0,0,0)
  /-- The link regions of the frame on screen, decoded once, by their text (`decodeKept`). -/
  links : Option (String × List Rendering.LinkRegion) := none
  /-- The last layout number given (`Laid.serial`). -/
  serial : Nat := 0
  /-- The last paint-only scene: the number of its layout, its values' key (`paintKey`),
  and the scene, so that a frame whose values did not change gives the same scene object
  (and `pageArtifact` its kept band). -/
  paintedScene : Option (Nat × String × Rendering.Scene) := none
  /-- Frames painted on a kept layout with transforms or animation values (`WebPaint`). -/
  paintWork : Nat := 0
  /-- Parsed trees, read sheets and image stores of the last layouts (`Kept`). -/
  kept : Kept := {}
  /-- The document's subresource requests in progress (`subresource`, Net.Subresource). -/
  subs : Net.Subresource.Table := {}
  /-- Image requests in progress whose URL is of their document's origin, by transfer id
  (`Engine.subresource`). -/
  subImages : List (Nat × String) := []
  /-- Image URLs of their document's origin whose last answer was opaque (a redirect to
  another origin): not origin-clean for a canvas (`canvasEnv`, origin isolation C2). Past
  `maxOpaqueImages` every image is taken as not origin-clean (`opaqueFull`). -/
  opaqueImages : Std.HashSet String := {}
  opaqueFull : Bool := false
  /-- The `@font-face` faces of the last script session started that has web fonts
  (`canvasFaceFonts`, issue 1075): its Canvas 2D text picks them by family. One engine (a worker
  or a session) holds one tab, so this is that tab's page; a frame that starts later with web fonts of its
  own replaces it. -/
  canvasFaces : Array Rendering.SfntProfile.Font := #[]
  /-- The live regions of the last accessibility tree given (`accessibilityAnswer`); none
  until a host asks for a tree. -/
  axLive : Option (String × List HTML.AccessibleTree.Region) := none
  /-- The last chrome layer answer and the inputs it was made from (`ChromeKey`, issue 1124). -/
  chromeKept : Option (ChromeKey × (String × Array ByteArray)) := none
  /-- The last answer with no layers and the inputs it was made from (`PlainKey`, issue 1124). -/
  plainKept : Option (PlainKey × (String × Array ByteArray)) := none
  /-- Chrome layers and answers with no layers given again from `chromeKept` and `plainKept`. -/
  keptWhole : Nat × Nat := (0,0)
  /-- The layout sections of the last band (`WebRender.layoutSections`), by the layout's number
  and the band's top (issue 1124, stage B). -/
  layoutKept : Option ((Nat × Nat) × (ByteArray × ByteArray)) := none
  /-- The last page layer answers given, whole: `damage.id`, storage bytes, tile bytes
  (`pageForHost`, issue 1124 stage C); at most `pagesSentSlots`. -/
  pagesSent : List (Nat × ByteArray × ByteArray) := []
  /-- The page layer answers kept for the next frame, their counts and the last `damage.id`
  (`pageArtifact`, `layersJSON`). -/
  pages : KeptPages := {}

instance : Inhabited Engine := ⟨{}⟩

/-- The layout of `key` from the memo, or laid out and kept. A layout also gives back the
word memo of the held fonts, which the engine keeps (`Laid.words`). A hit moves its entry
first, as `Lru.put`. -/
def Engine.layOutKept (e : Engine) (key : LayoutKey) : Engine × Except String Laid :=
  let (l,k,r) := e.frameWork
  match Lru.find? e.layouts key with
  | some laid => ({e with layouts := Lru.putIn LayoutKey.html layoutSlots e.layouts key laid,frameWork := (l,k+1,r)},.ok laid)
  | none =>
    match layOut e.holds key e.kept with
    | .error x => (e,.error x)
    | .ok laid =>
      let kept := e.kept.add laid.made
      let holds := match laid.words with
        | some words => {e.holds with font := e.holds.font.map ({· with memo := words})}
        | none => e.holds
      let laid := {laid with serial := e.serial+1,made := {}}
      let layouts := Lru.putIn LayoutKey.html layoutSlots e.layouts key laid
      ({e with layouts,frameWork := (l+1,k,r),holds,serial := e.serial+1,kept},.ok laid)

/-- `frameWith` over the kept layouts, counting a repaint. -/
def Engine.frameKept (e : Engine) (key : LayoutKey) : Engine × Except String Laid :=
  if key.pointer == (none,none) then e.layOutKept key else
  match e.layOutKept {key with pointer := (none,none)} with
  | (e,.ok base) =>
    match restyle base key.pointer with
    | some laid =>
      let (l,k,r) := e.frameWork
      ({e with frameWork := (l,k,r+1),serial := e.serial+1},.ok {laid with serial := e.serial+1})
    | none => e.layOutKept key
  | (e,.error _) => e.layOutKept key

/-- The layout of a render: a key with a pointer state is looked up in the painted memo
first. Does not say: that the answer is `layOut e.holds key`. `frameWith_eq` gives that
for a valid memo and a sound restyle; that `e.layouts` is valid for `e.holds` is not
proved (a layout changes the word memo in `e.holds`, which changes no layout). -/
def Engine.frame (e : Engine) (key : LayoutKey) : Engine × Except String Laid :=
  if key.pointer == (none,none) then e.frameKept key else
  match Lru.find? e.painted key with
  | some laid =>
    let (l,k,r) := e.frameWork
    ({e with painted := Lru.putIn LayoutKey.html paintedSlots e.painted key laid,frameWork := (l,k+1,r)},.ok laid)
  | none =>
    match e.frameKept key with
    | (e,.ok laid) => ({e with painted := Lru.putIn LayoutKey.html paintedSlots e.painted key laid},.ok laid)
    | other => other

/-- `WebPaint.patch` of `laid`'s scene with `values`: the scene made before for the same
kept layout (`Laid.serial`) and values again, else a new one (counted in `paintWork`).
Not proved: that the kept scene is `WebPaint.patch laid.paint values laid.scene`. It is
made only by `fresh`, for the layout of its number, and kept layouts with one number are
one value. -/
def Engine.paint (e : Engine) (laid : Laid) (values : Std.TreeMap Nat (Rendering.Transform × Option Float)) :
    Rendering.Scene × Engine :=
  let key := paintKey values
  match e.paintedScene with
  | some (n,k,made) =>
    if laid.serial != 0 && n == laid.serial && k == key then (made,e) else fresh key
  | none => fresh key
where fresh (key : String) :=
  let made := WebPaint.patch laid.paint values laid.scene
  (made,{e with paintedScene := some (laid.serial,key,made),paintWork := e.paintWork+1})

/-- `cpu:true`: each scene of a bytes answer also carries its CPU pixels. -/
private def cpuPixels (request : JSON.Json) : Bool := request.field? "cpu" == some (.bool true)

/-- A render answer in liberal mode says what it skipped, when the request asks
(`diagnostics:true`; a host asks on the first frame of a page): `diagnostics`
(`WebAccept.Diagnostic.json`) at the end of its JSON head. Other frames pay nothing. -/
def withDiagnostics (request : JSON.Json) (laid : Laid) (answer : String × Array ByteArray) : String × Array ByteArray :=
  let (text,sections) := answer
  if request.field? "diagnostics" != some (.bool true) || (laid.diagnostics.isEmpty && laid.limits.isEmpty) || !text.endsWith "}" then answer
  else
    let entries := laid.diagnostics.map WebAccept.Diagnostic.json ++ laid.limits.map WebAccept.LimitHit.json
    ((text.dropEnd 1).toString ++ ",\"diagnostics\":" ++ (JSON.Json.array entries).toString ++ "}",sections)

/-- A render answer of a layout whose text wants the serif face or the monospace face that the
engine does not hold (`Laid.wantsSerif`, `Laid.wantsMono`) says `"wantsSerif":true` or
`"wantsMono":true` at the end of its JSON head; others are as before. -/
def withWants (laid : Laid) (answer : String × Array ByteArray) : String × Array ByteArray :=
  let (text,sections) := answer
  if !(laid.wantsSerif || laid.wantsMono) || !text.endsWith "}" then answer
  else
    let more := (if laid.wantsSerif then ",\"wantsSerif\":true" else "") ++ (if laid.wantsMono then ",\"wantsMono\":true" else "")
    ((text.dropEnd 1).toString ++ more ++ "}",sections)

/-- What the accessibility tree reads of a layout (`HTML.AccessibleTree.Env`): an element
with `display: none` makes no box, `visibility` hides one, and the border boxes. With no
computed styles (a layout that kept none) the markup decides what makes no box. -/
def accessibilityEnv (laid : Laid) : HTML.AccessibleTree.Env :=
  let styles : Array Rendering.CSS.Computed := match laid.styles.get with
    | .ok s => s
    | .error _ => #[]
  let int := fun (f : Float) => f.round.toInt64.toInt
  let env : HTML.AccessibleTree.Env :=
    { rendered := fun k => match styles[k]? with
        | some s => !(s.display == .none)
        | none => !HTML.AccessibleTree.markupUnrendered laid.dom k,
      visible := fun k => match styles[k]? with
        | some s => s.visible
        | none => true,
      clipped := fun k => match styles[k]? with
        | some s => s.clipHidden
        | none => false }
  env.withBoxes (laid.boxes.map fun b => (b.source, ⟨int b.x, int b.y, (int b.width).toNat, (int b.height).toNat⟩))

/-- The first number of the chrome's accessibility nodes (`WebShell.accessible`): above the
node numbers of any page laid out. -/
def accessibilityChromeBase : Nat := 1073741824

/-- The live regions of the last accessibility tree the engine gave: the page's source and
its regions (`HTML.AccessibleTree.regions`). -/
abbrev LiveKept := Option (String × List HTML.AccessibleTree.Region)

/-- Op `accessibilityTree`: the accessibility tree of the page of a render request (the same
fields as the frame's, so the kept layout answers). `{"serial", "top", "scroll", "nodes",
"announce"}`: `nodes` as `HTML.AccessibleTree.json` gives them (with `mac: true`, each with
its `ax`: `jsonMac`; with `web: true`, each with its `web`: `jsonWeb`), each `box` in the layout's pixels from the top of the page; `top` is
the chrome's height and `scroll` the page's scroll, so a box is at `y - scroll + top` in
the window. With a `shell` the chrome's controls come first (`WebShell.accessible`), each
`fixed: true` with its box in window pixels. `announce` lists the live regions to speak, `{"live", "text"}`: those whose
text is not what the last tree of this page had (`live` is what the engine kept of that
tree; the first tree of a page speaks nothing). `serial` is the layout's number: with
`since` equal to it the answer is `{"serial", "unchanged": true, "top", "scroll"}` and no tree is made. With
`view: true` the answer is `{"source"}`: the tree as a page for a person
(`HTML.AccessibleTree.viewPage`), about the request's `url`. Also answers what the engine
keeps next. -/
def accessibilityAnswer (laid : Laid) (html : String) (request : JSON.Json) (top scroll : Nat) (live : LiveKept)
    (chrome : List HTML.AccessibleTree.Entry := []) : String × LiveKept :=
  let number := fun (n : Nat) => JSON.Json.number (toString n)
  let since := match request.field? "since" with
    | some (.number n) => n.toNat?
    | _ => none
  if laid.serial != 0 && since == some laid.serial then
    ((JSON.Json.object [("serial",number laid.serial),("unchanged",.bool true),("top",number top),
      ("scroll",number scroll)]).toString,live)
  else
    let entries := HTML.AccessibleTree.tree laid.dom (accessibilityEnv laid)
    if request.field? "view" == some (.bool true) then
      ((JSON.Json.object [("source",.string (HTML.AccessibleTree.viewPage (str request "url") entries))]).toString,live)
    else
      let regions := HTML.AccessibleTree.regions laid.dom entries
      let speak := match live with
        | some (page,old) => if page == html then HTML.AccessibleTree.announcements old regions else []
        | none => []
      let pick := fun (es : List HTML.AccessibleTree.Entry) =>
        match (if request.field? "mac" == some (.bool true) then HTML.AccessibleTree.jsonMac es
          else if request.field? "web" == some (.bool true) then HTML.AccessibleTree.jsonWeb es
          else HTML.AccessibleTree.json es) with
        | .object [(_,.array items)] => items
        | _ => []
      -- The chrome's nodes first, marked `fixed`: their boxes are window pixels and do not scroll.
      -- Their numbers start above every node of a page (a page that large gets no chrome nodes).
      let fixed := if laid.dom.size < accessibilityChromeBase then
          (pick chrome).map (fun n => match n with
            | .object fields => JSON.Json.object (fields ++ [("fixed",.bool true)])
            | other => other)
        else []
      ((JSON.Json.object ([("serial",number laid.serial),("top",number top),("scroll",number scroll),
        ("nodes",.array (fixed ++ pick entries))] ++
        [("announce",.array (speak.map fun (l,t) => .object [("live",.string l),("text",.string t)]))])).toString,
       some (html,regions))

/-- An operation of the engine: it reads and changes the engine's state, and reads the
machine through `M` (`BaseIO` in the engine, `Id` in tests: time 0, no random bytes). -/
abbrev DocM (M : Type → Type) := ExceptT String (StateT Engine M)

/-- A step on the state that also answers. -/
@[inline] def stepState {M : Type → Type} [Monad M] {α : Type} (f : Engine → Engine × Except String α) : DocM M α := do
  match ← modifyGet fun e => let (e,r) := f e; (r,e) with
  | .ok a => pure a
  | .error x => throw x

/-- An `ExceptT String M` operation in `DocM M`. -/
@[inline] def ofExceptT {M : Type → Type} [Monad M] {α : Type} (x : ExceptT String M α) : DocM M α := do
  match ← (x.run : M _) with
  | .ok a => pure a
  | .error e => throw e

/-- An answer of op `subresource`: the request for the host to make, done, or failed. -/
def subresourceJson : Net.Subresource.Out → JSON.Json
  | .wire id w => .object [("id", WebScripts.num id), ("wire", WebScripts.wireJson w)]
  | .done id st ty u hidden body =>
    .object [("id", WebScripts.num id), ("done", .object ([("status", WebScripts.num st), ("type", .string ty),
      ("url", .string u), ("opaque", .bool hidden)] ++
      (match body with | some b => [("bodyBase64", .string (WHATWG.Base64.encode b))] | none => [])))]
  | .fail id why => .object [("id", WebScripts.num id), ("fail", .string why)]

/-- Op `subresource` (Net.Subresource): a document's element request, one step a call.
`start`: `kind` (its destination), `url`, `documentURL`, `referrerPolicy` (the element's
`referrerpolicy` or the document's; "" for the default), `crossorigin` ("", "anonymous",
"use-credentials"), `hostCors` and `address` as for `scriptSession start`. `answer`: `id` and
the host's `answer` to the wire (as action `net` gives one; the body may be left out: the
host keeps the bytes). `cancel`: `id`. The referrer is the document's URL. -/
def subresourceOp (tab : Net.Subresource.Table) (request : JSON.Json) : Net.Subresource.Table × Option Net.Subresource.Out × String :=
  match str request "action" with
  | "start" =>
    let doc := str request "documentURL"
    let page := Net.PageFetch.Page.ofUrl doc (request.field? "hostCors" == some (.bool true)) (str request "address")
    let policy := (Net.ReferrerPolicy.Policy.ofToken (str request "referrerPolicy")).getD .default
    let cors := match str request "crossorigin" with
      | "" => none
      | "use-credentials" => some true
      | _ => some false
    let (tab, o) := Net.Subresource.start tab page (str request "kind") (str request "url") doc policy cors
    (tab, some o, (subresourceJson o).toString)
  | "answer" =>
    let id := match request.field? "id" with | some (.number n) => n.toNat?.getD 0 | _ => 0
    let (_, a) := WebScripts.netAnswer ((request.field? "answer").getD .null)
    let (tab, o) := Net.Subresource.answer tab id a
    (tab, some o, (subresourceJson o).toString)
  | "cancel" =>
    let id := match request.field? "id" with | some (.number n) => n.toNat?.getD 0 | _ => 0
    (Net.Subresource.cancel tab id, none, "{}")
  | _ => (tab, none, "{\"error\":\"subresource: unknown action\"}")

/-- Most image URLs `Engine.opaqueImages` holds. -/
def maxOpaqueImages : Nat := 4096

/-- Op `subresource`, and what a canvas needs of it: an image of its document's origin whose
answer is opaque (Fetch: a no-cors request redirected to another origin is) is recorded, so a
canvas that draws it is not origin-clean although its URL is of the page's origin (HTML
§4.12.5.1.14: "the image's current request's image data is CORS-cross-origin"). An image of
another origin needs no record: its URL marks it (`Net.PageFetch.Page.imageClean`). -/
def Engine.subresource (e : Engine) (request : JSON.Json) : Engine × String :=
  let (subs, out, answer) := subresourceOp e.subs request
  let live := fun (id : Nat) => subs.live.any (·.1 == id)
  let e := { e with subs }
  let e := match out with
    | some (.wire id _) =>
      let url := str request "url"
      if str request "action" == "start" && str request "kind" == "image" &&
          (Net.PageFetch.Page.ofUrl (str request "documentURL")).imageClean url then
        { e with subImages := (id, url) :: e.subImages.filter (live ·.1) }
      else e
    | some (.done id _ _ _ hidden _) =>
      match e.subImages.find? (·.1 == id) with
      | some (_, url) =>
        let e := { e with subImages := e.subImages.filter (·.1 != id) }
        if !hidden then { e with opaqueImages := e.opaqueImages.erase url }
        else if e.opaqueImages.size ≥ maxOpaqueImages then { e with opaqueFull := true }
        else { e with opaqueImages := e.opaqueImages.insert url }
      | none => e
    | some (.fail id _) => { e with subImages := e.subImages.filter (·.1 != id) }
    | none => e
  (e, answer)

/-- A document request, with `laidOut` as the layout of a render. `run` passes the
kept layout (`Engine.frame`); `runUncached` passes `layOut`, so that tests compare the two. With
`bytes`, a render answer names its storage floats and tile words as sections
(`DataForm.sections`) and gives their bytes; other answers have no section. -/
def answerWith {M : Type → Type} [Monad M] [WebWasm.Machine M] (laidOut : LayoutKey → DocM M Laid) (bytes : Bool) (html : String)
    (request : JSON.Json) (width height : Nat) : DocM M (String × Array ByteArray) := do
  let .object fields := request | throw "document request must be an object"
  if (fields.map Prod.fst).eraseDups.length != fields.length then throw "duplicate document request field"
  if str request "op" == "epubReader" then
    -- The host transports bytes. The EPUB reader sets all limits and generates passive HTML.
    if html.utf8ByteSize > (Epub.maxArchiveBytes + 2) / 3 * 4 then throw "EPUB archive size limit exceeded"
    let some archive := WHATWG.Base64.decode html | throw "Invalid EPUB byte transport"
    let book ← Epub.openBook archive
    let page ← book.readerHtml (some (natField request "epubChapter"))
    return ((JSON.Json.object [("source", .string page)]).toString, #[])
  if str request "op" == "fontLoad" then
    return (← stepState fun e => let (h,r) := loadFont e.holds request; ({e with holds := h},r),#[])
  -- A document's subresource requests go through the engine's network rules, step by step.
  if str request "op" == "subresource" then
    return (← stepState fun e => let (e, r) := e.subresource request; (e, .ok r),#[])
  -- What a navigation's response does: shown as a page, or saved as a download under a safe
  -- name (`Net.Subresource.navigated`, theorem `safeName_safe`). The host asks before it reads
  -- the body.
  -- The browser's cookies for page loads (`Net.Cookies`: `navCookie`, `navSet`, `Jar.persistent`,
  -- theorems `sentNav_safe`, `persistent_no_session`): the host keeps the jar as text and asks
  -- at each hop of a navigation; it writes to disk only what `keep` answers.
  if str request "op" == "cookies" then
    let jar := Net.Cookies.Jar.ofWire (str request "jar")
    let now := (str request "now").toNat?.getD 0
    let answer := match str request "action" with
      | "request" => JSON.Json.object [("cookie", .string (Net.Cookies.navCookie jar (str request "url") (str request "initiator") now (str request "method")))]
      | "response" => JSON.Json.object [("jar", .string (Net.Cookies.navSet jar (str request "url") now
          (((str request "setCookie").splitOn "\n").filter fun f => !f.isEmpty)).wire)]
      | "keep" => JSON.Json.object [("jar", .string (jar.persistent now).wire)]
      | _ => JSON.Json.object [("error", .string "cookies: the action is request, response or keep")]
    return (answer.toString, #[])
  if str request "op" == "download" then
    let answer := match Net.Subresource.navigated (str request "contentType") (str request "disposition") (str request "url") with
      | .show => JSON.Json.object [("action", .string "show")]
      | .save name => JSON.Json.object [("action", .string "save"), ("name", .string name)]
    return (answer.toString, #[])
  if str request "op" == "imageLoad" then
    return (← stepState fun e => let (h,r) := loadImage e.holds request; ({e with holds := h},r),#[])
  -- The ops of held images and frame work: a host asks this before it calls them (issue 1274).
  if str request "op" == "imageInfo" then
    let number := fun (n : Nat) => JSON.Json.number (toString n)
    return ((JSON.Json.object [("engine",.string "heldImages"),
      ("ops",.array (["imageLoad","imageLoadBin","imageDrop","frameWork"].map .string)),
      ("maxImages",number maxHeldImages),("maxBytes",number maxHeldImageBytes),
      ("held",number (← get).holds.images.length),("layoutSlots",number layoutSlots)]).toString,#[])
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
    let scene := chromeScene shell width (← get).holds.addressFont
    let (text,sections) ← WebRender.artifactWith scene #[] none live form checks false
    return ("{\"top\":" ++ toString scene.height ++ ",\"chrome\":" ++ text ++ "}",sections)
  if str request "op" == "imageDrop" then
    modify fun e => {e with holds := {e.holds with images := []}}
    return ((JSON.Json.object [("held",.number "0")]).toString,#[])
  -- Layouts done, kept layouts used and pointer states painted with no layout.
  if str request "op" == "frameWork" then
    let reset := request.field? "reset" == some (.bool true)
    let (layouts,kept,repaints) ← modifyGet fun e => (e.frameWork,if reset then {e with frameWork := (0,0,0)} else e)
    let (pagesMade,pagesKept,recompiled,reused,moved) ← modifyGet fun e =>
      (e.pages.work,if reset then {e with pages := {e.pages with work := (0,0,0,0,0)}} else e)
    let (chromesKept,framesKept) ← modifyGet fun e => (e.keptWhole,if reset then {e with keptWhole := (0,0)} else e)
    let paints ← modifyGet fun e => (e.paintWork,if reset then {e with paintWork := 0} else e)
    let number := fun (n : Nat) => JSON.Json.number (toString n)
    return ((JSON.Json.object [("layouts",number layouts),("kept",number kept),("repaints",number repaints),
      ("paintOnly",number paints),("recompiled",number recompiled),("reused",number reused),("moved",number moved),
      ("layoutSlots",number layoutSlots),("pagesMade",number pagesMade),("pagesKept",number pagesKept),
      ("chromesKept",number chromesKept),("framesKept",number framesKept)]).toString,#[])
  if str request "op" == "xmlStylesheet" then
    let url := match ← WebXslt.stylesheetHref html with
      | some href => JSON.Json.string (Syntax.resolveIri (str request "url") href)
      | none => .null
    return ((JSON.Json.object [("url",url)]).toString,#[])
  if str request "op" == "xslt" then
    let (source,engine) ← WebXslt.transform html (str request "stylesheet") (str request "url") (str request "stylesheetURL")
    return ((JSON.Json.object [("source",.string source),("engine",.string engine),
      ("syntax",.string (WebXslt.resultSyntax (str request "stylesheet")))]).toString,#[])
  -- `press` reads the link regions of the frame, decoded once (`decodeKept`).
  if str request "op" == "press" then
    match request.field? "linksText" with
    | some (.string text) =>
      let regions ← modifyGet fun e => let (links,r) := decodeKept e.links text; (r,{e with links})
      return (← press (fun _ => regions) request,#[])
    | _ => return (← press Rendering.Links.decode request,#[])
  if let some answer ← ofExceptT (inputOp (str request "op" "render") request) then return (answer,#[])
  -- Page scripts run by Lean: QuickJS in WasmVM on the page's arena (WebScripts). The
  -- session is taken out of the state for the call, so that it is not shared.
  if str request "op" == "scriptSession" then
    let holds := (← get).holds
    let (opaqueKeys, opaqueFull) := ((← get).opaqueImages, (← get).opaqueFull)
    -- Before the scripts' first layout read: the store of the page's images (`keepStoreAhead`).
    if str request "action" == "start" then
      modify fun e =>
        let faces := canvasFaceFonts holds e.kept html request
        {e with kept := keepStoreAhead holds e.kept html request, canvasFaces := if faces.isEmpty then e.canvasFaces else faces}
    let held ← modifyGet fun e => (e.scripts,{e with scripts := {}})
    let kept := (← get).kept
    let faces := (← get).canvasFaces
    let (held,answer) ← WebScripts.opSections held "scriptSession" html request (fun r => some (measure holds r kept))
      (fun _ => canvasEnv holds opaqueKeys opaqueFull faces)
    modify fun e => {e with scripts := held}
    match answer with
    | .ok (some a) => return a
    | .ok none => pure ()
    | .error x => throw x
  let op := str request "op" "render"
  if op != "render" && op != "selectedText" && op != "findInPage" && op != "printLayout" && op != "nodeAt" &&
      op != "accessibilityTree" then
    let dom ← stepState fun e => match prepareDOMIn e.kept html request with
      | .ok (dom,made) => ({e with kept := e.kept.add made},.ok dom)
      | .error x => (e,.error x)
    validateResources dom request
    if op == "inspect" then return ((← inspect dom (str request "url") request).toString,#[])
    let _ ← classicScripts request (WebRenderScript.scriptRecords dom)
    let textScale := cssTextScale (← scalePercent request) (zoomUnit request)
    let rules ← stepState fun e => match rulesWith e.kept dom request with
      | .ok (rules,made) => ({e with kept := e.kept.add made},.ok rules)
      | .error x => (e,.error x)
    if op == "droppedCSS" then
      return ((JSON.Json.object [("dropped",.array ((Rendering.CSS.droppedDeclarations dom rules).toList.map .string))]).toString,#[])
    -- The `@font-face` faces that the rendered text uses (CSS Fonts 4 §4.8), with the
    -- URLs to fetch in order: the host fetches only these.
    if op == "fontFaces" then
      let faces ← fontFaces dom request
      let held := (((← get).holds.font).map (fun h => h.fonts.toList.map (·.family))).getD []
      -- a face the text uses now, or one the page's rules name (text a script adds later).
      -- When the rules name every face, all are fetched and the text is not asked
      -- (`facesFetched`: that question is a cascade of the whole page).
      let declared := Rendering.FontFaceRule.declaredFaces faces rules
      let used ← facesFetched declared fun _ =>
        (Rendering.CSS.computeAll dom rules textScale).map (Rendering.FontFaceRule.usedFaces faces held dom ·)
      let list := (List.range faces.size).filterMap fun i =>
        if used[i]! then some (JSON.Json.object [("family",.string faces[i]!.family),
          ("sources",.array (faces[i]!.sources.map .string))]) else none
      return ((JSON.Json.object [("faces",.array list),("rules",.number (toString faces.size))]).toString,#[])
    if op == "fontRequests" then
      return (WebRenderFontRequests.requestsJSON (← WebRenderFontRequests.collectDOMWithRules dom rules textScale),#[])
    throw "unknown document operation"
  let shell := (request.field? "shell").map WebShell.Shell.ofJson
  -- `top` is the chrome on screen; the layout reads the full chrome (`layoutTop`), so a
  -- folding chrome lays nothing out again.
  let top := (shell.map (fun value => WebShell.height value width)).getD 0
  let holds := (← get).holds
  let fonts := holds.fontNames
  -- A script's `transform` values are not in the key (`WebPaint.slotKey`): the frame
  -- paints them on the kept layout. When a slot's element can not be painted alone,
  -- the layout takes the values (the key with them).
  let (slotRequest,slotValues) := WebPaint.slotKey (layoutRequest request)
  let key : LayoutKey := ⟨html,slotRequest,width,height,layoutTop shell width,fonts,
    heldNamed holds (← namedImages request),requestPointer request⟩
  -- A canceled call (an engine session that the host stopped, `WebSession.cancel`) stops here,
  -- before its layout, and below, before its paint. A layout in progress runs to its end.
  if ← WebWasm.Machine.canceled then throw "engine call canceled"
  let laid ← laidOut key
  let (laid,slotValues) ← if laid.paint.unpaintable.isEmpty || slotValues.isEmpty then pure (laid,slotValues)
    else do pure (← laidOut {key with request := layoutRequest request},{})
  if ← WebWasm.Machine.canceled then throw "engine call canceled"
  -- Paint-only values: slots and animations at the page clock (`animationTime`, ms),
  -- with the clicks of the page (`animationClicks`: [[ms, pageX, pageY], ...]).
  let now := natField request "animationTime"
  let clicks : List (Nat × Nat) := match request.field? "animationClicks" with
    | some (.array items) => (items.take 16).filterMap fun item => match item with
      | .array [.number t,.number x,.number y] => do
        let t ← t.toNat?
        let px ← (Rendering.CSS.number x).toOption
        let py ← (Rendering.CSS.number y).toOption
        let styles : Array Rendering.CSS.Computed := match laid.styles.get with
          | .ok styles => styles
          | .error _ => #[]
        let (node,_) ← WebHit.targetWithStyles laid.dom laid.scene laid.boxes styles px py
        some (t,node)
      | _ => none
    | _ => []
  let (scene,animating) ← if laid.paint.empty then pure (laid.scene,false) else do
    let (values,running) := WebPaint.state laid.paint laid.dom slotValues now clicks
    pure (← modifyGet (·.paint laid values),running)
  let boxes := laid.boxes
  let face := laid.face
  -- Printing (issue 1268): the host lays the document out at the paper width, with
  -- `media:"print"`, and `height` the rows of one page. The answer is the pages.
  if op == "printLayout" then
    -- The document and rules of the layout: its media environment, and in liberal mode its skips.
    let dom := laid.dom
    let sheet := laid.rules
    let styles ← Rendering.CSS.computeFor laid.treeScope dom sheet
    let content := WebPrint.contentHeight boxes
    let pages := WebPrint.paginate (WebPrint.pieces dom sheet styles boxes) content height
    let number := fun (n : Nat) => JSON.Json.number (toString n)
    return ((JSON.Json.object [("contentHeight",number content),
      ("pages",.array (pages.map fun (top,rows) => .array [number top,number rows]))]).toString,#[])
  -- The accessibility tree of the layout (`accessibilityAnswer`). Only a host with assistive
  -- technology attached asks: a frame does not make it.
  if op == "accessibilityTree" then
    let (answer,live) := accessibilityAnswer laid html request top ((shell.map (·.scroll)).getD 0) (← get).axLive
      ((shell.map fun value => WebShell.accessible value width accessibilityChromeBase).getD [])
    modify fun e => {e with axLive := live}
    return (answer,#[])
  -- Pointer positions are in window coordinates; the page starts below the chrome.
  let moved := Float.ofNat top-Float.ofNat ((shell.map (·.scroll)).getD 0)
  let chosen := (← selection request).map (fun value => WebSelection.shift value moved)
  -- The node under a window point (`x`, `y`), for the pointer events that page scripts
  -- receive: the smallest layout box that holds the point, in page rows (`y` below the
  -- chrome, plus the scroll), and inside an embedded `svg` the shape under the point
  -- (WebHit). The answer has the event's coordinates. Lean's DOM, not the host, then
  -- dispatches the events (WebScripts).
  if op == "nodeAt" then
    -- The event's coordinates are CSS pixels: the window's device pixels over the ratio.
    let ratio := if (request.field? "graphModel").isSome then 1 else Float.ofNat (zoomUnit request) / 100
    return ((WebHit.nodeAtAnswer laid.dom scene boxes (Float.ofNat (natField request "x"))
      (Float.ofNat (natField request "y")) (Float.ofNat top) (Float.ofNat ((shell.map (·.scroll)).getD 0)) ratio).toString,#[])
  -- Find in page: `find` is `{query, current}` (current from 0). The matches are found
  -- in the glyph cells of the whole page, in page rows.
  let finding : Option (String × Nat) := match request.field? "find" with
    | some f@(.object _) => match f.field? "query" with
      | some (.string q) => if q.isEmpty then none else some (q,match f.field? "current" with
        | some (.number c) => c.toNat?.getD 0 | _ => 0)
      | _ => none
    | _ => none
  -- The glyph cells only for a selection or find: a frame with neither does not read them.
  let items := if op == "selectedText" || op == "findInPage" || chosen.isSome || finding.isSome
    then WebSelection.cells scene.glyphRuns else #[]
  let found := match finding with
    | some (q,_) => WebSelection.findMatches items q
    | none => #[]
  let current := match finding with
    | some (_,c) => if found.isEmpty then 0 else c % found.size
    | none => 0
  -- The count, the current match (from 0, wrapped) and its rectangles in page rows, so the
  -- host can scroll it into view.
  if op == "findInPage" then
    let number := fun (f : Float) => JSON.Json.number (toString f.round)
    let rects := match found[current]? with
      | some (low,high) => (WebSelection.rangeRects items low high).toList.map fun (x,y,w,h) =>
        JSON.Json.array [number x,number y,number w,number h]
      | none => []
    return ((JSON.Json.object [("count",.number (toString found.size)),("current",.number (toString current)),
      ("rects",.array rects)]).toString,#[])
  if op == "selectedText" then
    return ((JSON.Json.object [("text",.string (match chosen with
      | some value => WebSelection.text items value
      | none => ""))]).toString,#[])
  -- The splash at the start of the app (WebShell.splashNodes): `splash` is `{ms, reduce}`;
  -- its words are the engine's own release (WebBuild), over the view below the chrome.
  let splash := match request.field? "splash" with
    | some sp@(.object _) =>
      let ms := match sp.field? "ms" with | some (.number m) => m.toNat?.getD 0 | _ => 0
      WebShell.splashNodes ("Foafnaut " ++ WebBuild.version) ms width ((shell.map (·.scroll)).getD 0) (height-min height top)
        (sp.field? "reduce" == some (.bool true))
    | _ => []
  let marks := WebSelection.findHighlight items found current ++ (match chosen with
    | some value => WebSelection.highlight items value
    | none => []) ++ splash
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
      -- The chrome layer from `chromeKept` when its inputs are those of the last frame.
      let chromeKey : ChromeKey := ⟨value,width,scene.width,mappingBits scene.mapping,holds.fontNames,faceHeader face,
        live,formCode form.next,checks,tree⟩
      let chrome ← match (← get).chromeKept with
        | some (k,answer) =>
          if k == chromeKey then
            modify fun e => {e with keptWhole := (e.keptWhole.1+1,e.keptWhole.2)}
            pure answer
          else
            let answer ← chromeArtifact value scene width holds.addressFont face live form.next checks tree
            modify fun e => {e with chromeKept := some (chromeKey,answer)}
            pure answer
        | none =>
          let answer ← chromeArtifact value scene width holds.addressFont face live form.next checks tree
          modify fun e => {e with chromeKept := some (chromeKey,answer)}
          pure answer
      -- `layoutSections:true` (a host with section answers): the boxes, glyph runs and links of
      -- the band as two sections, kept by the layout's number and the band's top.
      let sectionForm := match form with | .sections _ | .sectionsCpu _ => true | _ => false
      let layout ← if request.field? "layoutSections" == some (.bool true) && sectionForm then do
          let (_,b) := layersBand value width height
          let made := fun (_ : Unit) => WebRender.layoutSections boxes scene.glyphRuns
            (Rendering.moveLinks (· - Float.ofNat b.top) scene.links)
          if laid.serial == 0 || !laid.paint.empty then pure (some (made ()))
          else
            let key := (laid.serial,b.top)
            match (← get).layoutKept with
            | some (k,sections) => if k == key then pure (some sections) else
                let sections := made ()
                modify fun e => {e with layoutKept := some (key,sections)}
                pure (some sections)
            | none =>
              let sections := made ()
              modify fun e => {e with layoutKept := some (key,sections)}
              pure (some sections)
        else pure none
      -- `have:{page:id}`: the page answer the host holds, if the engine gave it (`pagesSent`).
      let haveId : Option Nat := match request.field? "have" with
        | some h@(.object _) => match h.field? "page" with
          | some (.number n) => n.toNat?
          | _ => none
        | _ => none
      let sentPages := (← get).pagesSent
      let held := haveId.bind fun h => sentPages.find? (·.1 == h)
      let (kp,result) := layersJSON (← get).pages value scene marks boxes face width height live form checks tree laid.hoverRules
        (canvasBoxes laid.dom boxes) animating (!laid.paint.animations.isEmpty)
        (request.field? "retained" != some (.bool false)) (!splash.isEmpty) holds.addressFont (some chrome) layout held
      modify fun e => {e with pages := kp}
      let (answer,sent) ← result
      if let some page := sent then
        modify fun e => {e with pagesSent := (page :: e.pagesSent.filter (·.1 != page.1)).take pagesSentSlots}
      return withWants laid <| withDiagnostics request laid answer
  -- The answer of the last frame when its inputs are these (`PlainKey`): the layout's own
  -- scene (no paint values; a number the engine gave), no marks.
  let plainKey : Option PlainKey :=
    if laid.paint.empty && laid.serial != 0 && marks.isEmpty then
      some ⟨laid.serial,shell,width,height,holds.fontNames,live,formCode form,checks,tree⟩
    else none
  let answer ← match plainKey,(← get).plainKept with
    | some key,some (k,answer) =>
      if k == key then
        modify fun e => {e with keptWhole := (e.keptWhole.1,e.keptWhole.2+1)}
        pure answer
      else
        let answer ← plainArtifact scene marks shell width height holds.addressFont boxes face live form checks tree
        modify fun e => {e with plainKept := some (key,answer)}
        pure answer
    | some key,none =>
      let answer ← plainArtifact scene marks shell width height holds.addressFont boxes face live form checks tree
      modify fun e => {e with plainKept := some (key,answer)}
      pure answer
    | none,_ => plainArtifact scene marks shell width height holds.addressFont boxes face live form checks tree
  return withWants laid <| withDiagnostics request laid answer

/-- The layout source of the engine: `Engine.frame`, which keeps layouts in the state. -/
def keptFrame {M : Type → Type} [Monad M] (key : LayoutKey) : DocM M Laid := stepState (·.frame key)

/-- The layout source with no memo: `layOut` of the held fonts and images. -/
def freshLayOut {M : Type → Type} [Monad M] (key : LayoutKey) : DocM M Laid := do
  match layOut (← get).holds key with
  | .ok laid => pure laid
  | .error x => throw x

/-- A request on the engine `e`: the next state and the answer. -/
def answerIn {M : Type → Type} [Monad M] [WebWasm.Machine M] (e : Engine) (bytes : Bool) (html : String)
    (request : JSON.Json) (width height : Nat) : M (Engine × Except String (String × Array ByteArray)) := do
  let (r,e) ← ((answerWith keptFrame bytes html request width height).run).run e
  return (e,r)

/-- The JSON text answer, in the logical model (`Id`), from the state `e`: storage floats
in Base64 (`binary:true`) or decimal. -/
def runIn (e : Engine) (html : String) (request : JSON.Json) (width height : Nat) : Engine × Except String String :=
  let (e,r) := Id.run (answerIn e false html request width height)
  (e,Prod.fst <$> r)

/-- `runIn` from an empty engine. -/
def run (html : String) (request : JSON.Json) (width height : Nat) : Except String String :=
  (runIn {} html request width height).2

/-- The answer with no kept layout, from an empty engine (tests compare it with `runIn`). -/
def answerUncached (bytes : Bool) (html : String) (request : JSON.Json) (width height : Nat) :
    Except String (String × Array ByteArray) :=
  (Id.run (((answerWith (M := Id) freshLayOut bytes html request width height).run).run {})).1

def runUncached (html : String) (request : JSON.Json) (width height : Nat) : Except String String :=
  Prod.fst <$> answerUncached false html request width height

/-- Only white space after character `pos`: `(request.toList.drop pos).all Char.isWhitespace`,
with no list of the request's characters (realperf: a list of 1 MiB of characters for
every frame of a large page). -/
def blankFrom (request : String) (pos : Nat) : Bool := (request.drop pos).all Char.isWhitespace
#guard blankFrom "{} \n" 2 && !blankFrom "{} x" 2 && blankFrom "é{}" 3 && !blankFrom "é{}é" 3 && blankFrom "" 5
#guard ["{\"a\":1}  ", "[1] x", "é\"é\" é", ""].all fun r =>
  (List.range (r.length+2)).all fun n => blankFrom r n == (r.toList.drop n).all Char.isWhitespace

/-- The request text as JSON, with the bounds of `compile`. -/
private def parseRequest (request : String) : Except String JSON.Json :=
  if request.utf8ByteSize > 20971520 then .error "document request exceeds20MiB"
  else match JSON.parseJsonText request with
  | .error _ => .error "invalid document request JSON"
  | .ok (j,pos) =>
    if !blankFrom request pos then .error "trailing document request data"
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
def compileBin (e : Engine) (html request : String) (width height : UInt32) : BaseIO (Engine × ByteArray) := do
  match parseRequest request with
  | .error message => return (e,packAnswer (WebRender.errorJSON message) #[])
  | .ok j =>
    let (e,r) ← answerIn e true html j width.toNat height.toNat
    return (e,match r with
      | .ok (head,sections) => packAnswer head sections
      | .error message => packAnswer (WebRender.errorJSON message) #[])

@[export web_document_compile]
def compile (e : Engine) (html request : String) (width height : UInt32) : BaseIO (Engine × String) := do
  match parseRequest request with
  | .error message => return (e,WebRender.errorJSON message)
  | .ok j =>
    let (e,r) ← answerIn e false html j width.toNat height.toNat
    return (e,match r with
      | .ok (value,_) => value
      | .error message => WebRender.errorJSON message)

/-- `compile` from an empty engine in the logical model (`Id`), for tests. -/
def compileText (html request : String) (width height : UInt32) : String :=
  match parseRequest request with
  | .error message => WebRender.errorJSON message
  | .ok j => match (Id.run (answerIn {} false html j width.toNat height.toNat)).2 with
    | .ok (value,_) => value
    | .error message => WebRender.errorJSON message

/-- A new engine, with nothing held: the shim makes one when it starts. -/
@[export web_document_engine_new]
def engineNew (_ : Unit) : Engine := {}

/-- `fontLoad` with the font file as bytes, with no Base64 and no JSON around it.
A host copies the file into engine memory, so a font is not limited by the call stack,
which holds string arguments in Wasm. `fallback` is 4 for the monospace face (`loadMonoFont`), 3 for the serif face (`loadSerifFont`), 2 for a web font (`loadWebFont`), 1 to
add the font to the held list, 0 to replace the list. The answer is the `fontLoad` answer. The guest module of page
scripts comes the same way, as bytes (WebScripts). -/
@[export web_document_font_load_bin]
def fontLoadBin (e : Engine) (bytes : ByteArray) (family sha256 : String) (fallback : UInt32) : Engine × String :=
  let (e,loaded) := if family == "guest:quickjs" || family == "guest:quickjs-aot" then
      let held := e.scripts
      let e := {e with scripts := {}}
      let (held,r) := WebScripts.loadModuleBytes held family bytes
      ({e with scripts := held},r)
    else
      let holds := e.holds
      let e := {e with holds := {}}
      let (holds,r) := if fallback == 4 then loadMonoFont holds bytes family sha256
        else if fallback == 3 then loadSerifFont holds bytes family sha256
        else if fallback == 2 then loadWebFont holds bytes sha256
        else loadFontBytes holds bytes family sha256 (fallback != 0)
      ({e with holds},r)
  (e,match loaded with | .ok value => value | .error message => WebRender.errorJSON message)

/-- `imageLoad` with the image as bytes, with no Base64 and no JSON around it. -/
@[export web_document_image_load_bin]
def imageLoadBin (e : Engine) (bytes : ByteArray) (key sha256 : String) : Engine × String :=
  let holds := e.holds
  let e := {e with holds := {}}
  let (holds,r) := loadImageBytes holds bytes key sha256
  ({e with holds},match r with | .ok value => value | .error message => WebRender.errorJSON message)

/-- `pickIn` on the engine's kept regions (the C shim's `web_render_hit`). -/
@[export web_render_pick_link_kept]
def pickKept (e : Engine) (regions : String) (width height : UInt32) (x y : Float) : Engine × String :=
  let (links,answer) := pickIn e.links regions width height x y
  ({e with links},answer)
end WebDocument
