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
import WebAbout
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
import L4Factoidal.Rendering.ComputedGeneric
import WebRepaint
import L4Factoidal.WHATWG.Encoding.Sniff
import WebHit
import WebAccept
import WebConsole
import WebPaint
import L4Factoidal.Rendering.FontFaceRule

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
  let css := fun (n : Nat) => n.toFloat * 100 / (max 1 percent).toFloat
  {medium, width := some (css width), height := some (css rows), dark := some false}

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
  store : Option ((List String × List (String × ByteArray)) × NativeImage.Store) := none
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
a field of the engine's state (issue 390). -/
initialize shapedKept : IO.Ref (Std.HashMap (String × String × Nat × Option Bool) (Except String Rendering.FontProvider.Word)) ← IO.mkRef {}

private unsafe def shapeKeptImpl (key : String) (fonts : Array Rendering.SfntProfile.Font) (text : String) (px : Nat)
    (rtl : Option Bool) : Except String Rendering.FontProvider.Word :=
  unsafeBaseIO do
    let k := (key,text,px,rtl)
    if let some w := (← shapedKept.get)[k]? then return w
    let w := Rendering.SfntProfile.shapeFresh fonts text px rtl
    shapedKept.modify fun m => (if m.size ≥ 16384 then {} else m).insert k w
    return w

/-- `SfntProfile.shapeFresh fonts`, kept; `key` is `SfntProfile.fontsKey fonts`. -/
@[implemented_by shapeKeptImpl, noinline]
def shapeKept (_key : String) (fonts : Array Rendering.SfntProfile.Font) (text : String) (px : Nat) (rtl : Option Bool) :
    Except String Rendering.FontProvider.Word := Rendering.SfntProfile.shapeFresh fonts text px rtl

/-- The document tree: the XML syntax for a `.xht`, `.xhtml` or `.svg` URL (HTML §14,
`DOM.parseXmlDocument`, `DOM.isXmlPath`), else the HTML syntax (HTML §13). -/
def prepareDOMIn (kept : Kept) (html : String) (request : JSON.Json) : Except String (DOM.Dom × Made) := do
  if html.utf8ByteSize > WebRender.maxSourceBytes then throw "document HTML exceeds 16 MiB"
  let (dom,made) := parseIn kept html (DOM.isXmlPath (str request "url"))
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

/-- The document's sheets in `env`, in tree order, each with the URL its own URLs resolve
against (the document's base for a `style` element, the sheet's URL for a supplied one,
CSS Values 4 §4.5.1), with the skip points of mode `m`: a `media` that can not be read, a
stylesheet the host could not fetch, and sheets past 2 MiB. -/
def sheetsIn (m : WebAccept.Mode) (dom : DOM.Dom) (request : JSON.Json) (env : Rendering.MediaQuery.Env) :
    Except String (List (String × String) × List WebAccept.Diagnostic) := do
  -- Preserve the existing SVG/HTML stylesheet boundary validation. This copy
  -- removes only the external-fetch refusal; it is never used for layout.
  let validation := {dom with nodes := dom.nodes.map (fun n =>
    if stylesheet n then {n with attrs := n.attrs.filter (fun a => a.lname != "href")} else n)}
  WebRender.validateStyleBoundaries validation
  let base := baseURL dom (str request "url")
  let mut sheets : List (String × String) := []
  let mut bytes := 0
  let mut ds : List WebAccept.Diagnostic := []
  for id in dom.treeOrder 0 do
    let n := dom.get id
    let inline := DOM.Dom.isHtmlElement n "style"
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
    if bytes+source.utf8ByteSize > 2097152 then
      let (_,d) ← WebAccept.skip m .stylesheetBytes (sheetWhere n id) "document stylesheets exceed 2MiB" ()
      ds := ds ++ d
      continue
    bytes := bytes+source.utf8ByteSize
    let from_ := if inline then base else (suppliedURL request id).getD base
    sheets := (from_,source)::sheets
  return (sheets.reverse,ds)

/-- The text of a document's sheets, read as one. -/
def sheetSource (sheets : List (String × String)) : String := String.intercalate "\n" (sheets.map (·.2))

/-- The rules of sheets in `env`: `CSS.parseIn env`, with the sheets read once (`sheetIn`). -/
def rulesOfSheets (kept : Kept) (env : Rendering.MediaQuery.Env) (sheets : List (String × String)) :
    Except String (List Rendering.CSS.Rule × Made) := do
  let (raw,made) := sheetIn kept (sheetSource sheets)
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

/-- The `@font-face` rules of the document's sheets, in the request's mode. -/
def fontFaces (dom : DOM.Dom) (request : JSON.Json) (env : Rendering.MediaQuery.Env := {medium := medium request}) :
    Except String (Array Rendering.FontFaceRule.Face) :=
  (WebAccept.accept (WebAccept.mode request) fun m => sheetsIn m dom request env).map (facesOf env ·.1)

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
  let (scripts,d) ← classicScriptsIn m scripting (WebRenderScript.scriptRecords dom)
  let scripts := scripts.map fun script =>
    match script with
    | .object fields => .object (fields ++ [("url",.string (Syntax.resolveIri base (str script "src")))])
    | other => other
  return (.object [("nodes",(snapshot.field? "nodes").getD (.array [])),
    ("scripts",.array scripts),("stylesheets",.array sheets.reverse),("images",.array (← imageRequests dom base)),
    ("baseURL",.string base),("title",.string (documentTitle dom)),
    ("icon",match iconURL dom base with | some url => .string url | none => .null)],ds ++ d)

/-- What the host fetches for a page, in the mode of `request`. In liberal mode the answer
has `diagnostics`, the skips (`WebAccept.Diagnostic.json`), when there are any. -/
def inspect (dom : DOM.Dom) (url : String) (request : JSON.Json := .object []) : Except String JSON.Json := do
  let (answer,ds) ← WebAccept.accept (WebAccept.mode request) fun m => inspectIn m dom url (scripting request)
  match answer, ds with
  | .object fields, _ :: _ => return .object (fields ++ [("diagnostics",WebAccept.diagnosticsJSON ds)])
  | _, _ => return answer

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
      | _ => WebRoute.routeAddress site (str request "base") (str request "href")
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
  /-- The compile of the band's primitives, for the next frame (`WebPaint.retainedAnswer`). -/
  retained : Option WebPaint.RetainedLayer := none
  /-- `layoutJSON` of this frame: the next frame with the same layout gives it again. -/
  layoutText : String := ""
  /-- The number that `damage.id` answers: a host that drew answer `id` can draw a later
  answer with `damage.base = id` by its damage rectangles alone. -/
  id : Nat := 0

/-- Page layer answers kept: the last two, for a chrome change and back. -/
def keptPageSlots : Nat := 2

initialize keptPageRef : IO.Ref (List KeptPage) ← IO.mkRef []
/-- Page layers made and given again from `keptPageRef`; then primitives compiled again, kept
and moved with their geometry kept by the retained compile. -/
initialize pageWorkRef : IO.Ref (Nat × Nat × Nat × Nat × Nat) ← IO.mkRef (0,0,0,0,0)
/-- Answers numbered for `damage.id`. -/
initialize pageIdRef : IO.Ref Nat ← IO.mkRef 0

set_option compiler.extract_closed false in
private unsafe def pageWorkImpl (reset : Bool) : Nat × Nat × Nat × Nat × Nat :=
  unsafeBaseIO do
    let work ← pageWorkRef.get
    if reset then pageWorkRef.set (0,0,0,0,0)
    return work
/-- Page layers made and page layers kept (`pageArtifact`), as `frameWork` counts layouts. -/
@[implemented_by pageWorkImpl, noinline] private opaque pageWork (reset : Bool) : Nat × Nat × Nat × Nat × Nat

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
    (form : NativeSVG.DataForm) (checks tree : Bool) (retainOn : Bool := true) : Except String (String × Array ByteArray) :=
  unsafeBaseIO do
    let same := fun (k : KeptPage) => ptrEq k.page page && ptrEq k.boxes boxes && ptrEq k.face face &&
      ptrEq k.extra extra && k.band == b && k.live == live && formSame k.form form && k.checks == checks && k.tree == tree &&
      (retainOn || k.retained.isNone)
    let kept ← keptPageRef.get
    match kept.find? same with
    | some k =>
      pageWorkRef.modify fun (m,g,x) => (m,g+1,x)
      return .ok k.answer
    | none =>
      let layer := pageLayer page extra b
      -- The retained compile only for a frame host's answer: sections, no probes, no tree.
      -- `pageArtifact` (the reference) stays the plain path, that `partial_frame_test.ts`
      -- compares this with.
      let previous := kept.find? fun k => k.band == b && k.live == live && formSame k.form form && k.checks == checks && k.tree == tree && k.retained.isSome
      match form,checks,tree,retainOn with
      | .sections first,false,false,true =>
        let layoutText := previous.bind fun k =>
          if ptrEq k.boxes boxes && ptrEq k.face face && ptrEq k.page.links page.links && ptrEq k.page.glyphRuns page.glyphRuns then
            some k.layoutText else none
        let reuseLeaf := fun (a b : WebPaint.LeafKey) =>
          if ptrEq a.primitive b.primitive && a.sameContext b then NativeSVG.Reuse.same
          else if ptrEq a.primitive.geometry b.primitive.geometry && ptrEq a.primitive.style b.primitive.style then a.movedOf b
          else NativeSVG.Reuse.different
        match WebPaint.retainedAnswer reuseLeaf (previous.bind (·.retained)) layer boxes face first layoutText with
        | .error e => return .error e
        | .ok (retained,damage,value,sections,layout,recompiled,moved) =>
          let id := (← pageIdRef.modifyGet fun n => (n+1,n+1))
          let number := fun (n : Nat) => toString n
          let damageText := "{\"id\":" ++ number id ++ ",\"base\":" ++
            (match previous.bind (·.retained),damage with
             | some _,some _ => number (previous.map (·.id)).get!
             | _,_ => "null") ++ ",\"rects\":" ++
            (match damage with | some rects => NativeSVG.damageJSON rects | none => "null") ++ "}"
          let value := (value.dropEnd 1).toString ++ ",\"damage\":" ++ damageText ++ "}"
          let answer := (value,sections)
          keptPageRef.set ((⟨page,extra,b,boxes,face,live,form,checks,tree,answer,some retained,layout,id⟩ :: kept).take keptPageSlots)
          pageWorkRef.modify fun (m,g,a,b,c) => (m+1,g,a+recompiled,b+(retained.items.size-recompiled-moved),c+moved)
          return .ok answer
      | _,_,_,_ =>
        let made := WebRender.artifactWith (WebPaint.cull layer) boxes face live form checks tree
        if let .ok answer := made then
          keptPageRef.set ((⟨page,extra,b,boxes,face,live,form,checks,tree,answer,none,"",0⟩ :: kept).take keptPageSlots)
          pageWorkRef.modify fun (m,g,x) => (m+1,g,x)
        return made

/-- The page layer of a layers answer. Its value is `artifactWith` of the band of the page,
with its curves off the band made lines (`WebPaint.cull`: the same pixels, fewer edges for a
zoomed group);
the engine gives a kept answer again when the inputs are the same objects (a frame whose
only change is in the chrome: loading, the address, a pressed chrome control, the menu). -/
@[implemented_by pageArtifactImpl]
def pageArtifact (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) (live : Bool)
    (form : NativeSVG.DataForm) (checks tree : Bool) (_retainOn : Bool := true) : Except String (String × Array ByteArray) :=
  WebRender.artifactWith (WebPaint.cull (pageLayer page extra b)) boxes face live form checks tree

theorem pageArtifact_eq (page : Rendering.Scene) (extra : List Rendering.Node) (b : Band)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) (live : Bool)
    (form : NativeSVG.DataForm) (checks tree retainOn : Bool) :
    pageArtifact page extra b boxes face live form checks tree retainOn =
      WebRender.artifactWith (WebPaint.cull (pageLayer page extra b)) boxes face live form checks tree := rfl

/-- The answer to a render with `layers:true`. -/
def layersJSON (shell : WebShell.Shell) (page : Rendering.Scene) (extra : List Rendering.Node)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face)
    (width height : Nat) (live : Bool) (form : NativeSVG.DataForm) (checks tree : Bool) (hoverRules : Bool := false)
    (canvases : List Rendering.Layout.Box := []) (animating : Bool := false) (animations : Bool := false)
    (retainOn : Bool := true) (splashing : Bool := false) :
    Except String (String × Array ByteArray) := do
  let top := WebShell.height shell width
  -- A chrome that may fold: the band covers the view under the strip, the most it shows,
  -- so a change of `collapse` keeps the band and only the chrome layer is drawn again.
  let view := max 1 (height-(if shell.collapsible then bandTop shell width else top))
  let b := band shell.scroll view
  let (pageText,pageSections) ← pageArtifact page extra b boxes face live form checks tree retainOn
  let (chromeText,chromeSections) ←
    WebRender.artifactWith (chromeLayer shell page width) #[] face live form.next checks tree
  let number := fun (n : Nat) => JSON.Json.number (toString n)
  let place := JSON.Json.object ([("top",number top),("view",number view),("bandTop",number b.top),
    ("bandHeight",number b.height),("keepFrom",number b.keepFrom),("keepTo",number (b.keepTo view)),
    ("composite",.string compositeShader),("hoverRules",.bool hoverRules),("animating",.bool animating),("animations",.bool animations),
    ("splash",.bool splashing),
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

/-- The faces of `faces` with their held fonts, by the `webFonts` of the request: the
font of the first source URL of each face that the request names with a held SHA-256,
with the rule's family and `unicode-range`. -/
def webFaceFonts (h : Holds) (faces : Array Rendering.FontFaceRule.Face) (request : JSON.Json) :
    Array (Option Rendering.SfntProfile.Font) :=
  let named : List (String × String) := match request.field? "webFonts" with
    | some (.array items) => items.filterMap fun item => match item.field? "url",item.field? "sha256" with
      | some (.string u),some (.string h) => some (u,h)
      | _,_ => none
    | _ => []
  if named.isEmpty then faces.map (fun _ => none) else
  let held := h.webFonts
  faces.map fun face => do
    let sha ← face.sources.findSome? fun u => (named.find? (·.1 == u)).map (·.2)
    let font ← held.find? (·.sha256 == sha)
    let ranges := if face.ranges == [(0,0x10FFFF)] then [] else face.ranges
    some {font with family := face.family, ranges}

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
  loadFontBytes h bytes (str request "fontFamily" "font") (str request "fontSha256" "unnamed")
    (request.field? "fallback" == some (.bool true))

/-! ### Held images (issues 1268, 1274 and 1292)

The host sends each image once, by key (the URL that `inspect` gave) and SHA-256, with
`imageLoad` (Base64 in JSON) or `web_document_image_load_bin` (bytes). Lean holds it;
a render names the images in `heldImages`, `[{key,sha256}]`, so the bytes of a render
request do not grow with the images (`frame_work_test.ts` counts them). `imageInfo`
says that the engine has these ops: a host calls none of them before it asks. -/

/-- Most images, and most bytes of images, that the engine holds; the oldest go first. -/
def maxHeldImages : Nat := 64
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
def canvasEnv (h : Holds) : L4Factoidal.PageCanvas.Env :=
  { fonts := (h.font.map (·.fonts)).getD #[],
    svgPath := fun d => (NativeSVGPath.parse NativeSVG.number d).toOption,
    image := fun key => (h.images.find? (·.key == key)).bind fun img =>
      match NativeImage.decode img.bytes with
      | .ok b => some (L4Factoidal.PageCanvas.Bitmap.ofStraight b.width b.height b.rgba)
      | .error _ => none }

/-- The request fields that a render reads before its layout ends. `shell` gives only
the height of the chrome, which the key holds as `top`; `selection`, `live`, `binary`,
`checks`, `tree`, `op` and the scroll act after layout. `hover` and `active` are not
here: the pointer state is painted (`WebRepaint`), and is in the key, as `pointer`,
only for a frame whose pointer styles change geometry. -/
def layoutFields : List String := ["commands","resources","images","heldImages","url","fontData","textScalePercent","graphModel",
  "visited","media","liberal","scripting","resourceFailures","zoomUnit","webFonts"]

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
  let dom := if m == .liberal && graph.isNone then partialNote dom else dom
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
  let loaded := h.font
  let memo := loaded.map fun held => Rendering.SfntProfile.remember held.fonts held.memo (Rendering.SfntProfile.wordsOf dom)
  -- Web fonts (`@font-face`): those the request names and the engine holds.
  let faces := facesOf env sheets
  let faceFonts := webFaceFonts h faces request
  let heldFamilies := ((loaded.map (·.fonts)).getD #[]).toList.map (·.family.toLower)
  let font ← match loaded,memo with
    | some held,some words =>
      Rendering.SfntProfile.profile held.fonts words
        (shapeKept (Rendering.SfntProfile.fontsKey held.fonts) held.fonts)
        (if faceFonts.all Option.isNone then fun _ => #[] else familyFonts faces faceFonts heldFamilies)
    | _,_ => pure (match face with | some f => Rendering.Layout.FontProfile.ofFace f | none => WebRender.asciiFont)
  let url := baseURL dom (str request "url")
  -- SVG text is drawn with the fonts of the HTML text.
  let svgFonts := (loaded.map (·.fonts)).getD #[] ++ faceFonts.filterMap id
  let images := (← suppliedImages request) ++ heldBytes h held
  -- The SVG of the page is read here. In liberal mode a refusal of it (the SVG reader reads all
  -- inline `svg` roots of the document together) lays the page out with no inline `svg`.
  let documentURL := if url.isEmpty then none else some url
  let (embedding,pictures,dom,d0,madeStore,madeWords) ← match graph with
    | some g => pure (WebGraph.embedding g,Rendering.Layout.noPictures,dom,([] : List WebAccept.Diagnostic),none,({} : NativeSVGText.Words))
    | none => match WebRender.makeReplacedIn kept.stores kept.words dom documentURL images svgFonts, m with
      | .ok (e,p,s,w), _ => pure (e,p,dom,[],s,w)
      | .error e, .strict => throw e
      | .error e, .liberal =>
        let (bare,n) := stripSvg dom
        if n == 0 then throw e else
        match WebRender.makeReplacedIn kept.stores kept.words bare documentURL images svgFonts with
        | .ok (e',p,s,w) => pure (e',p,bare,[{skip := .svgContent, «where» := s!"{n} inline svg elements", refusal := e}],s,w)
        | .error _ => throw e
  modify (·.merge {store := madeStore,words := madeWords})
  -- A window shorter than the chrome still lays out, on one row.
  let state := withPointer dom (← elementState dom url request) pointer
  let draw := fun (d : DOM.Dom) (e : Rendering.Layout.Embedding) => Rendering.Layout.render d rules font e width rows textScale state pictures treeScope
  -- Inline SVG is a skip point, checked so that liberal mode lays the page out once
  -- (2026-11-09: BBC News took three layouts). Before layout: an `svg` root with a percentage
  -- height, which layout refuses (`Layout.checkSVGBox`), is taken out. In the layout: the
  -- embedding draws a refused `svg` as nothing (`quiet`). After it: each `svg` root that was laid
  -- out is read again at its box size, and the refusals become one diagnostic.
  let quiet : Rendering.Layout.Embedding := fun id s w h => match embedding id s w h with
    | .ok nodes => .ok nodes
    | .error _ => .ok []
  let (first,used,d3,dom) ← match m with
    | .strict => pure (draw dom embedding,embedding,([] : List WebAccept.Diagnostic),dom)
    | .liberal => do
      let roots := svgRoots dom
      let styles ← if roots.isEmpty then pure #[] else Rendering.CSS.computeFor treeScope dom rules textScale state
      let tall := roots.filter fun id => match (styles[id]?).map (·.height) with
        | some (.percent _) => true
        | _ => false
      let bare := tall.foldl DOM.Dom.remove dom
      let dTall : List WebAccept.Diagnostic := if tall.isEmpty then [] else
        [{skip := .svgContent, «where» := s!"{tall.length} inline svg elements with a percentage height",
          refusal := "unsupported percentage SVG height without definite containing height"}]
      let result := draw bare quiet
      let refused := match result with
        | .ok (_,boxes) => svgRefusals embedding styles boxes (roots.filter (!tall.contains ·)) bare.size
        | .error _ => []
      let dRefused : List WebAccept.Diagnostic := match refused with
        | [] => []
        | e :: _ => [{skip := .svgContent, «where» := s!"{refused.length} inline svg elements", refusal := e}]
      pure (result,quiet,dTall ++ dRefused,bare)
  -- Nesting deeper than layout reads is a skip point: liberal mode draws the page with the
  -- content below some depth taken out, the first of these depths that lays out.
  let (scene,boxes,dom,d4) ← match first with
    | .ok (scene,boxes) => pure (scene,boxes,dom,([] : List WebAccept.Diagnostic))
    | .error e =>
      match m with
      | .strict => throw e
      | .liberal =>
        if e == depthRefusal then
          let tries := [48,40,32,24,16].map (pruneDeep dom)
          match tries.findSome? (fun (d,cut) => match draw d used with | .ok r => some (r,d,cut) | .error _ => none) with
          | some ((scene,boxes),d,cut) =>
            pure (scene,boxes,d,[{skip := .nestingDepth, «where» := s!"{cut} elements", refusal := e}])
          | none => throw e
        else
          -- A layout refusal of inline SVG (an SVG box that layout can not size, as BBC News's
          -- percentage heights): the page with no inline `svg`, when that lays out.
          let (bare,n) := stripSvg dom
          if n == 0 then throw e else
          match draw bare used with
          | .ok (scene,boxes) => pure (scene,boxes,bare,[{skip := .svgContent, «where» := s!"{n} inline svg elements", refusal := e}])
          | .error _ => throw e
  let hoverRules := rules.any fun rule => rule.selectors.any fun sel =>
    sel.parts.any (·.pseudo.contains .hover) || sel.slotted.any (·.pseudo.contains .hover)
  let laid : Laid := {scene := scene,boxes := boxes,face := face,hoverRules := hoverRules,words := memo}
  return ({laid with dom := dom}
    |> fun l => {l with rules := rules}
    |> fun l => {l with textScale := textScale}
    |> fun l => {l with state := state}
    |> fun l => {l with treeScope := treeScope}
    |> fun l => {l with styles := Thunk.mk fun _ => Rendering.CSS.computeFor treeScope dom rules textScale state}
    |> fun l => {l with paint := paint},d1 ++ d2 ++ d0 ++ d3 ++ d4)

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

/-- The answer of a layout read (op 35, the hit test, is below): op 17 "x y w h left top width height" (the border box
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
  -- 35: `elementFromPoint` and `elementsFromPoint` (CSSOM View §5.1). `node` carries the
  -- point, x × 65536 + y in whole CSS pixels of the page. The answer is the target of a
  -- pointer there (`WebHit.target`: the smallest box that holds the point, and inside an
  -- `svg` the shape whose `pointer-events` takes it) and its ancestor elements, topmost
  -- first, as node numbers; "" when no box holds the point.
  | 35 =>
    let px := (node / 65536).toFloat
    let py := (node % 65536).toFloat
    match WebHit.target l.dom l.scene l.boxes px py with
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
attribute as one text, or with "names" the longhands they declare. -/
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
        let textScale := cssTextScale (← scalePercent request) (zoomUnit request)
        let (rules,_) ← rulesWith kept dom request
        let state := withPointer dom (← elementState dom (baseURL dom (str request "url")) request) (none,none)
        let (flat,rules,treeScope) := flatView kept dom {medium := medium request} rules
        return (flat,rules,treeScope,state,textScale)
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
    -- the rule buckets of `computeFor`, built again only if such a value is asked for
    let matchesOf : Nat → List Rendering.CSS.Match := match treeScope with
      | some ts =>
        let ix : Thunk Rendering.CSS.ScopedIndex := Thunk.mk fun _ => Rendering.CSS.ScopedIndex.build rules
        let ks : Thunk Rendering.CSS.ElemKeys := Thunk.mk fun _ => Rendering.CSS.ElemKeys.of ts.tree
        fun id => ix.get.matched (ks.get.get ts.tree) ts id state
      | none =>
        match carry with
        -- a few elements are asked for: their keys are read when a rule tests them
        | some _ => fun id => index.get.matched (Rendering.CSS.readKeys flat) flat id state
        | none =>
          let ks : Thunk Rendering.CSS.ElemKeys := Thunk.mk fun _ => Rendering.CSS.ElemKeys.of flat
          fun id => index.get.matched (ks.get.get flat) flat id state
    let matchesOf := Rendering.CSS.withAnimated state matchesOf
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
             viewportW := width, viewportH := height }
  -- what this measure leaves for the next (`Page.Carry`): for a page with no shadow tree, at
  -- text scale 1, whose rules do not read the `style` attribute
  let left : Thunk (Option WasmVM.Hosts.Page.Carry) := Thunk.mk fun _ =>
    match styled.get, inputs.get with
    | .ok view, .ok (_,rules,none,state,textScale) =>
      if textScale == 1 && (carry.isSome || !Rendering.CSS.readsStyleAttribute rules) then
        some { index := index.get, rules := rules, state := {state with animated := []}, styles := view.styles }
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
  -- `CSS.computeFor` matches: an element tries only the rules of its buckets)
  let matchesOf : Thunk (Nat → List Rendering.CSS.Match) := Thunk.mk fun _ =>
    match inputs.get with
    | .ok (flat,_,treeScope,state,_) =>
      (match treeScope with
        | none =>
          let ix := Rendering.CSS.RuleIndex.build animationRules.get
          let ks := Rendering.CSS.ElemKeys.of flat
          fun id => ix.matched (ks.get flat) flat id state
        | some ts =>
          let ix := Rendering.CSS.ScopedIndex.build animationRules.get
          let ks := Rendering.CSS.ElemKeys.of ts.tree
          fun id => ix.matched (ks.get ts.tree) ts id state)
    | .error _ => fun _ => []
  let matchedOf := fun (node : Nat) => matchesOf.get node
  -- 40: the text of the document's style sheets, with no layout: the editing algorithms
  -- (`Hosts.Dom.editOp`, `document.execCommand`) read the styles of nodes from it
  let sheetText : Thunk String := Thunk.mk fun _ =>
    match WebAccept.accept (WebAccept.mode request) fun m => sheetsIn m dom request {medium := medium request} with
    | .ok (sheets,_) => sheetSource sheets
    | .error _ => ""
  let element := fun (node : Nat) => node < dom.size && (dom.get node).type == .element
  -- 22: the device pixel ratio of the layout request (`zoomUnit`/100), with no layout
  -- 23: the `@font-face` faces of the page and the state of each (`document.fonts`)
  let answers : WasmVM.Hosts.Page.Answers := fun node op q => if op == 22 then some (Rendering.FloatFormat.format (Float.ofNat (zoomUnit request) / 100))
    else if op == 23 then some (fontFacesAnswer h dom request)
    else if op == 40 then some sheetText.get
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
          -- with "names": the declared longhands; else the declarations as one text
          some (if q == "names" then "\x00".intercalate (Rendering.Animation.Computed.declaredNames view node)
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
    else if op == 20 || op == 36 || op ≥ 200 then
      match styled.get with
      -- CSSOM §9 getComputedStyle: an element that is not connected to the page's
      -- document has no computed style (the declaration is empty)
      | .ok view => if element node && dom.connected node then
          let c := view.styles[node]?.getD {}
          -- 36: the custom properties that apply to the element (35 is the hit test); 200 + k: the k-th property's value
          some (if op == 20 then Rendering.ComputedValues.text c
            else if op == 36 then Rendering.ComputedGeneric.customNamesText view node
            else Rendering.Animation.Computed.resolvedAt view node (op - 200))
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
  if request.field? "diagnostics" != some (.bool true) || laid.diagnostics.isEmpty || !text.endsWith "}" then answer
  else ((text.dropEnd 1).toString ++ ",\"diagnostics\":" ++ (WebAccept.diagnosticsJSON laid.diagnostics).toString ++ "}",sections)

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

/-- A document request, with `laidOut` as the layout of a render. `run` passes the
kept layout (`Engine.frame`); `runUncached` passes `layOut`, so that tests compare the two. With
`bytes`, a render answer names its storage floats and tile words as sections
(`DataForm.sections`) and gives their bytes; other answers have no section. -/
def answerWith {M : Type → Type} [Monad M] [WebWasm.Machine M] (laidOut : LayoutKey → DocM M Laid) (bytes : Bool) (html : String)
    (request : JSON.Json) (width height : Nat) : DocM M (String × Array ByteArray) := do
  let .object fields := request | throw "document request must be an object"
  if (fields.map Prod.fst).eraseDups.length != fields.length then throw "duplicate document request field"
  if str request "op" == "fontLoad" then
    return (← stepState fun e => let (h,r) := loadFont e.holds request; ({e with holds := h},r),#[])
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
    let scene := chromeScene shell width
    let (text,sections) ← WebRender.artifactWith scene #[] none live form checks false
    return ("{\"top\":" ++ toString scene.height ++ ",\"chrome\":" ++ text ++ "}",sections)
  if str request "op" == "imageDrop" then
    modify fun e => {e with holds := {e.holds with images := []}}
    return ((JSON.Json.object [("held",.number "0")]).toString,#[])
  -- Layouts done, kept layouts used and pointer states painted with no layout.
  if str request "op" == "frameWork" then
    let reset := request.field? "reset" == some (.bool true)
    let (layouts,kept,repaints) ← modifyGet fun e => (e.frameWork,if reset then {e with frameWork := (0,0,0)} else e)
    let (pagesMade,pagesKept,recompiled,reused,moved) := pageWork reset
    let paints ← modifyGet fun e => (e.paintWork,if reset then {e with paintWork := 0} else e)
    let number := fun (n : Nat) => JSON.Json.number (toString n)
    return ((JSON.Json.object [("layouts",number layouts),("kept",number kept),("repaints",number repaints),
      ("paintOnly",number paints),("recompiled",number recompiled),("reused",number reused),("moved",number moved),
      ("layoutSlots",number layoutSlots),("pagesMade",number pagesMade),("pagesKept",number pagesKept)]).toString,#[])
  if str request "op" == "xmlStylesheet" then
    let url := match ← WebXslt.stylesheetHref html with
      | some href => JSON.Json.string (Syntax.resolveIri (str request "url") href)
      | none => .null
    return ((JSON.Json.object [("url",url)]).toString,#[])
  if str request "op" == "xslt" then
    let (source,engine) ← WebXslt.transform html (str request "stylesheet") (str request "url") (str request "stylesheetURL")
    return ((JSON.Json.object [("source",.string source),("engine",.string engine)]).toString,#[])
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
    let held ← modifyGet fun e => (e.scripts,{e with scripts := {}})
    let kept := (← get).kept
    let (held,answer) ← WebScripts.opSections held "scriptSession" html request (fun r => some (measure holds r kept))
      (fun _ => canvasEnv holds)
    modify fun e => {e with scripts := held}
    match answer with
    | .ok (some a) => return a
    | .ok none => pure ()
    | .error x => throw x
  let op := str request "op" "render"
  if op != "render" && op != "selectedText" && op != "findInPage" && op != "printLayout" && op != "nodeAt" then
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
      let styles ← Rendering.CSS.computeAll dom rules textScale
      let held := (((← get).holds.font).map (fun h => h.fonts.toList.map (·.family))).getD []
      let used := Rendering.FontFaceRule.usedFaces faces held dom styles
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
  let fonts := (holds.font.map HeldFont.names).getD []
  -- A script's `transform` values are not in the key (`WebPaint.slotKey`): the frame
  -- paints them on the kept layout. When a slot's element can not be painted alone,
  -- the layout takes the values (the key with them).
  let (slotRequest,slotValues) := WebPaint.slotKey (layoutRequest request)
  let key : LayoutKey := ⟨html,slotRequest,width,height,layoutTop shell width,fonts,
    heldNamed holds (← namedImages request),requestPointer request⟩
  let laid ← laidOut key
  let (laid,slotValues) ← if laid.paint.unpaintable.isEmpty || slotValues.isEmpty then pure (laid,slotValues)
    else do pure (← laidOut {key with request := layoutRequest request},{})
  -- Paint-only values: slots and animations at the page clock (`animationTime`, ms),
  -- with the clicks of the page (`animationClicks`: [[ms, pageX, pageY], ...]).
  let now := natField request "animationTime"
  let clicks : List (Nat × Nat) := match request.field? "animationClicks" with
    | some (.array items) => (items.take 16).filterMap fun item => match item with
      | .array [.number t,.number x,.number y] => do
        let t ← t.toNat?
        let px ← (Rendering.CSS.number x).toOption
        let py ← (Rendering.CSS.number y).toOption
        let (node,_) ← WebHit.target laid.dom laid.scene laid.boxes px py
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
      return withDiagnostics request laid (← layersJSON value scene marks boxes face width height live form checks tree laid.hoverRules
        (canvasBoxes laid.dom boxes) animating (!laid.paint.animations.isEmpty)
        (request.field? "retained" != some (.bool false)) (!splash.isEmpty))
  let scrolled := Float.ofNat ((shell.map (·.scroll)).getD 0)
  let near := nearNodes (scrolled-512) (scrolled+Float.ofNat height+512) scene.tree
  let page := {scene with tree := near ++ marks}
  return withDiagnostics request laid (← WebRender.artifactWith (WebPaint.cull (match shell with
    | some value => WebShell.compose value page width height
    | none => page)) boxes face live form checks tree)

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
which holds string arguments in Wasm. `fallback` is 2 for a web font (`loadWebFont`), 1 to add the font to the held
list, 0 to replace the list. The answer is the `fontLoad` answer. The guest module of page
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
      let (holds,r) := if fallback == 2 then loadWebFont holds bytes sha256
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
