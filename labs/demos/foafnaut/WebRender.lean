import WebRenderSVG
import SVGRaster
import SVGText
import SVGForgiving
import SVGCssColour
import Font
import L4Factoidal.Rendering.Layout
import L4Factoidal.Rendering.Links
import L4Factoidal.HTML.ImageSource

/-! HTML source → existing Lean DOM → computed CSS → layout → common scene.
The bitmap font is an explicit temporary profile, not font-backed shaping. -/
namespace WebRender

/-- The largest HTML document or stylesheet the engine reads, in bytes. Real home pages pass
1 MiB (owner, 2026-11-09: BBC refused as over 1 MB). The host's `MAX_SOURCE_BYTES` is the same. -/
def maxSourceBytes : Nat := 16*1048576
open L4Factoidal

private def quote (s : String) : String := "\"" ++ JSON.escapeString s ++ "\""
def errorJSON (message : String) : String := "{\"error\":" ++ quote message ++ "}"

/-- Lit runs of one bitmap row, left to right, as (x,width). -/
def bitmapRuns (bits : Nat) : List (Nat × Nat) := Id.run do
  let mut runs : Array (Nat × Nat) := #[]
  let mut start : Option Nat := none
  for x in [:6] do
    let lit := x < 5 && bits / (2^(4-x)) % 2 == 1
    match start,lit with
    | none,true => start := some x
    | some from_,false => runs := runs.push (from_,x-from_); start := none
    | _,_ => pure ()
  return runs.toList

/-- Equal runs in touching rows become one rectangle. The lit area is unchanged;
    every primitive costs the same at each later stage, so the count is the cost. -/
def bitmapOutline (index : Nat) : List Rendering.Geometry := Id.run do
  let rows := NativeFont.bitmap (Char.ofNat index)
  let values := [rows.row0,rows.row1,rows.row2,rows.row3,rows.row4,rows.row5,rows.row6]
  let mut boxes : Array (Nat × Nat × Nat × Nat) := #[]
  for (bits,y) in values.zipIdx do
    for (x,w) in bitmapRuns bits do
      match boxes.findIdx? (fun b => b.1 == x && b.2.1 == w && b.2.2.1+b.2.2.2 == y) with
      | some i => boxes := boxes.modify i fun b => (b.1,b.2.1,b.2.2.1,b.2.2.2+1)
      | none => boxes := boxes.push (x,w,y,1)
  return boxes.toList.map fun (x,w,y,h) =>
    .rect (Float.ofNat x) (Float.ofNat y) (Float.ofNat w) (Float.ofNat h)

private def bitmapCovers (x y : Nat) : Rendering.Geometry → Bool
  | .rect left top w h =>
    left <= Float.ofNat x && Float.ofNat x+1 <= left+w && top <= Float.ofNat y && Float.ofNat y+1 <= top+h
  | _ => false

private def bitmapArea : Rendering.Geometry → Float
  | .rect _ _ w h => w*h
  | _ => 0

/-- Each lit cell is covered, no unlit cell is, and the boxes do not overlap. -/
private def bitmapOutlineExact (index : Nat) : Bool :=
  let rows := NativeFont.bitmap (Char.ofNat index)
  let values := [rows.row0,rows.row1,rows.row2,rows.row3,rows.row4,rows.row5,rows.row6]
  let boxes := bitmapOutline index
  let cells := values.zipIdx.flatMap fun (bits,y) =>
    (List.range 5).map fun x => (x,y,bits / (2^(4-x)) % 2 == 1)
  cells.all (fun (x,y,lit) => boxes.any (bitmapCovers x y) == lit) &&
    boxes.foldl (fun a g => a+bitmapArea g) 0 == Float.ofNat (cells.filter (·.2.2)).length

#guard (List.range 95).all fun n => bitmapOutlineExact (n+32)

/-- The ASCII geometries are fixed and shared by all layouts. Build the table lazily
so a font-backed session that never uses the bitmap font pays no outline work. -/
private def bitmapOutlines : Thunk (Array (List Rendering.Geometry)) :=
  Thunk.mk fun _ => Array.ofFn fun i : Fin 128 => bitmapOutline i.val

def bitmapOutlineCached (index : Nat) : List Rendering.Geometry :=
  if h : index < 128 then bitmapOutlines.get[index]'(by simpa [bitmapOutlines, Thunk.get] using h)
  else bitmapOutline index

/-- The cached bitmap profile returns the same geometry in the same order. -/
theorem bitmapOutlineCached_eq (index : Nat) :
    bitmapOutlineCached index = bitmapOutline index := by
  by_cases h : index < 128 <;> simp [bitmapOutlineCached, h, bitmapOutlines, Thunk.get]

#print axioms bitmapOutlineCached_eq

def asciiFont : Rendering.Layout.FontProfile :=
  {family := "factoidal-ascii-bitmap-v1",unitsPerEm := 7,advance := 6, ascent := 7,descent := 0,outline := bitmapOutlineCached, admits := fun n => 32 <= n && n <= 126}

/-- The HTML parser already adjusted element and foreign-attribute names.
This conversion transfers the semantic DOM values directly, without XML text. -/
def namespaceTree (dom : DOM.Dom) : Nat → Nat → Except String XML.NamespaceNode
  | 0, _ => throw "unsupported SVG embedding nesting depth (maximum 64)"
  | fuel+1, id => do
    let n := dom.get id
    if n.type == .element then
      let children ← n.kids.toList.mapM (namespaceTree dom fuel)
      let attrs := (n.attrs.toList.filter (fun a => a.ns != some DOM.xmlnsNS)).map fun a =>
        ({name := ⟨a.ns,a.lname⟩,value := a.value} : XML.NamespaceAttribute)
      return .element ⟨n.ns,n.lname⟩ attrs children
    else if n.type == .text || n.type == .cdata then return .other (.text n.data)
    else if n.type == .comment then return .other (.comment n.data)
    else throw "unsupported node in embedded SVG DOM"

/-- The document element as the source paths of SVG count from it: the `html` element, or,
in a document of another vocabulary (an SVG document read as XML), its first element. -/
def documentElement (dom : DOM.Dom) : Option Nat :=
  match dom.nodes[0]? with
  | none => none
  | some document =>
    (document.kids.find? (fun id => DOM.Dom.isHtmlElement (dom.get id) "html")).orElse fun _ =>
      document.kids.find? (fun id => (dom.get id).type == .element)

private def svgStyleAttribute (a : XML.NamespaceAttribute) : Bool :=
  a.name.namespace_.isNone && a.name.localPart == "style"

/-- Hand the SVG reader the browser's already-selected author values. The SVG
reader consumes a restricted declaration list; a value containing a delimiter
cannot be embedded in it. The original DOM and the presentation attributes keep
their identity. The SVG reader will still check each resulting paint value. -/
private def svgAuthorAttributes (attrs : List XML.NamespaceAttribute)
    (values : List (String × String)) : List XML.NamespaceAttribute :=
  let retained := attrs.filter (fun a => !svgStyleAttribute a)
  let value := String.intercalate ";" (values.filterMap fun (key,text) =>
    if text.contains ';' then none else some (key ++ ":" ++ text))
  if value.isEmpty then retained
  else retained ++ [{name := ⟨none,"style"⟩,value}]

private theorem svgAuthorAttributes_preservePresentation (attrs : List XML.NamespaceAttribute)
    (values : List (String × String)) :
    (svgAuthorAttributes attrs values).filter (fun a => !svgStyleAttribute a) =
      attrs.filter (fun a => !svgStyleAttribute a) := by
  simp only [svgAuthorAttributes]
  split <;> simp [List.filter_filter, svgStyleAttribute]

#print axioms svgAuthorAttributes_preservePresentation

/-- Convert the original HTML element subtree bottom-up. Every original child
index survives, including text/comments; no host extraction or XML reparse. A `script`
element (HTML's or SVG's) draws nothing: it stays in its place as an empty comment, so the
SVG reader does not meet it and the indices after it are unchanged. When the HTML
cascade is supplied, SVG style elements likewise keep their child position; their rules
have already been consumed with the rest of the document's author styles. -/
def documentNamespaceTree (dom : DOM.Dom) (cascade : Option (Array Rendering.CSS.Computed) := none) :
    Except String (Nat × XML.NamespaceNode) := do
  if dom.nodes.size == 0 then throw "HTML document root missing"
  let some root := documentElement dom
    | throw "HTML element root missing"
  let mut values : Std.TreeMap Nat XML.NamespaceNode := {}
  let mut pending := [(false,root)]
  for _ in [:2*dom.size+1] do
    match pending with
    | [] =>
      let some tree := values.get? root | throw "HTML namespace root not constructed"
      return (root,tree)
    | (finished,id)::rest =>
      let some node := dom.nodes[id]? | throw "invalid node in HTML namespace tree"
      pending := rest
      if node.type == .element && id != root &&
          ((node.lname == "script" && (node.ns == some DOM.htmlNS || node.ns == some DOM.svgNS)) ||
           (cascade.isSome && node.lname == "style" && node.ns == some DOM.svgNS)) then
        values := values.insert id (.other (.comment ""))
      else if node.type == .element then
        if !finished then pending := node.kids.toList.map (fun child => (false,child)) ++ ((true,id)::rest)
        else
          let children ← node.kids.toList.mapM (fun child =>
            match values.get? child with | some tree => .ok tree | none => .error "HTML namespace child missing")
          -- An attribute in `NativeSVG.glyphNS` names an entry of the glyph table of
          -- lowered SVG text; page content (markup or script) cannot give one.
          let attrs := (node.attrs.toList.filter (fun a => a.ns != some DOM.xmlnsNS && a.ns != some NativeSVG.glyphNS)).map fun a =>
            ({name := ⟨a.ns,a.lname⟩,value := a.value} : XML.NamespaceAttribute)
          let attrs := if node.ns == some DOM.svgNS then
            match cascade.bind (fun styles => styles[id]?) with
            | some style => svgAuthorAttributes attrs style.svgAuthor
            | none => attrs
          else attrs
          values := values.insert id (.element ⟨node.ns,node.lname⟩ attrs children)
      else if node.type == .text || node.type == .cdata then
        values := values.insert id (.other (.text node.data))
      else if node.type == .comment then values := values.insert id (.other (.comment node.data))
      else throw "unsupported node in original HTML namespace document"
  throw "HTML namespace conversion exceeds DOM arena"

def sourcePath (dom : DOM.Dom) (root : Nat) : Nat → Nat → List Nat → Except String (List Nat)
  | 0,_,_ => throw "SVG original source path exceeds DOM arena"
  | fuel+1,id,path => do
    if id == root then return path
    let some node := dom.nodes[id]? | throw "SVG source path node missing"
    let some parent := node.parent | throw "SVG root is outside original HTML document"
    let some p := dom.nodes[parent]? | throw "SVG source path parent missing"
    let some index := p.kids.findIdx? (· == id) | throw "SVG source path child index missing"
    sourcePath dom root fuel parent (index::path)

/-- Embedded style sheets are read from their DOM text nodes. No host selector, computed-style or layout API participates in this pipeline. -/
def styleSource (dom : DOM.Dom) : String := Id.run do
  let mut sheets : List String := []
  for n in dom.nodes do
    if DOM.Dom.isHtmlElement n "style" then
      let text := n.kids.foldl (fun s id => s ++ (dom.get id).data) ""
      sheets := text :: sheets
  return String.intercalate "\n" sheets.reverse

def validateStyleBoundaries (dom : DOM.Dom) : Except String Unit := do
  for node in dom.nodes do
    if DOM.Dom.isHtmlElement node "link" then
      let rel := ((Rendering.CSS.attrValue node "rel").toLower.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " ").splitOn " "
      if rel.contains "stylesheet" && Rendering.CSS.hasAttribute node "href" then
        throw "unsupported external HTML stylesheet without supplied resource transport"
    if node.type == .element && node.ns == some DOM.svgNS && node.lname == "style" then
      let text := node.kids.foldl (fun text id => text ++ (dom.get id).data) ""
      for rule in ← Rendering.CSS.parse text do
        for (target,id) in dom.nodes.zipIdx do
          if rule.selectors.any (Rendering.CSS.selectorMatches dom id) then
            if target.ns == some DOM.htmlNS ||
                (target.ns == some DOM.svgNS && target.lname == "svg" &&
                 (target.parent.map (fun p => (dom.get p).ns != some DOM.svgNS)).getD true &&
                 rule.declarations.any (fun d => Rendering.CSS.htmlProperties.contains d.property)) then
              throw "unsupported SVG stylesheet affecting HTML layout or outer SVG computed style"
def styleRules (dom : DOM.Dom) : Except String (List Rendering.CSS.Rule) := do
  validateStyleBoundaries dom
  Rendering.CSS.parse (styleSource dom)

/-- SVG embedding is injected only at the frontend adapter boundary. Tests can
supply an independent shape producer without changing CSS/layout semantics. -/
def renderDOM (dom : DOM.Dom) (width height : Nat)
    (embedding : Rendering.Layout.Embedding) (pictures : Rendering.Layout.Pictures := Rendering.Layout.noPictures) :
    Except String (Rendering.Scene × Array Rendering.Layout.Box) := do
  let rules ← styleRules dom
  Rendering.Layout.render dom rules asciiFont embedding width height 1 {} pictures

end WebRender

namespace WebRender
open L4Factoidal

/-- CSS dimensions and overflow belong to HTML layout for the embedded root.
SVG paint declarations remain in the existing SVG frontend. -/
private def embeddedAttributes (attrs : List XML.NamespaceAttribute) : Except String (List XML.NamespaceAttribute) := do
  let mut out : List XML.NamespaceAttribute := []
  for attr in attrs do
    if attr.name.namespace_.isNone && attr.name.localPart == "style" then
      let declarations ← Rendering.CSS.declarations attr.value
      -- `background-image` is a longhand that the `background` shorthand gives HTML layout
      -- (`CSS.declarationsOf`); the SVG reader takes none of it
      let declarations := declarations.filter (fun d =>
        !Rendering.CSS.htmlProperties.contains d.property && d.property != "background-image")
      if !declarations.isEmpty then
        let value := String.intercalate ";" (declarations.map fun d => d.property ++ ":" ++ d.value ++ if d.important then "!important" else "")
        out := {attr with value} :: out
    else if attr.name.namespace_.isNone && ["overflow","color","visibility","display"].contains attr.name.localPart then pure ()
    else out := attr :: out
  return out.reverse

private def embeddedRoot (root : XML.NamespaceNode) : Except String XML.NamespaceNode := do
  let .element name attrs children := root | throw "embedded SVG root must be an element"
  return .element name (← embeddedAttributes attrs) children

def placeSVG (scene : NativeSVG.Scene) (id : Nat) (style : Rendering.CSS.Computed) (width height : Float) : List Rendering.Node :=
  let m := scene.mapping
  let transform : Rendering.Transform := ⟨m.sx,0,0,m.sy,m.tx-m.minX*m.sx,m.ty-m.minY*m.sy⟩
  let background := match style.background with
    | none => []
    | some color => if style.visible then [.paint ⟨some id,{geometry := .rect 0 0 width height,style := {fill := .solid color}}⟩] else []
  let tree := (WebRenderSVG.fromScene scene).tree
  let content := if style.clipOverflow then
    Rendering.Node.clipped none transform ⟨0,0,width,height,Rendering.identity⟩ tree
    else .group none transform tree
  background ++ [content]

def embedding (dom : DOM.Dom) (id : Nat) (style : Rendering.CSS.Computed) (width height : Float) : Except String (List Rendering.Node) := do
  if Float.ofNat width.toUInt32.toNat != width || Float.ofNat height.toUInt32.toNat != height then
    throw "unsupported fractional embedded SVG viewport"
  let root ← embeddedRoot (← namespaceTree dom 64 id)
  let inherited : NativeSVG.Style := {currentColor := WebRenderSVG.toColor style.color, visible := style.visible}
  let scene ← NativeSVG.parseRoot root width.toUInt32.toNat height.toUInt32.toNat inherited
  return placeSVG scene id style width height

/-! ### The image an `img` shows (HTML §4.8.4.3, `srcset`, `sizes`, `picture`)

Before 2026-11-14 an `img` was its `src`: one with `srcset` alone, or whose `picture` has
the sources, showed its alt text. The source is now chosen by `HTML.ImageSource`
(`sourceSet`, `selectFrom`: the selection `img.currentSrc` answers with), in one nominal
environment, so that the list a host fetches (`inspect`) and every layout name the same
image whatever the window's size. Candidates in a format the engine does not decode are
passed over, and the `src` stands when nothing else is left. -/

/-- Formats excluded as alternate source-set candidates. -/
def undecodablePath (url : String) : Bool :=
  let path := ((((url.splitOn "#").headD "").splitOn "?").headD "").toLower
  [".avif", ".jxl", ".heic", ".heif"].any fun ending => path.endsWith ending

/-- The environment an image source is chosen in: one device pixel to the CSS pixel, a
viewport of 1280 by 800. -/
def sourceEnv : HTML.ImageSource.Env := {viewportW := 1280, viewportH := 800, dpr := 1}

/-- An `img` with no `srcset` that is no child of a `picture`: nothing is chosen. -/
def plainImage (dom : DOM.Dom) (id : Nat) : Bool :=
  let n := dom.get id
  !Rendering.CSS.hasAttribute n "srcset" &&
    !(n.parent.any fun p => DOM.Dom.isHtmlElement (dom.get p) "picture")

/-- The `src` of an `img`, as written; none when it has none. -/
def plainSource (dom : DOM.Dom) (id : Nat) : Option String :=
  let src := (Rendering.CSS.attrValue (dom.get id) "src").trimAscii.toString
  if src.isEmpty then none else some src

/-- The source chosen among the candidates of the element's source set that the engine can
decode; the `src` when there is none. -/
def chosenRequest (dom : DOM.Dom) (id : Nat) : Option (String × Rat) :=
  let fallback := fun _ : Unit => (plainSource dom id).map (·,1)
  let (set,size) := HTML.ImageSource.sourceSet dom id sourceEnv
  match HTML.ImageSource.selectFrom sourceEnv.dpr size (set.filter fun s => !undecodablePath s.url) with
  | some (source,density) =>
    let url := source.url.trimAscii.toString
    if url.isEmpty then fallback () else some (url,density)
  | none => fallback ()

/-- The image and current pixel density for this element. -/
def imageRequest (dom : DOM.Dom) (id : Nat) : Option (String × Rat) :=
  if plainImage dom id then (plainSource dom id).map (·,1) else chosenRequest dom id

/-- The URL, as written, of the image an `img` shows. -/
def imageSource (dom : DOM.Dom) (id : Nat) : Option String :=
  (imageRequest dom id).map Prod.fst

/-- Kind: property (zero cost, and no change). Says: an `img` with no `srcset` outside a
`picture` shows its `src`, as before: no source set is made for it. Does not say: which
candidate another `img` shows (that is `HTML.ImageSource.selectFrom`, with
`selectFrom_mem`: one of the element's own sources). -/
theorem imageSource_plain (dom : DOM.Dom) (id : Nat) (h : plainImage dom id = true) :
    imageSource dom id = plainSource dom id := by
  cases hs : plainSource dom id <;> simp [imageSource, imageRequest, h, hs]

/-- An image handled by the static decoder in an `object` or `embed`. An explicit type
takes precedence over a filename; the URL can also be a typed data URL. -/
private def embeddedImageSource (n : DOM.Node) : Option String := do
  let sourceAttr ←
    if DOM.Dom.isHtmlElement n "object" then some "data"
    else if DOM.Dom.isHtmlElement n "embed" then some "src"
    else none
  let url := (Rendering.CSS.attrValue n sourceAttr).trimAscii.toString
  if url.isEmpty then none else do
    let mimeType := fun s : String => ((s.splitOn ";").headD "").trimAscii.toString.toLower
    let declared := mimeType (Rendering.CSS.attrValue n "type")
    let types := ["image/png", "image/jpeg", "image/gif", "image/webp", "image/svg+xml"]
    let supported :=
      if !declared.isEmpty then types.contains declared
      else if url.toLower.startsWith "data:" then
        let header := (((url.drop 5).toString).splitOn ",").headD ""
        types.contains (mimeType header)
      else
        let path := (((url.splitOn "#").headD "").splitOn "?").headD ""
        [".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg"].any fun e => path.toLower.endsWith e
    if supported then some url else none

/-- HTML images, image embeds and video posters, keyed by the node that displays them.
Resolve each nonempty source with the same image-store key as SVG images. -/
def htmlImageRequests (dom : DOM.Dom) (base : Option String) : List (Nat × String × Rat) := Id.run do
  let mut out : Array (Nat × String × Rat) := #[]
  for id in [0:dom.size] do
    let n := dom.get id
    if DOM.Dom.isHtmlElement n "img" then
      if let some (src,density) := imageRequest dom id then out := out.push (id,NativeSVG.imageKey base src,density)
    else if DOM.Dom.isHtmlElement n "video" then
      let poster := (Rendering.CSS.attrValue n "poster").trimAscii.toString
      if !poster.isEmpty then out := out.push (id,NativeSVG.imageKey base poster,1)
    else if let some src := embeddedImageSource n then out := out.push (id,NativeSVG.imageKey base src,1)
  return out.toList

/-- Fetch and store keys depend on the URL alone. -/
def htmlImageKeys (dom : DOM.Dom) (base : Option String) : List (Nat × String) :=
  (htmlImageRequests dom base).map fun (id,key,_) => (id,key)

/-! ### An SVG document as the image of an `img` (2026-11-14)

Before, an `img` whose file is SVG showed its `alt` text (the logo of Hacker News, six of
the nine images of w3.org, eleven of lean-lang.org's nineteen): the image store read PNG,
JPEG and GIF. `vectorPicture` reads an SVG document with the forgiving reader
(`NativeSVGForgiving.parseNode`: what the strict reader can not draw is left out), with no
image or document from outside it (secure static mode), and draws it on the CPU
(`SVGRaster`) into a bitmap of `NativeSVGForgiving.imageRaster` pixels. The picture then
goes the way of any image: the store's pixel budget, layout by the image's size
(`imageSize`), one image primitive. A page with no SVG image file reads four bytes of each
file that is not PNG, JPEG or GIF, and no more. -/

/-- The bytes hold `<svg` in their first 4096 bytes (after an XML declaration, a doctype
or comments): an SVG document, to try. -/
def looksLikeSVG (bytes : ByteArray) : Bool := Id.run do
  for i in [0:min bytes.size 4096] do
    if i+3 < bytes.size && bytes.get! i == 60 && bytes.get! (i+1) == 115 && bytes.get! (i+2) == 118 && bytes.get! (i+3) == 103 then
      return true
  return false

/-- The picture with its alpha, from the picture drawn on white and the one drawn on black
(the scene shader draws on an opaque ground). A pixel of colour c and alpha a is
a·c + (1-a) on white and a·c on black: the difference is 1-a in every channel (the largest
of the three is taken), and c is the black one divided by a. Pixels are not premultiplied
(`Rendering.Bitmap`). -/
def alphaFrom (white black : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity white.size
  for p in [0:white.size/4] do
    let i := p*4
    let onWhite := fun (c : Nat) => (white.get! (i+c)).toNat
    let onBlack := fun (c : Nat) => (black.get! (i+c)).toNat
    let gap := max (onWhite 0 - onBlack 0) (max (onWhite 1 - onBlack 1) (onWhite 2 - onBlack 2))
    let alpha := 255 - min 255 gap
    let channel := fun (c : Nat) => if alpha == 0 then 0 else min 255 ((onBlack c*255 + alpha/2)/alpha)
    out := (((out.push (channel 0).toUInt8).push (channel 1).toUInt8).push (channel 2).toUInt8).push alpha.toUInt8
  return out

/-- An SVG document as a picture: its bitmap and the size of the image in CSS pixels. None
for bytes that are not an SVG document. -/
def vectorPicture : NativeImage.VectorReader := fun bytes =>
  if !looksLikeSVG bytes then none else some do
    let some xml := String.fromUTF8? bytes | throw "SVG image is not UTF-8 text"
    if xml.length > NativeSVG.maxInputChars then throw "SVG image exceeds 1048576 characters"
    let root ← XML.parseNamespaceView xml
    let .element _ attrs _ := root | throw "SVG image has no root element"
    let (w,h) := NativeSVGForgiving.imageSize attrs
    let (rw,rh) := NativeSVGForgiving.imageRaster w h
    let draw : Option String → Except String ByteArray := fun ground => do
      let (scene,_) ← NativeSVGForgiving.parseNode (NativeSVGForgiving.imageRoot root w h ground) rw rh none [] none #[] 64
      pure scene.rgba
    let white ← draw none
    let rgba ← if (NativeSVGText.plainAttr attrs "viewport-fill").isSome then pure white
      else do pure (alphaFrom white (← draw (some "#000000")))
    if rgba.size != rw*rh*4 then throw "SVG image: the picture drawn has another size than asked"
    return ({width := rw, height := rh, rgba},w,h,NativeSVGForgiving.naturalSize attrs)

/-- The natural width, height and ratio of an SVG image file (`NativeSVGForgiving.naturalSize`);
none for a file that is not SVG or does not read. -/
def vectorNatural (bytes : ByteArray) : Option (Option Float × Option Float × Option Float) :=
  if !looksLikeSVG bytes then none else do
    let xml ← String.fromUTF8? bytes
    if xml.length > NativeSVG.maxInputChars then none
    let .element _ attrs _ ← (XML.parseNamespaceView xml).toOption | none
    some (NativeSVGForgiving.naturalSize attrs)

/-- An SVG image file drawn for a tile of `tw` by `th` CSS pixels, its concrete object size
(CSS Images 3 §5.3): a `viewBox` of its own is kept, with its `preserveAspectRatio`; with
none, an image of a natural width and height is scaled to the tile as a whole, and an image
without them takes the tile as its viewport. The picture has `imageRaster tw th` pixels. -/
def vectorPictureAt (bytes : ByteArray) (tw th : Nat) : Option Rendering.Bitmap :=
  if !looksLikeSVG bytes || tw == 0 || th == 0 || tw > 4096 || th > 4096 then none else
    match (do
      let some xml := String.fromUTF8? bytes | throw "SVG image is not UTF-8 text"
      if xml.length > NativeSVG.maxInputChars then throw "SVG image exceeds 1048576 characters"
      let root ← XML.parseNamespaceView xml
      let .element name attrs children := root | throw "SVG image has no root element"
      let attrs := match NativeSVGForgiving.naturalSize attrs, (NativeSVGText.plainAttr attrs "viewBox").isSome with
        | (some w, some h, _), false =>
          (attrs.filter fun a => !(a.name.namespace_.isNone && a.name.localPart == "preserveAspectRatio")) ++
            [NativeSVGText.mkAttr "viewBox" s!"0 0 {w} {h}", NativeSVGText.mkAttr "preserveAspectRatio" "none"]
        | _, _ => attrs
      let root := XML.NamespaceNode.element name attrs children
      let (rw,rh) := NativeSVGForgiving.imageRaster tw th
      let draw : Option String → Except String ByteArray := fun ground => do
        let (scene,_) ← NativeSVGForgiving.parseNode (NativeSVGForgiving.imageRoot root tw th ground) rw rh none [] none #[] 64
        pure scene.rgba
      let white ← draw none
      let rgba ← if (NativeSVGText.plainAttr attrs "viewport-fill").isSome then pure white
        else do pure (alphaFrom white (← draw (some "#000000")))
      if rgba.size != rw*rh*4 then throw "SVG image: the picture drawn has another size than asked"
      pure ({width := rw, height := rh, rgba} : Rendering.Bitmap) : Except String Rendering.Bitmap) with
    | .ok b => some b
    | .error _ => none

/-- The image store of a page: `NativeSVG.imageStoreOf` with SVG files read by
`vectorPicture`. -/
def pageStore (keys : List String) (images : List (String × ByteArray)) : NativeImage.Store :=
  NativeSVG.imageStoreOf keys images vectorPicture

private def storedPicture (store : NativeImage.Store) (key : String) :
    Option (Rendering.Layout.Picture × Option NativeImage.VectorAxes) := do
  let (.ok (id,bitmap),axes) ← store.entries.get? key | none
  let natural := (store.natural key).map fun (w,h) => Rendering.Layout.PictureSize.fromPixels w h
  return (⟨id,bitmap,natural⟩,axes)

/-- The picture of each element whose image decoded within the limits of the store. -/
@[noinline] def picturesMap (store : NativeImage.Store) (keys : List (Nat × String)) :
    Std.TreeMap Nat Rendering.Layout.Picture :=
  keys.foldl (fun (out : Std.TreeMap Nat Rendering.Layout.Picture) (id,key) =>
    match storedPicture store key with
    | some (p,_) => out.insert id p
    | none => out) {}

/-- A finite, non-negative binary64 length as an exact rational, including fractional SVG lengths. -/
private def imageLength (v : Float) : Rat :=
  if !v.isFinite || v <= 0 then 0 else
  let (fraction,exponent) := v.frExp
  let significand := (fraction * 9007199254740992).toUInt64.toNat
  (significand : Rat) * (2 : Rat) ^ (exponent - 53)

/-- The source's CSS dimensions at this element's selected pixel density. The
largest actual axis saturates at the layout coordinate bound. The other axis
scales by the same factor. Missing SVG axes use their default object dimensions. -/
private def densityMetrics (p : Rendering.Layout.Picture) (density : Rat)
    (vector : Option NativeImage.VectorAxes) : Option Rendering.Layout.PictureSize := Id.run do
  let (w,h) := p.size
  let (nw,nh,ratio) := vector.getD (some w,some h,if h > 0 then some (w/h) else none)
  if nw.isNone && nh.isNone then return p.natural
  let width := (nw.orElse fun _ => do return (← nh) * (← ratio)).map imageLength
  let height := (nh.orElse fun _ => do return (← nw) / (← ratio)).map imageLength
  let largest := max (width.getD 0) (height.getD 0)
  let scale := if density ≤ 0 then 33554431 / largest else min (1 / density) (33554431 / largest)
  let css := fun (v : Rat) => Float.ofNat ((v * scale * 64).floor.toNat) / 64
  return some ⟨(width.map css).getD 300,(height.map css).getD 150,ratio⟩

def densityPicture (p : Rendering.Layout.Picture) (density : Rat) (axes : Option NativeImage.VectorAxes) :
    Rendering.Layout.Picture :=
  if density == 1 then p else {p with natural := densityMetrics p density axes}

/-- Density changes only an element's intrinsic metrics. It cannot replace its
backing pixels or allocate a new paint-table ID. -/
theorem densityPicture_resource (p : Rendering.Layout.Picture) (d : Rat) (v : Option NativeImage.VectorAxes) :
    (densityPicture p d v).id = p.id ∧ (densityPicture p d v).bitmap = p.bitmap := by
  unfold densityPicture
  split <;> exact ⟨rfl,rfl⟩

#print axioms densityPicture_resource

/-- Each element takes its selected density, while every use of a URL shares the
bitmap and its paint-table ID. The optional SVG axes came from the same decode. -/
@[noinline] def requestedPictures (store : NativeImage.Store) (requests : List (Nat × String × Rat)) :
    Std.TreeMap Nat Rendering.Layout.Picture := Id.run do
  let mut found : Std.TreeMap Nat Rendering.Layout.Picture := {}
  for (id,key,density) in requests do
    if let some (p,axes) := storedPicture store key then
      found := found.insert id (densityPicture p density axes)
  return found

/-- Reference lookup for the pictures of `keys` in `store`. The layout paths bind
`picturesMap` outside their lookup closures so the native compiler does not rebuild
the map on every call to the closure. -/
def picturesOf (store : NativeImage.Store) (keys : List (Nat × String)) : Rendering.Layout.Pictures :=
  let found := picturesMap store keys
  fun id => found.get? id

/-! Each layout decoded the page's images again (`imageStoreOf`): 44 ms of a relayout of
gov.uk (realperf). The engine keeps the last two stores by their keys and supplied bytes
(`StoresKept`, in `WebDocument.Engine`; issue 390): a layout looks a store up there, and
gives back the store it made, which the engine keeps.

A new store (another image came) decoded every image of the page again, not only the new
one: on a W3C specification whose SVG figures came in several groups, the decoding of the
same files was about 85% of the engine's time before the first frame (2026-11-17). So a
kept store also keeps what each file decoded to (`Decodes`), and a new store reads a file
that a kept one decoded from there (`memoDecode`): the same answer, made once. -/

/-- What files decoded to (`NativeImage.decodeWith vectorPicture`), by their bytes. -/
abbrev Decodes := Array (ByteArray × NativeImage.Decoded)

/-- Two byte arrays that `==` calls equal are equal. -/
theorem bytes_eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  have h' : (a.data == b.data) = true := h
  exact ByteArray.ext (eq_of_beq h')

/-- What the bytes decode to: as `cache` has it for the same bytes, else `decodeWith`. -/
def memoDecode (cache : Decodes) (b : ByteArray) : NativeImage.Decoded :=
  match cache.find? (·.1 == b) with
  | some (_,r) => r
  | none => NativeImage.decodeWith vectorPicture b

/-- Every entry of the cache is what its bytes decode to. -/
def DecodesValid (cache : Decodes) : Prop := ∀ e ∈ cache, e.2 = NativeImage.decodeWith vectorPicture e.1

/-- Kind: refinement. Says: from a valid cache, `memoDecode` answers what `decodeWith` does,
for any bytes. Does not say: that the cache holds the bytes (then it decodes them). -/
theorem memoDecode_eq (cache : Decodes) (valid : DecodesValid cache) (b : ByteArray) :
    memoDecode cache b = NativeImage.decodeWith vectorPicture b := by
  unfold memoDecode
  split
  · next _ b' r h =>
    have mem := Array.mem_of_find?_eq_some h
    have sat := Array.find?_some h
    have v := valid _ mem
    simp only at v sat
    rw [v, bytes_eq_of_beq sat]
  · rfl

/-- What the supplied files that `keys` names decode to, read from `cache` where it has them:
the sequential form, which `decodesFor` is proved equal to (`decodesFor_eq`). -/
def decodesForSeq (cache : Decodes) (keys : List String) (images : List (String × ByteArray)) : Decodes :=
  ((images.filter fun (k,_) => keys.contains k).map fun (_,b) => (b, memoDecode cache b)).toArray

/-- Below this many files a store decodes them on the calling thread (`decodesFor`). -/
def decodeParLeast : Nat := 2

/-- `decodesForSeq`, with each file decoded in a task of its own when there are at least
`decodeParLeast` (issue 1031: image decode was 7 to 68% of the first layout of five real
pages). Each decode is a function of the file's bytes and the kept cache alone, so the files
are independent; one task per file, because one large image can take most of the time. A
task reaches only the bytes of its file and the cache. -/
def decodesFor (cache : Decodes) (keys : List String) (images : List (String × ByteArray)) : Decodes :=
  let files := ((images.filter fun (k,_) => keys.contains k).map (·.2)).toArray
  L4Factoidal.Par.mapChunksAbove decodeParLeast files.size (fun b => (b, memoDecode cache b)) files

/-- Kind: equality. Says: the parallel decode gives the sequential one's entries, in the same
order, for every number of files and threads. Does not say: that it is faster. -/
theorem decodesFor_eq (cache : Decodes) (keys : List String) (images : List (String × ByteArray)) :
    decodesFor cache keys images = decodesForSeq cache keys images := by
  unfold decodesFor decodesForSeq
  rw [L4Factoidal.Par.mapChunksAbove_eq]
  simp [List.map_map, Function.comp_def]

/-- Kind: invariant. Says: what `decodesFor` makes from a valid cache is a valid cache. -/
theorem decodesFor_valid (cache : Decodes) (valid : DecodesValid cache) (keys : List String)
    (images : List (String × ByteArray)) : DecodesValid (decodesFor cache keys images) := by
  intro e he
  rw [decodesFor_eq] at he
  simp only [decodesForSeq, List.mem_toArray, List.mem_map] at he
  obtain ⟨⟨k, b⟩, _, rfl⟩ := he
  exact memoDecode_eq cache valid b

/-- A kept store: the keys and supplied bytes it was made for, the store, and what the
files it decoded decoded to. -/
abbrev StoreEntry := (List String × List (String × ByteArray)) × NativeImage.Store × Decodes

abbrev StoresKept := Array StoreEntry

/-- The store of `keys` and `images`: the kept one, or a new one, which is also given back
to be kept. A new one decodes only the files that no kept store decoded. -/
def storeIn (kept : StoresKept) (keys : List String) (images : List (String × ByteArray)) :
    NativeImage.Store × Option StoreEntry :=
  match kept.find? (fun ((k,i),_) => k == keys && i == images) with
  | some (_,store,_) => (store,none)
  | none =>
    let decs := decodesFor (kept.flatMap (·.2.2)) keys images
    let store := NativeSVG.imageStoreOfWith (memoDecode decs) keys images
    (store,some ((keys,images),store,decs))

/-- `kept` with `made` last, at most two. -/
def keepStore (kept : StoresKept) (made : StoreEntry) : StoresKept :=
  (if kept.size ≥ 2 then kept.extract 1 kept.size else kept).push made

/-- A table is valid when each store is `imageStoreOf` of any keys and images that its own
compare equal to (`==`, as `storeIn` compares them), and what it keeps of the files is what
they decode to. -/
def StoresValid (kept : StoresKept) : Prop :=
  ∀ e ∈ kept, (∀ keys images, (e.1.1 == keys && e.1.2 == images) = true → e.2.1 = pageStore keys images) ∧
    DecodesValid e.2.2

/-- Kind: refinement. Says: a store made with the files decoded by a valid cache is
`pageStore`. -/
theorem imageStoreOfWith_memo (decs : Decodes) (valid : DecodesValid decs) (keys : List String)
    (images : List (String × ByteArray)) :
    NativeSVG.imageStoreOfWith (memoDecode decs) keys images = pageStore keys images :=
  NativeSVG.imageStoreOfWith_congr _ vectorPicture (memoDecode_eq decs valid) keys images

/-- Kind: invariant. Says: the decodes of a valid table, all together, are a valid cache. -/
theorem StoresValid.decodes (kept : StoresKept) (valid : StoresValid kept) :
    DecodesValid (kept.flatMap (·.2.2)) := by
  intro d hd
  rw [Array.mem_flatMap] at hd
  obtain ⟨e, he, hd⟩ := hd
  exact (valid e he).2 d hd

/-- Refinement: from a valid table, `storeIn` gives `imageStoreOf`. -/
theorem storeIn_eq (kept : StoresKept) (valid : StoresValid kept) (keys : List String) (images : List (String × ByteArray)) :
    (storeIn kept keys images).1 = pageStore keys images := by
  unfold storeIn
  split
  · next _ k store decs h =>
    obtain ⟨k1,k2⟩ := k
    have sat := Array.find?_some h
    exact (valid _ (Array.mem_of_find?_eq_some h)).1 keys images sat
  · exact imageStoreOfWith_memo _ (decodesFor_valid _ (StoresValid.decodes kept valid) keys images) keys images

/-- Kind: invariant. Says: what a new store keeps of the files, from a valid table, is valid. -/
theorem storeIn_made_decodes (kept : StoresKept) (valid : StoresValid kept) (keys : List String)
    (images : List (String × ByteArray)) (made : StoreEntry) (h : (storeIn kept keys images).2 = some made) :
    DecodesValid made.2.2 := by
  unfold storeIn at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    exact decodesFor_valid _ (StoresValid.decodes kept valid) keys images

/-- The keys of a document's image store, in the order `makeReplacedIn` asks for them: the
images of its SVG content, then the `img` elements'. -/
def storeKeys (dom : DOM.Dom) (documentURL : Option String) : Except String (List String) := do
  let imgs := (htmlImageKeys dom documentURL).map (·.2)
  if !(dom.nodes.any (fun node => node.type == .element && node.ns == some DOM.svgNS)) then return imgs
  let (_,tree) ← documentNamespaceTree dom
  return NativeSVG.imageKeys tree documentURL ++ imgs

/-- The store of a document's images made ahead of its first layout, to be kept
(`keepStore`): none when the table has it, or when the document's SVG content can not be
read (the layout then says so). A page's scripts start before its first frame, and each
layout that a script read asked for decoded every image again, since no layout had kept a
store yet: on a page with large images and SVG image files the first turn of its scripts
took 150 s in place of 8 (lean-lang.org, 2026-11-14). The work is the first frame's, done
once and earlier; a page with no image makes an empty store. -/
def storeAhead (kept : StoresKept) (dom : DOM.Dom) (documentURL : Option String)
    (images : List (String × ByteArray)) : Option StoreEntry :=
  match storeKeys dom documentURL with
  | .ok keys => if keys.isEmpty then none else (storeIn kept keys images).2
  | .error _ => none

/-- Kind: refinement. Says: a store made ahead from a valid table is `pageStore` of the
document's own keys (`storeKeys`) and of the images given, under those keys and images:
what a layout that asks `storeIn` for the same keys and images would make itself. Does not
say: that the next layout asks with lists that compare equal to these (it asks with
`storeKeys`' expression and the request's images; that the kept store is then found is
tested, not proved). -/
theorem storeAhead_made (kept : StoresKept) (valid : StoresValid kept) (dom : DOM.Dom) (documentURL : Option String)
    (images : List (String × ByteArray)) (made : StoreEntry)
    (h : storeAhead kept dom documentURL images = some made) :
    ∃ keys, storeKeys dom documentURL = .ok keys ∧ made.1 = (keys,images) ∧ made.2.1 = pageStore keys images := by
  unfold storeAhead at h
  split at h
  · rename_i keys hk
    split at h
    · simp at h
    · refine ⟨keys, hk, ?_⟩
      have hs := storeIn_eq kept valid keys images
      unfold storeIn at h hs
      split at h
      · simp at h
      · rename_i hnone
        simp only [hnone] at hs
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, hs⟩
  · simp at h

/-- The embedding of SVG roots and the pictures of `img` elements, from one image
store: each image decodes once, and the ids of bitmaps do not collide. One
source-bound index per render, shared by all embedded SVG roots. SVG text is lowered
to glyph paths first, with `fonts`, the fonts that draw HTML text
(`NativeSVGText.lowerDocumentGlyphs`); each element keeps its source path, and the
glyph outlines go to the reader as numbers in a table. -/
def makeReplacedIn (kept : StoresKept) (words : NativeSVGText.Words) (dom : DOM.Dom) (documentURL : Option String := none)
    (images : List (String × ByteArray) := []) (fonts : Array Rendering.SfntProfile.Font := #[])
    (cascade : Option (Array Rendering.CSS.Computed) := none) :
    Except String (Rendering.Layout.Embedding × Rendering.Layout.Pictures ×
      Option StoreEntry × NativeSVGText.Words) := do
  let imgs := htmlImageRequests dom documentURL
  if !(dom.nodes.any (fun node => node.type == .element && node.ns == some DOM.svgNS)) then
    let (store,made) := storeIn kept (imgs.map (·.2.1)) images
    let found := requestedPictures store imgs
    return (embedding dom,(fun id => found.get? id),made,{})
  if documentURL.isNone && dom.nodes.any (fun node => DOM.Dom.isHtmlElement node "base" && Rendering.CSS.hasAttribute node "href") then
    throw "unsupported HTML base href without explicit document URL/base transport"
  let (root,source) ← documentNamespaceTree dom cascade
  -- CSS Color 4 colours the reader does not read, as `#rrggbb` (`SVGCssColour`); the tree's
  -- shape is unchanged, so source paths still point at the same elements
  let source := NativeSVGCssColour.tree 256 source
  let (tree,_,glyphs,madeWords) := NativeSVGText.lowerDocumentGlyphsIn words fonts source
  let context ← NativeSVG.ReferenceContext.create tree documentURL
  -- Each image decodes once for the document, not once for each SVG root. The keys are
  -- those of the tree as it was read (`storeKeys`: text lowered to glyphs names no image),
  -- so a store made ahead of the layout (`storeAhead`) is the one found here.
  let (store,made) := storeIn kept (NativeSVG.imageKeys source documentURL ++ imgs.map (·.2.1)) images
  -- A viewport of fractional CSS pixels (a percentage width with `height:auto`) keeps its
  -- exact size: the viewBox maps onto it, and the backing raster is the next whole pixel.
  let found := requestedPictures store imgs
  return (fun id style width height => do
    let path ← sourcePath dom root (dom.size+1) id []
    let inherited : NativeSVG.Style := {currentColor := WebRenderSVG.toColor style.color, visible := style.visible}
    let scene ← NativeSVG.parseRootInContextSized context path width height inherited embeddedAttributes (some store) glyphs
    return placeSVG scene id style width height,(fun id => found.get? id),made,madeWords)

/-- The pictures of a page drawn with no SVG: the `img` pictures, made as on a page with no
`svg` element, and an embedding that refuses every `svg` root with `refusal` (liberal mode
draws a refused root as nothing). The fallback of liberal mode when the SVG of a document
can not be read at all: the rest of the page is still drawn. -/
def makeReplacedNoSvg (kept : StoresKept) (dom : DOM.Dom) (documentURL : Option String)
    (images : List (String × ByteArray)) (refusal : String) :
    Rendering.Layout.Embedding × Rendering.Layout.Pictures ×
      Option StoreEntry × NativeSVGText.Words :=
  let imgs := htmlImageRequests dom documentURL
  let (store,made) := storeIn kept (imgs.map (·.2.1)) images
  let found := requestedPictures store imgs
  (fun _ _ _ _ => .error refusal,(fun id => found.get? id),made,{})

/-- Precomputing the lookup table in the SVG fallback preserves the picture
lookup for every ID, including missing or refused images. -/
theorem makeReplacedNoSvg_pictures (kept : StoresKept) (dom : DOM.Dom)
    (documentURL : Option String) (images : List (String × ByteArray)) (refusal : String) :
    (makeReplacedNoSvg kept dom documentURL images refusal).2.1 =
      let imgs := htmlImageRequests dom documentURL
      let found := requestedPictures (storeIn kept (imgs.map (·.2.1)) images).1 imgs
      fun id => found.get? id := rfl

/-- Kind: safety. Says: the embedding of `makeReplacedNoSvg` answers every `svg` root with its
refusal and nothing else, so the layout that takes it (liberal mode, `quiet`) draws no SVG and
reads no SVG source. -/
theorem makeReplacedNoSvg_refuses (kept : StoresKept) (dom : DOM.Dom) (documentURL : Option String)
    (images : List (String × ByteArray)) (refusal : String) (id : Nat) (s : Rendering.CSS.Computed) (w h : Float) :
    (makeReplacedNoSvg kept dom documentURL images refusal).1 id s w h = .error refusal := rfl

/-- `makeReplacedIn` with no kept store. -/
def makeReplaced (dom : DOM.Dom) (documentURL : Option String := none)
    (images : List (String × ByteArray) := []) (fonts : Array Rendering.SfntProfile.Font := #[]) :
    Except String (Rendering.Layout.Embedding × Rendering.Layout.Pictures) :=
  (fun (e,p,_) => (e,p)) <$> makeReplacedIn #[] {} dom documentURL images fonts

/-- The SVG embedding of `makeReplaced`. -/
def makeEmbedding (dom : DOM.Dom) (documentURL : Option String := none)
    (images : List (String × ByteArray) := []) (fonts : Array Rendering.SfntProfile.Font := #[]) :
    Except String Rendering.Layout.Embedding :=
  Prod.fst <$> makeReplaced dom documentURL images fonts

/-- A page with its document URL and the bytes of the images it names (keys of
`storeKeys`), as a host supplies them. With no URL and no images it is `render`. -/
def renderWith (html : String) (width height : Nat) (documentURL : Option String)
    (images : List (String × ByteArray)) : Except String (Rendering.Scene × Array Rendering.Layout.Box) := do
  if html.length > maxSourceBytes then throw s!"unsupported HTML input exceeding {maxSourceBytes} characters"
  let dom := DOM.parseHtmlDocument html
  let (embedding,pictures) ← makeReplaced dom documentURL images
  renderDOM dom width height embedding pictures

def render (html : String) (width height : Nat) : Except String (Rendering.Scene × Array Rendering.Layout.Box) :=
  renderWith html width height none []

/-- Kind: refinement. Says: `render` is `renderWith` with no document URL and no images.
Does not say: anything about a page whose images are supplied. -/
theorem render_eq_renderWith (html : String) (width height : Nat) :
    render html width height = renderWith html width height none [] := rfl

private def array (xs : List String) := "[" ++ String.intercalate "," xs ++ "]"
private def runJSON (r : Rendering.GlyphRun) : String :=
  "{\"source\":" ++ toString r.source ++ ",\"font\":" ++ quote r.font ++ ",\"size\":" ++ toString r.fontSize ++
  ",\"text\":" ++ quote r.text ++ ",\"glyphs\":" ++ array (r.glyphs.toList.map fun g =>
    array [toString g.index,toString g.x,toString g.y,toString g.advance,toString g.clusterStart,toString g.clusterEnd]) ++ "}"
private def layoutHeader (font : Option Rendering.FontProvider.Face) : String :=
  match font with
    | none => "{\"profile\":\"lean-block-inline-ascii-bitmap-v1\",\"fontScope\":\"ASCII bitmap; no real font shaping\""
    | some face => "{\"profile\":\"lean-block-inline-font-data-v1\",\"fontScope\":\"Supplied HarfBuzz/FreeType horizontal LTR words; canonical font contours with checked backend compilation; no bidi or fallback\",\"fontResource\":{\"family\":" ++ quote face.family ++ ",\"fontSha256\":" ++ quote face.fontSha256 ++ ",\"faceIndex\":" ++ toString face.faceIndex ++ ",\"style\":" ++ quote face.style ++ ",\"unitsPerEm\":" ++ toString face.unitsPerEm ++ "}"
private def boxesJSON (boxes : Array Rendering.Layout.Box) : String :=
  array (boxes.toList.map fun b => array [toString b.source,toString b.x,toString b.y,toString b.width,toString b.height])

/-- The part of `layoutJSON` before the links: the font header, the boxes and the glyph
runs. It reads no link and no band, so every band of one layout has the same head: the
engine keeps it with a page layer answer and gives it again for another band
(`WebDocument.pageArtifact`). On a long page the boxes and glyph runs of the whole page are
most of a band's compile (a W3C specification, 2026-11-17: about 60%). -/
def layoutHead (boxes : Array Rendering.Layout.Box) (runs : Array Rendering.GlyphRun)
    (font : Option Rendering.FontProvider.Face) : String :=
  layoutHeader font ++ ",\"boxes\":" ++ boxesJSON boxes ++ ",\"glyphRuns\":" ++ array (runs.toList.map runJSON)

/-- The part of `layoutJSON` after the head: the links, and the end of the object. -/
def layoutTail (links : Array Rendering.LinkRegion) : String :=
  ",\"links\":" ++ Rendering.Links.encode links ++ "}"

def layoutJSON (s : Rendering.Scene) (boxes : Array Rendering.Layout.Box)
    (font : Option Rendering.FontProvider.Face) : String :=
  layoutHead boxes s.glyphRuns font ++ layoutTail s.links

/-- Kind: equality (the answer's format). Says: `layoutJSON` is the text it was before the
head and the tail were split out (2026-11-17): the font header, then `"boxes"`,
`"glyphRuns"` and `"links"` in that order, each written by the same function as before.
Does not say: anything about what a host does with the text. -/
theorem layoutJSON_eq_flat (s : Rendering.Scene) (boxes : Array Rendering.Layout.Box)
    (font : Option Rendering.FontProvider.Face) :
    layoutJSON s boxes font = layoutHeader font ++ ",\"boxes\":" ++ boxesJSON boxes ++
      ",\"glyphRuns\":" ++ array (s.glyphRuns.toList.map runJSON) ++ ",\"links\":" ++
      Rendering.Links.encode s.links ++ "}" := by
  simp only [layoutJSON, layoutHead, layoutTail, String.append_assoc]

/-- Kind: equality. Says: for a scene whose glyph runs are `runs`, `layoutJSON` is the head
of the boxes, `runs` and the font, then the tail of the scene's own links. So a head made
for one scene is the head of every scene with the same runs, boxes and font, whatever its
links. Does not say: that the links of two such scenes are the same. -/
theorem layoutJSON_of_head (s : Rendering.Scene) (runs : Array Rendering.GlyphRun)
    (boxes : Array Rendering.Layout.Box) (font : Option Rendering.FontProvider.Face)
    (h : s.glyphRuns = runs) :
    layoutJSON s boxes font = layoutHead boxes runs font ++ layoutTail s.links := by
  subst h; rfl

/-- The layout header closed with the mark `"layoutSections":true`: the boxes, glyph runs and
link regions are not in the text but in the sections of `layoutSections` (issue
https://github.com/danbri/factoidal-core/issues/1124, stage B; request field `layoutSections`). -/
def layoutHeadOnly (font : Option Rendering.FontProvider.Face) : String :=
  layoutHeader font ++ ",\"layoutSections\":true}"

@[inline] private def pushF64 (b : ByteArray) (x : Float) : ByteArray :=
  let w := x.toBits
  b.push w.toUInt8 |>.push (w >>> 8).toUInt8 |>.push (w >>> 16).toUInt8 |>.push (w >>> 24).toUInt8
    |>.push (w >>> 32).toUInt8 |>.push (w >>> 40).toUInt8 |>.push (w >>> 48).toUInt8 |>.push (w >>> 56).toUInt8

@[inline] private def pushNat (b : ByteArray) (n : Nat) : ByteArray := pushF64 b (Float.ofNat n)

/-- Boxes, glyph runs and link regions as two sections, in place of the JSON arrays of
`layoutJSON` (issue 1124, stage B). The first is float64 little-endian numbers: the counts of
boxes, runs, glyphs and links; each box as `[source, x, y, width, height]`; each run as
`[source, fontSize, fontStart, fontBytes, textStart, textBytes, glyphCount]`; the glyphs of
every run in run order, each as `[index, x, y, advance, clusterStart, clusterEnd]`; each link as
`[sourceNode, hrefStart, hrefBytes, x, y, width, height]`. The second is UTF-8: the run fonts,
run texts and link targets that the starts and byte counts name. Every number is the Lean
`Float` itself (a natural number below 2^53 is exact), so a host reads the values that
`layoutJSON` writes as decimal text, without the text. One pass over each array; no list. -/
def layoutSections (boxes : Array Rendering.Layout.Box) (runs : Array Rendering.GlyphRun)
    (links : Array Rendering.LinkRegion) : ByteArray × ByteArray := Id.run do
  let glyphs := runs.foldl (fun n r => n+r.glyphs.size) 0
  let mut nums := ByteArray.emptyWithCapacity (8*(4+5*boxes.size+7*runs.size+6*glyphs+7*links.size))
  let mut text := ByteArray.emptyWithCapacity 4096
  nums := pushNat (pushNat (pushNat (pushNat nums boxes.size) runs.size) glyphs) links.size
  for b in boxes do
    nums := pushF64 (pushF64 (pushF64 (pushF64 (pushNat nums b.source) b.x) b.y) b.width) b.height
  for r in runs do
    let fontStart := text.size
    text := text ++ r.font.toUTF8
    let textStart := text.size
    text := text ++ r.text.toUTF8
    nums := pushNat (pushNat (pushNat (pushNat (pushNat (pushF64 (pushNat nums r.source) r.fontSize)
      fontStart) (textStart-fontStart)) textStart) (text.size-textStart)) r.glyphs.size
  for r in runs do
    for g in r.glyphs do
      nums := pushNat (pushNat (pushF64 (pushF64 (pushF64 (pushNat nums g.index) g.x) g.y) g.advance) g.clusterStart) g.clusterEnd
  for l in links do
    let start := text.size
    text := text ++ l.href.toUTF8
    nums := pushF64 (pushF64 (pushF64 (pushF64 (pushNat (pushNat (pushNat nums l.sourceNode) start) (text.size-start))
      l.x) l.y) l.width) l.height
  return (nums,text)

/-- Shared checked scene serialization for HTML and structured-document frontends:
the artifact with the storage floats and tile words in the form `form`, and the
sections that it names. -/
def artifactWith (scene : Rendering.Scene) (boxes : Array Rendering.Layout.Box)
    (font : Option Rendering.FontProvider.Face) (live : Bool) (form : NativeSVG.DataForm) (checks tree : Bool)
    (layoutOff : Bool := false) :
    Except String (String × Array ByteArray) := do
  let native ← WebRenderSVG.toScene scene
  let (value,sections) ← native.artifactWith live form checks tree
  -- `layoutOff`: the boxes, glyph runs and links go in sections (`layoutSections`), not here.
  let value := (value.dropEnd 1).toString ++ ",\"webRender\":" ++
    (if layoutOff then layoutHeadOnly font else layoutJSON scene boxes font)
  match form with
  -- The scene drawn on the CPU (`SVGRaster`): the section after the tile words.
  | .sectionsCpu k => return (value ++ ",\"pixelsSection\":" ++ toString (k+2) ++ "}",sections.push native.rgba)
  | _ => return (value ++ "}",sections)

def artifact (scene : Rendering.Scene) (boxes : Array Rendering.Layout.Box)
    (font : Option Rendering.FontProvider.Face := none) (live binary : Bool := false) (checks : Bool := true)
    (tree : Bool := true) : Except String String :=
  Prod.fst <$> artifactWith scene boxes font live (if binary then .base64 else .decimal) checks tree

@[export web_render_compile]
/-- `compile` of `renderWith`: the page with its document URL and supplied images. -/
def compileWith (html : String) (width height : UInt32) (documentURL : Option String)
    (images : List (String × ByteArray)) : String :=
  match renderWith html width.toNat height.toNat documentURL images >>= (fun (scene,boxes) => artifact scene boxes) with
  | .error message => errorJSON message
  | .ok value => value

def compile (html : String) (width height : UInt32) : String :=
  match render html width.toNat height.toNat >>= (fun (scene,boxes) => artifact scene boxes) with
  | .error message => errorJSON message
  | .ok value => value

end WebRender
