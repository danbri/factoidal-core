import WebRenderSVG
import SVGRaster
import SVGText
import SVGForgiving
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

def asciiFont : Rendering.Layout.FontProfile :=
  {family := "factoidal-ascii-bitmap-v1",unitsPerEm := 7,advance := 6, ascent := 7,descent := 0,outline := bitmapOutline, admits := fun n => 32 <= n && n <= 126}

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

/-- Convert the original HTML element subtree bottom-up. Every original child
index survives, including text/comments; no host extraction or XML reparse. A `script`
element (HTML's or SVG's) draws nothing: it stays in its place as an empty comment, so the
SVG reader does not meet it and the indices after it are unchanged. -/
def documentNamespaceTree (dom : DOM.Dom) : Except String (Nat × XML.NamespaceNode) := do
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
      if node.type == .element && node.lname == "script" && id != root &&
          (node.ns == some DOM.htmlNS || node.ns == some DOM.svgNS) then
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
      let declarations := declarations.filter (fun d =>
        !Rendering.CSS.htmlProperties.contains d.property)
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

/-- A URL whose path names an image format the engine has no decoder for: WebP, AVIF, JPEG
XL, HEIF. -/
def undecodablePath (url : String) : Bool :=
  let path := ((((url.splitOn "#").headD "").splitOn "?").headD "").toLower
  [".webp", ".avif", ".jxl", ".heic", ".heif"].any fun ending => path.endsWith ending

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
def chosenSource (dom : DOM.Dom) (id : Nat) : Option String :=
  let (set,size) := HTML.ImageSource.sourceSet dom id sourceEnv
  match HTML.ImageSource.selectFrom sourceEnv.dpr size (set.filter fun s => !undecodablePath s.url) with
  | some (source,_) =>
    let url := source.url.trimAscii.toString
    if url.isEmpty then plainSource dom id else some url
  | none => plainSource dom id

/-- The URL, as written, of the image an `img` shows. -/
def imageSource (dom : DOM.Dom) (id : Nat) : Option String :=
  if plainImage dom id then plainSource dom id else chosenSource dom id

/-- Kind: property (zero cost, and no change). Says: an `img` with no `srcset` outside a
`picture` shows its `src`, as before: no source set is made for it. Does not say: which
candidate another `img` shows (that is `HTML.ImageSource.selectFrom`, with
`selectFrom_mem`: one of the element's own sources). -/
theorem imageSource_plain (dom : DOM.Dom) (id : Nat) (h : plainImage dom id = true) :
    imageSource dom id = plainSource dom id := by
  simp [imageSource, h]

/-- The image of each HTML `img`, by node, as a key of the image store
(`NativeSVG.imageKey`: a `data:` URI as it stands, another URL resolved). -/
def htmlImageKeys (dom : DOM.Dom) (base : Option String) : List (Nat × String) := Id.run do
  let mut out : Array (Nat × String) := #[]
  for id in [0:dom.size] do
    let n := dom.get id
    if DOM.Dom.isHtmlElement n "img" then
      if let some src := imageSource dom id then out := out.push (id,NativeSVG.imageKey base src)
  return out.toList

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
    return ({width := rw, height := rh, rgba},w,h)

/-- The image store of a page: `NativeSVG.imageStoreOf` with SVG files read by
`vectorPicture`. -/
def pageStore (keys : List String) (images : List (String × ByteArray)) : NativeImage.Store :=
  NativeSVG.imageStoreOf keys images vectorPicture

/-- The picture of each `img` whose image decoded within the limits of the store. -/
def picturesOf (store : NativeImage.Store) (keys : List (Nat × String)) : Rendering.Layout.Pictures :=
  let found := keys.foldl (fun (out : Std.TreeMap Nat Rendering.Layout.Picture) (id,key) =>
    match store.get? key with
    | some (.ok (n,bitmap)) => out.insert id ⟨n,bitmap,store.natural key⟩
    | _ => out) {}
  fun id => found.get? id

/-! Each layout decoded the page's images again (`imageStoreOf`): 44 ms of a relayout of
gov.uk (realperf). The engine keeps the last two stores by their keys and supplied bytes
(`StoresKept`, in `WebDocument.Engine`; issue 390): a layout looks a store up there, and
gives back the store it made, which the engine keeps. -/
abbrev StoresKept := Array ((List String × List (String × ByteArray)) × NativeImage.Store)

/-- The store of `keys` and `images`: the kept one, or a new one, which is also given back
to be kept. -/
def storeIn (kept : StoresKept) (keys : List String) (images : List (String × ByteArray)) :
    NativeImage.Store × Option ((List String × List (String × ByteArray)) × NativeImage.Store) :=
  match kept.find? (fun ((k,i),_) => k == keys && i == images) with
  | some (_,store) => (store,none)
  | none => let store := pageStore keys images; (store,some ((keys,images),store))

/-- `kept` with `made` last, at most two. -/
def keepStore (kept : StoresKept) (made : (List String × List (String × ByteArray)) × NativeImage.Store) : StoresKept :=
  (if kept.size ≥ 2 then kept.extract 1 kept.size else kept).push made

/-- A table is valid when each store is `imageStoreOf` of any keys and images that its own
compare equal to (`==`, as `storeIn` compares them). -/
def StoresValid (kept : StoresKept) : Prop :=
  ∀ e ∈ kept, ∀ keys images, (e.1.1 == keys && e.1.2 == images) = true → e.2 = pageStore keys images

/-- Refinement: from a valid table, `storeIn` gives `imageStoreOf`. -/
theorem storeIn_eq (kept : StoresKept) (valid : StoresValid kept) (keys : List String) (images : List (String × ByteArray)) :
    (storeIn kept keys images).1 = pageStore keys images := by
  unfold storeIn
  split
  · next _ k store h =>
    obtain ⟨k1,k2⟩ := k
    have sat := Array.find?_some h
    exact valid _ (Array.mem_of_find?_eq_some h) keys images sat
  · rfl

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
    (images : List (String × ByteArray)) : Option ((List String × List (String × ByteArray)) × NativeImage.Store) :=
  match storeKeys dom documentURL with
  | .ok keys => if keys.isEmpty then none else (storeIn kept keys images).2
  | .error _ => none

/-- Kind: refinement. Says: a store made ahead is `pageStore` of the document's own keys
(`storeKeys`) and of the images given, under those keys and images: what a layout that asks
`storeIn` for the same keys and images would make itself. Does not say: that the next layout
asks with lists that compare equal to these (it asks with `storeKeys`' expression and the
request's images; that the kept store is then found is tested, not proved: `==` on byte
arrays has no lawfulness instance here). -/
theorem storeAhead_made (kept : StoresKept) (dom : DOM.Dom) (documentURL : Option String)
    (images : List (String × ByteArray)) (made : (List String × List (String × ByteArray)) × NativeImage.Store)
    (h : storeAhead kept dom documentURL images = some made) :
    ∃ keys, storeKeys dom documentURL = .ok keys ∧ made = ((keys,images),pageStore keys images) := by
  unfold storeAhead at h
  split at h
  · rename_i keys hk
    split at h
    · simp at h
    · refine ⟨keys, hk, ?_⟩
      unfold storeIn at h
      split at h
      · simp at h
      · simpa using h.symm
  · simp at h

/-- The embedding of SVG roots and the pictures of `img` elements, from one image
store: each image decodes once, and the ids of bitmaps do not collide. One
source-bound index per render, shared by all embedded SVG roots. SVG text is lowered
to glyph paths first, with `fonts`, the fonts that draw HTML text
(`NativeSVGText.lowerDocumentGlyphs`); each element keeps its source path, and the
glyph outlines go to the reader as numbers in a table. -/
def makeReplacedIn (kept : StoresKept) (words : NativeSVGText.Words) (dom : DOM.Dom) (documentURL : Option String := none)
    (images : List (String × ByteArray) := []) (fonts : Array Rendering.SfntProfile.Font := #[]) :
    Except String (Rendering.Layout.Embedding × Rendering.Layout.Pictures ×
      Option ((List String × List (String × ByteArray)) × NativeImage.Store) × NativeSVGText.Words) := do
  let imgs := htmlImageKeys dom documentURL
  if !(dom.nodes.any (fun node => node.type == .element && node.ns == some DOM.svgNS)) then
    let (store,made) := storeIn kept (imgs.map (·.2)) images
    return (embedding dom,picturesOf store imgs,made,{})
  if documentURL.isNone && dom.nodes.any (fun node => DOM.Dom.isHtmlElement node "base" && Rendering.CSS.hasAttribute node "href") then
    throw "unsupported HTML base href without explicit document URL/base transport"
  let (root,source) ← documentNamespaceTree dom
  let (tree,_,glyphs,madeWords) := NativeSVGText.lowerDocumentGlyphsIn words fonts source
  let context ← NativeSVG.ReferenceContext.create tree documentURL
  -- Each image decodes once for the document, not once for each SVG root. The keys are
  -- those of the tree as it was read (`storeKeys`: text lowered to glyphs names no image),
  -- so a store made ahead of the layout (`storeAhead`) is the one found here.
  let (store,made) := storeIn kept (NativeSVG.imageKeys source documentURL ++ imgs.map (·.2)) images
  -- A viewport of fractional CSS pixels (a percentage width with `height:auto`) keeps its
  -- exact size: the viewBox maps onto it, and the backing raster is the next whole pixel.
  return (fun id style width height => do
    let path ← sourcePath dom root (dom.size+1) id []
    let inherited : NativeSVG.Style := {currentColor := WebRenderSVG.toColor style.color, visible := style.visible}
    let scene ← NativeSVG.parseRootInContextSized context path width height inherited embeddedAttributes (some store) glyphs
    return placeSVG scene id style width height,picturesOf store imgs,made,madeWords)

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

def render (html : String) (width height : Nat) : Except String (Rendering.Scene × Array Rendering.Layout.Box) := do
  if html.length > maxSourceBytes then throw s!"unsupported HTML input exceeding {maxSourceBytes} characters"
  let dom := DOM.parseHtmlDocument html
  let (embedding,pictures) ← makeReplaced dom
  renderDOM dom width height embedding pictures

private def array (xs : List String) := "[" ++ String.intercalate "," xs ++ "]"
private def runJSON (r : Rendering.GlyphRun) : String :=
  "{\"source\":" ++ toString r.source ++ ",\"font\":" ++ quote r.font ++ ",\"size\":" ++ toString r.fontSize ++
  ",\"text\":" ++ quote r.text ++ ",\"glyphs\":" ++ array (r.glyphs.toList.map fun g =>
    array [toString g.index,toString g.x,toString g.y,toString g.advance,toString g.clusterStart,toString g.clusterEnd]) ++ "}"
def layoutJSON (s : Rendering.Scene) (boxes : Array Rendering.Layout.Box)
    (font : Option Rendering.FontProvider.Face) : String :=
  let header := match font with
    | none => "{\"profile\":\"lean-block-inline-ascii-bitmap-v1\",\"fontScope\":\"ASCII bitmap; no real font shaping\""
    | some face => "{\"profile\":\"lean-block-inline-font-data-v1\",\"fontScope\":\"Supplied HarfBuzz/FreeType horizontal LTR words; canonical font contours with checked backend compilation; no bidi or fallback\",\"fontResource\":{\"family\":" ++ quote face.family ++ ",\"fontSha256\":" ++ quote face.fontSha256 ++ ",\"faceIndex\":" ++ toString face.faceIndex ++ ",\"style\":" ++ quote face.style ++ ",\"unitsPerEm\":" ++ toString face.unitsPerEm ++ "}"
  header ++ ",\"boxes\":" ++
  array (boxes.toList.map fun b => array [toString b.source,toString b.x,toString b.y,toString b.width,toString b.height]) ++
  ",\"glyphRuns\":" ++ array (s.glyphRuns.toList.map runJSON) ++ ",\"links\":" ++ Rendering.Links.encode s.links ++ "}"

/-- Shared checked scene serialization for HTML and structured-document frontends:
the artifact with the storage floats and tile words in the form `form`, and the
sections that it names. -/
def artifactWith (scene : Rendering.Scene) (boxes : Array Rendering.Layout.Box)
    (font : Option Rendering.FontProvider.Face) (live : Bool) (form : NativeSVG.DataForm) (checks tree : Bool) :
    Except String (String × Array ByteArray) := do
  let native ← WebRenderSVG.toScene scene
  let (value,sections) ← native.artifactWith live form checks tree
  let value := (value.dropEnd 1).toString ++ ",\"webRender\":" ++ layoutJSON scene boxes font
  match form with
  -- The scene drawn on the CPU (`SVGRaster`): the section after the tile words.
  | .sectionsCpu k => return (value ++ ",\"pixelsSection\":" ++ toString (k+2) ++ "}",sections.push native.rgba)
  | _ => return (value ++ "}",sections)

def artifact (scene : Rendering.Scene) (boxes : Array Rendering.Layout.Box)
    (font : Option Rendering.FontProvider.Face := none) (live binary : Bool := false) (checks : Bool := true)
    (tree : Bool := true) : Except String String :=
  Prod.fst <$> artifactWith scene boxes font live (if binary then .base64 else .decimal) checks tree

@[export web_render_compile]
def compile (html : String) (width height : UInt32) : String :=
  match render html width.toNat height.toNat >>= (fun (scene,boxes) => artifact scene boxes) with
  | .error message => errorJSON message
  | .ok value => value

end WebRender
