import L4Factoidal.Rendering.Layout

/-! Replaced elements in HTML layout: `img` sizes (CSS 2.1 §10.3.2, §10.4, §10.6.2,
§10.7, HTML §15.4.3), `object-fit` (CSS Images 3 §5.5), alt text, and the small CSS
gaps of https://github.com/danbri/factoidal/issues/1273 fixed beside them: `pre`
spaces, the canvas background, inline backgrounds and margins on inline `svg`. The
test face is monospace, 6 px advance, 7 px ascent, no descent. -/
namespace L4Factoidal.Rendering.ReplacedTests
open DOM CSS Layout

/-- A result equals a value when it is that value; an error equals nothing. -/
private instance [BEq α] : BEq (Except String α) where
  beq | .ok a, .ok b => a == b | _, _ => false

private def font : FontProfile :=
  {family := "replaced-test",unitsPerEm := 7,advance := 6,ascent := 7,descent := 0,
   outline := fun _ => [.rect 0 0 5 7],admits := fun n => n >= 32 && n <= 126}
private def noSVG : Embedding := fun _ _ _ _ => .ok []
/-- A 40 by 20 picture for every element with `src="a.png"`; nothing for others. -/
private def picture : Picture := ⟨0,⟨40,20,ByteArray.mk (Array.replicate (40*20*4) 255)⟩,none⟩
/-- The same image held at half its size on each side (a host that keeps a large image
reduced): 20 by 10 pixels that stand for 40 by 20. -/
private def reducedPicture : Picture := ⟨0,⟨20,10,ByteArray.mk (Array.replicate (20*10*4) 255)⟩,some (PictureSize.fromPixels 40 20)⟩
-- A picture held reduced has the size of its image, and is painted in the same rectangle with
-- a map that reaches half as many pixels on each side.
#guard reducedPicture.size == picture.size

-- Both density-corrected dimensions can round to zero. CSS minima still
-- transfer through the source ratio. The tighter opposing maximum wins.
private def subpixelPicture : Picture := {picture with natural := some ⟨0,0,some (101/51)⟩}
#guard subpixelPicture.usedSize {minWidth := .px 101} 800 == (101,51)
#guard subpixelPicture.usedSize {minHeight := .px 51} 800 == (101,51)
#guard subpixelPicture.usedSize {minWidth := .px 101, maxHeight := .px 20} 800 == (101,20)

private def paintOf (p : Picture) : Option (Float × Float × Float × Float × Float × Float) :=
  match pictureNodes 1 {} p 10 5 80 40 with
  | [Node.paint ⟨_,painted⟩] =>
    match painted.geometry, painted.style.fill with
    | .rect x y w h, .image record => some (x,y,w,h,record.map.a,record.map.d)
    | _, _ => none
  | _ => none
#guard paintOf picture == some (10,5,80,40,0.5,0.5)
#guard paintOf reducedPicture == some (10,5,80,40,0.25,0.25)
private def picturesOf (dom : Dom) : Pictures := fun id =>
  if CSS.attrValue (dom.get id) "src" == "a.png" then some picture else none
private def css := "body{margin:0;font-size:7px;line-height:7px}"
private def render (html extra : String) (width : Nat := 200) : Except String (Scene × Array Box) := do
  let dom := DOM.parseHtmlDocument html
  Layout.render dom (← CSS.parse (css ++ extra)) font noSVG width 100 1 {} (picturesOf dom)
/-- The border boxes of the elements with an `id`, by id, in layout order. -/
private def boxes (html : String) (extra : String := "") (width : Nat := 200) :
    Except String (List (String × Float × Float × Float × Float)) := do
  let dom := DOM.parseHtmlDocument html
  let (_,found) ← Layout.render dom (← CSS.parse (css ++ extra)) font noSVG width 100 1 {} (picturesOf dom)
  return found.toList.filterMap fun b =>
    let id := CSS.attrValue (dom.get b.source) "id"
    if id.isEmpty || (dom.get b.source).type != .element then none else some (id,b.x,b.y,b.width,b.height)

-- Sizing, CSS 2.1 §10.3.2 and §10.6.2: intrinsic size, one dimension with the ratio, both.
private def size (style : Computed) (available : Float := 200) := replacedSize style (some (40,20)) available
#guard size {} == (40,20)
#guard size {width := .px 80} == (80,40)
#guard size {height := .px 10} == (20,10)
#guard size {width := .px 10,height := .px 30} == (10,30)
#guard size {width := .percent 0.5} == (100,50)
-- While a width is measured (available 0) a percentage counts as auto.
#guard size {width := .percent 0.5} 0 == (40,20)
-- No content: 300 by 150, or the one dimension given.
#guard replacedSize {} none 200 == (300,150)
#guard replacedSize {width := .px 30} none 200 == (30,150)
-- §10.4 and §10.7, both auto: the ratio is kept within the limits where it can be.
#guard size {maxWidth := .px 20} == (20,10)
#guard size {maxWidth := .percent 1} 30 == (30,15)
#guard size {maxHeight := .px 5} == (10,5)
#guard size {minWidth := .px 80} == (80,40)
#guard size {minHeight := .px 40} == (80,40)
#guard size {maxWidth := .px 20,minHeight := .px 15} == (20,15)
#guard size {minWidth := .px 100,maxHeight := .px 30} == (100,30)
-- A minimum wins over a maximum.
#guard size {minWidth := .px 50,maxWidth := .px 30} == (50,25)
-- One dimension given: the other follows the used value of the first.
#guard size {width := .px 100,maxWidth := .px 60} == (60,30)
#guard size {height := .px 100,maxHeight := .px 10} == (20,10)
#guard constrainBoth 40 20 0 unbounded 0 unbounded == (40,20)

-- object-fit, CSS Images 3 §5.5.
#guard fitScale .fill 40 20 80 80 == (2,4)
#guard fitScale .contain 40 20 80 80 == (2,2)
#guard fitScale .cover 40 20 80 80 == (4,4)
#guard fitScale .none 40 20 80 80 == (1,1)
#guard fitScale .scaleDown 40 20 80 80 == (1,1)
#guard fitScale .scaleDown 40 20 20 20 == (0.5,0.5)
/-- The painted rectangle and the pixel map's scale and offset of a picture. -/
private def painted (fit : ObjectFit) (w h : Float) (position : String := "") :
    List (Float × Float × Float × Float × Float × Float) :=
  let style : Computed := {objectFit := fit}
  let style := if position.isEmpty then style else (CSS.applyDeclaration style "object-position" position).getD style
  (pictureNodes 1 style picture 0 0 w h).filterMap fun
    | .paint ⟨_,{geometry := .rect x y pw ph,style := {fill := .image r,..},..}⟩ => some (x,y,pw,ph,r.map.a,r.map.e)
    | _ => none
#guard painted .fill 80 40 == [(0,0,80,40,0.5,0)]
-- contain: the image is 80 by 40 in an 80 by 80 box, centred.
#guard painted .contain 80 80 == [(0,20,80,40,0.5,0)]
-- cover: 160 by 80, cut to the box.
#guard painted .cover 80 80 == [(0,0,80,80,0.25,10)]
#guard painted .fill 0 10 == []
#guard painted .contain 80 80 "50% 75%" == [(0,30,80,40,0.5,0)]
#guard painted .contain 80 80 "center bottom" == [(0,40,80,40,0.5,0)]
#guard painted .cover 80 80 "right center" == [(0,0,80,80,0.25,20)]

-- In flow. Inline: the bottom margin edge on the baseline of the line.
#guard boxes "<div><img id='i' src='a.png'></div>" == .ok [("i",0,0,40,20)]
-- The width attribute, with the ratio (HTML §15.4.3).
#guard boxes "<div><img id='i' src='a.png' width='80'></div>" == .ok [("i",0,0,80,40)]
-- Author CSS wins over the attribute.
#guard boxes "<div><img id='i' src='a.png' width='80' style='width:20px'></div>" == .ok [("i",0,0,20,10)]
-- In text: after "AB " (3 advances of 6), on a line as tall as the image.
#guard (boxes "<div>AB <img id='i' src='a.png'> C</div>").map (·.head?) == .ok (some ("i",18,0,40,20))
-- max-width: 100% in a narrow container.
#guard boxes "<div style='width:30px'><img id='i' src='a.png' style='max-width:100%'></div>" == .ok [("i",0,0,30,15)]
-- Block: its own line, with its margins. They adjoin the margins of the `div`, which has
-- no border or padding, and collapse with them (CSS 2.1 §8.3.1): the `div` is the image's box.
#guard boxes "<div id='d'><img id='i' src='a.png' style='display:block;margin:5px'></div>" == .ok [("d",0,5,200,20),("i",5,5,40,20)]
-- A border on the `div` keeps the margins inside it.
#guard boxes "<div id='d' style='border:1px solid black'><img id='i' src='a.png' style='display:block;margin:5px'></div>" == .ok [("d",0,0,200,32),("i",6,6,40,20)]
-- Border and padding grow the box; the image keeps its size.
#guard boxes "<div><img id='i' src='a.png' style='border:2px solid red;padding:3px'></div>" == .ok [("i",0,0,50,30)]
-- vertical-align: middle centres the image half an x-height above the baseline.
#guard (boxes "<div>A<img id='i' src='a.png' style='vertical-align:middle'></div>").map (·.head?) == .ok (some ("i",6,0,40,20))
-- An image's paint is one image rectangle.
#guard (render "<img src='a.png'>" "").map (fun r => (r.1.tree.flatMap (fun n => n.lower identity [])).length) == .ok 1
-- Missing: the alt text in brackets, nothing for alt="", [image] with no alt.
private def text (html : String) : Except String (List String) :=
  (render html "").map fun r => r.1.glyphRuns.toList.map (·.text)
#guard text "<img src='b.png' alt='A cat'>" == .ok ["[A","cat]"]
#guard text "<img src='b.png' alt=''>" == .ok []
#guard text "<img src='b.png'>" == .ok ["[image]"]
#guard text "<img src='b.png' alt='Gone' style='display:block'>" == .ok ["[Gone]"]
-- Measured in a table: the image's width.
#guard (boxes "<table style='border-spacing:0'><tr><td id='c' style='padding:0'><img src='a.png'></td></tr></table>").map (·.head?.map (·.2.2.2.1)) == .ok (some 40)

-- A picture whose `width` is a percentage is compressible (CSS Sizing 3 §5.2.2): inside a grid
-- item its min-content contribution is 0, so `1fr 1fr` columns stay equal (30 and 30 in 60)
-- and the picture fills its column; with its natural 40 px the first column took 40.
private def gridHtml (img : String) : String :=
  s!"<div style='display:grid;grid-template-columns:1fr 1fr;width:60px'><div id='a'>{img}</div><div id='b'>x</div></div>"
private def across (html : String) : Except String (List (String × Float × Float)) :=
  (boxes html).map (·.filterMap fun (id,x,_,w,_) => if id == "a" then none else some (id,x,w))
#guard across (gridHtml "<img id='i' src='a.png' style='width:100%'>") == .ok [("i",0,30),("b",30,30)]
#guard across (gridHtml "<img id='i' src='a.png' style='max-width:100%'>") == .ok [("i",0,30),("b",30,30)]
-- A px width is not compressible: the first column takes the picture's 40 px.
#guard across (gridHtml "<img id='i' src='a.png' style='width:40px'>") == .ok [("i",0,40),("b",40,20)]
-- A `min-width` that is a length is the least the picture asks.
#guard across (gridHtml "<img id='i' src='a.png' style='width:100%;min-width:36px'>") == .ok [("i",0,36),("b",36,24)]
-- In the max-content width the picture keeps its natural size.
#guard (boxes "<div id='f' style='float:left'><img src='a.png' style='width:100%'></div>").map (·.head?.map (·.2.2.2.1)) == .ok (some 40)

-- A `linear-gradient()` background: its line through the box's centre, as long as the box's
-- extent along it; `to right` across the width, the default down the height.
private def lineOf (g : String) (w h : Float) : Option (Float × Float × Float × Float × List Float) := do
  let bg ← (CSS.parseLinearGradient g).toOption
  match Layout.gradientPaint bg 0 0 w h with
  | .gradient p => match p.shape with
    | .linear a b c d => some (a,b,c,d,p.stops.map (·.offset))
    | _ => none
  | _ => none
#guard lineOf "to right,red,blue" 100 20 == some (0,10,100,10,[0,1])
#guard lineOf "red,white,blue 75%" 100 20 == some (50,0,50,20,[0,0.375,0.75])
-- A box with a gradient background paints two rectangles when it has a colour too: the colour,
-- then the image over it.
private def paints (html : String) : Option Nat :=
  ((render html "").toOption.map fun r => (r.1.tree.flatMap (·.lower identity [])).length)
#guard paints "<div style='width:100px;height:20px;background:#eee linear-gradient(red,blue)'></div>" == some 2
#guard paints "<div style='width:100px;height:20px;background:#eee'></div>" == some 1
#guard Layout.stopOffsets 200 [some (0.25,true),none,some (100,false)] == [0.25,0.375,0.5]
#guard Layout.stopOffsets 100 [some (0.5,true),some (0.2,true)] == [0.5,0.5]

-- Multi-column containers (CSS Multi-column Layout 1): balanced columns, cut between children.
#guard Layout.columnPlan (some 2) none 10 110 == some (2,50)
#guard Layout.columnPlan none (some 40) 10 110 == some (2,50)
#guard Layout.columnPlan none (some 200) 10 110 == none
#guard Layout.columnPlan (some 3) (some 40) 10 110 == some (2,50)
#guard Layout.columnStarts #[(0,10),(10,20),(20,30)] 20 == #[0,20]
#guard Layout.columnFirsts #[(0,10),(10,20),(20,30)] 20 == #[2]
#guard Layout.columnFirsts #[(0,10),(10,20),(20,30)] 9 == #[1,2]
#guard (Layout.balancedHeight #[(0,10),(10,20),(20,30)] 30 2 - 20).abs < 1/32
#guard Layout.balancedHeight #[(0,10),(10,20),(20,30),(30,40)] 40 2 == 20
private def cols (extra : String) : Except String (List (String × Float × Float × Float × Float)) :=
  boxes ("<div id='m' style='column-count:2;column-gap:10px;width:110px" ++ extra ++ "'>" ++
    "<p id='a' style='margin:0;height:20px'></p><p id='b' style='margin:0;height:20px'></p><p id='c' style='margin:0;height:10px'></p></div>")
#guard cols "" == .ok [("m",0,0,110,30),("a",0,0,50,20),("b",60,0,50,20),("c",60,20,50,10)]
-- `columns` gives both; one column is no multi-column box.
#guard cols ";column-count:auto;columns:40px 4" == .ok [("m",0,0,110,30),("a",0,0,50,20),("b",60,0,50,20),("c",60,20,50,10)]
#guard cols ";column-count:1" == .ok [("m",0,0,110,50),("a",0,0,110,20),("b",0,20,110,20),("c",0,40,110,10)]

-- `pre` keeps spaces and tabs (CSS Text 3 §4.1.1): the glyph x of each word.
private def wordsAt (html : String) : Except String (List (String × Float)) :=
  (render html "").map fun r => r.1.glyphRuns.toList.map fun run => (run.text,(run.glyphs[0]?.map (·.x)).getD 0)
#guard wordsAt "<pre>a  b</pre>" == .ok [("a",0),("b",18)]
#guard wordsAt "<pre>a\tb</pre>" == .ok [("a",0),("b",48)]
#guard wordsAt "<p>a  b</p>" == .ok [("a",0),("b",12)]
-- CSS Text 3 §8.1 to §8.3: letter-spacing after each character (the space too), word-spacing on
-- each separator, text-indent on the first line only (a percentage of the line's room).
#guard wordsAt "<p style='letter-spacing:10px'>a b</p>" == .ok [("a",0),("b",32)]
#guard wordsAt "<p style='word-spacing:5px'>a b</p>" == .ok [("a",0),("b",17)]
-- a percentage inherits as a percentage, of the font size where it is used; an em value
-- inherits as px (CSS Text 4 §8.1). The test face's default size is 7 px.
#guard wordsAt "<div style='font-size:32px;letter-spacing:62.5%'><p style='font-size:16px'>a b</p></div>"
  == wordsAt "<p style='font-size:16px;letter-spacing:10px'>a b</p>"
#guard wordsAt "<div style='font-size:32px;letter-spacing:0.3125em'><p style='font-size:16px'>a b</p></div>"
  == wordsAt "<p style='font-size:16px;letter-spacing:10px'>a b</p>"
#guard wordsAt "<div style='letter-spacing:10px'><p>a b</p></div>" == .ok [("a",0),("b",32)]
#guard wordsAt "<p style='letter-spacing:calc(5px + 31.25%)'>a b</p>" == .ok [("a",0),("b",26.375)]
#guard wordsAt "<p style='text-indent:7px'>a b</p>" == .ok [("a",7),("b",19)]
#guard wordsAt "<div style='text-indent:7px'><p>a b</p></div>" == .ok [("a",7),("b",19)]
#guard wordsAt "<p style='text-indent:7px'>a<br>b</p>" == .ok [("a",7),("b",0)]
-- And does not wrap.
#guard (render "<pre>aaaa bbbb</pre>" "pre{width:30px}").map (·.1.glyphRuns.toList.map (fun r => (r.glyphs[0]?.map (·.y)).getD 0)) == .ok [7,7]

-- CSS 2.1 §14.2: the body background fills the canvas, not the body's box.
private def firstFill (html extra : String) : Except String (Option (Float × Float × Float × Float)) :=
  (render html extra).map fun r => match r.1.tree.head? with
    | some (.paint ⟨_,{geometry := .rect x y w h,style := {fill := .solid _,..},..}⟩) => some (x,y,w,h)
    | _ => none
#guard firstFill "<p>A</p>" "body{background:red;margin:8px}" == .ok (some (0,0,200,100))
#guard firstFill "<p>A</p>" "html{background:blue}body{background:red}" == .ok (some (0,0,200,100))
-- The body then paints no background of its own: one rectangle, then the glyph.
#guard (render "<p>A</p>" "body{background:red}").map (·.1.tree.length) == .ok 2

-- An inline element's background is drawn behind its text: one rectangle for its box on
-- the line, under the two glyphs.
#guard (render "<p><span style='background:red'>A B</span></p>" "").map (fun r =>
  (r.1.tree.flatMap (fun n => n.lower identity [])).length) == .ok 3

-- A margin on inline SVG moves it; it no longer refuses the page.
#guard (boxes "<div><svg id='s' width='10' height='10' style='margin:4px'></svg></div>").map (·.head?) == .ok (some ("s",4,4,10,10))

-- `content: url(...)` (CSS Content 3 §2.1, CSS 2.1 §12.2, issue 874): the image is a replaced
-- box of its natural size (40 by 20 here) in the pseudo-element, between the texts beside it.
-- `Generated.fill` adds the image as a node `Generated.imageName` after the pseudo-element's
-- own two nodes; the picture is given for it by node number, as the engine does after the
-- cascade (`WebDocument.generatedImages`).
private def generated (html extra : String) (imageNode : Nat) : Except String (Scene × Array Box) := do
  let dom := DOM.parseHtmlDocument html
  Layout.render dom (← CSS.parse (css ++ extra)) font noSVG 200 100 1 {} fun id =>
    if id == dom.size + imageNode then some picture else none
private def generatedWords (html extra : String) (imageNode : Nat := 2) : Except String (List (String × Float)) :=
  (generated html extra imageNode).map fun r => r.1.glyphRuns.toList.map fun run => (run.text,(run.glyphs[0]?.map (·.x)).getD 0)
private def generatedBox (html extra : String) (imageNode : Nat := 2) :
    Except String (Option (Float × Float × Float × Float)) := do
  let dom := DOM.parseHtmlDocument html
  let (_,found) ← Layout.render dom (← CSS.parse (css ++ extra)) font noSVG 200 100 1 {} fun id =>
    if id == dom.size + imageNode then some picture else none
  return found.toList.findSome? fun b =>
    if CSS.attrValue (dom.get b.source) "id" == "a" then some (b.x,b.y,b.width,b.height) else none
private def beside := "<p id=a>AA</p>"
-- the image takes its 40 px, and the text starts after it
#guard generatedWords beside "#a::before{content:url(a.png)}" == .ok [("AA",40)]
-- after: the text first
#guard generatedWords beside "#a::after{content:url(a.png)}" == .ok [("AA",0)]
-- the line is as high as the image (it stands on the baseline); the 7 px is the paragraph's margin
#guard generatedBox beside "#a::before{content:url(a.png)}" == .ok (some (0,7,200,20))
-- no picture (the host did not give the image, or it did not decode): nothing is drawn, and the
-- text is where it is with no pseudo-element (CSS 2.1 §12.2)
#guard generatedWords beside "#a::before{content:url(a.png)}" (imageNode := 9) == .ok [("AA",0)]
#guard generatedBox beside "#a::before{content:url(a.png)}" (imageNode := 9) == .ok (some (0,7,200,7))
-- a string, the image, a string: "x" first, the image next, "y" last (the image is the third
-- node added; the second text is the fourth)
#guard generatedWords beside "#a::before{content:'x' url(a.png) 'y'}" == .ok [("x",0),("y",46),("AA",52)]
-- the image is as large as its natural size, and `width` and `height` of the pseudo-element
-- do not resize an inline box (CSS 2.1 §10.3.1): the same
#guard generatedWords beside "#a::before{content:url(a.png);width:100px}" == .ok [("AA",40)]
-- two images
#guard generatedWords beside "#a::before{content:url(a.png) url(a.png)}" == .ok [("AA",40)]
-- a counter beside an image
#guard generatedWords beside "#a::before{content:'1' url(a.png)}" == .ok [("1",0),("AA",46)]

/-! `border-image` (CSS Backgrounds 3 §6, https://github.com/danbri/factoidal-core/issues/874):
a 6 by 6 picture, 100 by 60 border boxes. The paint records are `(x,y,w,h,map.a,map.d)`. -/
private def borderPicture : Bitmap := ⟨6,6,ByteArray.mk (Array.replicate (6*6*4) 255)⟩
private def boxStyle (bi : BorderImage) (widths : Edges := ⟨10,10,10,10⟩) : Computed :=
  {borderStyles := .all .solid, borderWidth := widths, borderImage := {bi with bitmap := some (7,borderPicture)}}
private def partsOf (s : Computed) : Option (List (Float × Float × Float × Float × Float × Float)) :=
  (borderImageNodes 1 s 0 0 100 60).map fun nodes => nodes.toList.filterMap fun
    | Node.paint ⟨_,painted⟩ =>
      match painted.geometry, painted.style.fill with
      | .rect x y w h, .image r => some (x,y,w,h,r.map.a,r.map.d)
      | _, _ => none
    | _ => none
private def near (a b : Float) : Bool := (a-b).abs < 0.000001
private def sameParts (a b : List (Float × Float × Float × Float × Float × Float)) : Bool :=
  a.length == b.length && (a.zip b).all fun ((a0,a1,a2,a3,a4,a5),(b0,b1,b2,b3,b4,b5)) =>
    near a0 b0 && near a1 b1 && near a2 b2 && near a3 b3 && near a4 b4 && near a5 b5
-- slice 2 on a 6 pixel picture, width 1 (the border is 10 wide): eight parts, the middle only with `fill`
private def sliced : BorderImage := {slice := .all (.number 2)}
#guard (partsOf (boxStyle sliced)).map List.length == some 8
#guard (partsOf (boxStyle {sliced with fill := true})).map List.length == some 9
-- the corners are stretched from 2 to 10 px (0.2 picture px per px); the top edge from 2 to 80
#guard (partsOf (boxStyle sliced)).map (fun ps => sameParts (ps.take 1) [(0,0,10,10,0.2,0.2)]) == some true
#guard (partsOf (boxStyle sliced)).map (fun ps => sameParts (ps.drop 4 |>.take 1) [(10,0,80,10,0.025,0.2)]) == some true
-- the fill covers the inside of the border
#guard (partsOf (boxStyle {sliced with fill := true})).map (fun ps => sameParts (ps.drop 8) [(10,10,80,40,0.025,0.05)]) == some true
-- each part draws its own slice: the top left corner gets the 2 by 2 slice, the top edge the 2 by
-- 2 slice next to it, each with its own paint-table id
private def partImages (s : Computed) : List ImageRecord :=
  ((borderImageNodes 1 s 0 0 100 60).getD #[]).toList.filterMap fun
    | Node.paint ⟨_,painted⟩ => match painted.style.fill with | .image r => some r | _ => none
    | _ => none
#guard (partImages (boxStyle sliced)).map (fun r => (r.bitmap.width,r.bitmap.height)) ==
  [(2,2),(2,2),(2,2),(2,2),(2,2),(2,2),(2,2),(2,2)]
#guard (partImages (boxStyle sliced)).map (·.id) == [0,1,2,3,4,5,6,7].map (borderSliceIdBase+7*9+·)
-- a picture whose two left columns are red and the rest blue: the right edge of the top left
-- corner shows red only (before 2026-11-25 it mixed in the blue of the top edge's slice)
private def twoColour : Bitmap := ⟨6,6,ByteArray.mk <| Id.run do
  let mut out : Array UInt8 := #[]
  for _ in [0:6] do
    for i in [0:6] do
      out := out ++ (if i < 2 then #[255,0,0,255] else #[0,0,255,255])
  return out⟩
#guard match partImages {boxStyle sliced with borderImage := {sliced with bitmap := some (7,twoColour)}} with
  | corner :: _ => match corner.colorAt 9.9 5 with
    | [r,g,b,a] => near r 1 && near g 0 && near b 0 && near a 1
    | _ => false
  | [] => false
-- no decoded image, no border style: the border style is drawn
#guard (borderImageNodes 1 {borderStyles := .all .solid,borderWidth := ⟨10,10,10,10⟩} 0 0 100 60).isNone
#guard (borderImageNodes 1 {borderImage := {bitmap := some (7,borderPicture)}} 0 0 100 60).isNone
-- the image replaces the border style: the same `borderPaint` is the image's nodes
#guard (borderPaint 1 (boxStyle sliced) 0 0 100 60).size == 8
#guard (borderPaint 1 {borderStyles := .all .solid,borderWidth := ⟨10,10,10,10⟩} 0 0 100 60).size ==
  (borderNodes 1 {borderStyles := .all .solid,borderWidth := ⟨10,10,10,10⟩} 0 0 100 60).size
-- jvns.ca: `0 35 0 0 repeat`, here slice 4 of 6 on the right only, a 4 px right border: the right
-- edge is the picture's last 4 columns, tiled down the side at 4 px wide and 6 px high: 60/6 = 10 tiles
#guard (partsOf (boxStyle {slice := ⟨.number 0,.number 4,.number 0,.number 0⟩,repeatX := .tile,repeatY := .tile} ⟨0,4,0,0⟩)).map
  (fun ps => (ps.length, ps.all fun (x,_,w,h,_,_) => near x 96 && near w 4 && near h 6)) == some (10, true)
-- `border-image-width` as a length and `outset` move and resize the parts
#guard (partsOf (boxStyle {sliced with width := .all (.length 5)})).map (fun ps => sameParts (ps.take 1) [(0,0,5,5,0.4,0.4)]) == some true
#guard (partsOf (boxStyle {sliced with outset := .all (.length 3)})).map (fun ps => sameParts (ps.take 1) [(-3,-3,10,10,0.2,0.2)]) == some true
-- widths that together exceed the box are reduced by one factor: 80 + 80 > 100 reduces 80 to 50
#guard (partsOf (boxStyle {sliced with width := .all (.length 80)})).map (fun ps => sameParts (ps.take 1) [(0,0,30,30,2/30,2/30)]) == some true
-- the tiles of one edge, CSS Backgrounds 3 §6.6
#guard (borderImageTiles .stretch 10 80 99).size == 1
#guard (borderImageTiles .round 0 70 30).size == 2 && near (borderImageTiles .round 0 70 30)[1]!.1 35
#guard (borderImageTiles .space 0 100 30).size == 3 && near (borderImageTiles .space 0 100 30)[0]!.1 2.5
#guard (borderImageTiles .space 0 20 30).isEmpty
-- repeat: centred, the end tiles cut: 70 px of 30 px tiles start at -10; the first shows 2/3 of its picture
#guard (borderImageTiles .tile 0 70 30).size == 3 && near (borderImageTiles .tile 0 70 30)[0]!.2.1 20 &&
  near (borderImageTiles .tile 0 70 30)[0]!.2.2.1 (1/3)
#guard (borderImageTiles .tile 0 70 35).size == 2

end L4Factoidal.Rendering.ReplacedTests

#print axioms L4Factoidal.Rendering.Layout.pictureOffset_default
#print axioms L4Factoidal.Rendering.Layout.pictureOffset_percent
