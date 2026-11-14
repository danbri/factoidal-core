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
private def reducedPicture : Picture := ⟨0,⟨20,10,ByteArray.mk (Array.replicate (20*10*4) 255)⟩,some (40,20)⟩
-- A picture held reduced has the size of its image, and is painted in the same rectangle with
-- a map that reaches half as many pixels on each side.
#guard reducedPicture.size == picture.size
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
private def painted (fit : ObjectFit) (w h : Float) : List (Float × Float × Float × Float × Float × Float) :=
  (pictureNodes 1 {objectFit := fit} picture 0 0 w h).filterMap fun
    | .paint ⟨_,{geometry := .rect x y pw ph,style := {fill := .image r,..},..}⟩ => some (x,y,pw,ph,r.map.a,r.map.e)
    | _ => none
#guard painted .fill 80 40 == [(0,0,80,40,0.5,0)]
-- contain: the image is 80 by 40 in an 80 by 80 box, centred.
#guard painted .contain 80 80 == [(0,20,80,40,0.5,0)]
-- cover: 160 by 80, cut to the box.
#guard painted .cover 80 80 == [(0,0,80,80,0.25,10)]
#guard painted .fill 0 10 == []

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

-- `pre` keeps spaces and tabs (CSS Text 3 §4.1.1): the glyph x of each word.
private def wordsAt (html : String) : Except String (List (String × Float)) :=
  (render html "").map fun r => r.1.glyphRuns.toList.map fun run => (run.text,(run.glyphs[0]?.map (·.x)).getD 0)
#guard wordsAt "<pre>a  b</pre>" == .ok [("a",0),("b",18)]
#guard wordsAt "<pre>a\tb</pre>" == .ok [("a",0),("b",48)]
#guard wordsAt "<p>a  b</p>" == .ok [("a",0),("b",12)]
-- And does not wrap.
#guard (render "<pre>aaaa bbbb</pre>" "pre{width:30px}").map (·.1.glyphRuns.toList.map (fun r => (r.glyphs[0]?.map (·.y)).getD 0)) == .ok [3.5,3.5]

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
end L4Factoidal.Rendering.ReplacedTests
