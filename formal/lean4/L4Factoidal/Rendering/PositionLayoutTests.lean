import L4Factoidal.Rendering.Layout

/-! Positioning and box sizing through `Layout.render`, on a monospace test face (6 px
advance, 7 px line). Original fixtures; expected numbers by CSS 2.1 §9.4.3, §10.1,
§10.3.7, §10.6.4 and CSS Sizing 3 §3.3, by hand. -/
namespace L4Factoidal.Rendering.PositionLayoutTests
open DOM CSS Layout
private def font : FontProfile :=
  {family := "layout-test-monospace",unitsPerEm := 7,advance := 6, ascent := 7,descent := 0,outline := fun _ => [.rect 0 0 5 7],admits := fun n => n >= 32 && n <= 126}
private def noSVG : Embedding := fun _ _ _ _ => throw "unsupported SVG test embedding"
private def css := "body{margin:0;font-size:7px;line-height:7px} "
private def render (html extra : String) (width : Nat := 200) : Except String (Scene × Array Box) := do
  let dom := DOM.parseHtmlDocument html
  Layout.render dom (← CSS.parse (css ++ extra)) font noSVG width 200
private def box (html extra id : String) (width : Nat := 200) : Option (Float × Float × Float × Float) := do
  let dom := DOM.parseHtmlDocument html
  let n ← dom.getElementById 0 id
  let (_,boxes) ← (render html extra width).toOption
  let b ← boxes.find? (·.source == n)
  return (b.x,b.y,b.width,b.height)
private def at? (html extra text : String) (width : Nat := 200) : Option (Float × Float) := do
  let (scene,_) ← (render html extra width).toOption
  let run ← scene.glyphRuns.find? (·.text == text)
  let g ← run.glyphs[0]?
  return (g.x,g.y)

private def page := "<div id=a>AA</div><div id=c><div id=p>PP</div><div id=q>Q</div></div><div id=z>ZZ</div>"

-- Relative: the box moves, the flow after it does not.
#guard box page "#a{position:relative;left:10px;top:3px}" "a" == some (10,3,200,7)
#guard box page "#a{position:relative;left:10px;top:3px}" "c" == some (0,7,200,14)
#guard at? page "#a{position:relative;left:10px;top:3px}" "AA" == some (10,3)
#guard box page "#a{position:relative;right:10px;bottom:3px}" "a" == some (-10,-3,200,7)
#guard box page "#a{position:relative;left:10%}" "a" == some (20,0,200,7)
-- A percentage `top` is of the containing block's height when that is definite, else auto.
#guard box page "#c{height:40px} #p{position:relative;top:50%}" "p" == some (0,27,200,7)
#guard box page "#c{height:40px} #p{position:relative;bottom:25%}" "p" == some (0,-3,200,7)
#guard box page "#p{position:relative;top:50%}" "p" == some (0,7,200,7)
-- Absolute: out of flow; the next sibling takes its place.
#guard box page "#p{position:absolute}" "q" == some (0,7,200,7)
#guard box page "#p{position:absolute}" "c" == some (0,7,200,7)
-- With no insets it stays at its static position, as wide as its content.
#guard box page "#p{position:absolute}" "p" == some (0,7,12,7)
#guard box page "#q{position:absolute}" "q" == some (0,14,6,7)
-- No positioned ancestor: the containing block is the viewport (200 by 200).
#guard box page "#p{position:absolute;top:5px;left:9px}" "p" == some (9,5,12,7)
#guard box page "#p{position:absolute;right:0;bottom:0}" "p" == some (188,193,12,7)
#guard box page "#p{position:absolute;left:10px;right:20px;top:10px;bottom:20px}" "p" == some (10,10,170,170)
-- A positioned ancestor: its padding box.
private def rel := "#c{position:relative;margin-left:20px;padding:5px;border:2px solid black;width:100px;height:40px} "
#guard box page rel "c" == some (20,7,114,54)
#guard box page (rel ++ "#p{position:absolute;top:0;left:0}") "p" == some (22,9,12,7)
#guard box page (rel ++ "#p{position:absolute;right:0;bottom:0}") "p" == some (120,52,12,7)
#guard box page (rel ++ "#p{position:absolute;top:10%;left:50%}") "p" == some (77,14,12,7)
#guard box page (rel ++ "#p{position:absolute;left:0;right:0;top:0;height:10px}") "p" == some (22,9,110,10)
#guard box page (rel ++ "#p{position:absolute;width:50%;height:50%;top:0;left:0}") "p" == some (22,9,55,25)
#guard at? page (rel ++ "#p{position:absolute;right:0;bottom:0}") "PP" == some (120,52)
-- Insets with a width and auto margins: centred.
#guard box page (rel ++ "#p{position:absolute;left:0;right:0;width:30px;margin-left:auto;margin-right:auto}") "p" == some (62,14,30,7)
#guard box page (rel ++ "#p{position:absolute;top:0;bottom:0;left:0;height:10px;margin-top:auto;margin-bottom:auto}") "p" == some (22,29,12,10)
-- Self-alignment between two insets (CSS Box Alignment 3 §6.1.2, §6.2.2): an aligned box is
-- as large as its content and goes to the start, centre or end of the room (110 by 50
-- here); auto margins take the free room first.
#guard box page (rel ++ "#p{position:absolute;inset:0;justify-self:center;align-self:end}") "p" == some (71,52,12,7)
#guard box page (rel ++ "#p{position:absolute;inset:0;justify-self:start}") "p" == some (22,9,12,50)
#guard box page (rel ++ "#p{position:absolute;inset:0;justify-self:end;align-self:center}") "p" == some (120,30.5,12,7)
#guard box page (rel ++ "#p{position:absolute;inset:0;margin:auto;width:fit-content;height:fit-content}") "p" == some (71,30.5,12,7)
#guard box page (rel ++ "#p{position:absolute;inset:0;margin:auto;align-self:start}") "p" == some (22,30.5,110,7)
#guard box page (rel ++ "#p{position:absolute;inset:0;margin:auto 0 0;align-self:start}") "p" == some (22,52,110,7)
-- Larger than the room: at the start.
#guard box page (rel ++ "#p{position:absolute;inset:0;width:200px;justify-self:center}") "p" == some (22,9,200,50)
-- Margins, padding and border of the box itself.
#guard box page (rel ++ "#p{position:absolute;top:0;left:0;margin:3px;padding:1px}") "p" == some (25,12,14,9)
-- The static position of a later child follows the flow.
#guard box page (rel ++ "#q{position:absolute}") "q" == some (27,21,6,7)
-- An absolute box in an absolute box.
#guard box "<div id=o><div id=i>I</div></div>" "#o{position:absolute;left:50px;top:20px;width:60px;height:30px} #i{position:absolute;right:0;bottom:0}" "i" == some (104,43,6,7)
-- Fixed: the viewport, even inside a positioned ancestor.
#guard box page (rel ++ "#p{position:fixed;top:1px;right:1px}") "p" == some (187,1,12,7)
-- Inside inline content: the static position is its place in the line.
#guard box "<div>ab <span id=s>S</span> cd</div>" "#s{position:absolute}" "s" == some (18,0,6,7)
#guard at? "<div>ab <span id=s>S</span>cd</div>" "#s{position:absolute}" "cd" == some (18,0)
-- A flex container: an absolute child is not an item.
#guard box "<div id=f><div id=a>AA</div><div id=p>P</div><div id=b>B</div></div>" "#f{display:flex;position:relative} #p{position:absolute;right:0;top:0}" "b" == some (12,0,6,7)
#guard box "<div id=f><div id=a>AA</div><div id=p>P</div><div id=b>B</div></div>" "#f{display:flex;position:relative} #p{position:absolute;right:0;top:0}" "p" == some (194,0,6,7)
-- The static position of an absolute child of a flex container: as the only item (free 194 by 43).
private def flexAbs := "<div id=f><div id=p>P</div></div>"
private def flexAbsCss := "#f{display:flex;position:relative;height:50px} #p{position:absolute} "
#guard box flexAbs flexAbsCss "p" == some (0,0,6,7)
#guard box flexAbs (flexAbsCss ++ "#f{justify-content:center}") "p" == some (97,0,6,7)
#guard box flexAbs (flexAbsCss ++ "#f{justify-content:flex-end;align-items:center}") "p" == some (194,21.5,6,7)
#guard box flexAbs (flexAbsCss ++ "#f{justify-content:space-around} #p{align-self:flex-end}") "p" == some (97,43,6,7)
#guard box flexAbs (flexAbsCss ++ "#f{flex-direction:column;justify-content:flex-end;align-items:center}") "p" == some (97,43,6,7)
#guard box flexAbs (flexAbsCss ++ "#f{flex-direction:row-reverse}") "p" == some (194,0,6,7)
-- An inset wins over the static position on its axis.
#guard box flexAbs (flexAbsCss ++ "#f{justify-content:center;align-items:center} #p{left:3px}") "p" == some (3,21.5,6,7)
-- inset.
#guard box page (rel ++ "#p{position:absolute;inset:1px 2px 3px 4px}") "p" == some (26,10,104,46)

-- box-sizing: border-box: width and height name the border box.
#guard box page "#a{box-sizing:border-box;width:100px;height:30px;padding:5px;border:2px solid black}" "a" == some (0,0,100,30)
#guard box page "#a{width:100px;height:30px;padding:5px;border:2px solid black}" "a" == some (0,0,114,44)
#guard box page "#a{box-sizing:border-box;width:50%;padding:5px}" "a" == some (0,0,100,17)
#guard box page "#a{box-sizing:border-box;max-width:50px;padding:5px}" "a" == some (0,0,50,17)
#guard box page "#a{box-sizing:border-box;min-height:40px;padding:5px}" "a" == some (0,0,200,40)
#guard box "<div id=f><div id=a>AA</div><div id=b>B</div></div>" "#f{display:flex} #f div{box-sizing:border-box;width:50%;padding:0 5px}" "b" == some (100,0,100,7)
-- calc(): a percentage plus a length.
#guard box page "#a{width:calc(100% - 30px)}" "a" == some (0,0,170,7)
#guard box page "#a{width:calc(50% + 10px)}" "a" == some (0,0,110,7)

-- CSS 2.1 §10.5: a percentage height is of a containing block with a definite height;
-- of one whose height is its content's it is `auto`.
#guard box page "#c{height:40px} #p{height:50%}" "p" == some (0,7,200,20)
#guard box page "#c{height:40px} #p{height:50%}" "q" == some (0,27,200,7)
#guard box page "#p{height:50%}" "p" == some (0,7,200,7)
#guard box page "#c{height:40px} #p{height:calc(50% + 5px)}" "p" == some (0,7,200,25)
#guard box page "#c{height:40px} #p{box-sizing:border-box;height:50%;padding:2px}" "p" == some (0,7,200,20)
#guard box "<div id=o><div id=m><div id=i>I</div></div></div>" "#o{height:80px} #m{height:50%} #i{height:25%}" "i" == some (0,0,200,10)

-- A percentage height inside a box whose height layout made definite: a flex item stretched
-- to its container's height, and an absolutely positioned box between two insets.
private def tall := "<div id=f><div id=i><div id=k>K</div></div></div>"
#guard box tall "#f{display:flex;height:60px} #k{height:50%}" "k" == some (0,0,6,30)
#guard box tall "#f{display:flex;height:60px} #i{padding:5px 0} #k{height:100%}" "k" == some (0,5,6,50)
#guard box tall "#f{display:flex;height:60px;align-items:flex-start} #k{height:50%}" "k" == some (0,0,6,7)
#guard box tall "#f{display:flex} #k{height:50%}" "k" == some (0,0,6,7)
#guard box tall "#f{position:relative;height:80px} #i{position:absolute;top:10px;bottom:10px} #k{height:50%}" "k" == some (0,10,6,30)
-- aspect-ratio (CSS Sizing 4 §5.1): with `height: auto` the height is the width's by the ratio.
#guard box page "#a{aspect-ratio:2;width:100px}" "a" == some (0,0,100,50)
#guard box page "#a{aspect-ratio:2;width:100px}" "c" == some (0,50,200,14)
#guard box page "#a{aspect-ratio:2/1}" "a" == some (0,0,200,100)
#guard box page "#a{aspect-ratio:1/2;width:10px}" "a" == some (0,0,10,20)
-- A height that is given wins; content taller than the ratio's height shows (§5.2), unless the box clips.
#guard box page "#a{aspect-ratio:2;width:100px;height:10px}" "a" == some (0,0,100,10)
#guard box page "#a{aspect-ratio:100;width:100px}" "a" == some (0,0,100,7)
#guard box page "#a{aspect-ratio:100;width:100px;overflow:hidden}" "a" == some (0,0,100,1)
-- The ratio is of the content box, or of the border box with `box-sizing: border-box`.
#guard box page "#a{aspect-ratio:2;width:100px;padding:5px}" "a" == some (0,0,110,60)
#guard box page "#a{aspect-ratio:2;width:100px;box-sizing:border-box;padding:5px}" "a" == some (0,0,100,50)
#guard box page "#p{position:absolute;aspect-ratio:2;width:40px}" "p" == some (0,7,40,20)
-- A canvas is a replaced box of its natural size: its attributes, or 300 by 150.
private def drawing := "<div id=o><canvas id=k width=15 height=15>no canvas</canvas></div><div id=z>Z</div>"
#guard box drawing "" "k" == some (0,0,15,15)
#guard box drawing "" "z" == some (0,15,200,7)
#guard box "<canvas id=k></canvas>" "#k{display:block}" "k" == some (0,0,300,150)
-- With `aspect-ratio` and auto sizes: the natural width, the height by the ratio, within
-- the limits of both axes (the cases of WPT css-sizing/aspect-ratio/replaced-element-043).
private def ratioCss := "#k{display:block;width:auto;height:auto;aspect-ratio:2;"
#guard box drawing (ratioCss ++ "}") "k" == some (0,0,15,7.5)
#guard box drawing (ratioCss ++ "width:40px}") "k" == some (0,0,40,20)
#guard box drawing (ratioCss ++ "height:25px}") "k" == some (0,0,50,25)
#guard box drawing (ratioCss ++ "min-height:10px}") "k" == some (0,0,20,10)
#guard box drawing (ratioCss ++ "max-width:10px}") "k" == some (0,0,10,5)
#guard box drawing (ratioCss ++ "min-width:20px;max-height:5px}") "k" == some (0,0,20,5)
#guard box drawing (ratioCss ++ "max-width:10px;min-height:10px}") "k" == some (0,0,10,10)

-- Sizing keywords (CSS Sizing 3 §3.2): widths taken from the contents ("AA BBB": the
-- longest word is 18 wide, the whole line 36), or the width that fills the containing block.
private def words := "<div id=w>AA BBB</div><div id=z>Z</div>"
#guard box words "#w{width:min-content}" "w" == some (0,0,18,14)
#guard box words "#w{width:max-content}" "w" == some (0,0,36,7)
#guard box words "#w{width:fit-content}" "w" == some (0,0,36,7)
#guard box words "#w{width:fit-content}" "w" (width := 30) == some (0,0,30,14)
#guard box words "#w{width:fit-content}" "w" (width := 10) == some (0,0,18,14)
#guard box words "#w{width:fit-content;margin:0 auto}" "w" == some (82,0,36,7)
#guard box words "#w{width:stretch;margin:0 5px}" "w" == some (5,0,190,7)
#guard box words "#w{width:-webkit-fill-available;padding:0 5px}" "w" == some (0,0,200,7)
#guard box words "#w{width:10px;min-width:min-content}" "w" == some (0,0,18,14)
#guard box words "#w{max-width:max-content}" "w" == some (0,0,36,7)
#guard box words "#w{width:max-content;padding:0 2px;border:1px solid black}" "w" == some (0,0,42,9)
-- On a float and on an absolutely positioned box.
#guard box words "#w{float:left;width:min-content}" "w" == some (0,0,18,14)
#guard box words "#w{float:left;width:max-content}" "w" (width := 20) == some (0,0,36,7)
#guard box words "#w{position:absolute;left:0;right:0;width:max-content}" "w" == some (0,0,36,7)
#guard box words "#w{position:absolute;left:0;right:0}" "w" == some (0,0,200,7)
-- `height: stretch` fills a definite containing height; the other keywords are the content height.
#guard box page "#c{height:40px} #p{height:stretch;border:1px solid black}" "p" == some (0,7,200,40)
#guard box page "#p{height:stretch}" "p" == some (0,7,200,7)
#guard box page "#c{height:40px} #p{height:min-content}" "p" == some (0,7,200,7)

-- scrollWidth and scrollHeight (CSSOM View §6.1): the padding box extended to the boxes inside.
private def scroll (html extra id : String) : Option (Float × Float) := do
  let dom := DOM.parseHtmlDocument html
  let n ← dom.getElementById 0 id
  let (_,boxes) ← (render html extra).toOption
  Layout.scrollSize dom boxes {} 200 200 n
#guard scroll page "" "c" == some (200,14)
#guard scroll page "#c{height:10px;width:50px}" "c" == some (50,14)
#guard scroll page "#c{height:10px;width:50px} #q{width:80px}" "c" == some (80,14)
#guard scroll page "#c{height:10px} #p{position:relative;top:-100px}" "c" == some (200,14)
-- The root element scrolls the viewport (200 by 200 here) over the whole page.
#guard scroll "<html id=h><body><div id=a>AA</div></body></html>" "" "h" == some (200,200)
#guard scroll "<html id=h><body><div id=a>AA</div></body></html>" "#a{height:500px}" "h" == some (200,500)

-- List markers (CSS Lists 3 §3): outside the item's box by default, half an em before its
-- content edge (the list's 40px of padding leaves the room); the item's text is at the edge.
private def listed := "<ul id=u><li id=i>AA</li><li id=j>BB</li></ul>"
private def xOf (html extra text : String) : Option Float := (at? html extra text).map (·.1)
#guard xOf listed "" "AA" == some 40
#guard xOf listed "" "*" == some 30.5
#guard box listed "" "i" == (box listed "ul{list-style:none}" "i")
-- `list-style-type: none` (also through `list-style`, and inherited) draws no marker.
#guard xOf listed "ul{list-style-type:none}" "*" == none
#guard xOf listed "ul{list-style:none}" "*" == none
#guard xOf ("<div id=g>" ++ listed ++ "</div>") "#g{list-style:none}" "*" == none
#guard xOf listed "ul{list-style:none} #j{list-style-type:disc}" "*" == some 30.5
-- A numbering style numbers the items, as an `ol` does by default.
#guard xOf listed "ul{list-style-type:decimal}" "2." == some 24.5
#guard xOf "<ol><li>AA</li><li>BB</li></ol>" "" "2." == some 24.5
#guard xOf "<ol><li>AA</li><li>BB</li></ol>" "ol{list-style-type:square}" "2." == none
-- `list-style-position: inside`: the marker is the first thing in the line.
#guard xOf listed "ul{list-style-position:inside}" "*" == some 40
#guard xOf listed "ul{list-style-position:inside}" "AA" == some 52
#guard xOf listed "ul{list-style:inside none}" "AA" == some 40
-- The bullet is U+2022 (U+25E6 and U+25AA in nested lists, or by `list-style-type`) in a
-- font that has it; the test face has ASCII only, so the fixtures above see a star.
private def round : FontProfile := {font with admits := fun n => (n >= 32 && n <= 126) || n == 0x2022 || n == 0x25E6 || n == 0x25AA}
private def markers (html extra : String) : Option (List String) := do
  let (scene,_) ← (Layout.render (DOM.parseHtmlDocument html) (← (CSS.parse (css ++ extra)).toOption) round noSVG 200 200).toOption
  pure ((scene.glyphRuns.toList.map (·.text)).filter fun t => t != "A")
#guard markers "<ul><li>A<ul><li>A<ul><li>A</li></ul></li></ul></li></ul>" "" == some ["•","◦","▪"]
#guard markers "<ul><li>A</li></ul>" "ul{list-style-type:square}" == some ["▪"]
#guard markers "<ol><li>A</li></ol>" "ol{list-style:circle}" == some ["◦"]
#guard markers "<ul><li>A</li></ul>" "ul{list-style:none}" == some []
-- An item with nothing in it is still one line high.
#guard (box "<ul><li id=e></li></ul>" "" "e").map (·.2.2.2) == some 7

-- Margin collapse (CSS 2.1 §8.3.1): adjoining margins of siblings; the larger stands.
private def stack := "<div id=a>A</div>\n<div id=b>B</div><div id=c><div id=d>D</div></div><div id=e>E</div>"
#guard box stack "#a{margin-bottom:10px} #b{margin-top:4px}" "b" == some (0,17,200,7)
#guard box stack "#a{margin-bottom:4px} #b{margin-top:10px}" "b" == some (0,17,200,7)
-- A first child's top margin sticks out of a parent with no border or padding...
#guard box stack "#d{margin-top:10px}" "c" == some (0,24,200,7)
#guard box stack "#d{margin-top:10px}" "d" == some (0,24,200,7)
#guard box stack "#b{margin-bottom:6px} #c{margin-top:3px} #d{margin-top:10px}" "d" == some (0,24,200,7)
-- ...and a last child's bottom margin likewise.
#guard box stack "#d{margin-bottom:10px}" "c" == some (0,14,200,7)
#guard box stack "#d{margin-bottom:10px}" "e" == some (0,31,200,7)
-- A border, padding, a height, `overflow: hidden` or a flex container keeps them in.
#guard box stack "#c{border-top:0;padding:1px} #d{margin-top:10px}" "d" == some (1,25,198,7)
#guard box stack "#c{overflow:hidden} #d{margin:10px 0}" "c" == some (0,14,200,27)
#guard box stack "#c{display:flex;flex-direction:column} #d{margin:10px 0}" "c" == some (0,14,200,27)
#guard box stack "#c{height:20px} #d{margin-bottom:10px}" "e" == some (0,34,200,7)
-- Text between two blocks keeps their margins apart.
#guard box "<div id=a>A</div>x<div id=b>B</div>" "#a{margin-bottom:10px} #b{margin-top:4px}" "b" == some (0,28,200,7)
-- The body's margin and its first child's collapse; the root's does not.
#guard box "<h1 id=h>H</h1>" "body{margin:8px} #h{margin:20px 0;font-size:7px}" "h" == some (8,20,184,7)

-- Floats (CSS 2.1 §9.5): out of flow, against the sides; lines go beside them, blocks under.
private def floated := "<div id=c><div id=f>F</div><div id=g>G</div><div id=t>TT</div></div><div id=n>N</div>"
private def floatCss := "#f{float:left;width:30px;height:20px} #g{float:right;width:40px;height:10px} "
#guard box floated floatCss "f" == some (0,0,30,20)
#guard box floated floatCss "g" == some (160,0,40,10)
#guard box floated floatCss "t" == some (0,0,200,7)
#guard at? floated floatCss "TT" == some (30,0)
-- A plain block does not hold its floats: they stay in the formatting context, and the
-- lines of the block after it are beside them too.
#guard box floated floatCss "c" == some (0,0,200,7)
#guard box floated floatCss "n" == some (0,7,200,7)
#guard at? floated floatCss "N" == some (30,7)
#guard box floated (floatCss ++ "#n{clear:both}") "n" == some (0,20,200,7)
-- §10.6.7: a box that is the root of a formatting context is as high as its floats.
#guard box floated (floatCss ++ "#c{overflow:hidden}") "c" == some (0,0,200,20)
#guard box floated (floatCss ++ "#c{overflow:hidden}") "n" == some (0,20,200,7)
-- `display: flow-root` is such a root too, and keeps its children's margins inside.
#guard box floated (floatCss ++ "#c{display:flow-root}") "c" == some (0,0,200,20)
#guard box floated (floatCss ++ "#c{display:flow-root}") "n" == some (0,20,200,7)
#guard box floated (floatCss ++ "#c{display:flow-root} #c{display:block}") "c" == some (0,0,200,7)
#guard box "<div id=a>A</div><div id=c><div id=d>D</div></div>" "#c{display:flow-root} #d{margin-top:10px}" "c" == some (0,7,200,17)
-- Flex items do not float (CSS Flexbox 1 §3): the column is 20 + 10 + 7 high.
#guard box floated (floatCss ++ "#c{display:flex;flex-direction:column}") "n" == some (0,37,200,7)
-- A float in a paragraph: the next paragraph is beside it as well.
private def article := "<div id=p1><div id=f>F</div>AA</div><div id=p2>BB</div><div id=p3>CC</div>"
#guard at? article "#f{float:left;width:30px;height:10px}" "AA" == some (30,0)
#guard at? article "#f{float:left;width:30px;height:10px}" "BB" == some (30,7)
#guard at? article "#f{float:left;width:30px;height:10px}" "CC" == some (0,14)
#guard box article "#f{float:left;width:30px;height:10px}" "p2" == some (0,7,200,7)
-- A second float on the same side goes beside the first.
#guard box floated "#f{float:left;width:30px;height:20px} #g{float:left;width:40px;height:10px}" "g" == some (30,0,40,10)
-- With no room beside it, below.
#guard box floated "#f{float:left;width:150px;height:20px} #g{float:left;width:100px;height:10px}" "g" == some (0,20,100,10)
-- A float with no width is as wide as its content.
#guard box floated "#f{float:left}" "f" == some (0,0,6,7)
#guard box floated "#f{float:right}" "f" == some (194,0,6,7)
-- A box that shrinks to fit is as wide as its floats side by side (30 + 40), and a float
-- in it that clears starts a new row.
private def menu := "<div id=u><div id=f>F</div><div id=g>G</div></div>"
private def menuCss := "#u{float:left} #f{float:left;width:30px;height:20px} #g{float:left;width:40px;height:10px} "
#guard box menu menuCss "u" == some (0,0,70,20)
#guard box menu menuCss "g" == some (30,0,40,10)
#guard box menu (menuCss ++ "#g{clear:left}") "u" == some (0,0,40,30)
#guard box menu (menuCss ++ "#g{clear:left}") "g" == some (0,20,40,10)
-- §9.5.2 clear: below the floats of that side.
#guard box floated (floatCss ++ "#t{clear:left}") "t" == some (0,20,200,7)
#guard box floated (floatCss ++ "#t{clear:right}") "t" == some (0,10,200,7)
#guard box floated (floatCss ++ "#t{clear:both}") "t" == some (0,20,200,7)
-- A box with a formatting context of its own is beside the floats.
#guard box floated (floatCss ++ "#t{overflow:hidden}") "t" == some (30,0,130,7)

-- An inline-block with a block inside is a block container (CSS 2.1 §9.2.2).
private def inlineBlock := "<div id=o><span id=w><div id=d>AB</div></span></div>"
#guard box inlineBlock "#w{display:inline-block;width:50px} #d{width:20px;height:10px}" "d" == some (0,0,20,10)
#guard box inlineBlock "#w{display:inline-block;width:50px} #d{width:20px;height:10px}" "w" == some (0,0,50,10)
-- ...as wide as its content when it has no width.
#guard box inlineBlock "#w{display:inline-block} #d{width:20px;height:10px}" "w" == some (0,0,20,10)
-- vertical-align of an atomic box in its line (CSS 2.1 §10.8.1): the 30px box makes the
-- line 30 high; the 10px box is at its top, its bottom, its middle (the baseline plus a
-- quarter em, here 1.75), or with its bottom edge on the baseline.
private def twoBoxes := "<div id=o><span id=a class=b></span><span id=t class=b></span></div>"
private def twoCss := ".b{display:inline-block;width:10px} #a{height:30px} #t{height:10px;"
#guard box twoBoxes (twoCss ++ "}") "t" == some (10,20,10,10)
#guard box twoBoxes (twoCss ++ "vertical-align:top}") "t" == some (10,0,10,10)
#guard box twoBoxes (twoCss ++ "vertical-align:bottom}") "t" == some (10,20,10,10)
#guard box twoBoxes (twoCss ++ "vertical-align:middle}") "t" == some (10,23.25,10,10)
#guard box twoBoxes (twoCss ++ "vertical-align:top} #a{vertical-align:top}") "o" == some (0,0,200,30)
-- ...and of an inline-block with blocks inside, and an inline flex container.
#guard box "<div id=o><span id=a class=b></span><span id=t class=b><div id=k></div></span></div>" (twoCss ++ "vertical-align:top} #k{height:10px}") "t" == some (10,0,10,10)
#guard box twoBoxes (twoCss ++ "vertical-align:top;display:inline-flex}") "t" == some (10,0,10,10)
-- A positioned inline-block is the containing block of its absolute descendants: the box
-- is at the right of its padding box (10 wide), 4 from its left edge.
private def badge := "<div id=o>ab <span id=w>W<b id=p>P</b></span></div>"
private def badgeCss := "#w{display:inline-block;position:relative;padding:2px} #p{position:absolute;right:0;top:0}"
#guard (do let w ← box badge badgeCss "w"; let p ← box badge badgeCss "p"; pure (p.1-w.1,p.2.1-w.2.1,w.2.2.1,p.2.2)) == some (4,0,10,6,7)


-- Generated content (`Generated`, CSS 2.1 §12.1): `::before` is laid out as the first child
-- of its originating element and `::after` as the last, with the text of `content`.
private def gen := "<div id=a>AA</div><div id=b>BB</div>"
#guard at? gen "#a::before{content:'x'}" "x" == some (0,0)
#guard at? gen "#a::before{content:'x'}" "AA" == some (6,0)
#guard at? gen "#a:after{content:\"yz\"}" "yz" == some (12,0)
#guard at? gen "#a:AFTER{content:\"yz\"}" "yz" == some (12,0)
#guard at? gen "div#a::before{content:'x'} #b::before{content:'yy'}" "BB" == some (12,7)
-- as blocks: 10 px, the line, a line
#guard box gen "#a::before{content:'';display:block;height:10px} #a::after{content:'e';display:block}" "a" == some (0,0,200,24)
#guard at? gen "#a::before{content:'';display:block;height:10px} #a::after{content:'e';display:block}" "e" == some (0,17)
#guard box gen "#a::before{content:'';display:block;height:10px} #a::after{content:'e';display:block}" "b" == some (0,24,200,7)
-- the clearfix: a cleared block (or table) at the end holds the element's floats
private def clearfix := "<div id=a><div id=f style='float:left;height:30px;width:20px'></div>AA</div><div id=b>BB</div>"
#guard box clearfix "" "a" == some (0,0,200,7)
#guard box clearfix "#a::after{content:'';display:block;clear:both}" "a" == some (0,0,200,30)
#guard box clearfix "#a::after{content:'';display:block;clear:both}" "b" == some (0,30,200,7)
#guard box clearfix "#a:before,#a:after{content:' ';display:table} #a:after{clear:both}" "a" == some (0,0,200,30)
-- attr() reads the originating element
#guard at? "<div id=a title=Hi>AA</div>" "#a::before{content:attr(title) ': '}" "AA" == some (24,0)
#guard at? "<div id=a>AA</div>" "#a::before{content:attr(title) '.'}" "AA" == some (6,0)
-- no `content`, or `none`: no box
#guard box gen "#a::before{display:block;height:10px}" "b" == some (0,7,200,7)
#guard box gen "#a::before{content:none;display:block;height:10px}" "b" == some (0,7,200,7)
#guard box gen "#a::before{content:'';display:block;height:10px} #a::before{content:normal}" "b" == some (0,7,200,7)
#guard box gen "*,*::before,*::after{box-sizing:border-box}" "b" == some (0,7,200,7)
-- the cascade of the pseudo-element's own rules: order, specificity, importance
#guard at? "<div id=a class=c>AA</div>" ".c::before{content:'1'} #a::before{content:'22'}" "AA" == some (12,0)
#guard at? "<div id=a class=c>AA</div>" "#a::before{content:'22'} .c::before{content:'1'}" "AA" == some (12,0)
#guard at? "<div id=a class=c>AA</div>" "#a::before{content:'22'} .c::before{content:'1' !important}" "AA" == some (6,0)
#guard at? "<div id=a class=c>AA</div>" ".c::before{content:'1'} .c::before{content:'333'}" "AA" == some (18,0)
-- it inherits from its originating element, and the element's own rules are not its rules
#guard at? gen "#a{font-size:14px;line-height:14px} #a::before{content:'x'}" "AA" == some (12,0)
#guard at? gen "#a{margin-left:30px;padding-left:5px} #a::before{content:'x'}" "x" == some (35,0)
-- selectors see the page's tree: the pseudo-element is nobody's first child or sibling
#guard box "<div id=a><span id=s>S</span></div>" "#a::before{content:'';display:block;height:9px} #s:first-child{display:block;margin-left:12px}" "s" == some (12,9,188,7)
#guard box "<div id=a><span id=s>S</span></div>" "#a::before{content:'';display:block;height:9px} #a > *{display:block;margin-left:12px}" "s" == some (12,9,188,7)
#guard box "<div id=a></div><div id=b>BB</div>" "#a::before{content:'x'} #a:empty{height:20px}" "b" == some (0,20,200,7)
-- positioned in its originating element; an item of a flex container
#guard at? "<div id=a>AA</div>" "#a{position:relative;height:50px} #a::before{content:'x';position:absolute;left:10px;top:5px}" "x" == some (10,5)
#guard at? "<div id=a>AA</div>" "#a{display:flex} #a::before{content:'b'} #a::after{content:'c'}" "c" == some (18,0)
#guard at? "<div id=a>AA</div>" "#a{display:flex;justify-content:space-between} #a::before{content:'b'} #a::after{content:'c'}" "c" == some (194,0)
-- a replaced element has none; a rule that names several
#guard (at? "<p>P</p><img id=i>" "img::before{content:'no'}" "no").isNone
#guard at? gen "#a::before,#b::before{content:'x'}" "BB" == some (6,7)
#guard at? gen "#b,#a::before{content:'x';margin-left:6px}" "BB" == some (6,7)
-- the boxes answered are the page's own, in the page's numbers
#guard ((render gen "#a::before{content:'x';display:block} #b::after{content:'y'}").toOption.map fun (_,boxes) =>
  boxes.all (·.source < (DOM.parseHtmlDocument gen).size)) == some true
#guard ((render gen "#a::before{content:'x'} #b::after{content:'y'}").toOption.map (·.2.size)) ==
  ((render gen "").toOption.map (·.2.size))
-- the derived tree: two nodes a pseudo-element, the page's nodes as they were
#guard (do
  let dom := DOM.parseHtmlDocument gen
  let (tree,styles) ← (Generated.styled none dom (← (CSS.parse "#a::before{content:'x'} #b::after{content:'y'} #b::before{content:none}").toOption)).toOption
  pure (tree.size == dom.size + 6 && styles.size == tree.size &&
    (List.range dom.size).all fun i => (tree.get i).lname == (dom.get i).lname && (tree.get i).parent == (dom.get i).parent)) == some true
#guard (do
  let dom := DOM.parseHtmlDocument gen
  let (tree,_) ← (Generated.styled none dom (← (CSS.parse "*::before{box-sizing:border-box} #a{color:red}").toOption)).toOption
  pure (tree.size == dom.size)) == some true


-- Intrinsic contributions are within `min-width` and `max-width` (CSS Sizing 3 §5.1):
-- four empty items of min-width 20 and margins 10 make a 160 px inline-flex container
-- (and nothing overflows it: its scroll width is its client width); a float around a
-- box of max-width 30 is 30 wide.
private def items4 := "<div id=o><div class=i></div><div class=i></div><div class=i></div><div class=i></div></div>"
#guard box items4 "#o{display:inline-flex} .i{min-width:20px;height:5px;margin:0 10px}" "o" == some (0,2,160,5)
#guard scroll items4 "#o{display:inline-flex} .i{min-width:20px;height:5px;margin:0 10px}" "o" == some (160,5)
#guard box "<div id=f><div id=k>AAAAAAAAAA</div></div>" "#f{float:left} #k{max-width:30px}" "f" == some (0,0,30,7)
#guard box "<div id=f><div id=k>AA</div></div>" "#f{float:left} #k{min-width:50px}" "f" == some (0,0,50,7)
#guard box "<div id=f><div id=k>AA</div></div>" "#f{float:left} #k{width:20px;min-width:50px;max-width:40px}" "f" == some (0,0,50,7)
-- A block-level replaced element with a percentage width is compressible (§5.2.2): it adds
-- nothing to the min-content width of its container. (One on a line is still measured at
-- its natural size.)
#guard (box "<div id=z><div id=w><canvas style='display:block;width:50%;max-width:100px'></canvas></div></div>" "#z{width:0} #w{float:left}" "w").map (·.2.2.1) == some 0
#guard (box "<div id=z><div id=w><canvas style='display:block;width:100px;max-width:50%'></canvas></div></div>" "#z{width:0} #w{float:left}" "w").map (·.2.2.1) == some 0
#guard (box "<div id=z><div id=w><canvas style='display:block;width:50%;min-width:30px'></canvas></div></div>" "#z{width:0} #w{float:left}" "w").map (·.2.2.1) == some 30
#guard (box "<div id=z><div id=w><canvas style='display:block;width:40px'></canvas></div></div>" "#z{width:0} #w{float:left}" "w").map (·.2.2.1) == some 40
-- A box of no width and no height is not scrollable overflow, wherever it is; one with an
-- extent in one axis is.
#guard scroll "<div id=c><div id=e></div></div>" "#c{width:100px;height:50px} #e{position:relative;width:0;height:0;left:500px;top:300px}" "c" == some (100,50)
#guard scroll "<div id=c><div id=e></div></div>" "#c{width:100px;height:50px} #e{position:relative;width:10px;height:10px;left:500px;top:300px}" "c" == some (510,310)
#guard scroll "<div id=c><div id=e></div></div>" "#c{width:100px;height:0} #e{width:0;height:100px}" "c" == some (100,100)
#guard scroll "<div id=c><div id=e></div></div>" "#c{width:0;height:100px} #e{width:100px;height:0}" "c" == some (100,100)


-- Inline boxes (CSS 2.1 §9.2.2, §9.4.2; `InlineBox`): an inline element has a box on each
-- line that holds part of it, from its first content to its last, and the line gives
-- room for its margins, borders and padding. Glyphs are 6 px, lines 7 px.
#guard box "<div>ab <span id=s>cd ef</span> gh</div>" "" "s" == some (18,0,30,7)
#guard at? "<div>ab <span id=s>cd ef</span> gh</div>" "" "gh" == some (54,0)
-- margin 3, border 2, padding 5 on each side: the border box starts after the margin and
-- is 2+5+12+5+2 wide; the border is above and below the content area; the text after
-- the box starts after its right margin and a space.
#guard box "<div>ab <span id=s>cd</span> gh</div>" "#s{padding:0 5px;margin:0 3px;border:2px solid red}" "s" == some (21,-2,26,11)
#guard at? "<div>ab <span id=s>cd</span> gh</div>" "#s{padding:0 5px;margin:0 3px;border:2px solid red}" "cd" == some (28,0)
#guard at? "<div>ab <span id=s>cd</span> gh</div>" "#s{padding:0 5px;margin:0 3px;border:2px solid red}" "gh" == some (56,0)
-- vertical padding and margins of an inline box do not move the line
#guard box "<div id=d>ab <span id=s>cd</span></div>" "#s{padding:4px 0;margin:9px 0}" "d" == some (0,0,200,7)
#guard box "<div id=d>ab <span id=s>cd</span></div>" "#s{padding:4px 0;margin:9px 0}" "s" == some (18,-4,12,15)
-- a box broken over two lines: the left edge on the first, the right edge on the second
private def broken := "<div id=d>ab <span id=s>cd ef gh</span> ij</div>"
#guard at? broken "#d{width:60px} #s{padding:0 5px}" "cd" == some (23,0)
#guard at? broken "#d{width:60px} #s{padding:0 5px}" "gh" == some (0,7)
#guard at? broken "#d{width:60px} #s{padding:0 5px}" "ij" == some (23,7)
#guard ((render broken "#d{width:60px} #s{padding:0 5px}").toOption.map fun (_,boxes) =>
  (boxes.filter (·.source == ((DOM.parseHtmlDocument broken).getElementById 0 "s").getD 0)).toList.map fun b => (b.x,b.y,b.width,b.height)) ==
  some [(18,0,35,7),(0,7,17,7)]
-- the start of a box is never left at the end of a line: it goes down with its first word
#guard box "<div id=d>abcdefg <span id=s>hij</span></div>" "#d{width:60px} #s{padding-left:5px}" "s" == some (0,7,23,7)
-- nested boxes: the outer one covers the inner one with its padding
#guard box "<div>a <b id=o>b <i id=n>c</i> d</b> e</div>" "#n{padding:0 2px}" "o" == some (12,0,34,7)
#guard box "<div>a <b id=o>b <i id=n>c</i> d</b> e</div>" "#n{padding:0 2px}" "n" == some (24,0,10,7)
-- an empty inline box has a box where it stands and makes no line; with padding it does
#guard box "<div id=d><span id=s></span></div>" "" "d" == some (0,0,200,0)
#guard box "<div id=d>x<span id=s></span></div>" "" "s" == some (6,0,0,7)
#guard box "<div id=d><span id=s></span></div>" "#s{padding:0 4px}" "d" == some (0,0,200,7)
#guard box "<div id=d><span id=s></span></div>" "#s{padding:0 4px}" "s" == some (0,0,8,7)
-- a box that ends with a forced break has no box on the line after it
#guard box "<div id=d><span id=s>ab<br></span></div>" "" "d" == some (0,0,200,7)
-- shrink-to-fit counts the padding of inline boxes
#guard box "<div id=w><span id=s>ab cd</span></div>" "#w{float:left} #s{padding:0 5px}" "w" == some (0,0,40,7)
-- background and border are painted once for the box on a line, under its text: the six
-- glyphs, one rectangle more for a background, four more for a border
private def paints (html extra : String) : Option Nat :=
  (render html extra).toOption.map fun (scene,_) => (scene.tree.flatMap (fun n => n.lower ⟨1,0,0,1,0,0⟩ [])).length
#guard paints "<div><span>ab cd ef</span></div>" "" == some 6
#guard paints "<div><span>ab cd ef</span></div>" "span{background:red}" == some 7
#guard paints "<div><span>ab cd ef</span></div>" "span{background:red;border:1px solid blue}" == some 11
-- link regions are still cut from the text of a link, one for each word and space
#guard ((render "<div><a href=x>ab cd</a></div>" "a{padding:0 4px}").toOption.map (·.1.links.size)) == some 3

end L4Factoidal.Rendering.PositionLayoutTests
