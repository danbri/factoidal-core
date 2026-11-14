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

end L4Factoidal.Rendering.PositionLayoutTests
