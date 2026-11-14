import L4Factoidal.Rendering.Layout

/-! Flex layout through `Layout.render`, on a monospace test face (6 px advance, 7 px
line): the border boxes of containers and items. Original fixtures; the expected
numbers follow CSS Flexible Box Layout 1 §9 by hand. -/
namespace L4Factoidal.Rendering.FlexLayoutTests
open DOM CSS Layout
private def font : FontProfile :=
  {family := "layout-test-monospace",unitsPerEm := 7,advance := 6, ascent := 7,descent := 0,outline := fun _ => [.rect 0 0 5 7],admits := fun n => n >= 32 && n <= 126}
private def noSVG : Embedding := fun _ _ _ _ => throw "unsupported SVG test embedding"
private def css := "body{margin:0;font-size:7px;line-height:7px} "
private def render (html extra : String) (width : Nat := 200) : Except String (Scene × Array Box) := do
  let dom := DOM.parseHtmlDocument html
  Layout.render dom (← CSS.parse (css ++ extra)) font noSVG width 200
/-- The border box of the element with this id: x, y, width, height. -/
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

private def three := "<div id=c><div id=a>AA</div><div id=b>B</div><div id=d>DDD</div></div>"

-- Items of a row sit side by side at their max-content widths; the container fills its block.
#guard box three "#c{display:flex}" "c" == some (0,0,200,7)
#guard box three "#c{display:flex}" "a" == some (0,0,12,7)
#guard box three "#c{display:flex}" "b" == some (12,0,6,7)
#guard box three "#c{display:flex}" "d" == some (18,0,18,7)
-- flex-grow shares the free space (200 - 36 = 164) in proportion to the factors.
#guard box three "#c{display:flex} #b{flex-grow:1}" "b" == some (12,0,170,7)
#guard box three "#c{display:flex} #b{flex-grow:1}" "d" == some (182,0,18,7)
#guard box three "#c{display:flex} #a{flex-grow:1} #b{flex-grow:3}" "a" == some (0,0,53,7)
#guard box three "#c{display:flex} #a{flex-grow:1} #b{flex-grow:3}" "b" == some (53,0,129,7)
-- `flex: 1` is `1 1 0%`: equal shares of the whole width, to the layout unit (1/64 px).
#guard (box three "#c{display:flex} #c div{flex:1}" "a").map (·.2.2.1) == some (66.65625)
#guard (box three "#c{display:flex} #c div{flex:1}" "d").map (fun b => b.1 + b.2.2.1) == some 200
-- flex-shrink: widths 100 + 100 + 100 in 200 shrink equally; a min-width holds one back.
#guard box three "#c{display:flex} #c div{width:100px}" "b" == some (66.671875,0,66.671875,7)
#guard box three "#c{display:flex} #c div{width:100px} #a{flex-shrink:0}" "b" == some (100,0,50,7)
#guard box three "#c{display:flex} #c div{width:100px} #a{min-width:90px}" "a" == some (0,0,90,7)
#guard box three "#c{display:flex} #c div{width:100px} #a{min-width:90px}" "b" == some (90,0,55,7)
-- The automatic minimum: an item does not shrink below its min-content width (18 for DDD)...
#guard box three "#c{display:flex;width:20px} #c div{flex:1}" "d" == some (18,0,18,7)
-- ...unless it clips or has `min-width: 0`.
#guard (box three "#c{display:flex;width:21px} #c div{flex:1;min-width:0}" "d").map (·.2.2.1) == some 7
-- max-width stops growth; the rest goes to the others.
#guard box three "#c{display:flex} #c div{flex:1} #a{max-width:20px}" "a" == some (0,0,20,7)
#guard box three "#c{display:flex} #c div{flex:1} #a{max-width:20px}" "b" == some (20,0,90,7)
-- gap.
#guard box three "#c{display:flex;gap:10px}" "b" == some (22,0,6,7)
#guard box three "#c{display:flex;column-gap:10px} #b{flex:1}" "b" == some (22,0,150,7)
-- justify-content (free space 164).
#guard box three "#c{display:flex;justify-content:flex-end}" "a" == some (164,0,12,7)
#guard box three "#c{display:flex;justify-content:center}" "a" == some (82,0,12,7)
#guard box three "#c{display:flex;justify-content:space-between}" "b" == some (94,0,6,7)
#guard box three "#c{display:flex;justify-content:space-between}" "d" == some (182,0,18,7)
#guard box three "#c{display:flex;justify-content:space-around}" "a" == some (27.328125,0,12,7)
#guard box three "#c{display:flex;justify-content:space-evenly}" "a" == some (41,0,12,7)
-- Auto margins take the free space before justify-content does.
#guard box three "#c{display:flex;justify-content:center} #d{margin-left:auto}" "a" == some (0,0,12,7)
#guard box three "#c{display:flex;justify-content:center} #d{margin-left:auto}" "d" == some (182,0,18,7)
#guard box three "#c{display:flex} #b{margin-left:auto;margin-right:auto}" "b" == some (94,0,6,7)
-- row-reverse and right-to-left start from the right.
#guard box three "#c{display:flex;flex-direction:row-reverse}" "a" == some (188,0,12,7)
#guard box three "#c{display:flex;flex-direction:row-reverse}" "d" == some (164,0,18,7)
#guard box three "#c{display:flex;direction:rtl}" "a" == some (188,0,12,7)
#guard box three "#c{display:flex;direction:rtl;flex-direction:row-reverse}" "a" == some (0,0,12,7)
-- order.
#guard box three "#c{display:flex} #d{order:-1}" "d" == some (0,0,18,7)
#guard box three "#c{display:flex} #d{order:-1}" "a" == some (18,0,12,7)
-- Cross axis: items stretch to the line; align-items moves an item that does not.
#guard box three "#c{display:flex} #b{height:30px}" "c" == some (0,0,200,30)
#guard box three "#c{display:flex} #b{height:30px}" "a" == some (0,0,12,30)
#guard box three "#c{display:flex;align-items:flex-start} #b{height:30px}" "a" == some (0,0,12,7)
#guard box three "#c{display:flex;align-items:center} #b{height:30px}" "a" == some (0,11.5,12,7)
#guard box three "#c{display:flex;align-items:flex-end} #b{height:30px}" "a" == some (0,23,12,7)
#guard box three "#c{display:flex} #b{height:30px} #a{align-self:flex-end}" "a" == some (0,23,12,7)
#guard box three "#c{display:flex} #b{height:30px} #a{margin-top:auto}" "a" == some (0,23,12,7)
#guard box three "#c{display:flex;height:50px}" "a" == some (0,0,12,50)
#guard box three "#c{display:flex;height:50px;align-items:center}" "a" == some (0,21.5,12,7)
#guard at? three "#c{display:flex;height:50px;align-items:center}" "AA" == some (0,21.5)
-- Padding, border and margin of an item are part of its outer size.
#guard box three "#c{display:flex} #a{padding:2px;margin:3px;border:1px solid black}" "a" == some (3,3,18,13)
#guard box three "#c{display:flex} #a{padding:2px;margin:3px;border:1px solid black}" "b" == some (24,0,6,19)
-- Text directly in a flex container is an anonymous item.
#guard at? "<div id=c>AA<div id=b>B</div>CC</div>" "#c{display:flex}" "B" == some (12,0)
#guard at? "<div id=c>AA<div id=b>B</div>CC</div>" "#c{display:flex}" "CC" == some (18,0)
-- An inline child is blockified.
#guard box "<div id=c><span id=a>AA</span><span id=b>B</span></div>" "#c{display:flex} #b{flex:1}" "b" == some (12,0,188,7)

-- Multi-line: items wrap when the next does not fit; each line is as high as its highest item.
private def wrapping := "<div id=c><div id=a>A</div><div id=b>B</div><div id=d>D</div><div id=e>E</div><div id=f>F</div></div>"
private def wrapCss := "#c{display:flex;flex-wrap:wrap;width:100px} #c div{width:40px} #d{height:20px} "
#guard box wrapping wrapCss "b" == some (40,0,40,7)
#guard box wrapping wrapCss "d" == some (0,7,40,20)
#guard box wrapping wrapCss "e" == some (40,7,40,20)
#guard box wrapping wrapCss "f" == some (0,27,40,7)
#guard box wrapping wrapCss "c" == some (0,0,100,34)
-- Each line resolves its own flexible lengths.
#guard box wrapping (wrapCss ++ "#c div{flex-grow:1}") "b" == some (50,0,50,7)
#guard box wrapping (wrapCss ++ "#c div{flex-grow:1}") "f" == some (0,27,100,7)
-- align-content in a definite height (free space 100 - 34 = 66): stretch by default.
#guard box wrapping (wrapCss ++ "#c{height:100px}") "d" == some (0,29,40,20)
#guard box wrapping (wrapCss ++ "#c{height:100px}") "a" == some (0,0,40,29)
#guard box wrapping (wrapCss ++ "#c{height:100px;align-content:flex-start}") "f" == some (0,27,40,7)
#guard box wrapping (wrapCss ++ "#c{height:100px;align-content:flex-end}") "a" == some (0,66,40,7)
#guard box wrapping (wrapCss ++ "#c{height:100px;align-content:center}") "a" == some (0,33,40,7)
#guard box wrapping (wrapCss ++ "#c{height:100px;align-content:space-between}") "d" == some (0,40,40,20)
#guard box wrapping (wrapCss ++ "#c{height:100px;align-content:space-between}") "f" == some (0,93,40,7)
#guard box wrapping (wrapCss ++ "#c{height:100px;align-content:space-around}") "a" == some (0,11,40,7)
-- row-gap between lines, column-gap between items (two fit: 40 + 10 + 40).
#guard box wrapping (wrapCss ++ "#c{gap:5px 10px}") "b" == some (50,0,40,7)
#guard box wrapping (wrapCss ++ "#c{gap:5px 10px}") "d" == some (0,12,40,20)
-- wrap-reverse stacks the lines from the bottom.
#guard box wrapping "#c{display:flex;flex-wrap:wrap-reverse;width:100px} #c div{width:40px} #d{height:20px}" "a" == some (0,27,40,7)
#guard box wrapping "#c{display:flex;flex-wrap:wrap-reverse;width:100px} #c div{width:40px} #d{height:20px}" "f" == some (0,0,40,7)
-- A single-line container ignores align-content.
#guard box three "#c{display:flex;height:50px;align-content:center;align-items:flex-start}" "a" == some (0,0,12,7)

-- Column: items stack, each as wide as the container (stretch) or as its content.
#guard box three "#c{display:flex;flex-direction:column}" "c" == some (0,0,200,21)
#guard box three "#c{display:flex;flex-direction:column}" "b" == some (0,7,200,7)
#guard box three "#c{display:flex;flex-direction:column;align-items:flex-start}" "b" == some (0,7,6,7)
#guard box three "#c{display:flex;flex-direction:column;align-items:center}" "b" == some (97,7,6,7)
#guard box three "#c{display:flex;flex-direction:column;align-items:flex-end}" "d" == some (182,14,18,7)
-- A definite height: flex-grow shares the free height (100 - 21 = 79).
#guard box three "#c{display:flex;flex-direction:column;height:100px} #b{flex-grow:1}" "b" == some (0,7,200,86)
#guard box three "#c{display:flex;flex-direction:column;height:100px} #b{flex-grow:1}" "d" == some (0,93,200,7)
#guard at? three "#c{display:flex;flex-direction:column;height:100px} #b{flex-grow:1}" "DDD" == some (0,93)
#guard box three "#c{display:flex;flex-direction:column;min-height:100px} #b{flex:1}" "d" == some (0,93,200,7)
#guard box three "#c{display:flex;flex-direction:column;height:100px;justify-content:center}" "a" == some (0,39.5,200,7)
#guard box three "#c{display:flex;flex-direction:column;height:100px;justify-content:space-between}" "b" == some (0,46.5,200,7)
#guard box three "#c{display:flex;flex-direction:column-reverse;height:100px}" "a" == some (0,93,200,7)
#guard box three "#c{display:flex;flex-direction:column;gap:5px}" "d" == some (0,24,200,7)
#guard box three "#c{display:flex;flex-direction:column;gap:5px}" "c" == some (0,0,200,31)
#guard box three "#c{display:flex;flex-direction:column;height:100px} #d{margin-top:auto}" "d" == some (0,93,200,7)

-- A multi-line column (§9.3): the items break into columns at the container's height (two
-- of 7 fit in 14); a column is as wide as its widest item (12 and 18) and `align-content:
-- stretch` shares the free width (100 - 30 = 70) between the columns.
private def columns := "#c{display:flex;flex-direction:column;flex-wrap:wrap;width:100px;height:14px} "
#guard box three columns "c" == some (0,0,100,14)
#guard box three columns "a" == some (0,0,47,7)
#guard box three columns "b" == some (0,7,47,7)
#guard box three columns "d" == some (47,0,53,7)
#guard box three (columns ++ "#c{align-content:flex-start}") "b" == some (0,7,12,7)
#guard box three (columns ++ "#c{align-content:flex-start}") "d" == some (12,0,18,7)
#guard box three (columns ++ "#c{align-content:flex-start;align-items:flex-start}") "b" == some (0,7,6,7)
#guard box three (columns ++ "#c{align-content:center}") "a" == some (35,0,12,7)
#guard box three (columns ++ "#c{align-content:center}") "d" == some (47,0,18,7)
#guard box three (columns ++ "#c{align-content:space-between}") "d" == some (82,0,18,7)
#guard box three (columns ++ "#c{align-content:flex-end}") "a" == some (70,0,12,7)
-- wrap-reverse: the columns start from the right.
#guard box three "#c{display:flex;flex-direction:column;flex-wrap:wrap-reverse;width:100px;height:14px}" "a" == some (53,0,47,7)
#guard box three "#c{display:flex;flex-direction:column;flex-wrap:wrap-reverse;width:100px;height:14px}" "d" == some (0,0,53,7)
-- With no height to break at there is one column, as wide as the container.
#guard box three "#c{display:flex;flex-direction:column;flex-wrap:wrap}" "c" == some (0,0,200,21)
#guard box three "#c{display:flex;flex-direction:column;flex-wrap:wrap}" "b" == some (0,7,200,7)
-- max-height breaks a container whose height is its content's; it is as high as its longest column.
#guard box three "#c{display:flex;flex-direction:column;flex-wrap:wrap;max-height:15px;width:100px}" "c" == some (0,0,100,14)
#guard box three "#c{display:flex;flex-direction:column;flex-wrap:wrap;max-height:15px;width:100px}" "d" == some (47,0,53,7)
-- column-gap is between the columns, row-gap between the items of a column (7 + 3 + 7 fit in 17).
#guard box three "#c{display:flex;flex-direction:column;flex-wrap:wrap;width:100px;height:17px;gap:3px 10px;align-content:flex-start}" "b" == some (0,10,12,7)
#guard box three "#c{display:flex;flex-direction:column;flex-wrap:wrap;width:100px;height:17px;gap:3px 10px;align-content:flex-start}" "d" == some (22,0,18,7)

-- Nesting: a row in a column in a row; a flex container in block flow and a block in a flex item.
private def nested := "<div id=o><div id=l>LL</div><div id=m><div id=h>H</div><div id=r><div id=x>X</div><div id=y>Y</div></div></div></div><div id=p>P</div>"
private def nestedCss := "#o{display:flex} #m{flex:1;display:flex;flex-direction:column} #r{display:flex} #y{flex:1}"
#guard box nested nestedCss "m" == some (12,0,188,14)
#guard box nested nestedCss "r" == some (12,7,188,7)
#guard box nested nestedCss "y" == some (18,7,182,7)
#guard box nested nestedCss "l" == some (0,0,12,14)
#guard box nested nestedCss "p" == some (0,14,200,7)
-- A stretched nested container is laid out again at its new height: its items stretch too.
#guard box nested (nestedCss ++ " #l{height:40px}") "m" == some (12,0,188,40)
-- inline-flex is one box on a line, as wide as its content.
#guard box "<div>ab <span id=c><span id=a>AA</span><span id=b>B</span></span> cd</div>" "#c{display:inline-flex}" "c" == some (18,0,18,7)
-- display:none items and white space between items make no boxes.
#guard box "<div id=c> <div id=a>AA</div> <div id=n>N</div> <div id=b>B</div> </div>" "#c{display:flex} #n{display:none}" "b" == some (12,0,6,7)

end L4Factoidal.Rendering.FlexLayoutTests
