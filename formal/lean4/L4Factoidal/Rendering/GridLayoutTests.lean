import L4Factoidal.Rendering.Layout
import L4Factoidal.Rendering.GridResolved

/-! Grid layout through `Layout.render`, on a monospace test face (6 px advance, 7 px
line): the border boxes of containers and items. Original fixtures; the expected numbers
follow CSS Grid Layout 2 by hand (§8.5 placement, §12 track sizing, §11 alignment). -/
namespace L4Factoidal.Rendering.GridLayoutTests
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

private def four := "<div id=c><div id=a>AA</div><div id=b>B</div><div id=d>DDD</div><div id=e>E</div></div>"

-- Fixed columns: items fill the cells row by row; rows are as high as their content.
#guard box four "#c{display:grid;grid-template-columns:50px 100px}" "c" == some (0,0,200,14)
#guard box four "#c{display:grid;grid-template-columns:50px 100px}" "a" == some (0,0,50,7)
#guard box four "#c{display:grid;grid-template-columns:50px 100px}" "b" == some (50,0,100,7)
#guard box four "#c{display:grid;grid-template-columns:50px 100px}" "d" == some (0,7,50,7)
#guard box four "#c{display:grid;grid-template-columns:50px 100px}" "e" == some (50,7,100,7)
-- With no template there is one column, as wide as the container.
#guard box four "#c{display:grid}" "d" == some (0,14,200,7)
-- Flexible tracks share the width in proportion; a fixed track and the gap come off first.
#guard box four "#c{display:grid;grid-template-columns:1fr 3fr}" "b" == some (50,0,150,7)
#guard box four "#c{display:grid;grid-template-columns:50px 1fr;gap:10px}" "b" == some (60,0,140,7)
#guard box four "#c{display:grid;grid-template-columns:50px 1fr;gap:10px}" "d" == some (0,17,50,7)
#guard box four "#c{display:grid;grid-template-columns:50px 1fr;gap:10px}" "c" == some (0,0,200,24)
#guard (box four "#c{display:grid;grid-template-columns:repeat(3,1fr)}" "d").map (fun b => b.1+b.2.2.1) == some 200
-- Auto columns take their max-content widths (18 and 6) and stretch into the free space.
#guard box four "#c{display:grid;grid-template-columns:auto auto}" "b" == some (106,0,94,7)
#guard box four "#c{display:grid;grid-template-columns:auto auto;justify-content:start}" "b" == some (18,0,6,7)
#guard box four "#c{display:grid;grid-template-columns:auto auto;justify-content:center}" "a" == some (88,0,18,7)
#guard box four "#c{display:grid;grid-template-columns:min-content max-content;justify-content:end}" "a" == some (176,0,18,7)
-- Fixed rows: items stretch to their areas; the container is as high as its rows.
#guard box four "#c{display:grid;grid-template-columns:50px 50px;grid-template-rows:20px 30px}" "a" == some (0,0,50,20)
#guard box four "#c{display:grid;grid-template-columns:50px 50px;grid-template-rows:20px 30px}" "e" == some (50,20,50,30)
#guard box four "#c{display:grid;grid-template-columns:50px 50px;grid-template-rows:20px 30px}" "c" == some (0,0,200,50)
-- Rows past the template take `grid-auto-rows`.
#guard box four "#c{display:grid;grid-template-columns:100px 100px;grid-auto-rows:15px}" "d" == some (0,15,100,15)
#guard box four "#c{display:grid;grid-template-columns:100px 100px;grid-template-rows:5px;grid-auto-rows:15px}" "d" == some (0,5,100,15)
-- A definite position is kept; the others flow round it.
#guard box four "#c{display:grid;grid-template-columns:50px 50px;grid-template-rows:20px 30px} #a{grid-column:2;grid-row:2}" "a" == some (50,20,50,30)
#guard box four "#c{display:grid;grid-template-columns:50px 50px;grid-template-rows:20px 30px} #a{grid-column:2;grid-row:2}" "b" == some (0,0,50,20)
#guard box four "#c{display:grid;grid-template-columns:50px 50px;grid-template-rows:20px 30px} #a{grid-column:2;grid-row:2}" "e" == some (0,20,50,30)
#guard box four "#c{display:grid;grid-template-columns:50px 50px} #a{grid-area:1 / 2 / 2 / 3}" "a" == some (50,0,50,7)
#guard box four "#c{display:grid;grid-template-columns:50px 50px 50px} #a{grid-column:-2}" "a" == some (100,0,50,7)
-- A span covers its tracks and the gap between them.
#guard box four "#c{display:grid;grid-template-columns:50px 50px} #a{grid-column:span 2}" "a" == some (0,0,100,7)
#guard box four "#c{display:grid;grid-template-columns:50px 50px} #a{grid-column:span 2}" "d" == some (50,7,50,7)
#guard box four "#c{display:grid;grid-template-columns:50px 50px;column-gap:8px} #a{grid-column:1 / 3}" "a" == some (0,0,108,7)
#guard box four "#c{display:grid;grid-template-columns:50px 50px;grid-auto-rows:10px} #a{grid-row:span 2}" "a" == some (0,0,50,20)
-- Dense packing fills the hole a wide item leaves.
#guard box four "#c{display:grid;grid-template-columns:50px 50px 50px} #b{grid-column:span 3}" "d" == some (0,14,50,7)
#guard box four "#c{display:grid;grid-template-columns:50px 50px 50px} #b{grid-column:span 3} #d{grid-column:span 2}" "d" == some (0,14,100,7)
#guard box four "#c{display:grid;grid-template-columns:50px 50px 50px;grid-auto-flow:dense} #b{grid-column:span 3} #d{grid-column:span 2}" "d" == some (50,0,100,7)
#guard box four "#c{display:grid;grid-template-columns:50px 50px 50px;grid-auto-flow:dense} #b{grid-column:span 3} #d{grid-column:span 2}" "e" == some (0,14,50,7)
-- Column flow fills columns; new columns take `grid-auto-columns`.
#guard box four "#c{display:grid;grid-template-rows:10px 10px;grid-auto-flow:column;grid-auto-columns:30px}" "b" == some (0,10,30,10)
#guard box four "#c{display:grid;grid-template-rows:10px 10px;grid-auto-flow:column;grid-auto-columns:30px}" "d" == some (30,0,30,10)
-- Named areas and named lines.
#guard box four "#c{display:grid;grid-template-columns:40px 60px;grid-template-areas:\"h h\" \"s m\"} #a{grid-area:h} #b{grid-area:m} #d{grid-area:s}" "a" == some (0,0,100,7)
#guard box four "#c{display:grid;grid-template-columns:40px 60px;grid-template-areas:\"h h\" \"s m\"} #a{grid-area:h} #b{grid-area:m} #d{grid-area:s}" "b" == some (40,7,60,7)
#guard box four "#c{display:grid;grid-template-columns:40px 60px;grid-template-areas:\"h h\" \"s m\"} #a{grid-area:h} #b{grid-area:m} #d{grid-area:s}" "e" == some (0,14,40,7)
#guard box four "#c{display:grid;grid-template-columns:[x] 30px [y] 40px [z]} #a{grid-column:y / z}" "a" == some (30,0,40,7)
-- repeat(auto-fill, 60px) in 200px: three columns.
#guard box four "#c{display:grid;grid-template-columns:repeat(auto-fill,60px)}" "e" == some (0,7,60,7)
#guard box four "#c{display:grid;grid-template-columns:repeat(auto-fill,60px);gap:20px}" "d" == some (0,27,60,7)
-- minmax() and fit-content().
#guard box four "#c{display:grid;grid-template-columns:minmax(20px,60px) 1fr}" "b" == some (60,0,140,7)
-- fit-content(15px) is not below the min-content width (18 for DDD); fit-content(100px) is the max-content width.
#guard box four "#c{display:grid;grid-template-columns:fit-content(15px) 1fr}" "b" == some (18,0,182,7)
#guard box four "#c{display:grid;grid-template-columns:fit-content(100px) 1fr}" "b" == some (18,0,182,7)
-- Alignment of an item in its area: its fit-content width, its own height.
#guard box four "#c{display:grid;grid-template-columns:50px;grid-template-rows:21px} #a{justify-self:end;align-self:center}" "a" == some (38,7,12,7)
#guard box four "#c{display:grid;grid-template-columns:50px;grid-template-rows:21px;justify-items:center;align-items:end}" "a" == some (19,14,12,7)
#guard box four "#c{display:grid;grid-template-columns:50px;grid-template-rows:21px} #a{margin:auto}" "a" == some (19,7,12,7)
#guard box four "#c{display:grid;grid-template-columns:50px} #a{margin:5px}" "a" == some (5,5,40,7)
#guard box four "#c{display:grid;grid-template-columns:50px} #a{margin:5px}" "b" == some (0,17,50,7)
-- Percentages of an item are of its area.
#guard box four "#c{display:grid;grid-template-columns:100px;grid-template-rows:40px} #a{width:50%;height:100%}" "a" == some (0,0,50,40)
-- The tracks in a container with a definite height: content distribution.
#guard box four "#c{display:grid;height:100px;grid-template-columns:100px 100px;grid-template-rows:10px 10px;align-content:center}" "a" == some (0,40,100,10)
#guard box four "#c{display:grid;height:100px;grid-template-columns:100px 100px;grid-template-rows:10px 10px;align-content:space-between}" "d" == some (0,90,100,10)
#guard box four "#c{display:grid;height:100px;grid-template-columns:100px 100px;grid-template-rows:1fr 3fr}" "d" == some (0,25,100,75)
#guard box four "#c{display:grid;height:100px;grid-template-columns:100px 100px}" "d" == some (0,50,100,50)
-- `order`, and a right-to-left container.
#guard box four "#c{display:grid;grid-template-columns:50px 100px} #d{order:-1}" "d" == some (0,0,50,7)
#guard box four "#c{display:grid;grid-template-columns:50px 100px;direction:rtl}" "a" == some (150,0,50,7)
#guard box four "#c{display:grid;grid-template-columns:50px 100px;direction:rtl}" "b" == some (50,0,100,7)
-- A run of text is an anonymous item.
#guard box "<div id=c>text<div id=a>AA</div></div>" "#c{display:grid;grid-template-columns:50px 50px}" "a" == some (50,0,50,7)
-- An inline grid is as wide as its columns; a grid in a grid item is laid out in its area.
#guard box four "#c{display:inline-grid;grid-template-columns:auto auto}" "c" == some (0,0,24,14)
#guard box "<div id=c><div id=a><div id=x>X</div><div id=y>Y</div></div></div>"
  "#c{display:grid;grid-template-columns:80px} #a{display:grid;grid-template-columns:1fr 1fr}" "y" == some (40,0,40,7)
-- Block flow goes on after the grid.
#guard box (four ++ "<p id=p>after</p>") "#c{display:grid;grid-template-columns:50px 100px} p{margin:0}" "p" == some (0,14,200,7)

/-- The resolved `grid-template-columns` and `grid-template-rows` of the element with this id. -/
private def tracks (html extra id : String) : Option (String × String) := do
  let dom := DOM.parseHtmlDocument html
  let n ← dom.getElementById 0 id
  let (scene,_) ← (render html extra).toOption
  gridRecord n gridRecordFuel scene.tree

-- Resolved values (§7.2.6): used sizes of every track, with the names of explicit lines.
#guard tracks four "#c{display:grid;grid-template-columns:50px 1fr}" "c" == some ("50px 150px", "7px 7px")
#guard tracks four "#c{display:grid;grid-template-columns:[a] 50px [b c] 100px [d];grid-auto-rows:10px}" "c" ==
  some ("[a] 50px [b c] 100px [d]", "10px 10px")
#guard tracks four "#c{display:grid;grid-template-columns:repeat(4,1fr)}" "c" == some ("50px 50px 50px 50px", "7px")
#guard tracks four "#c{display:grid;grid-template-columns:repeat(2,20%) auto}" "c" == some ("40px 40px 120px", "7px 7px")
#guard (tracks "<div id=c></div>" "#c{display:grid}" "c") == some ("none", "none")
#guard (tracks four "#c{display:block}" "c") == none
-- An item before the explicit grid: the implicit track comes first, with no line name.
#guard (tracks "<div id=c><div id=a style='width:10px'></div></div>" "#c{display:grid;grid-template-columns:[x] 30px [y];justify-content:start} #a{grid-column:auto / 1}" "c").map (·.1) ==
  some "10px [x] 30px [y]"
-- repeat(auto-fit): the tracks no item is in collapse to 0 and take no gap.
#guard (tracks four "#c{display:grid;grid-template-columns:repeat(auto-fit,30px);gap:10px;justify-content:start}" "c").map (·.1) ==
  some "30px 30px 30px 30px 0px"
#guard box four "#c{display:grid;grid-template-columns:repeat(auto-fit,30px);gap:10px;justify-content:center}" "a" == some (25,0,30,7)
#guard (tracks four "#c{display:grid;grid-template-columns:repeat(auto-fill,30px);gap:10px;justify-content:start}" "c").map (·.1) ==
  some "30px 30px 30px 30px 30px"


-- A positioned child is not a grid item (§9.2): the items fill the cells as if it were not
-- there, and it is placed against the positioned container's padding box.
#guard box "<div id=c><div id=p>PP</div><div id=a>AA</div><div id=b>B</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px} #p{position:absolute;top:3px;left:4px}" "a" == some (0,0,50,7)
#guard box "<div id=c><div id=p>PP</div><div id=a>AA</div><div id=b>B</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px} #p{position:absolute;top:3px;left:4px}" "b" == some (50,0,100,7)
#guard box "<div id=c><div id=p>PP</div><div id=a>AA</div><div id=b>B</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px} #p{position:absolute;top:3px;left:4px}" "p" == some (4,3,12,7)


-- The containing block of an absolutely positioned box whose containing block is a grid
-- container is the area between the lines it names (§9.1); an `auto` line is the padding
-- edge. The same for a child (`p`) and for a box inside an item (`q`).
#guard box "<div id=c><div id=a>A<div id=q>Q</div></div><div id=b>B</div><div id=p>P</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px;grid-template-rows:10px 20px;padding:5px} #p,#q{position:absolute;left:0;top:0;right:0;bottom:0} #p{grid-column:2 / 3;grid-row:2 / 3}" "p" == some (55,15,100,20)
#guard box "<div id=c><div id=a>A<div id=q>Q</div></div><div id=b>B</div><div id=p>P</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px;grid-template-rows:10px 20px;padding:5px} #p,#q{position:absolute;left:0;top:0;right:0;bottom:0} #p{grid-area:1 / 1 / 3 / 3}" "p" == some (5,5,150,30)
#guard box "<div id=c><div id=a>A<div id=q>Q</div></div><div id=b>B</div><div id=p>P</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px;grid-template-rows:10px 20px;padding:5px} #p,#q{position:absolute;left:0;top:0;right:0;bottom:0} #p{grid-column:auto / 2;grid-row:2 / auto}" "p" == some (0,15,55,25)
#guard box "<div id=c><div id=a>A<div id=q>Q</div></div><div id=b>B</div><div id=p>P</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px;grid-template-rows:10px 20px;padding:5px} #p,#q{position:absolute;left:0;top:0;right:0;bottom:0}" "p" == some (0,0,200,40)
#guard box "<div id=c><div id=a>A<div id=q>Q</div></div><div id=b>B</div><div id=p>P</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px;grid-template-rows:10px 20px;padding:5px} #p,#q{position:absolute;left:0;top:0;right:0;bottom:0} #q{grid-column:2 / 3;grid-row:1 / 2}" "q" == some (55,5,100,10)
-- one line given: the other side is `auto`, the padding edge (not a span of one track)
#guard box "<div id=c><div id=a>A<div id=q>Q</div></div><div id=b>B</div><div id=p>P</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px;grid-template-rows:10px 20px;padding:5px} #p,#q{position:absolute;left:0;top:0;right:0;bottom:0} #p{grid-column:2;grid-row:2}" "p" == some (55,15,145,25)
-- a line the grid does not have is `auto`
#guard box "<div id=c><div id=a>A<div id=q>Q</div></div><div id=b>B</div><div id=p>P</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px;grid-template-rows:10px 20px;padding:5px} #p,#q{position:absolute;left:0;top:0;right:0;bottom:0} #q{grid-column:7 / 9}" "q" == some (0,0,200,40)
-- with a gap the area ends where its last track does
#guard box "<div id=c><div id=a>A<div id=q>Q</div></div><div id=b>B</div><div id=p>P</div></div>" "#c{display:grid;position:relative;grid-template-columns:50px 100px;grid-template-rows:10px 20px;padding:5px} #p,#q{position:absolute;left:0;top:0;right:0;bottom:0} #c{column-gap:10px} #p{grid-column:1 / 3}" "p" == some (5,0,160,40)


-- A percentage row of a container with no definite height counts as `auto` for that height
-- (7 px of text), then is 60% of it (§7.2.1).
#guard box "<div id=c><div id=a>A</div></div>" "#c{display:grid;grid-template-rows:60%}" "c" == some (0,0,200,7)
#guard (box "<div id=c><div id=a>A</div></div>" "#c{display:grid;grid-template-rows:60%}" "a").map (·.2.2.2) == some 4.1875


-- Baseline alignment (§11.6): with a 14 px font the second item's baseline is 7 px lower,
-- so the first moves down 7 px; the row is as high as the shifted item needs.
#guard box "<div id=c><div id=a>A</div><div id=b>B</div></div>" "#c{display:grid;grid-template-columns:50px 50px;align-items:baseline} #b{font-size:14px;line-height:14px}" "a" == some (0,7,50,7)
#guard box "<div id=c><div id=a>A</div><div id=b>B</div></div>" "#c{display:grid;grid-template-columns:50px 50px;align-items:baseline} #b{font-size:14px;line-height:14px}" "b" == some (50,0,50,14)
#guard box "<div id=c><div id=a>A</div><div id=b>B</div></div>" "#c{display:grid;grid-template-columns:50px 50px;align-items:baseline} #b{font-size:14px;line-height:14px}" "c" == some (0,0,200,14)
-- an item with no line box: its baseline is its border box's bottom edge
#guard box "<div id=c><div id=a></div><div id=b>B</div></div>" "#c{display:grid;grid-template-columns:50px 50px;align-items:baseline} #a{height:20px}" "b" == some (50,13,50,7)

end L4Factoidal.Rendering.GridLayoutTests
