import L4Factoidal.Rendering.Layout

/-! Table layout through `Layout.render`, on a monospace test face (6 px advance,
7 px line): positions of glyph runs and of cell boxes in the scene. -/
namespace L4Factoidal.Rendering.TableLayoutTests
open DOM CSS Layout
private def font : FontProfile :=
  {family := "layout-test-monospace",unitsPerEm := 7,advance := 6, ascent := 7,descent := 0,outline := fun _ => [.rect 0 0 5 7],admits := fun n => n >= 32 && n <= 126}
private def noSVG : Embedding := fun _ _ _ _ => throw "unsupported SVG test embedding"
private def css := "body{margin:0;font-size:7px;line-height:7px} "
private def render (html extra : String) (width : Nat := 200) : Except String (Scene × Array Box) := do
  let dom := DOM.parseHtmlDocument html
  Layout.render dom (← CSS.parse (css ++ extra)) font noSVG width 200
/-- The first glyph's position of the run with this text. -/
private def at? (html extra text : String) (width : Nat := 200) : Option (Float × Float) := do
  let (scene,_) ← (render html extra width).toOption
  let run ← scene.glyphRuns.find? (·.text == text)
  let g ← run.glyphs[0]?
  return (g.x,g.y)
private def cellBox (html extra id : String) : Option (Float × Float × Float × Float) := do
  let dom := DOM.parseHtmlDocument html
  let n ← dom.getElementById 0 id
  let (_,boxes) ← (render html extra).toOption
  let b ← boxes.find? (·.source == n)
  return (b.x,b.y,b.width,b.height)

-- Cells of a row are side by side: border-spacing 2px, padding 1px (HTML's defaults).
-- "AA" is 12 px wide, so the second cell starts at 2+1+12+1+2+1 = 19.
#guard at? "<table><tr><td>AA<td>B</table>" "" "AA" == some (3,3)
#guard at? "<table><tr><td>AA<td>B</table>" "" "B" == some (19,3)
-- A second row is below the first: 2+1+7+1+2+1 = 14.
#guard at? "<table><tr><td>A<tr><td>C</table>" "" "C" == some (3,14)
-- colspan: the spanning cell starts in its first column and covers both.
#guard at? "<table><tr><td>AA<td>BB<tr><td colspan=2>W</table>" "" "W" == some (3,14)
#guard cellBox "<table><tr><td>AA<td>BB<tr><td id=w colspan=2>W</table>" "" "w" == some (2,13,30,9)
-- rowspan: the cell after a row-spanning cell moves to the next column.
#guard at? "<table><tr><td rowspan=2>R<td>A<tr><td>B</table>" "" "B" == some (13,14)
-- vertical-align: HTML cells are middle by default; top and bottom when asked.
#guard at? "<table><tr><td>A<br>A<td>M</table>" "" "M" == some (13,6.5)
#guard at? "<table><tr><td>A<br>A<td style='vertical-align:top'>M</table>" "" "M" == some (13,3)
#guard at? "<table><tr><td>A<br>A<td style='vertical-align:bottom'>M</table>" "" "M" == some (13,10)
-- CSS display values make tables of other elements; a lone cell gets an anonymous table
-- (CSS 2.1 §17.2.1) with no border spacing.
#guard at? "<div style='display:table'><div style='display:table-cell'>A</div><div style='display:table-cell'>B</div></div>" "" "B" == some (6,0)
#guard at? "<p style='margin:0'><span style='display:table-cell'>A</span><span style='display:table-cell'>B</span></p>" "" "B" == some (6,0)
-- border-spacing, cellspacing and cellpadding.
#guard at? "<table cellspacing=0 cellpadding=0><tr><td>A<td>B</table>" "" "B" == some (6,0)
#guard at? "<table><tr><td>A<td>B</table>" "table{border-spacing:10px 0} td{padding:0}" "B" == some (26,0)
#guard at? "<table><tr><td>A<td>B</table>" "table{border-collapse:collapse} td{padding:0}" "B" == some (6,0)
-- Width: a table with a width shares the extra room among auto columns by their max-content widths.
#guard at? "<table cellspacing=0 cellpadding=0 width=100><tr><td>A<td>BBB</table>" "" "BBB" == some (25,0)
-- A cell with a width keeps it; the other takes the rest.
#guard at? "<table cellspacing=0 cellpadding=0 width=100><tr><td width=60>A<td>B</table>" "" "B" == some (60,0)
-- Percentages of the table width.
#guard at? "<table cellspacing=0 cellpadding=0 width=200><tr><td width='25%'>A<td>B</table>" "" "B" == some (50,0)
-- Narrow room: each column gets at least its longest word, and text wraps inside the cell.
#guard at? "<table cellspacing=0 cellpadding=0><tr><td>AAA BBB<td>CC</table>" "" "CC" (width := 40) == some (28,3.5)
#guard at? "<table cellspacing=0 cellpadding=0><tr><td>AAA BBB<td>CC</table>" "" "BBB" (width := 40) == some (0,7)
-- Captions are above the grid by default, and below with caption-side: bottom.
#guard at? "<table cellspacing=0 cellpadding=0><caption>T</caption><tr><td>A</table>" "" "A" == some (0,7)
#guard at? "<table cellspacing=0 cellpadding=0><caption style='caption-side:bottom'>T</caption><tr><td>A</table>" "" "T" == some (0,7)
-- Header groups come first and footer groups last, wherever they are in the source.
#guard at? "<table cellspacing=0 cellpadding=0><tfoot><tr><td>F</tfoot><tbody><tr><td>B</tbody><thead><tr><td>H</thead></table>" "" "F" == some (0,14)
#guard at? "<table cellspacing=0 cellpadding=0><tfoot><tr><td>F</tfoot><tbody><tr><td>B</tbody><thead><tr><td>H</thead></table>" "" "H" == some (0,0)
-- A specified table height goes to the rows.
#guard cellBox "<table cellspacing=0 cellpadding=0 style='height:40px'><tr><td id=a>A<tr><td>B</table>" "" "a" == some (0,0,6,20)
-- Fixed layout: widths from the first row, the rest shared equally.
#guard at? "<table cellspacing=0 cellpadding=0 style='table-layout:fixed;width:100px'><tr><td style='width:40px'>A<td>B<td>C</table>" "" "C" == some (70,0)
-- Column elements make columns even where no cell is (HTML §4.9.12).
#guard cellBox "<table id=t cellspacing=0 cellpadding=0><col width=50><col width=50><col width=50><tr><td>A</table>" "" "t" == some (0,0,150,7)
-- A table nested in a cell is measured and laid out inside it.
#guard at? "<table cellspacing=0 cellpadding=0><tr><td><table cellspacing=0 cellpadding=0><tr><td>A<td>B</table><td>C</table>" "" "C" == some (12,0)
-- Text outside cells in a table element is moved before it by the HTML parser; text in a
-- CSS table gets an anonymous cell.
#guard at? "<div style='display:table'>X<div style='display:table-cell'>Y</div></div>" "" "Y" == some (6,0)
-- Row backgrounds paint under each cell: a table with a coloured row draws a rectangle.
#guard ((render "<table><tr style='background:red'><td>A</table>" "").toOption.map fun r => r.1.tree.length) ==
  ((render "<table><tr><td>A</table>" "").toOption.map fun r => r.1.tree.length+1)

end L4Factoidal.Rendering.TableLayoutTests
