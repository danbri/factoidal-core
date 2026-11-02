import L4Factoidal.Rendering.Layout

namespace L4Factoidal.Rendering.Tests
open DOM CSS Layout
private def font : FontProfile :=
  {family := "layout-test-monospace",unitsPerEm := 7,advance := 6, ascent := 7,descent := 0,outline := fun _ => [.rect 0 0 5 7],admits := fun n => n >= 32 && n <= 126}
private def noSVG : Embedding := fun _ _ _ => throw "unsupported SVG test embedding"
private def run (html css : String) : Except String (Scene × Array Box) := do
  let dom := DOM.parseHtmlDocument html
  Layout.render dom (← CSS.parse css) font noSVG 120 100
private def css := "body {margin:0;font-size:7px;line-height:7px} div {width:24px;background:red}"
private def wrapped := run "<div id='box'>AA BB</div>" css
#guard wrapped matches .ok _
#guard (wrapped.toOption.map fun r => r.1.glyphRuns.size) == some 2
#guard (wrapped.toOption.map fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.y))) == some [[0,0],[7,7]]
#guard (wrapped.toOption.map fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.clusterStart))) == some [[0,1],[3,4]]
#guard ((run "<div>AA BB</div>" (css ++ "div{width:60px}")).toOption.map fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.y))) == some [[0,0],[0,0]]
#guard ((run "<div>A</div>" (css ++ "div{display:none}")).toOption.map fun r => r.1.tree.length) == some 0
#guard ((run "<div>A</div>" (css ++ "div{margin:5px}")).toOption.isNone)
#guard ((run "<span style='background:red'>A</span>" css).toOption.isNone)
#guard ((run "<div style='font-family:Ahem'>A</div>" css).toOption.isNone)
#guard ((run "<div>λ</div>" css).toOption.isNone)

private def computedAt (html css id : String) : Except String Computed := do
  let dom := DOM.parseHtmlDocument html
  let some idx := dom.getElementById 0 id | throw "test id missing"
  let styles ← CSS.computeAll dom (← CSS.parse css)
  return styles[idx]!
#guard ((computedAt "<div id='x' class='a b c d e f g h i j k'></div>"
  "#x{color:red}.a.b.c.d.e.f.g.h.i.j.k{color:blue}" "x").toOption.map fun s => s.color.r) == some 1
#guard ((computedAt "<div id='x'></div>"
  "div{background-color:blue;background:red}" "x").toOption.map fun s => s.background.map (·.r)) == some (some 1)
#guard ((computedAt "<div id='x' style='color:blue'></div>"
  "#x{color:red!important}" "x").toOption.map fun s => s.color.r) == some 1
#guard ((computedAt "<div style='font-size:10px;line-height:2'><span id='x' style='font-size:20px'></span></div>"
  "" "x").toOption.map (·.lineHeight)) == some 40

/-- Mutation reaches the real DOM arena: re-rendering recomputes style/layout. -/
private def mutated : Except String (List Float × List Float) := do
  let dom := DOM.parseHtmlDocument "<body style='margin:0;font-size:7px;line-height:7px'><div id='x' style='width:24px'>AA BB</div>"
  let some id := dom.getElementById 0 "x" | throw "missing mutation target"
  let before ← Layout.render dom [] font noSVG 120 100
  let (dom,ok) := dom.setAttribute id "style" "width:60px"
  let _ ← ok.mapError (fun _ => "DOM mutation failed")
  let after ← Layout.render dom [] font noSVG 120 100
  return (before.1.glyphRuns.toList.map (fun g => (g.glyphs[0]?).map (·.y) |>.getD (-1)), after.1.glyphRuns.toList.map (fun g => (g.glyphs[0]?).map (·.y) |>.getD (-1)))
#guard mutated.toOption == some ([0,7],[0,0])

/-- Larger text raises the common baseline before either run is emitted. -/
private def baseline := run "<div style='width:100px'>A <span style='font-size:14px;line-height:14px'>B</span></div>" css
#guard (baseline.toOption.map fun r => r.1.glyphRuns.toList.map (fun g => (g.glyphs[0]?).map (·.y))) == some [some 7,some 0]

#print axioms Node.lower_eq_lowerTR
#print axioms Node.lowerList_eq_lowerListTR
#print axioms Node.lowerList_append
end L4Factoidal.Rendering.Tests
