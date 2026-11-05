import L4Factoidal.Rendering.Layout
import L4Factoidal.Rendering.Links

namespace L4Factoidal.Rendering.Tests
open DOM CSS Layout
private def font : FontProfile :=
  {family := "layout-test-monospace",unitsPerEm := 7,advance := 6, ascent := 7,descent := 0,outline := fun _ => [.rect 0 0 5 7],admits := fun n => n >= 32 && n <= 126}
private def noSVG : Embedding := fun _ _ _ _ => throw "unsupported SVG test embedding"
private def run (html css : String) (textScale : Float := 1) : Except String (Scene × Array Box) := do
  let dom := DOM.parseHtmlDocument html
  Layout.render dom (← CSS.parse css) font noSVG 120 100 textScale
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

private def computedAt (html css id : String) (textScale : Float := 1) : Except String Computed := do
  let dom := DOM.parseHtmlDocument html
  let some idx := dom.getElementById 0 id | throw "test id missing"
  let styles ← CSS.computeAll dom (← CSS.parse css) textScale
  return styles[idx]!
#guard ((computedAt "<div id='x' class='a b c d e f g h i j k'></div>"
  "#x{color:red}.a.b.c.d.e.f.g.h.i.j.k{color:blue}" "x").toOption.map fun s => s.color.r) == some 1
#guard ((computedAt "<div id='x'></div>"
  "div{background-color:blue;background:red}" "x").toOption.map fun s => s.background.map (·.r)) == some (some 1)
#guard ((computedAt "<div id='x' style='color:blue'></div>"
  "#x{color:red!important}" "x").toOption.map fun s => s.color.r) == some 1
#guard ((computedAt "<div style='font-size:10px;line-height:2'><span id='x' style='font-size:20px'></span></div>"
  "" "x").toOption.map (·.lineHeight)) == some 40

-- Reader scaling must reflow text at the unchanged CSS width, and must not
-- compound once per ancestor. These assertions inspect the actual Lean scene.
#guard ((run "<div>AA BB</div>" (css ++ "div{width:48px}") 1).toOption.map
  fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.y))) == some [[0,0],[0,0]]
#guard ((run "<div>AA BB</div>" (css ++ "div{width:48px}") 2).toOption.map
  fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.y))) == some [[0,0],[14,14]]
#guard ((computedAt "<div style='font-size:10px;line-height:2'><span><b id='x'>A</b></span></div>"
  "" "x" 1.5).toOption.map fun s => (s.fontSize,s.lineHeight)) == some (15,30)
#guard ((computedAt "<div style='font-size:10px;line-height:18px'><span id='x'>A</span></div>"
  "" "x" 1.5).toOption.map fun s => (s.fontSize,s.lineHeight)) == some (15,27)
#guard ((run "<div>A</div>" css 0.49).toOption.isNone)
#guard ((run "<div>A</div>" css 2.51).toOption.isNone)

private def paddingAt (source : String) := (computedAt "<div id='x'></div>" source "x").toOption.map
  (fun s => (s.padding.top,s.padding.right,s.padding.bottom,s.padding.left))
#guard paddingAt "div{padding-top:1px;padding-right:2px;padding-bottom:3px;padding-left:4px}" == some (1,2,3,4)
#guard paddingAt "div{padding-left:9px;padding:1px}" == some (1,1,1,1)
#guard paddingAt "div{padding:1px;padding-left:9px}" == some (1,1,1,9)
#guard paddingAt "div{padding-left:9px!important;padding:1px}" == some (1,1,1,9)
#guard paddingAt "div{padding-left:9px;padding:1px!important}" == some (1,1,1,1)
#guard paddingAt "#x{padding-left:9px}div{padding:1px}" == some (1,1,1,9)
#guard paddingAt "div{padding:1px 2px 3px 4px}" == some (1,2,3,4)
#guard ((computedAt "<div id='x'></div>" "div{margin-top:1px;margin-right:2px;margin-bottom:3px;margin-left:4px}" "x").toOption.map
  (fun s => (s.margin.top,s.margin.right,s.margin.bottom,s.margin.left))) == some (1,2,3,4)
#guard ((computedAt "<div id='x'></div>" "div{margin-left:9px;margin:1px 2px 3px}" "x").toOption.map
  (fun s => (s.margin.top,s.margin.right,s.margin.bottom,s.margin.left))) == some (1,2,3,2)
#guard ((run "<div style='padding-bottom:-1px'>A</div>" css).toOption.isNone)
#guard ((run "<div style='margin-left:-1px'>A</div>" css).toOption.isNone)
#guard ((run "<div style='padding:1px -2px'>A</div>" css).toOption.isNone)
#guard ((run "<div style='padding-left:3px;padding-top:2px'>A</div>" css).toOption.bind
  (fun r => r.1.glyphRuns[0]? >>= fun g => g.glyphs[0]? |>.map (fun p => (p.x,p.y)))) == some (3,2)
#guard ((run "<div style='height:7px;padding-bottom:3px'>A</div><div>B</div>" css).toOption.bind
  (fun r => r.1.glyphRuns[1]? >>= fun g => g.glyphs[0]? |>.map (·.y))) == some 10

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

private def links := run "<div><a id='target' href='https://example.test/link'>AA BB CC</a><a>Plain</a></div>" css
#guard (links.toOption.map fun r => r.1.links.size) == some 3
#guard (links.toOption.map fun r => r.1.links.toList.map (fun a => (a.x,a.y,a.width))) == some [(0,0,12),(0,7,12),(0,14,12)]
#guard (links.toOption.bind fun r => hitLink r.1.links.toList 3 8 |>.map (·.href)) == some "https://example.test/link"
#guard (links.toOption.bind fun r => hitLink r.1.links.toList 18 14) |>.isNone
private def spacedLink := run "<div style='width:60px'><a href='url'>AA BB</a></div>" css
#guard (spacedLink.toOption.map fun r => r.1.links.size) == some 3
#guard (spacedLink.toOption.bind fun r => hitLink r.1.links.toList 14 3 |>.map (·.href)) == some "url"
#guard ((computedAt "<a id='x' href='url'>AA</a>" "" "x").toOption.map fun s => (s.color.b,s.underline)) == some (1,true)
#guard ((computedAt "<a id='x' href='url'>AA</a>" "a{color:red}" "x").toOption.map fun s => (s.color.r,s.decorationColor.map (·.r))) == some (1,some 1)
#guard ((computedAt "<a id='x'>AA</a>" "" "x").toOption.map (·.underline)) == some false
#guard ((computedAt "<a id='x' href=''>AA</a>" "" "x").toOption.map (·.underline)) == some true
#guard ((run "<a href='url' style='visibility:hidden'>AA</a>" css).toOption.map fun r => r.1.links.size) == some 0
#guard ((run "<a href='url' style='display:none'>AA</a>" css).toOption.map fun r => r.1.links.size) == some 0

/-- Overflow affects both paint clips and the Lean link picker. -/
private def clippedLink := run "<div style='height:7px;overflow:clip'><a href='url'>AA BB</a></div>" css
#guard (clippedLink.toOption.map fun r => r.1.links.size) == some 1
#guard (clippedLink.toOption.bind fun r => hitLink r.1.links.toList 3 3 |>.map (·.href)) == some "url"
#guard (clippedLink.toOption.bind fun r => hitLink r.1.links.toList 3 8) |>.isNone
#guard (clippedLink.toOption.map fun r => (Node.lowerList identity [] r.1.tree).all
  (fun p => p.primitive.clips.any (fun c => c.width == 24 && c.height == 7))) == some true
#guard ((run "<div style='height:7px;overflow:visible'><a href='url'>AA BB</a></div>" css).toOption.map fun r => r.1.links.size) == some 2
#guard ((run "<body style='overflow:clip'>A</body>" css).toOption.isNone)
#guard ((run "<span style='overflow:clip'>A</span>" css).toOption.isNone)
#guard ((run "<svg style='padding:1px'></svg>" css).toOption.isNone)
#guard ((run "<svg style='height:50%'></svg>" css).toOption.isNone)
#guard ((computedAt "<svg id='x' style='fill:red;stroke:blue'></svg>" "" "x").toOption.isSome)
#guard ((computedAt "<svg id='x'><rect style='fill:red'/></svg>" "rect{fill:blue}" "x").toOption.isNone)
#guard ((computedAt "<svg id='x' color='red'></svg>" "" "x").toOption.map (·.color.r)) == some 1
#guard ((computedAt "<svg id='x' color='red' style='color:blue'></svg>" "svg{color:green!important}" "x").toOption.map (·.color.g)) == some (128/255)

private def svgDimensions (attributes css : String) : Except String (Float × Float) := do
  let dom := DOM.parseHtmlDocument ("<svg id='s' " ++ attributes ++ "></svg>")
  let some id := dom.getElementById 0 "s" | throw "SVG sizing target missing"
  let styles ← CSS.computeAll dom (← CSS.parse css)
  svgSize (dom.get id) styles[id]! 120
#guard (svgDimensions "height='200' viewBox='0 0 100.5 100'" "").toOption == some (201,200)
#guard (svgDimensions "width='80' viewBox='0 0 2 1'" "").toOption == some (80,40)
#guard (svgDimensions "height='20px' viewBox='0,0,2,1'" "").toOption == some (40,20)
#guard (svgDimensions "viewBox='0 0 2 1'" "").toOption == some (120,60)
#guard (svgDimensions "height='20' viewBox='0 0 2 1'" "svg{height:30px}").toOption == some (60,30)
#guard (svgDimensions "width='80' height='20' viewBox='0 0 2 1'" "svg{width:auto}").toOption == some (40,20)
#guard (svgDimensions "viewBox='0 0 2 1'" "svg{width:50%}").toOption == some (60,30)
#guard (svgDimensions "width='80' height='20' viewBox='0 0 2 1'" "").toOption == some (80,20)
#guard (svgDimensions "height='20' viewBox='0 0 0 1'" "").toOption == some (300,20)
#guard (svgDimensions "height='20' viewBox='0 0 -2 1'" "").toOption == some (300,20)
#guard (svgDimensions "" "").toOption == some (300,150)
private def svgFlow (display : String) : Except String (List (Float × Float)) := do
  let dom := DOM.parseHtmlDocument "<svg height='200' viewBox='0 0 100.5 100'></svg>"
  let (_,boxes) ← Layout.render dom (← CSS.parse ("body{margin:0}svg{display:" ++ display ++ "}")) font (fun _ _ _ _ => .ok []) 800 600
  return boxes.toList.filterMap (fun box => if (dom.get box.source).ns == some DOM.svgNS then some (box.width,box.height) else none)
#guard (svgFlow "inline").toOption == some [(201,200)]
#guard (svgFlow "block").toOption == some [(201,200)]

/-- Content and clip frames compose independently under the parent frame. -/
private def framedClip : Node := .group (some "parent") ⟨1,0,0,1,10,20⟩
  [.clipped (some "viewport") ⟨2,0,0,3,0,0⟩ ⟨0,0,5,7,⟨1,0,0,1,3,4⟩⟩
    [.paint ⟨some 9,{geometry := .rect 0 0 1 1}⟩]]
private def framedPaint := (framedClip.lower identity []).head?
#guard (framedPaint.map fun p => (p.primitive.transform.a,p.primitive.transform.d,
  p.primitive.transform.e,p.primitive.transform.f)) == some (2,3,10,20)
#guard (framedPaint.bind fun p => p.primitive.clips.head? |>.map
  (fun c => (c.transform.e,c.transform.f,c.width,c.height))) == some (13,24,5,7)
#guard (framedPaint.map fun p => (p.source,p.primitive.groupPath)) == some (some 9,[some "parent",some "viewport"])
#print axioms anchorAncestor_is_anchor
#print axioms hitLink_mem

#print axioms Node.lower_eq_lowerTR
#print axioms Node.lowerList_eq_lowerListTR
#print axioms Node.lowerList_append
end L4Factoidal.Rendering.Tests
