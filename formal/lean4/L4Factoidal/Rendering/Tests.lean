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
#guard ((run "<div>A</div>" (css ++ "div{margin:5px}")).toOption.isSome)
#guard ((run "<span style='background:red'>A</span>" css).toOption.isSome)
#guard ((run "<div style='font-family:Ahem'>A</div>" css).toOption.isSome)
#guard ((run "<div>λ</div>" css).toOption.isSome)

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
-- No largest text scale: 2.51 and 20 lay out.
#guard ((run "<div>A</div>" css 2.51).toOption.isSome)
#guard ((run "<div>A B C</div>" css 20).toOption.isSome)
#guard ((run "<div>A</div>" css (1/0)).toOption.isNone)

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
#guard ((run "<div style='padding-bottom:-1px'>A</div>" css).toOption.isSome)
#guard ((run "<div style='margin-left:-1px'>A</div>" css).toOption.isSome)
#guard ((run "<div style='padding:1px -2px'>A</div>" css).toOption.isSome)
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
-- HTML §15.3.4: an unvisited hyperlink is #0000EE and underlined.
#guard ((computedAt "<a id='x' href='url'>AA</a>" "" "x").toOption.map fun s => ((s.color.b*255).round,s.color.r,s.underline)) == some (238,0,true)
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
#guard ((run "<body style='overflow:clip'>A</body>" css).toOption.isSome)
#guard ((run "<span style='overflow:clip'>A</span>" css).toOption.isSome)
#guard ((run "<svg style='padding:1px'></svg>" css).toOption.isNone)
#guard ((run "<svg style='height:50%'></svg>" css).toOption.isNone)
#guard ((computedAt "<svg id='x' style='fill:red;stroke:blue'></svg>" "" "x").toOption.isSome)
#guard ((computedAt "<svg id='x'><rect style='fill:red'/></svg>" "rect{fill:blue}" "x").toOption.isSome)
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

-- CSS error handling: what is not understood is dropped, the rest still applies.
private def rules (source : String) : Nat := ((CSS.parse source).toOption.map List.length).getD 999
#guard rules ".a > b{color:red} p{color:blue}" == 1
#guard rules "@media (max-width: 800px) { .a { color: red } } p{color:blue}" == 1
-- `@media` blocks of a media type apply for that type only (issue 1268, printing).
private def rulesFor (medium source : String) : Nat := ((CSS.parseFor medium source).toOption.map List.length).getD 999
#guard rulesFor "print" "@media print { .a { color: red } h2 { break-before: page } } p{color:blue}" == 3
#guard rules "@media print { .a { color: red } } p{color:blue}" == 1
#guard rules "@media screen, projection { .a { color: red } } p{color:blue}" == 2
#guard rulesFor "print" "@media only print, (max-width:1px) { p{color:red} }" == 1
#guard rulesFor "print" "@media not print { p{color:red} } @media all { p{color:blue} }" == 1
#guard CSS.mediaMatches "print" "all" && !CSS.mediaMatches "screen" "print" && !CSS.mediaMatches "print" "print and (color)"
#guard rules "@import 'x.css'; @charset \"utf-8\"; p{color:blue}" == 1
#guard rules "a:focus, p{color:red} p{color:blue}" == 1
#guard rules "a:hover, p{color:red} p{color:blue}" == 2
#guard rules "p{color:blue" == 1
#guard rules "p{color:blue} /* never closed" == 1
#guard rules "} p{content:'}'}" == 1
#guard ((CSS.declarations "background:url(http://x.org/a.png);color:;nonsense;width:1px").toOption.map List.length) == some 3
-- Old pages: lists, definition lists, images, blocks inside links, and CSS we do not lay out.
#guard (run "<ul><li>A<li>B</ul><ol><li>C</ol>" css) matches .ok _
#guard (run "<dl><dt>A<dd><p>B</dl><a href=x><h3>C</h3></a>" css) matches .ok _
#guard (run "<img src=a.png alt=A><img src=b.png>" css) matches .ok _
#guard (run "<table><tr><td>A<td>B</table><hr><pre>A\nB</pre>" css) matches .ok _
#guard (run "<div style='display:grid;gap:1px'>A</div>" (css ++ ".a > div{color:red} div{font-family:Arial,serif}")) matches .ok _
#guard ((run "<pre>A\nB</pre>" css).toOption.map fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.y)) |>.eraseDups |>.length) == some 2

/-! ### User agent sheet, `:link`, `:visited`, `:hover`, `:active` (issue 1268) -/

/-- The computed style of element `id` with the element state of ids `hover`, `active`
and `visited`, named by their `id` attributes. -/
private def stateAt (html css id : String) (hover active : Option String := none) (visited : List String := []) :
    Except String Computed := do
  let dom := DOM.parseHtmlDocument html
  let some idx := dom.getElementById 0 id | throw "test id missing"
  let named := fun (name : String) => dom.getElementById 0 name
  let state : ElementState := {hover := hover.bind named, active := active.bind named, visited := visited.filterMap named}
  let styles ← CSS.computeAll dom (← CSS.parse css) 1 state
  return styles[idx]!
private def rgb255 (c : Color) : Nat × Nat × Nat :=
  ((c.r*255).round.toUInt32.toNat,(c.g*255).round.toUInt32.toNat,(c.b*255).round.toUInt32.toNat)
private def page := "<p><a id='a' href='u'><span id='s'>AA</span></a> <a id='b'>B</a> <button id='k'>OK</button></p>"
#guard userAgentRules.length == 7
#guard ((stateAt page "" "a").toOption.map (rgb255 ·.color)) == some (0,0,238)
#guard ((stateAt page "" "a" (visited := ["a"])).toOption.map fun s => (rgb255 s.color,s.underline)) == some ((85,26,139),true)
-- `:active` on the link, or on a descendant of it (Selectors 4 §9.2), gives #FF0000.
#guard ((stateAt page "" "a" (active := some "a")).toOption.map (rgb255 ·.color)) == some (255,0,0)
#guard ((stateAt page "" "a" (active := some "s")).toOption.map (rgb255 ·.color)) == some (255,0,0)
#guard ((stateAt page "" "a" (active := some "s") (visited := ["a"])).toOption.map (rgb255 ·.color)) == some (255,0,0)
-- An `a` with no href is not a link, active or not.
#guard ((stateAt page "" "b" (active := some "b")).toOption.map fun s => (rgb255 s.color,s.underline)) == some ((0,0,0),false)
-- Author rules win over the user agent origin, whatever the specificity.
#guard ((stateAt page "a{color:green}" "a" (active := some "a")).toOption.map (rgb255 ·.color)) == some (0,128,0)
-- `:hover` matches the designated element and its ancestors only.
#guard ((stateAt page "a:hover{color:red}" "a" (hover := some "s")).toOption.map (rgb255 ·.color)) == some (255,0,0)
#guard ((stateAt page "span:hover{color:red}" "s" (hover := some "a")).toOption.map (rgb255 ·.color)) == some (0,0,238)
-- A pseudo-class counts as a class in specificity.
#guard ((stateAt "<p id='x' class='c'>A</p>" ".c:hover{color:red} .c{color:green}" "x" (hover := some "x")).toOption.map (rgb255 ·.color)) == some (255,0,0)
#guard ((stateAt "<p id='x' class='c'>A</p>" ".c:hover{color:red} .c{color:green}" "x").toOption.map (rgb255 ·.color)) == some (0,128,0)
-- `:any-link` matches visited and unvisited links.
#guard ((stateAt page ":any-link{color:red}" "a" (visited := ["a"])).toOption.map (rgb255 ·.color)) == some (255,0,0)
-- A rule that matches only through `:visited` sets colours only.
#guard ((stateAt page "a:visited{color:red;display:none}" "a" (visited := ["a"])).toOption.map fun s => (rgb255 s.color,s.display == .inline)) == some ((255,0,0),true)
#guard ((stateAt page "a:link{display:none}" "a").toOption.map (·.display == .none)) == some true
-- An unknown pseudo-class drops its rule; the other rules stand.
#guard ((stateAt page "a:focus{color:red} a{color:green}" "a" (active := some "a")).toOption.map (rgb255 ·.color)) == some (0,128,0)
-- HTML §15.5.4: a button is an inline-block with a raised border; pressed, it is sunken and darker.
#guard ((stateAt page "" "k").toOption.map fun s => (s.display == .inlineBlock,s.borderStyle == .outset,s.borderEdges.top,s.background.map rgb255)) == some (true,true,2,some (239,239,239))
#guard ((stateAt page "" "k" (active := some "k")).toOption.map fun s => (s.borderStyle == .inset,s.background.map rgb255)) == some (true,some (200,200,200))
#guard ((stateAt page "" "k" (hover := some "k")).toOption.map fun s => s.background.map rgb255) == some (some (229,229,229))
#guard ((stateAt "<p id='x' style='border:1px solid red'>A</p>" "" "x").toOption.map fun s => (s.borderEdges.left,s.borderColor.map rgb255)) == some (1,some (255,0,0))
#guard ((stateAt "<p id='x' style='border-width:4px'>A</p>" "" "x").toOption.map (·.borderEdges.left)) == some 0

private def runState (html css : String) (active : Option String := none) : Except String (Scene × Array Box) := do
  let dom := DOM.parseHtmlDocument html
  Layout.render dom (← CSS.parse css) font noSVG 120 100 1 {active := active.bind (dom.getElementById 0 ·)}
private def boxOf (html css id : String) : Option (Float × Float) :=
  let dom := DOM.parseHtmlDocument html
  match dom.getElementById 0 id, runState html css with
  | some idx, .ok (_,boxes) => (boxes.find? (·.source == idx)).map fun b => (b.width,b.height)
  | _, _ => none
private def fills (r : Except String (Scene × Array Box)) : List (Nat × Nat × Nat) :=
  match r with
  | .ok (scene,_) => scene.tree.flatMap fun
      | .paint p => match p.primitive.style.fill with | .solid c => [rgb255 c] | _ => []
      | .group _ _ kids => kids.flatMap fun
          | .paint p => match p.primitive.style.fill with | .solid c => [rgb255 c] | _ => []
          | .group _ _ deeper => deeper.flatMap fun
            | .paint p => match p.primitive.style.fill with | .solid c => [rgb255 c] | _ => []
            | _ => []
          | _ => []
      | _ => []
  | .error _ => []
-- The button's border box: 2+6 + two glyphs of 6 + 6+2 wide; 2+1 + 7 + 1+2 high.
#guard boxOf "<button id='k'>OK</button>" css "k" == some (28,13)
#guard ((runState "<button>OK</button>" css).toOption.map fun r => r.1.glyphRuns.size) == some 1
-- A block border adds to the border box.
#guard boxOf "<div id='d' style='border:1px solid red'>A</div>" css "d" == some (26,9)
-- Pressed and unpressed buttons paint different colours: the face and the bevel.
#guard (fills (runState "<button id='k'>OK</button>" css)).contains (239,239,239)
#guard !(fills (runState "<button id='k'>OK</button>" css (some "k"))).contains (239,239,239)
#guard (fills (runState "<button id='k'>OK</button>" css (some "k"))).contains (200,200,200)
#guard fills (runState "<button id='k'>OK</button>" css) != fills (runState "<button id='k'>OK</button>" css (some "k"))
-- A pressed link paints its glyphs and underline red.
#guard (fills (runState "<a id='a' href='u'>AA</a>" css (some "a"))).contains (255,0,0)
#guard !(fills (runState "<a id='a' href='u'>AA</a>" css)).contains (255,0,0)

end L4Factoidal.Rendering.Tests
