import L4Factoidal.Rendering.Layout
namespace L4Factoidal.Rendering.FontLayoutTests
open FontData FontProvider Layout DOM
private def outline (id : Nat) : Outline :=
  ⟨id,#[.move 0 800,.line 500 800,.line 500 (-200),.line 0 (-200),.close]⟩
private def shaped (text : String) (glyphs : Array ShapedGlyph) (outlines : Array Outline) (advance : Float) : ShapedWord := {
  text,fontSha256 := String.ofList (List.replicate 64 'a'),fontPath := "test-font",faceIndex := 0,
  family := "TestShape",style := "Regular",metrics := ⟨1000,800,-200,0⟩,
  direction := "ltr",script := "Latn",language := "en",harfbuzzVersion := "test",freeTypeVersion := "test",
  pixelSize := 20,glyphs,outlines,bitmaps := #[],advance}
private def fi := shaped "fi" #[⟨77,0,0,2,500,0,50,10⟩] #[outline 77] 500
private def aa := shaped "AA" #[⟨10,0,0,1,500,0,0,0⟩,⟨10,1,1,2,500,0,0,0⟩] #[outline 10] 1000
private def space := shaped " " #[⟨3,0,0,1,200,0,0,0⟩] #[⟨3,#[]⟩] 200
private def noSVG : Embedding := fun _ _ _ _ => throw "unsupported SVG in font-layout test"
private def run (text : String := "fi AA") (extra : String := "") : Except String (Scene × Array Box) := do
  let face ← Face.make #[fi,aa,space]
  let dom := DOM.parseHtmlDocument ("<div><a href='target'>" ++ text ++ "</a></div>")
  let rules ← CSS.parse ("body{margin:0;font-family:TestShape;font-size:20px;line-height:20px}div{width:25px}" ++ extra)
  Layout.render dom rules (.ofFace face) noSVG 100 100
#guard (run).toOption.isSome
#guard ((run).toOption.map fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.index))) == some [[77],[10,10]]
#guard ((run).toOption.map fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (fun p => (p.clusterStart,p.clusterEnd)))) == some [[(0,2)],[(3,4),(4,5)]]
#guard ((run).toOption.map fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.y))) == some [[(-0.2 : Float)],[20,20]]
#guard ((run).toOption.map fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.x))) == some [[1],[0,10]]
#guard ((run "fi AA" "div{width:40px}").toOption.map fun r => r.1.glyphRuns.toList.map (fun g => g.glyphs.toList.map (·.x))) == some [[1],[14,24]]
#guard ((run).toOption.map fun r => r.1.links.size) == some 2
#guard ((run).toOption.bind fun r => hitLink r.1.links.toList 2 21 |>.map (·.href)) == some "target"
#guard ((run "fi AA" "div{width:40px}").toOption.map fun r => r.1.links.size) == some 3
#guard ((run "ZZ").toOption.isNone)
#guard ((run "fi" "body{font-family:OtherFace}").toOption.isNone)
#guard ((run "fi" "body{font-size:21px}").toOption.isNone)
#guard ((run "fi" "body{font-size:20.5px}").toOption.isNone)
private def strutScene (html : String) : Except String (DOM.Dom × Scene × Array Box) := do
  let face ← Face.make #[fi,aa,space]
  let dom := DOM.parseHtmlDocument html
  let rules ← CSS.parse "body{margin:0;font-family:TestShape;font-size:20px;line-height:20px}"
  let embedding : Embedding := fun _ _ _ _ => pure []
  let (scene,boxes) ← Layout.render dom rules (.ofFace face) embedding 100 100
  return (dom,scene,boxes)
private def svgBaseline : Except String Float := do
  let (dom,_,boxes) ← strutScene "<svg id='icon' width='10' height='10'></svg>"
  let some id := dom.getElementById 0 "icon" | throw "missing icon"
  let some box := boxes.find? (fun box => box.source == id) | throw "missing icon box"
  return box.y
#guard svgBaseline.toOption == some 6
#guard ((strutScene "<div><br><br>AA</div>").toOption.bind fun (_,scene,_) =>
  scene.glyphRuns[0]? >>= fun run => run.glyphs[0]? |>.map (·.y)) == some 40
end L4Factoidal.Rendering.FontLayoutTests
