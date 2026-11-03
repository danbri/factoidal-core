import L4Factoidal.Rendering.FontProvider

namespace L4Factoidal.Rendering.FontProviderTests
open FontData FontProvider
private def outline : Outline := ⟨77,#[.move 0 800,.line 500 800,.line 500 (-200),.line 0 (-200),.close]⟩
private def shaped : ShapedWord := {
  text := "fi",fontSha256 := String.ofList (List.replicate 64 'a'),fontPath := "test-font",faceIndex := 0,
  family := "test-shaped-font",style := "Regular",metrics := ⟨1000,800,-200,0⟩,
  direction := "ltr",script := "Latn",language := "en",harfbuzzVersion := "test",freeTypeVersion := "test",
  pixelSize := 20,glyphs := #[⟨77,0,0,2,500,0,50,10⟩],outlines := #[outline],bitmaps := #[],advance := 500}
#guard (prepare shaped).toOption.isSome
#guard ((prepare shaped).toOption.map (·.advance)) == some 500
#guard ((prepare shaped).toOption.map (·.pixelSize)) == some 20
#guard ((prepare shaped).toOption.map fun word => (word.unitsPerEm,word.ascent,word.descent)) == some (1000,800,200)
#guard ((prepare shaped).toOption.bind fun word => word.glyphs[0]? |>.map
  (fun g => (g.index,g.x,g.y,g.clusterStart,g.clusterEnd))) == some (77,50,(-10 : Float),0,2)
private def points : Except String (List (Float × Float)) := do
  let word ← prepare shaped
  let some g := word.glyphs[0]? | throw "missing test glyph"
  let [.path [contour]] := g.geometry | throw "missing test path"
  return (← contour.toLinear).points.map fun p => (p.x,p.y)
#guard points.toOption == some [(0,0),(500,0),(500,1000),(0,1000)]
private def withMark := prepare {shaped with
  glyphs := #[⟨77,0,0,2,500,0,0,0⟩,⟨88,0,0,2,0,0,-100,100⟩],
  outlines := #[outline,{outline with id := 88}]}
#guard (withMark.toOption.bind fun word => word.glyphs[1]? |>.map
  (fun g => (g.index,g.x,g.y,g.advance,g.clusterStart,g.clusterEnd))) == some (88,400,(-100 : Float),0,0,2)
#guard (prepare {shaped with direction := "rtl"}).toOption.isNone
#guard (prepare {shaped with outlines := #[]}).toOption.isNone
#guard (prepare {shaped with glyphs := #[⟨0,0,0,2,500,0,0,0⟩]}).toOption.isNone
#guard (prepare {shaped with glyphs := #[⟨77,0,0,2,500,1,0,0⟩]}).toOption.isNone
#guard (prepare {shaped with glyphs := #[⟨77,0,0,3,500,0,0,0⟩]}).toOption.isNone
#guard (prepare {shaped with advance := 501}).toOption.isNone
private def quadraticControls : Except String (Float × Float × Float × Float) := do
  let [.path [.path _ [.quadratic control endpoint] true]] ← outlineGeometry 800 ⟨77,#[.move 0 0,.quadratic 1 1 2 2,.close]⟩ | throw "missing quadratic controls"
  return (control.x,control.y,endpoint.x,endpoint.y)
#guard quadraticControls.toOption == some (1,799,2,798)
private def cubicControls : Except String (Float × Float × Float × Float × Float × Float) := do
  let [.path [.path _ [.cubic a b endpoint] true]] ← outlineGeometry 800 ⟨77,#[.move 0 0,.cubic 1 1 2 2 3 3,.close]⟩ | throw "missing cubic controls"
  return (a.x,a.y,b.x,b.y,endpoint.x,endpoint.y)
#guard cubicControls.toOption == some (1,799,2,798,3,797)
#guard ((outlineGeometry 800 ⟨77,#[]⟩).toOption.map List.isEmpty) == some true
#guard (outlineGeometry 800 ⟨77,#[.move 0 0]⟩).toOption.isNone
#guard (outlineGeometry 800 ⟨77,#[.line 0 0]⟩).toOption.isNone
end L4Factoidal.Rendering.FontProviderTests
