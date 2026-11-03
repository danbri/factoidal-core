import L4Factoidal.Rendering.FontFace
namespace L4Factoidal.Rendering.FontFaceTests
open FontData FontProvider
private def outline : Outline := ⟨77,#[.move 0 800,.line 500 800,.line 500 (-200),.close]⟩
private def word : ShapedWord := {
  text := "fi",fontSha256 := String.ofList (List.replicate 64 'a'),fontPath := "test-font",faceIndex := 0,
  family := "test-shaped-font",style := "Regular",metrics := ⟨1000,800,-200,0⟩,
  direction := "ltr",script := "Latn",language := "en",harfbuzzVersion := "test",freeTypeVersion := "test",
  pixelSize := 20,glyphs := #[⟨77,0,0,2,500,0,0,0⟩],outlines := #[outline],bitmaps := #[],advance := 500}
private def other := {word with text := "ff"}
#guard (Face.make #[word,other]).toOption.isSome
#guard ((Face.make #[word]).toOption.bind fun f => (f.lookup "fi" 20).toOption |>.map (·.advance)) == some 500
#guard ((Face.make #[word]).toOption.bind fun f => (f.lookup "missing" 20).toOption).isNone
#guard ((Face.make #[word]).toOption.bind fun f => (f.lookup "fi" 21).toOption).isNone
#guard (Face.make #[word,{word with pixelSize := 40}]).toOption.isSome
#guard (Face.make #[]).toOption.isNone
#guard (Face.make #[word,word]).toOption.isNone
#guard (Face.make #[word,{other with fontSha256 := String.ofList (List.replicate 64 'b')}]).toOption.isNone
#guard (Face.make #[word,{other with metrics := ⟨2000,800,-200,0⟩}]).toOption.isNone
#guard (Face.make #[word,{other with outlines := #[⟨77,#[.move 0 800,.line 501 800,.close]⟩]}]).toOption.isNone
#guard (Face.make (Array.replicate 4097 word)).toOption.isNone
#guard (Face.decode "[]").toOption.isNone
#guard (Face.decode "{}").toOption.isNone
#guard (Face.decode "[{\"schema\":\"wrong-font-data-schema\"}]").toOption.isNone
end L4Factoidal.Rendering.FontFaceTests
