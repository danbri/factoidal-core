import L4Factoidal.Rendering.FontData
import L4Factoidal.JSON.Serialize

/-! Synthetic protocol fixtures test validation, not font conformance. Actual
HB/FT output is exercised separately using a local font, never bundled here. -/
namespace L4Factoidal.Rendering.FontDataTests
open JSON FontData
private def n (value : Nat) : Json := .number (toString value)
private def s := Json.string
private def glyph (id cluster : Nat) : Json := .object [
  ("id",n id),("cluster",n cluster),("xAdvance",n 500),("yAdvance",n 0),
  ("xOffset",n 0),("yOffset",n 0)]
private def outline (id : Nat) : Json := .object [
  ("id",n id),("commands",.array [.array [s "M",n 0,n 0],
    .array [s "Q",n 1,n 2,n 3,n 4],.array [s "Z"]])]
private def bitmap (id : Nat) : Json := .object [
  ("id",n id),("pixelSize",n 20),("width",n 1),("height",n 1),
  ("left",n 0),("top",n 1),("alpha",.array [n 127])]
private def base : Json := .object [
  ("schema",s "factoidal-font-data-v1"),("fontSha256",s (String.ofList (List.replicate 64 '0'))),
  ("fontPath",s "synthetic-protocol-fixture"),("fontBytes",n 100),("faceIndex",n 0),
  ("family",s "synthetic"),("style",s "regular"),("unitsPerEm",n 1000),
  ("ascender",n 800),("descender",.number "-200"),("lineGap",n 0),
  ("coordinateSystem",s "font units, positive y up"),("clusterUnits",s "UTF-8 byte offsets"),
  ("rasterMode",s "FreeType normal grayscale, no hinting, no embedded bitmap"),
  ("text",s "λA"),("direction",s "ltr"),("script",s "Grek"),("language",s "en"),
  ("harfbuzzVersion",s "test"),("freeTypeVersion",s "test"),("bitmapPixelSize",n 20),
  ("glyphs",.array [glyph 1 0,glyph 2 2]),
  ("outlines",.array [outline 1,outline 2]),("bitmaps",.array [bitmap 1,bitmap 2])]
private def set (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .object fields => .object (fields.map fun (k,v) => (k,if k == key then value else v))
  | _ => j
private def bad (j : Json) : Bool := (decodeValue j).toOption.isNone

#guard (decodeValue base).toOption.isSome
#guard ((decodeValue base).toOption.map fun w => w.glyphs.toList.map (·.clusterChar)) == some [0,1]
#guard ((decodeValue base).toOption.map fun w => w.glyphs.toList.map (·.clusterEndChar)) == some [1,2]
#guard byteOffsetToChar? "λ🙂A" 0 == some 0
#guard byteOffsetToChar? "λ🙂A" 2 == some 1
#guard byteOffsetToChar? "λ🙂A" 6 == some 2
#guard byteOffsetToChar? "λ🙂A" 7 == some 3
#guard byteOffsetToChar? "λ🙂A" 1 == none
#guard byteOffsetToChar? "λ🙂A" 3 == none
#guard (decode base.toString).toOption.isSome
#guard bad (set base "unitsPerEm" (n 0))
#guard bad (set base "bitmapPixelSize" (n 0))
#guard bad (set base "fontSha256" (s "not-a-hash"))
#guard bad (set base "clusterUnits" (s "characters"))
#guard bad (set base "glyphs" (.array [glyph 1 1,glyph 2 2]))
#guard bad (set base "glyphs" (.array [glyph 1 0,glyph 2 3]))
#guard bad (set base "glyphs" (.array [glyph 1 2,glyph 2 0]))
#guard bad (set base "glyphs" (.array [glyph 0 0,glyph 2 2]))
#guard bad (set base "outlines" (.array [outline 1]))
#guard bad (set base "outlines" (.array [outline 1,outline 1]))
#guard bad (set base "bitmaps" (.array [bitmap 1,bitmap 3]))
#guard bad (set base "bitmaps" (.array [set (bitmap 1) "alpha" (.array [n 256]),bitmap 2]))
#guard bad (set base "bitmaps" (.array [set (bitmap 1) "width" (n 2),bitmap 2]))
#guard bad (set base "bitmaps" (.array [set (bitmap 1) "pixelSize" (n 21),bitmap 2]))
#guard bad (set base "outlines" (.array [set (outline 1) "commands" (.array [.array [s "M",n 0,n 0]]),outline 2]))
#guard bad (set base "outlines" (.array [set (outline 1) "commands" (.array [.array [s "L",n 0,n 0]]),outline 2]))
#guard bad (set base "outlines" (.array [set (outline 1) "commands" (.array [.array [s "Q",n 0,n 0]]),outline 2]))
#guard bad (set base "unitsPerEm" (.number "1000.0"))
#guard bad (set base "unitsPerEm" (.number "1e3"))
#guard bad (set base "unitsPerEm" (.number "999999999999999999999999999"))
private def duplicate : Json := match base with
  | .object fields => .object (fields ++ [("schema",s "factoidal-font-data-v1")])
  | other => other
#guard bad duplicate

private def rtl := set (set base "direction" (s "rtl")) "glyphs" (.array [glyph 2 2,glyph 1 0])
#guard (decodeValue rtl).toOption.isSome
#guard ((decodeValue rtl).toOption.map fun w => w.glyphs.toList.map (·.clusterEndChar)) == some [2,1]
private def merged := set base "glyphs" (.array [glyph 1 0,glyph 2 0])
#guard ((decodeValue merged).toOption.map fun w => w.glyphs.toList.map (·.clusterEndChar)) == some [2,2]
private def fallback := set (set (set base "glyphs" (.array [glyph 0 0,glyph 2 2]))
  "outlines" (.array [outline 0,outline 2])) "bitmaps" (.array [bitmap 0,bitmap 2])
#guard (decodeValue fallback false).toOption.isSome
#guard (decodeValue fallback).toOption.isNone
private def empty := set (set (set (set base "text" (s "")) "glyphs" (.array [])) "outlines" (.array [])) "bitmaps" (.array [])
#guard (decodeValue empty).toOption.isSome
end L4Factoidal.Rendering.FontDataTests
