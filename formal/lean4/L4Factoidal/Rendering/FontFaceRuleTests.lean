import L4Factoidal.Rendering.FontFaceRule

/-! Checks of `@font-face` reading and font matching (CSS Fonts 4 §4 and §5). -/
namespace L4Factoidal.Rendering.FontFaceRuleTests
open L4Factoidal.Rendering FontFaceRule

-- Family lists (§2.1).
#guard CSS.familyNames "\"Spinal Tap\", serif" == some ["Spinal Tap","serif"]
#guard CSS.familyNames "Noto  Sans" == some ["Noto Sans"]
#guard CSS.familyNames "'A', B C, monospace" == some ["A","B C","monospace"]
#guard CSS.familyNames "a,,b" == none
#guard CSS.familyNames "\"open" == none
#guard CSS.familyNames "x\\y" == none
#guard CSS.familyList (CSS.familyValue ["Spinal Tap","serif"]) == ["Spinal Tap","serif"]
#guard CSS.familyValue ["Noto Sans"] == "Noto Sans"

-- `@font-face` blocks, also in a matching `@media` block, never from other at-rules.
#guard (CSS.fontFaceBlocks "screen" "@font-face{font-family:A;src:url(a.ttf)} p{color:red}").length == 1
#guard (CSS.fontFaceBlocks "screen" "@media print{@font-face{font-family:A;src:url(a.ttf)}}").length == 0
#guard (CSS.fontFaceBlocks "screen" "@media screen{@font-face{font-family:A;src:url(a.ttf)}}").length == 1
#guard (CSS.fontFaceBlocks "screen" "@supports (x:y){@font-face{font-family:A;src:url(a.ttf)}}").length == 0
-- The rules of a sheet are not changed by an `@font-face` in it.
#guard ((CSS.parse "@font-face{font-family:A;src:url(a.ttf)} p{color:red}").toOption.map (·.length)) == some 1

-- `src` (§4.3): readable formats only, in order; `local()` never matches.
#guard sourceURL "url(a.ttf)" == some "a.ttf"
#guard sourceURL "url(\"a b.otf\") format(\"opentype\")" == some "a b.otf"
#guard sourceURL "url(a.woff2) format(\"woff2\")" == none
#guard sourceURL "local(Foo)" == none
#guard sourceURL "url(a.ttf) format(truetype)" == some "a.ttf"

-- `unicode-range` (§4.6) and `<urange>`.
#guard urange "U+0-7F" == some (0,0x7F)
#guard urange "u+4??" == some (0x400,0x4FF)
#guard urange "U+308" == some (0x308,0x308)
#guard urange "U+110000" == none
#guard urange "U+4?0" == none
#guard rangeList "U+0-FF, U+300-36F" == some [(0,0xFF),(0x300,0x36F)]

#guard weightRange "bold" == some (700,700)
#guard weightRange "100 900" == some (100,900)
#guard weightRange "1001" == none
#guard styleValue "oblique 10deg" == some "oblique"

private def sheet : String :=
  "@font-face { font-family: \"Spinal\"; src: url(fonts/blackletter.ttf) format(\"truetype\"); }\n" ++
  "@font-face { font-family: Spinal; font-weight: bold; src: url(fonts/bold.ttf); }\n" ++
  "@font-face { font-family: Greek; src: url(g1.ttf); unicode-range: U+370-3FF; }\n" ++
  "@font-face { font-family: Greek; src: url(g2.ttf); unicode-range: U+0-FF; }\n" ++
  "@font-face { font-family: Broken; src: url(x.woff2) format(woff2); }\n" ++
  "@font-face { src: url(nofamily.ttf); }"

private def faces : Array Face :=
  ofSheets "screen" (fun base url => base ++ url) [("https://example.org/", sheet)]

#guard faces.size == 4
#guard faces[0]!.sources == ["https://example.org/fonts/blackletter.ttf"]
#guard faces[1]!.weight == (700,700)
-- §5.2: weight 400 takes the normal face, not the bold one.
#guard selected faces "spinal" == [0]
#guard selected faces "Spinal" (weight := 700) == [1]
-- Overlapping ranges of one family: the last defined face is tried first.
#guard selected faces "Greek" == [3,2]
#guard faceFor faces [] ["Greek"] 0x3B1 == some 2
#guard faceFor faces [] ["Greek"] 0x41 == some 3
-- A held or generic family before the web family ends the search.
#guard faceFor faces ["noto sans"] ["Noto Sans","Spinal"] 0x41 == none
#guard faceFor faces [] ["Nope","Spinal"] 0x41 == some 0
#guard faceFor faces [] ["serif","Spinal"] 0x41 == none
-- A character outside every range of a family goes on to the next family.
#guard faceFor faces [] ["Greek","Spinal"] 0x5D0 == some 0

-- Lazy loading (§4.8): only faces of rendered text are used.
private def page (body : String) : DOM.Dom := DOM.parseHtmlDocument
  ("<!doctype html><html><head><style>" ++ sheet ++ " h1{font-family:Spinal, serif} .g{font-family:Greek} .n{display:none}</style></head><body>" ++ body ++ "</body></html>")

private def usedIn (body : String) : List Nat :=
  let dom := page body
  let rules := (CSS.parse (sheet ++ " h1{font-family:Spinal, serif} .g{font-family:Greek} .n{display:none}")).toOption.getD []
  match CSS.computeAll dom rules with
  | .ok styles => let used := usedFaces faces ["Noto Sans"] dom styles
    (List.range used.size).filter (used[·]!)
  | .error _ => [99]

#guard usedIn "<p>plain text</p>" == []
#guard usedIn "<h1>Spinal Tap</h1>" == [0]
#guard usedIn "<h1 class=n>Spinal Tap</h1>" == []
#guard usedIn "<p class=g>αβ</p>" == [2]
#guard usedIn "<p class=g>ab</p>" == [3]
-- SVG text takes its family from its own attributes.
#guard usedIn "<svg width=10 height=10><text font-family=\"Spinal\">Tap</text></svg>" == [0]
#guard usedIn "<svg width=10 height=10><g style=\"font-family: Greek\"><text>α</text></g></svg>" == [2]
#guard usedIn "<svg width=10 height=10><text>Tap</text></svg>" == []

end L4Factoidal.Rendering.FontFaceRuleTests
