import L4Factoidal.Rendering.SfntProfile

/-! Base64 of font files. `labs/demos/foafnaut/native_html_test.ts` draws a real
font through the engine; `outline-compare.sh` checks its outlines against FreeType. -/
namespace L4Factoidal.Rendering.SfntProfileTests
open SfntProfile

private def bytes (s : String) : Option (List UInt8) := (decodeBase64 s).map (·.toList)

#guard bytes "" == some []
#guard bytes "TWFu" == some [77,97,110]
#guard bytes "TWE=" == some [77,97]
#guard bytes "TQ==" == some [77]
#guard bytes "/+8A" == some [255,239,0]
#guard bytes "TWF" == none
#guard bytes "TW!u" == none
#guard bytes "T=Fu" == none

-- The word memo takes only drawn text: never the text of script, style, template,
-- noscript or title (issue 1268: a JSON script of one long word cost seconds).
private def memoWords (html : String) : List String :=
  (wordsOf (DOM.parseHtmlDocument html)).toList
private def page : String :=
  "<!doctype html><html><head><title>Tab name</title><style>p{color:red}</style>" ++
  "<script type=application/json>{\"long\":\"xxxxxxxxxxxxxxxxxxxxxxxx\"}</script></head><body>" ++
  "<p>shown words</p><noscript>fallback text</noscript><template><p>inert content</p></template>" ++
  "<svg><style>.a{}</style><text>drawn</text></svg><script>var hidden = 1;</script></body></html>"
#guard memoWords page == ["drawn","shown","words"]
#guard ["Tab","name","p{color:red}","fallback","inert","content","var","hidden"].all (!(memoWords page).contains ·)
#guard memoWords "<p>a <b>b</b></p><title>t</title>" == ["a","b"]

end L4Factoidal.Rendering.SfntProfileTests
