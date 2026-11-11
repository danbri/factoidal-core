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

-- UTS #51 §4 presentation of a grapheme cluster (`runsOf` sends an emoji cluster to
-- a colour font for emoji presentation, to a font without colour for text).
private def pres (cs : List Nat) : Option Bool := presentationOf cs.toArray
#guard pres [97] == none                         -- not an emoji
#guard pres [0x1F600] == some true            -- Emoji_Presentation=Yes
#guard pres [0x1F600, 0xFE0E] == some false   -- U+FE0E asks for text
#guard pres [0x2764] == some false              -- Emoji_Presentation=No: text by default
#guard pres [0x2764, 0xFE0F] == some true       -- U+FE0F asks for emoji
#guard pres [49] == some false                   -- a digit is an emoji character, text by default
#guard pres [49, 0xFE0F, 0x20E3] == some true      -- a keycap
#guard pres [0x1F44D, 0x1F3FD] == some true    -- a skin tone
#guard pres [0x1F1EC, 0x1F1E7] == some true    -- a flag
#guard pres [0x1F468, 0x200D, 0x1F469] == some true -- a ZWJ sequence
#guard pres [0x1F3F4, 0xE0067, 0xE0062, 0xE0073, 0xE0063, 0xE0074, 0xE007F] == some true -- tags
-- Plain text pays nothing for emoji: no character from U+2000 is an emoji.
#guard !"Hello, world 123 #*".toList.any fun c => c.toNat ≥ 0x2000 && emojiish c.toNat
#guard emojiish 0x1F600 && emojiish 0xFE0F && emojiish 0x20E3 && !emojiish 0x4E00

end L4Factoidal.Rendering.SfntProfileTests
