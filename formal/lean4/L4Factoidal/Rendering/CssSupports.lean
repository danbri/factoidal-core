/-
L4Factoidal.Rendering.CssSupports — the `CSS` namespace of page scripts: `CSS.supports`
(CSS Conditional Rules 3 §8.1, the `<supports-condition>` grammar of §2) and `CSS.escape`
(CSSOM §2.1 "serialize an identifier").

`supports` answers for what this engine's style profile reads (`CSS.supportsDeclaration`)
and what `DOM.Selectors` parses (`selector(...)`): a page that asks gets the truth about
this engine, not about other browsers.
-/
import L4Factoidal.Rendering.Style
import L4Factoidal.Rendering.SupportsCondition
import L4Factoidal.DOM.Selectors

namespace L4Factoidal.Rendering.CssSupports

/-- `CSS.supports(conditionText)`: the condition, or the text in parentheses as a
declaration (CSS Conditional 3 §8.1). -/
def supportsText (text : String) : Bool :=
  let cs := text.toList
  match condition (cs.length + 2) cs with
  | some v => v
  | none => (declaration cs).getD false

/-- `CSS.escape(ident)`: "serialize an identifier" (CSSOM §2.1). -/
def escape (s : String) : String := Id.run do
  let cs := s.toList
  let mut out := ""
  let hex := fun (c : Char) => "\\" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ " "
  for i in [0:cs.length] do
    let c := cs[i]!
    let n := c.toNat
    if n == 0 then out := out.push (Char.ofNat 0xFFFD)
    else if (1 ≤ n && n ≤ 0x1F) || n == 0x7F then out := out ++ hex c
    else if i == 0 && c.isDigit then out := out ++ hex c
    else if i == 1 && c.isDigit && cs[0]! == '-' then out := out ++ hex c
    else if i == 0 && c == '-' && cs.length == 1 then out := out ++ "\\-"
    else if n ≥ 0x80 || c == '-' || c == '_' || c.isAlphanum then out := out.push c
    else out := out ++ "\\" ++ String.singleton c
  return out

#guard escape "0a" == "\\30 a"
#guard escape "-1x" == "-\\31 x"
#guard escape "-" == "\\-"
#guard escape "a b#c" == "a\\ b\\#c"
#guard escape "\x01" == "\\1 "
#guard supportsText "(display: block)"
#guard supportsText "display: block"
#guard supportsText "(display: grid)"
#guard !supportsText "(display: gridd)"
#guard supportsText "not (display: gridd)"
#guard supportsText "(display: gridd) or (color: red)"
#guard !supportsText "(display: gridd) and (color: red)"
#guard supportsText "selector(div > p)"
#guard !supportsText "(display: block) and (color: red) or (x: y)"
#guard supportsText "(--foo: bar)"
#guard !supportsText "foo(bar)"
#guard CSS.supportsDeclaration "margin" "1px 2px"
#guard CSS.supportsDeclaration "COLOR" "red"
#guard !CSS.supportsDeclaration "color" "red !important"

end L4Factoidal.Rendering.CssSupports
