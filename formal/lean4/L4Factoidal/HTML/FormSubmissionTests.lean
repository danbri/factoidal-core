/-
L4Factoidal.HTML.FormSubmissionTests — build-time checks (`#guard`) of
`HTML.FormSubmission`: the fast path (`WHATWG.URL.percentEncodeAfterEncoding`, one
encode-or-fail run per unencodable code point) agrees with the spec-level composition
(`componentSpec`: the encoder in mode html, then `encodeByte` per byte) for every
encoding that has an encoder, on encodable and unencodable code points; and the plan of a
GET form as the WPT `encoding/*-encode-form*` pages make it.
-/
import L4Factoidal.HTML.FormSubmission
import L4Factoidal.DOM.OfHtml

namespace L4Factoidal.HTML.FormSubmissionTests
open L4Factoidal.HTML.FormSubmission
open L4Factoidal.WHATWG.Encoding (Encoding getEncoding)

/-- Inputs with ASCII, the separators, a space, a `+`, CJK, Hangul, a symbol, a code point
above the BMP and U+FFFD: most are unencodable in some legacy encoding. -/
def samples : List String :=
  ["a b+c&d=e", "¥‾−", "一二,三", "가힣", "€é",
   "𠀀x", "�", "　", "｡ﾟ", ""]

-- The fast path is the specification's composition, in every encoding with an encoder.
#guard Encoding.all.all fun e =>
  (L4Factoidal.WHATWG.Encoding.getEncoder e).isNone || samples.all fun s => component e s == componentSpec e s

-- An unencodable code point is its numeric character reference, percent-encoded.
#guard component .shift_jis "가" == "%26%2344032%3B"
#guard component .euc_kr "丂" == "%EA%B2%95" || component .euc_kr "丂" == "%26%2319970%3B"
#guard component .iso_2022_jp "一가" == "%1B%24B0l%1B%28B%26%2344032%3B"
#guard component .utf_8 "a b" == "a+b"

-- Selecting the form's encoding (HTML §4.10.21.5).
#guard pickEncoding (some "  bogus euc-jp ") .utf_8 == .euc_jp
#guard pickEncoding (some "bogus") .shift_jis == .utf_8
#guard pickEncoding none .big5 == .big5
#guard pickEncoding (some "utf-16le") .utf_8 == .utf_8

-- Converting to name-value pairs (§4.10.21.6).
#guard normalizeLineBreaks "a\rb\nc\r\nd" == "a\r\nb\r\nc\r\nd"

/-- A form as `encoding/resources/encode-form-common.js` makes it. -/
def page : L4Factoidal.DOM.Dom := L4Factoidal.DOM.parseHtmlDocument
  "<!doctype html><meta charset=euc-jp><iframe name=frame-0></iframe>\
   <form method=GET action=/common/blank.html accept-charset=euc-jp target=frame-0>\
   <input name=input-0 value=\"一,二가\"></form>"

def formIn (d : L4Factoidal.DOM.Dom) : Nat := ((d.treeOrder 0).find? fun k => L4Factoidal.DOM.Forms.isHtml d k ["form"]).getD 0
def formNode : Nat := formIn page
def planOf (src url : String) : Option Plan :=
  let d := L4Factoidal.DOM.parseHtmlDocument src
  plan d (formIn d) none url .utf_8

#guard plan page formNode none "http://web-platform.test/encoding/x.html" .utf_8 ==
  some { target := "frame-0",
         url := "http://web-platform.test/common/blank.html?input-0=%B0%EC%2C%C6%F3%26%2344032%3B" }

-- POST does not navigate here; a missing action is the document's URL.
#guard planOf "<form method=post><input name=a value=b></form>" "http://x.test/p" == none
#guard (planOf "<form><input name=a value='b c'><input type=checkbox name=k>\
  <input type=checkbox name=c checked><input name=d disabled value=x><button name=s value=v></button></form>"
  "http://x.test/p?q#f").map (·.url) == some "http://x.test/p?a=b+c&c=on#f"
#guard (planOf "<form action='javascript:x'><input name=a></form>" "http://x.test/") == none

end L4Factoidal.HTML.FormSubmissionTests
