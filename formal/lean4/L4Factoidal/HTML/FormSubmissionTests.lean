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

-- POST is "submit as entity body"; a missing action is the document's URL.
def postOf (src url : String) : Option (String × String × String × String) :=
  (planOf src url).map fun p => (p.method, p.url, p.contentType, String.fromUTF8! p.body)
#guard postOf "<form method=post><input name=a value='b c&'></form>" "http://x.test/p?q" ==
  some ("POST", "http://x.test/p?q", "application/x-www-form-urlencoded", "a=b+c%26")
#guard postOf "<form method=post enctype=text/plain><input name=a value=b><textarea name=t>x
y</textarea></form>" "http://x.test/p" ==
  some ("POST", "http://x.test/p", "text/plain", "a=b\r\nt=x\r\ny\r\n")
#guard postOf "<form method=post enctype=multipart/form-data><input name='a\"b' value=v><input type=file name=f></form>" "http://x.test/p" ==
  some ("POST", "http://x.test/p", "multipart/form-data; boundary=----FoafnautFormBoundary0",
    "------FoafnautFormBoundary0\r\nContent-Disposition: form-data; name=\"a%22b\"\r\n\r\nv\r\n\
     ------FoafnautFormBoundary0\r\nContent-Disposition: form-data; name=\"f\"; filename=\"\"\r\n\
     Content-Type: application/octet-stream\r\n\r\n\r\n------FoafnautFormBoundary0--\r\n")
-- a submit button's formmethod and formenctype win
def buttonPlan (src : String) : Option Plan :=
  let d := L4Factoidal.DOM.parseHtmlDocument src
  let b := (d.treeOrder 0).find? fun k => L4Factoidal.DOM.Forms.isHtml d k ["button"]
  plan d (formIn d) b "http://x.test/" .utf_8
#guard (buttonPlan "<form enctype=text/plain><input name=a value=b><button formmethod=post formenctype=application/x-www-form-urlencoded>").map
  (fun p => (p.method, p.contentType)) == some ("POST", "application/x-www-form-urlencoded")
-- the body is in the form's encoding, an unencodable code point its character reference
#guard (planOf "<form method=post accept-charset=shift_jis enctype=text/plain><input name=a value='あ가'></form>" "http://x.test/").map (·.body.toList) ==
  some ("a=".toUTF8.toList ++ [0x82, 0xA0] ++ "&#44032;\r\n".toUTF8.toList)
-- dialog navigates nowhere; POST to data: sends nothing
#guard planOf "<form method=dialog><input name=a></form>" "http://x.test/" == none
#guard (planOf "<form method=post action='data:,x'><input name=a value=b></form>" "http://x.test/").map (fun p => (p.method, p.url)) == some ("GET", "data:,x")
-- the entry list the script host passes back after the formdata event
#guard (entriesOfWire "s\x00a\\0b\x00c\\\\d\x00f\x00n\x00f.txt\x00text/plain\x00\x01\xff").map (·.size) == some 2
#guard (entriesOfWire "s\x00a\\0b\x00c\\\\d").map (·.map fun (n, v) => (n, v.asText)) == some #[("a\x00b", "c\\d")]
#guard entriesOfWire "s\x00a" == none
#guard let es : Array (String × Value) := #[("a\\\x00", .text "\\0x"), ("f", .file "n" "t" (ByteArray.mk #[0, 92, 255]))]
  entriesOfWire (entriesToWire es) == some es
#guard entriesOfWire "f\x00n\x00f\x00t\x00\u0100" == none
-- where a submission may go
def pg (u : String) (addr : String := "") := L4Factoidal.Net.PageFetch.Page.ofUrl u false addr
def ok (p : L4Factoidal.Net.PageFetch.Page) (pageScheme u : String) (post : Bool) : Bool :=
  match L4Factoidal.WHATWG.URL.parseUrl u with
  | some x => navigationAllowed p pageScheme x post
  | none => false
#guard ok (pg "https://a.test/") "https" "https://b.test/x" true
#guard !ok (pg "https://a.test/") "https" "http://b.test/x" true
#guard !ok (pg "http://a.test/") "http" "http://127.0.0.1/admin" true
#guard !ok (pg "http://a.test/") "http" "http://router.localhost/" false
#guard ok (pg "http://web-platform.test:8000/" "127.0.0.1") "http" "http://127.0.0.1:8000/x" true
#guard ok (pg "http://a.test/") "http" "data:,x" false && !ok (pg "http://a.test/") "http" "data:,x" true
#guard !ok (pg "http://a.test/") "http" "file:///etc/passwd" false
#guard (planOf "<form><input name=a value='b c'><input type=checkbox name=k>\
  <input type=checkbox name=c checked><input name=d disabled value=x><button name=s value=v></button></form>"
  "http://x.test/p?q#f").map (·.url) == some "http://x.test/p?a=b+c&c=on#f"
#guard (planOf "<form action='javascript:x'><input name=a></form>" "http://x.test/") == none

end L4Factoidal.HTML.FormSubmissionTests
