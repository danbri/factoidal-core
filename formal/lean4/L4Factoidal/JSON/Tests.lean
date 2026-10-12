/-
L4Factoidal.JSON.Tests — compile-time executable checks.

Every `#guard` below is evaluated during `lake build`: a wrong answer
is a BUILD FAILURE (same discipline as `L4Factoidal/Tests.lean`).
Covers RFC 8259 examples, every escape form (§7), number-lexeme
preservation (§6), rejection cases, key-order/duplicate preservation,
and parse∘serialize round-trips.
-/
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.JSON.Tests

open L4Factoidal.JSON

/-! ### RFC 8259 §13 example object (adapted) -/

def rfcExample : Json :=
  .object [
    ("Image", .object [
      ("Width", .number "800"),
      ("Height", .number "600"),
      ("Title", .string "View from 15th Floor"),
      ("Thumbnail", .object [
        ("Url", .string "http://www.example.com/image/481989943"),
        ("Height", .number "125"),
        ("Width", .number "100")
      ]),
      ("Animated", .bool false),
      ("IDs", .array [.number "116", .number "943", .number "234", .number "38793"])
    ])
  ]

#guard parseJson rfcExample.toString == .ok rfcExample

/-! ### Literal forms -/

#guard parseJson "null" == .ok Json.null
#guard parseJson "true" == .ok (Json.bool true)
#guard parseJson "false" == .ok (Json.bool false)
#guard parseJson "  null  " == .ok Json.null   -- leading/trailing whitespace (§2)
#guard parseJson "\t\n\rnull\r\n\t" == .ok Json.null

/-! ### Numbers (§6) — lexical preservation -/

#guard parseJson "0" == .ok (Json.number "0")
#guard parseJson "-0" == .ok (Json.number "-0")
#guard parseJson "-0.0" == .ok (Json.number "-0.0")
#guard parseJson "123" == .ok (Json.number "123")
#guard parseJson "-123" == .ok (Json.number "-123")
#guard parseJson "1.5" == .ok (Json.number "1.5")
#guard parseJson "1e10" == .ok (Json.number "1e10")
#guard parseJson "1E10" == .ok (Json.number "1E10")
#guard parseJson "1e+10" == .ok (Json.number "1e+10")
#guard parseJson "1e-10" == .ok (Json.number "1e-10")
#guard parseJson "1.5E-3" == .ok (Json.number "1.5E-3")
#guard parseJson "3.14159" == .ok (Json.number "3.14159")

/-! ### Strings — the full escape set (§7) -/

#guard parseJson "\"\"" == .ok (Json.string "")
#guard parseJson "\"hello\"" == .ok (Json.string "hello")
#guard parseJson "\"\\\"\"" == .ok (Json.string "\"")       -- \"
#guard parseJson "\"\\\\\"" == .ok (Json.string "\\")       -- \\
#guard parseJson "\"\\/\"" == .ok (Json.string "/")         -- \/
#guard parseJson "\"\\b\"" == .ok (Json.string "\x08")      -- \b
#guard parseJson "\"\\f\"" == .ok (Json.string "\x0C")      -- \f
#guard parseJson "\"\\n\"" == .ok (Json.string "\n")        -- \n
#guard parseJson "\"\\r\"" == .ok (Json.string "\r")        -- \r
#guard parseJson "\"\\t\"" == .ok (Json.string "\t")        -- \t
#guard parseJson "\"\\u0041\"" == .ok (Json.string "A")     -- \u ASCII
#guard parseJson "\"\\u00e9\"" == .ok (Json.string "é")     -- \u non-ASCII BMP
#guard parseJson "\"\\uD83D\\uDE00\"" == .ok (Json.string "😀")  -- surrogate pair
#guard parseJson "\"raw utf8 café ☺\"" == .ok (Json.string "raw utf8 café ☺")  -- raw pass-through

/-! ### Nested structures -/

#guard parseJson "[]" == .ok (Json.array [])
#guard parseJson "{}" == .ok (Json.object [])
#guard parseJson "[1,2,3]" ==
  .ok (Json.array [Json.number "1", Json.number "2", Json.number "3"])
#guard parseJson "[[1,2],[3,4]]" ==
  .ok (Json.array [Json.array [Json.number "1", Json.number "2"],
                    Json.array [Json.number "3", Json.number "4"]])
#guard parseJson "{\"a\":{\"b\":{\"c\":1}}}" ==
  .ok (Json.object [("a", Json.object [("b", Json.object [("c", Json.number "1")])])])
#guard parseJson "[{\"a\":1},{\"b\":2}]" ==
  .ok (Json.array [Json.object [("a", Json.number "1")], Json.object [("b", Json.number "2")]])

/-! ### Key order and duplicate keys are preserved (Value.lean's module header) -/

#guard parseJson "{\"z\":1,\"a\":2,\"m\":3}" ==
  .ok (Json.object [("z", Json.number "1"), ("a", Json.number "2"), ("m", Json.number "3")])
#guard parseJson "{\"a\":1,\"a\":2}" ==
  .ok (Json.object [("a", Json.number "1"), ("a", Json.number "2")])
-- first-match lookup on a duplicate-keyed object (Json.field?):
#guard (Json.object [("a", Json.number "1"), ("a", Json.number "2")]).field? "a" ==
  some (Json.number "1")

/-! ### Rejection cases -/

#guard (parseJson "").isError                       -- empty input
#guard (parseJson "01").isError                      -- leading zero
#guard (parseJson "-01").isError                     -- leading zero, negative
#guard (parseJson "{a:1}").isError                   -- unquoted key
#guard (parseJson "{\"a\":1,}").isError               -- trailing comma, object
#guard (parseJson "[1,2,]").isError                  -- trailing comma, array
#guard (parseJson "\"\\uD800\"").isError              -- lone high surrogate
#guard (parseJson "\"\\uDC00\"").isError              -- lone low surrogate
#guard (parseJson "\"\\uD800\\u0041\"").isError       -- high surrogate not followed by low
#guard (parseJson "\"a\nb\"").isError                 -- raw control character (unescaped LF)
#guard (parseJson "[1,2").isError                    -- truncated: unterminated array
#guard (parseJson "\"abc").isError                    -- truncated: unterminated string
#guard (parseJson "tru").isError                      -- truncated keyword
#guard (parseJson "null extra").isError               -- trailing content after value
#guard (parseJson "\"\\x\"").isError                  -- invalid escape letter
#guard (parseJson "1.").isError                       -- dot with no fraction digit
#guard (parseJson "1e").isError                       -- exponent with no digit
#guard (parseJson "+1").isError                       -- leading '+' not permitted

/-! ### parse ∘ serialize round-trips on every positive fixture above -/

def fixtures : List Json := [
  Json.null, Json.bool true, Json.bool false,
  Json.number "0", Json.number "-0", Json.number "-0.0", Json.number "123",
  Json.number "1.5E-3", Json.number "1e+10",
  Json.string "", Json.string "hello", Json.string "\"", Json.string "\\",
  Json.string "/", Json.string "\x08", Json.string "\x0C", Json.string "\n",
  Json.string "\r", Json.string "\t", Json.string "A", Json.string "é",
  Json.string "😀", Json.string "raw utf8 café ☺",
  Json.array [], Json.object [],
  Json.array [Json.number "1", Json.number "2", Json.number "3"],
  Json.object [("z", Json.number "1"), ("a", Json.number "2")],
  Json.object [("a", Json.number "1"), ("a", Json.number "2")],
  rfcExample
]

#guard fixtures.all (fun j => parseJson j.toString == .ok j)
#guard fixtures.all (fun j => parseJson j.toStringPretty == .ok j)

/-! ### The reverse-accumulator parser (issue 729, OKR batch 1 KR 2.3)

`parseJson` runs `parseJsonTextCharsR` and `charsOfString` at run time
(`@[csimp]` in `Parser.lean`, proved equal to the specification by `parseR_eq`
and `charsOfString_eq`). These guards fix the element order the reversed
accumulators must restore, and the error each rejection reports, as literal
values, so an implementation that kept the accumulators reversed, or accepted
everything, fails the build. -/

#guard parseJson "[1,2,3,4,5]" ==
  .ok (.array [.number "1", .number "2", .number "3", .number "4", .number "5"])
#guard parseJson "{\"b\":1,\"a\":2,\"b\":3}" ==
  .ok (.object [("b", .number "1"), ("a", .number "2"), ("b", .number "3")])
#guard parseJson "[[1,2],[3,[4,5]],{\"k\":[6,7]}]" ==
  .ok (.array [.array [.number "1", .number "2"],
               .array [.number "3", .array [.number "4", .number "5"]],
               .object [("k", .array [.number "6", .number "7"])]])
#guard parseJson " [ ] " == .ok (.array [])
#guard parseJson "{ }" == .ok (.object [])
-- 3,000 items in order: the last one read is the last one in the list.
#guard (match parseJson ("[" ++ String.intercalate "," ((List.range 3000).map toString) ++ "]") with
  | .ok (.array items) => items.length == 3000 && items.head? == some (.number "0") &&
      items.getLast? == some (.number "2999")
  | _ => false)
-- Rejections: the message and the character position of the specification.
#guard parseJson "[1,2,]" == .error ⟨"unexpected character in JSON value", 5⟩
#guard parseJson "{\"a\":1,}" == .error ⟨"expected JSON string", 7⟩
#guard parseJson "[1 2]" == .error ⟨"expected comma or closing bracket in JSON array", 3⟩
#guard parseJson "{\"a\":1 \"b\":2}" ==
  .error ⟨"expected comma or closing brace in JSON object", 7⟩
#guard parseJson "[1,2] x" == .error ⟨"trailing content after JSON value", 6⟩
-- `charsOfString` reads every character, multi-byte ones included.
#guard charsOfString "a\u00e9\u263a" == #['a', 'é', '☺']
#guard charsOfString "" == #[]
#guard charsOfString "😀x" == "😀x".toList.toArray

/-! ### `escapeString` at run time (issue 744)

`escapeString` runs `escapeStringFast` (`@[csimp] escapeString_eq_fast`). The
first guards compare it with the specification's expression written out here
(the `csimp` does not rewrite this expression, so two programs are compared);
the literal ones fix the escapes. -/

def escapeSamples : List String :=
  ["", "plain", "a\"b", "back\\slash", "line\nfeed\r\t", "\x01\x1f\x7f",
   "caf\u00e9 \u263a 😀", "<http://e/x> <http://e/p> \"lit\\n\" .\n"]

#guard escapeSamples.all fun s => escapeString s == (s.toList.map escapeChar).foldl (· ++ ·) ""
#guard escapeString "a\"b\\c\nd\x01\u00e9" == "a\\\"b\\\\c\\nd\\u0001\u00e9"
#guard escapeString "" == ""
#guard escapeString "\x7f" == "\x7f"
#guard (Json.string "x\ty").toString == "\"x\\ty\""

end L4Factoidal.JSON.Tests
