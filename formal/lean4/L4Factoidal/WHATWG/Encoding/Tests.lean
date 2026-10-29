/-
L4Factoidal.WHATWG.Encoding.Tests — build-time checks (`#guard`) of statements
that the Encoding Standard (whatwg/encoding commit `be17ac5c`, 2026-10-19)
makes about its own tables. The web-platform-tests run is
`tests/whatwg-encoding/run.sh`.
-/
import L4Factoidal.WHATWG.Encoding.Core

namespace L4Factoidal.WHATWG.Encoding.Tests

open L4Factoidal.WHATWG.Encoding

-- Section 4.2: "For each encoding, ASCII-lowercasing its name yields one of
-- its labels."
#guard Encoding.all.all fun e => getEncoding (asciiLower e.name) == some e

-- Section 4.2: 40 encodings and 228 labels; no label is listed twice.
#guard Encoding.all.length == 40
#guard labelTable.length == 228
#guard (labelTable.map (·.1)).eraseDups.length == labelTable.length

-- Section 4.1: replacement, UTF-16BE and UTF-16LE have no encoder; every
-- other encoding has one.
#guard Encoding.all.all fun e =>
  (getEncoder e).isNone == (e == .replacement || e == .utf_16be || e == .utf_16le)

-- Section 4.3: get an output encoding gives an encoding that has an encoder.
#guard Encoding.all.all fun e => (getEncoder (getOutputEncoding e)).isSome

-- Section 5: index sizes as in indexes.json.
#guard idxJis0208.get.size == 11280
#guard idxBig5.get.size == 19782
#guard idxGb18030.get.size == 23940
#guard idxGb18030Ranges.get.size == 207

-- Section 10.2.2: index gb18030 maps 0xA3 0xA0 to U+3000, and the encoder
-- refuses U+E5E5.
#guard decode (ByteArray.mk #[0xA3, 0xA0]) .gb18030 == "　"
#guard encode #[0xE5E5] .gb18030 == some "&#58853;".toUTF8

-- Section 12.2.2 note: encoding U+00A5 twice and decoding the concatenation
-- gives U+00A5 U+FFFD U+00A5.
#guard (do
    let one ← encode #[0xA5] .iso_2022_jp
    pure (decode (one ++ one) .iso_2022_jp)) == some "¥�¥"

end L4Factoidal.WHATWG.Encoding.Tests
