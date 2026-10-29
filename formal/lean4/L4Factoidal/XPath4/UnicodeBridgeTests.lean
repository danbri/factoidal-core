/-
XPath Unicode 18 bridge regressions through the public XPath entry point.
F&O 4.0 §5.4.9 (normalize-unicode) and fn:graphemes.
https://github.com/danbri/factoidal/issues/1195
-/
import L4Factoidal.XPath4.Eval

namespace L4Factoidal.XPath4.UnicodeBridgeTests

private def answer (src : String) : String :=
  match evalString src with
  | .ok s => showSeq s
  | .error e => e.code

-- Compatibility APIs used by the collation implementation.
#guard Unicode.hexVal "1ADD" == 0x1ADD
#guard Unicode.ccc 0x1ADD == 220
#guard Unicode.decompChar false 0xC5 == [0x41, 0x30A]
#guard Unicode.decompose false "Å" == #[0x41, 0x30A]

-- Form-name handling and XPath errors stay at the XPath boundary.
#guard answer "normalize-unicode('Å') eq 'Å'" == "true"
#guard answer "normalize-unicode('Å', ' nFd ') eq 'Å'" == "true"
#guard answer "normalize-unicode('ﬁ', 'NFKC') eq 'fi'" == "true"
#guard answer "normalize-unicode('ẛ̣', 'NFKD') eq 'ṩ'" == "true"
#guard answer "normalize-unicode('Å', '') eq 'Å'" == "true"
#guard answer "normalize-unicode('abc', 'unsupported')" == "FOCH0003"
#guard answer "normalize-unicode('', 'unsupported')" == "FOCH0003"
#guard answer "normalize-unicode(()) eq ''" == "true"
#guard answer "normalize-unicode('abc', 'NFC', 'extra')" == "XPST0017"

-- FULLY-NORMALIZED includes composing characters of combining class zero.
#guard answer "string-to-codepoints(normalize-unicode(codepoints-to-string(2494), 'FULLY-NORMALIZED'))" == "32 2494"
#guard answer "string-to-codepoints(normalize-unicode(codepoints-to-string((769, 97)), 'FULLY-NORMALIZED'))" == "32 769 97"
#guard answer "string-to-codepoints(normalize-unicode(codepoints-to-string(4449), 'FULLY-NORMALIZED'))" == "32 4449"
#guard answer "string-to-codepoints(normalize-unicode(codepoints-to-string(4520), 'FULLY-NORMALIZED'))" == "32 4520"
#guard answer "normalize-unicode('é', 'FULLY-NORMALIZED') eq 'é'" == "true"
#guard answer "normalize-unicode('', 'FULLY-NORMALIZED') eq ''" == "true"
#guard answer "normalize-unicode('각', 'NFC') eq '각'" == "true"

#guard answer "empty(graphemes(())) and empty(graphemes(''))" == "true"
#guard answer "deep-equal(graphemes('éx'), ('é', 'x'))" == "true"
#guard answer "count(graphemes(codepoints-to-string((13, 10))))" == "1"
#guard answer "count(graphemes(codepoints-to-string((127462, 127463, 127464))))" == "2"
#guard answer "count(graphemes(codepoints-to-string((128105, 8205, 128187))))" == "1"
#guard answer "count(graphemes(codepoints-to-string((2325, 2381, 2340))))" == "1"

-- UAX #29 rev49 changes GB9c to Linker Extend* × Consonant:
-- https://www.unicode.org/reports/tr29/tr29-49.html#GB9c
-- Unicode 18 GraphemeBreakTest.txt lines 179–180 and 859–860 join these strings.
-- QT4's Unicode 15.1 cases graphemes-1045/1046/1187/1188 expect two clusters instead.
-- This is a version change, not an implementation defect or an exclusion.
#guard answer "count(graphemes(codepoints-to-string((97, 2381, 2340))))" == "1"
#guard answer "count(graphemes(codepoints-to-string((63, 2381, 2340))))" == "1"
#guard answer "count(graphemes(codepoints-to-string((2381, 2325))))" == "1"
#guard answer "count(graphemes(codepoints-to-string((2381, 776, 2325))))" == "1"

end L4Factoidal.XPath4.UnicodeBridgeTests
