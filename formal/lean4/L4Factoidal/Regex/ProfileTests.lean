import L4Factoidal.Regex.Profiles
import L4Factoidal.JSONSchema.Validate

namespace L4Factoidal.Regex.Profiles

#guard (matchWith .xsd10 "a" "" "cat").toOption == some false
#guard (matchWith .xpath20 "a" "" "cat").toOption == some true
#guard (matchWith .ecma2020 "a" "" "cat").toOption == some true
#guard (matchWith .xsd10 "^a$" "" "^a$").toOption == some true
#guard (matchWith .xsd10 "^a$" "" "a").toOption == some false
#guard (matchWith .xpath20 "^a$" "" "a").toOption == some true
#guard (matchWith .ecma2020 "\\w+" "" "_").toOption == some true
#guard (matchWith .xsd10 "\\w+" "" "_").toOption.isNone
#guard (matchWith .xpath20 "a" "q" "a").toOption.isNone
#guard (matchWith .ecma2020 "(?=a)a" "" "a").toOption.isNone
#guard (matchWith .ecma2020 "\\s" "" " ").toOption == some true
#guard (matchWith .ecma2020 "." "" "😀").toOption.isNone
#guard L4Factoidal.JSONSchema.patternMatch "(?=a)a" "a" == .unsupported
#guard L4Factoidal.JSONSchema.validate
  (.object [("patternProperties", .object [("(?=a)a", .bool false)]),
            ("additionalProperties", .bool false)]) (.object [("a", .null)]) == .unsupported
#guard (matchSparql "a?+*.{}()[]c" "q" "a?+*.{}()[]c").toOption == some true
-- A hyphen BETWEEN classes is concatenation, not XSD class subtraction.
#guard (matchWith .xpath20 "^[0-9A-F]{8}-[0-9A-F]{4}$" "i" "0123abcd-ABCD").toOption == some true
#print axioms matchWith
-- Repeated zero-width assertions must not become supported negative matches.
#guard (matchWith .xpath20 "^^a" "" "a").toOption.isNone
#guard (matchWith .xpath20 "a$$" "" "a").toOption.isNone
#guard (matchWith .ecma2020 "^^a" "" "a").toOption.isNone
#guard (matchWith .xpath20 "^a$" "" "a").toOption == some true
#guard (matchWith .xpath30 "^^a" "q" "^^a").toOption == some true

#guard (matchWith .xpath20 "^(^a)" "" "a").toOption.isNone
#guard (matchWith .xpath20 "(^)a$" "" "a").toOption.isNone
#guard (matchWith .xpath20 "^a$" "" "a").toOption == some true
#guard (matchWith .xpath20 "\\^a" "" "^a").toOption == some true
#guard (matchWith .xpath20 "[^b]" "" "a").toOption == some true

/-! ## XPath F&O 4.0 (`.xpath40`, `Regex.XPath40`)

The 4.0 constructs are accepted only by `.xpath40`; the older profiles keep
refusing them. -/
-- class subtraction, also nested, and with the flag i (F&O 4.0 §6.2)
#guard (matchWith .xpath40 "^[a-d-[b-c]]$" "" "d").toOption == some true
#guard (matchWith .xpath40 "^[a-d-[b-c]]$" "" "b").toOption == some false
#guard (matchWith .xpath40 "^[a-z-[aeiou-[e]]]$" "" "e").toOption == some true
#guard (matchWith .xpath40 "^[a-z-[aeiou-[e]]]$" "" "o").toOption == some false
#guard (matchWith .xpath40 "[A-Z-[OI]]" "i" "o").toOption == some false
#guard (matchWith .xsd10 "[a-d-[b-c]]" "" "a").toOption.isNone
#guard (matchWith .xpath20 "[a-d-[b-c]]" "" "a").toOption.isNone
-- category and block escapes (Unicode 16.0.0)
#guard (matchWith .xpath40 "^\\p{Lu}+$" "" "ÀB").toOption == some true
#guard (matchWith .xpath40 "^\\p{Lu}+$" "" "Àb").toOption == some false
#guard (matchWith .xpath40 "\\p{IsLatinExtended-A}" "" "Ā").toOption == some true
#guard (matchWith .xpath40 "\\p{IsCJKUnifiedIdeographs}" "" "中").toOption == some true
#guard (matchWith .xpath40 "\\p{IsNoSuchBlock}" "" "a").toOption.isNone
#guard (matchWith .xpath20 "\\p{Lu}" "" "A").toOption.isNone
#guard (matchWith .xsd10 "\\p{Lu}" "" "A").toOption.isNone
-- \d and \w are the Unicode classes of XSD 1.1 G.4.2.5
#guard (matchWith .xpath40 "^\\d$" "" "٣").toOption == some true
#guard (matchWith .xpath40 "^\\w$" "" "ʰ").toOption == some true
#guard (matchWith .xpath40 "^\\w$" "" "-").toOption == some false
-- back-references, also case-blind with i
#guard (matchWith .xpath40 "^(ki|ke)\\1$" "" "kiki").toOption == some true
#guard (matchWith .xpath40 "^(ki|ke)\\1$" "" "kike").toOption == some false
#guard (matchWith .xpath40 "([md])[aeiou]\\1" "i" "Mum").toOption == some true
#guard (matchWith .xpath40 "^(?<q>'|\").*\\k<q>$" "" "'ab'").toOption == some true
#guard (matchWith .xpath40 "\\1(a)" "" "aa").toOption.isNone
#guard (matchWith .xpath20 "(a)\\1" "" "aa").toOption.isNone
-- lookaround and word boundaries
#guard (matchWith .xpath40 "Chapter(?=\\s+[1-9])" "" "Chapter 3").toOption == some true
#guard (matchWith .xpath40 "Chapter(?!\\s*[1-9])" "" "Chapter 3").toOption == some false
#guard (matchWith .xpath40 "(?<!\\$)[0-9]+" "" "$5").toOption == some false
#guard (matchWith .xpath40 "(*positive_lookbehind:\\[)[0-9]" "" "[5").toOption == some true
#guard (matchWith .xpath40 "^.\\b" "" "a-").toOption == some true
#guard (matchWith .xpath40 "^aa\\B" "" "aa").toOption == some false
#guard (matchWith .xpath40 "(?<=a*)b" "" "ab").toOption.isNone
#guard (matchWith .xpath40 "^*a" "" "a").toOption.isNone
-- F&O 4.0 §6.1.8.1: no line after a final newline
#guard (matchWith .xpath40 "^$" "m" "abcd\ndefg\n").toOption == some false
#guard (matchWith .xpath40 "\\n$" "m" "a\n").toOption == some false
#guard (matchWith .xpath40 "a$" "m" "a\n").toOption == some true
-- XSD 1.1 G.4.1 class syntax errors
#guard (matchWith .xpath40 "[a--b]" "" "a").toOption.isNone
#guard (matchWith .xpath40 "[^]" "" "a").toOption.isNone
#guard (matchWith .xpath40 "a[]b" "" "ab").toOption.isNone
#guard (matchWith .xpath40 "[a-\\d]" "" "a").toOption.isNone
#guard (matchWith .xpath40 "[\\u0041]" "" "A").toOption.isNone
#guard (matchWith .xpath40 "[a\\-[bc]" "" "a").toOption.isNone
#guard (matchWith .xpath40 "[-a]" "" "-").toOption == some true
#guard (matchWith .xpath40 "[a-]" "" "-").toOption == some true
-- flags x (also after a backslash) and c
#guard (matchWith .xpath40 "hello\\ sworld" "x" "hello world").toOption == some true
#guard (matchWith .xpath40 "a#comment#b" "c" "ab").toOption == some true

end L4Factoidal.Regex.Profiles
