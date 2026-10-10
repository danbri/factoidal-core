# Unicode case mapping in the Lean tree

Date: 2026-10-10. Issue: <https://github.com/danbri/factoidal/issues/706>.
Code: `formal/lean4/L4Factoidal/Text/CaseMap.lean`,
`formal/lean4/L4Factoidal/Text/CaseMapData.lean` (generated),
`formal/lean4/L4Factoidal/Text/CaseMapTests.lean`, generator
`tools/gen_casemap.py`.

## 1. What the specifications require

| Place | Text | Requirement |
|---|---|---|
| SPARQL 1.1 §17.4.3.8 `UCASE`, §17.4.3.9 `LCASE` | <https://www.w3.org/TR/sparql11-query/#func-ucase> | defined by XPath `fn:upper-case` and `fn:lower-case` |
| F&O 3.1 §5.4.7 `fn:upper-case`, §5.4.8 `fn:lower-case` | <https://www.w3.org/TR/xpath-functions-31/#func-upper-case> | case mapping "as defined by the Unicode Standard" (UnicodeData.txt and the unconditional lines of SpecialCasing.txt; `ß` gives `SS`) |
| F&O 3.1 §5.6.1.1 flag `i` | <https://www.w3.org/TR/xpath-functions-31/#flags> | C2 is a case-variant of C1 when `fn:lower-case(C1) eq fn:lower-case(C2)` or `fn:upper-case(C1) eq fn:upper-case(C2)` |
| RIF-DTB 4.7 `func:upper-case`, `func:lower-case` | <https://www.w3.org/TR/rif-dtb/> | the same two functions |
| GREL `toUpperCase`, `toLowerCase` (RML-FNML) | Java `String.toUpperCase()` / `toLowerCase()` | Unicode default case mapping with SpecialCasing unconditional rules; Final_Sigma context rule; root locale |
| Unicode Standard 15.1 §3.13, Table 3-17 | <https://www.unicode.org/versions/Unicode15.1.0/ch03.pdf> | Final_Sigma context condition |

Before this change Lean core `String.toUpper` and `String.toLower` served all
of these. `Char.toUpper` and `Char.toLower` change `a`-`z` and `A`-`Z` only.
`"ÉCOLE".toLower` is `"École"` (pinned by a guard in
`L4Factoidal/SPARQL/FullText.lean`).

No W3C SPARQL evaluation test uses a non-ASCII letter in `UCASE` or `LCASE`,
so the SPARQL score did not show the defect.

## 2. The module

`L4Factoidal.Text.CaseMap` is the one implementation. Functions:

| Function | Meaning |
|---|---|
| `upperCase`, `lowerCase` | full Unicode default case mapping of a string; language-independent; `lowerCase` applies Final_Sigma |
| `caseFold` | simple case folding, CaseFolding.txt statuses C and S, character by character |
| `caseVariants`, `isCaseVariant`, `ciRanges` | the case-variant relation of F&O §5.6.1.1, as a set per code point and as a range expansion |
| `searchFold` | the characterwise fold a search index uses (section 6) |

Rules implemented:

* A character maps through the unconditional FULL mapping of SpecialCasing.txt
  when one exists (`ß` to `SS`, `ŉ` to `ʼN`, `ǰ`, `ΐ`, the `ﬁ` ligatures, the
  Greek letters with ypogegrammeni), else through the SIMPLE mapping of
  UnicodeData.txt.
* `İ` (U+0130) lower-cases to `i` and U+0307 in every language (SpecialCasing
  unconditional line). The Lithuanian, Turkish and Azeri lines are not applied.
  Reason: F&O and Java's root locale define no language parameter.
* Final_Sigma: `Σ` lower-cases to `ς` when a cased letter precedes it, with
  case-ignorable characters between allowed, and no cased letter follows it,
  with case-ignorable characters between allowed. Else to `σ`. The
  properties Cased and Case_Ignorable come from DerivedCoreProperties.txt.
  The lookahead and lookbehind are one function (`casedAhead`); a character
  that is both case-ignorable and cased ends the scan with `true`, which is
  the regular-expression reading of the definition.
* Upper-casing has no context rule.

### Tables

`tools/gen_casemap.py` reads four Unicode Character Database files of ONE
pinned version, Unicode **15.1.0**. The Lean tree had no earlier Unicode
table, so the task default applied. The generator checks each file against the
SHA-256 it records; it downloads a missing file from unicode.org. The
generated header repeats the URLs and digests:

| File | SHA-256 |
|---|---|
| UnicodeData.txt | `2fc713e6a31a87c4850a37fe2caffa4218180fadb5de86b43a143ddb4581fb86` |
| SpecialCasing.txt | `55a477efd933a52cd27e6a9bf70265bb2d8814af31aab07767abc8eb421f27ef` |
| CaseFolding.txt | `4e55acfdc32825a22e87670e9056a3bf94ad7c5400065778e9e10f8314372bcf` |
| DerivedCoreProperties.txt | `f55d0db69123431a7317868725b1fcbf1eab6b265d756d1bd7f0f6d9f9ee108b` |

`python3 tools/gen_casemap.py --check` fails when the committed file differs
from the generator output.

Shape: simple mappings are sorted arrays of stride runs `(lo, hi, stride,
delta)` (200 runs for 1,450 uppercase mappings, 182 for 1,433 lowercase, 205
for 1,457 foldings). SpecialCasing entries are a sorted array (102 uppercase
lines, 1 lowercase line that differs from the simple mapping). Cased and
Case_Ignorable are sorted range arrays (157 and 437 ranges). Every lookup is a
binary search (`upperBound`). Code points below U+0080 skip the tables.
`CaseMapTests` re-counts every run table against the digits in the header.

Elaboration cost of the data file: 3.7 s. Size: 1,371 lines.

### Cost

`lowerCase` takes one pass over a string with no U+03A3. A string with U+03A3
takes the loop `lowerGo`, which reads the neighbouring characters; the two
agree wherever the one-pass path applies (`CaseMapTests`). The case-variant
tables (`caseAffected`, `variantGroups`) are built on first use (`Thunk`), so a
program that never uses the regex flag `i` pays nothing at start-up.

Measured 2026-10-10, native code (`leanc -O3`), a shared 4-CPU container, one
run, so the figures are rough. 1,000,000 ASCII characters: `upperCase` 8.6 to
13.6 ms (core `String.toUpper` 5.5 to 9.5 ms), `lowerCase` 25 ms (core
`String.toLower` 7.7 to 9.0 ms). 1,000,000 characters with 10% `é` and 1% `Σ`:
`upperCase` 35 to 70 ms, `lowerCase` 55 to 73 ms. First `caseVariants` call
(tables built): 5 to 7 ms. `ciRanges` of the whole code space: 3 to 6 ms.

## 3. Call sites

Changed:

| File | Change |
|---|---|
| `Fn/String.lean` | `upperCase` and `lowerCase` call `Text.CaseMap`. This is the single function behind SPARQL `UCASE`/`LCASE`, RIF `func:upper-case`/`func:lower-case` and GREL `toUpperCase`/`toLowerCase`. |
| `SPARQL/Expr.lean` | `UCASE` and `LCASE` called `s.toUpper` and `s.toLower` directly. They now call `Fn.String.upperCase` and `Fn.String.lowerCase`, as the function-library rule requires (`docs/designissues/2026-09-07-function-library.md`). |
| `RML/Functions.lean` | the expected-failure guard on `é` is a positive assertion; more guards added. |
| `Regex/XSDPattern.lean`, `Regex/XPath.lean` | flag `i` (section 5). |
| `Storage/LiteralGramIndex.lean` | the index fold (section 6). |

`XPath/Eval.lean` is XPath 1.0. It has no `fn:upper-case` or `fn:lower-case`;
its three `toLower` calls are ASCII by specification (below). XSLT 1.0
reaches no Unicode case function.

Left as ASCII, with the reason:

| Call site | Why ASCII is right |
|---|---|
| BCP 47 language tags: `RDF/Core.lean` `langTagEq` and literal normalisation, `RDF/Isomorphism.lean`, `RDF/LangTag.lean`, `SPARQL/Expr.lean` CONCAT tag comparison, `SPARQL/AlgebraRefinement.lean`, `Fn/String.lean` `matchesLanguageRange`, `langMatchesBasic`, `ShEx/Validation.lean`, `ShEx/FromJson.lean`, `ShEx/Compact.lean` language tags, `SHACL/Validation.lean`, `XML/XmlAttributes.lean`, `JSONLD/Expand.lean`, `JSONLD/ToRdf.lean`, `JSONLD/Compact.lean` `cmpLower`, `Syntax/NTriples.lean`, `XPath/Eval.lean` `lang()` | RFC 5646 tags are ASCII; RFC 4647 §2 matching is ASCII case-insensitive; RDF 1.1 Concepts §3.3 lowercases tags |
| IRI scheme and hex digits: `RML/Functions.lean` `d.toUpper` in `\uXXXX` escape (hex digits) | RFC 3986 §6.2.2.1: ASCII |
| Keywords: `Syntax/Turtle.lean`, `Syntax/TurtleStatementScan.lean` (`PREFIX`, `BASE`, `GRAPH`), `ShEx/Compact.lean` keyword `ns.toUpper`, `Geo/Wkt.lean` | the grammars spell keywords with ASCII `[Pp][Rr]...` classes |
| HTML and XML names: `JSONLD/Html.lean`, `XML/Document.lean` `toLowerAscii`, `XPath/Eval.lean` attribute name `id`, `XML/Parser.lean` and `XML/Encoding.lean` charset names | the HTML specification says "ASCII case-insensitive"; IANA charset names are ASCII |
| HTTP, Solid and format tags: `HTTP/*`, `Solid/*`, `Wasm/Ops/*`, `RDF/Format.lean`, `Storage/PackStream.lean`, `Harness/Manifest.lean` | RFC 9110 §5.1: field names are ASCII case-insensitive; media types and format tags are ASCII tokens |
| Test fixtures: `Cottas/LazyTermCache.lean`, `Cottas/LazyDict.lean`, `Harness/XmlConfRun.lean` | a key function chosen by the test; no specification applies |
| `SPARQL/FullText.lean` | an explicit ASCII fold written out so that the tokeniser floor does not move; not an `UCASE`/`LCASE` consumer |
| `XSLT/Transform.lean` `collateLe` | `xsl:sort` `lang` and `case-order` select an implementation-defined collation (XSLT 1.0 §10); the function says in its comment that it is not a Unicode collation |

## 4. Differences between the F&O relation and CaseFolding.txt

F&O §5.6.1.1 defines case-variants with `fn:lower-case` and `fn:upper-case`.
CaseFolding.txt gives a different partition in five code points of Unicode
15.1:

| Code point | F&O case-variants | CaseFolding.txt C+S class |
|---|---|---|
| `I` U+0049, `i` U+0069 | `I`, `i`, `ı` | `I`, `i` |
| `ı` U+0131 | `I`, `i`, `ı` | `ı` |
| `ϑ` U+03D1 | `Θ`, `θ`, `ϑ` | `Θ`, `θ`, `ϑ`, `ϴ` |
| `ϴ` U+03F4 | `Θ`, `θ`, `ϴ` | `Θ`, `θ`, `ϑ`, `ϴ` |

F&O is the normative text for the regex flag, so `caseVariants` implements
F&O. `caseFold` is CaseFolding.txt C+S, as the task required, and is the
function to use where a specification names Unicode case folding.

## 5. The regular-expression flag `i`

Old behaviour: the parser produced a regular expression, then `foldCi`
added the ASCII case partner of every range in every leaf. Two defects:

1. Non-ASCII letters had no case-variants.
2. The expansion saw every leaf, including leaves made by `[^q]`, `\W`, `\S`
   and `\D`. F&O says a range in a negated class is expanded BEFORE the
   complement (`[^Q]` rejects `Q` and `q`) and that "all other constructs are
   unaffected by the `i` flag". The old code accepted `q` for `[^q]` with `i`.

Adding Unicode expansion to the old post-pass would have made defect 2 worse:
`\W` (the complement of the ASCII word characters) contains U+212A KELVIN SIGN,
whose variants are `k` and `K`, so `\W` with `i` would have matched `k`.

New behaviour: the flag is a parser parameter (`XSDPattern.parseCpsWith ci`,
`parseCapturing ci`). With it, a literal character, a character range and a
single-character escape (`\n`, `\uHHHH`, ...) accept their case-variants
(`Text.CaseMap.ciRanges`); a negated class takes its complement after the
expansion, on merged intervals; `.`, `\d \s \w \i \c` and their complements
are unchanged. The flag `q` expands each literal character the same way.
`foldCi` is deleted. Parsing without the flag is byte-for-byte the old
behaviour (`parseCps = parseCpsWith false`).

`ciRanges` returns sorted, merged intervals. `[A-Z]` with `i` becomes
`[A-Za-z]` plus U+0131, U+017F and U+212A.

The F* tree still folds the ASCII letters after parsing (`rx_fold_ci`). On
non-ASCII input and on negated classes the two trees now differ. The
`l4diff` runner compares the trees on the W3C manifests, whose regex tests are
ASCII.

## 6. The literal search index

`Storage/LiteralGramIndex.lean` indexes character 3-grams of a case-folded
lexical form so that `CONTAINS(LCASE(STR(?l)), "needle")` is answered from
candidates. Its header said the fold is `String.toLower`, "the same function
`Expr` evaluates for `LCASE`", so that the two "cannot drift". That held while
`LCASE` was `String.toLower`. Changing `LCASE` alone would have broken the
superset property silently: the index would list no candidate for
`école` against `École Normale`, and for U+212A KELVIN SIGN against `kelvin`,
and the scan would keep both rows. No guard tied the two functions.

`LCASE` is not a character map (`İ` gives two characters; `Σ` depends on its
neighbours), so the index fold is `Text.CaseMap.searchFold`: each character
becomes the context-free full lowercase, with `Σ` and `ς` both folded to `σ`.
Two properties make it sound:

1. A contiguous part of a string folds to a contiguous part of the fold
   (`listContainsSublist_flatMap`, proved), so a case-sensitive `CONTAINS`
   match implies a match of the folded needle in the folded text.
2. `searchFold (lowerCase s) = searchFold s`. The two outputs of `lowerCase`
   that depend on context, `σ` and `ς`, fold to one image. `CaseMapTests`
   checks this over every case-affected code point and over strings with
   sigma in context; `LiteralGramIndex` checks it on a dictionary with
   `École`, KELVIN SIGN, `İstanbul`, `ΟΔΥΣΣΕΥΣ` and `Straße`.

For ASCII text the index bytes are unchanged. An index file packed before this
change holds ASCII-folded grams for non-ASCII literals and is not a superset
for the Unicode `LCASE`: re-pack it. The LGI1 and LGI2 headers carry no fold
identifier. Whether to add one (a new wire version) is an owner decision;
there are no users of old files (CLAUDE.md, "There are no users").

## 7. Tests

* `Text/CaseMapTests.lean`: table counts and order; simple mappings at run
  edges; `upperCase`, `lowerCase`, `caseFold` on é/É, ß, ẞ, ŉ, ﬁ, ΐ, İ, ı,
  KELVIN SIGN, Cherokee, Deseret (astral), digits, punctuation, CJK and
  already-cased strings; Final_Sigma in 19 contexts (positive and negative); variants and `ciRanges`;
  idempotence and the `searchFold` property over all 2,938 case-affected
  code points; 20,000-character strings.
* `Regex/RegexTests.lean`: flag `i` with KELVIN SIGN, accents, Greek sigma
  forms, ı, İ, ß, Cherokee, Deseret, negated classes, `\W`, `.`, flag `q`,
  `fn:replace`.
* `SPARQL/ExprTests.lean`, `Fn/String.lean`: `UCASE`, `LCASE`,
  `fn:upper-case`, `fn:lower-case`, language-tag preservation.
* `RML/Functions.lean`: `grel:toUpperCase("é")` is `"É"`.
* `Storage/LiteralGramIndex.lean`: candidates for Unicode needles.

Sabotage runs (a defect put in, the build must fail, the defect taken out):

| Defect | First failing guard |
|---|---|
| `upperCase` skips the tables for non-ASCII | `CaseMapTests` `upperCase "é"` |
| no Final_Sigma | `CaseMapTests` `lowerCase "ΑΣ"` |
| Final_Sigma always true | `CaseMapTests` `lowerCase "ΑΣΑ"` |
| negated class not expanded before complement | `RegexTests` `^[^q]$` with `i` on `Q` |
| multi-character escapes expanded | `RegexTests` `^\W$` with `i` on `k` |
| index fold ASCII only | `LiteralGramIndex` `candidatesSpec uniDict "école"` |

## 8. Scores

See the commit message of the landing. Suites gated: `l4w3c` sparql11
manifest-all and sparql12, `l4xpath`, `l4xslt`, `l4rml`, `l4shacl`, `l4shex`,
`Wasm/native-smoke.sh`, full `lake build`.
