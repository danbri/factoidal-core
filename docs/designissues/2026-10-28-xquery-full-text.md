# XQuery and XPath Full Text 3.0 in Lean (L4Factoidal/FullText)

Date: 2026-10-28. Work: https://github.com/danbri/factoidal/issues/1101
(QT4, agent qt4-M). Open items: https://github.com/danbri/factoidal/issues/1179.
Defective test data: https://github.com/danbri/factoidal/issues/1173.

## Result

Specification: XQuery and XPath Full Text 3.0, W3C Recommendation
2015-03-24 (https://www.w3.org/TR/xpath-full-text-30/), on top of XQuery
4.0. The QT4 Community Group has no 4.0 Full Text draft. Tests: qt4tests
`ft/` (84 test sets, 685 cases), commit `b1616b79`.

From `formal/lean4/`, with `ulimit -s 65520`:

```
lake build l4qt4
.lake/build/bin/l4qt4 --isolate 60 --lang xquery --family ft
  ft: 675 pass, 0 fail, 0 unsupported (out of 675); 10 excluded (defective test data)
```

The other families do not lose passes: XQuery mode (`--lang xquery`)
42920 pass, 1745 fail, 1956 unsupported (out of 46621, `ft` included);
`main` before: 42244 pass, 1746 fail, 1956 unsupported (out of 45946).
XPath mode: 28250 pass, 705 fail, 9704 unsupported (out of 38659) before
and after. `bin` and `file`: 914 pass, 0 fail, 5 unsupported (out of 919)
before and after.

## Modules

| Module | Content |
|---|---|
| `FullText/Model.lean` | The AllMatches model (§4.2.1) and one function per `fts:Apply*` function (§4.2.6): or, and, unary not, mild not, order, scope, content, window, distance, times, with `joinIncludes`, `wordDistance`, `FormCombinations`, `FormRange`. |
| `FullText/Tokenize.lean` | The tokenizer (§4.1, implementation-defined). |
| `FullText/Stem.lean` | The Porter stemmer (1980), for English. |
| `FullText/Select.lean` | Match options (§3.4, §4.2.5), token comparison, wildcards, thesaurus lookup, FTWords (§4.2.4), `fts:evaluate` (§4.2.3) over a resolved selection `RSel`, scores. |
| `FullText/Parser.lean` | The grammar (Appendix A: FTContainsExpr to FTIgnoreOption) as an extension of the XPath 4.0 parser. |
| `FullText/Eval.lean` | `contains text` in the evaluator: resolution of the embedded expressions, stop word lists and thesauri from the resources, tokenization of nodes (`fts:reconstruct`), scores of `for ... score` and `let score`. |
| `FullText/Theorems.lean` | The bridge theorems (below). |

The tree is not imported by the library root `L4Factoidal.lean`, so the
wasm and the npm package do not change. `Harness.Qt4Run` imports it.

## How a query is evaluated

1. **Parsing.** The XPath 4.0 parser calls the hook `ExtGrammar.postConcat`
   after every StringConcatExpr (production FTContainsExpr sits between
   ComparisonExpr and StringConcatExpr). The XQuery 4.0 grammar sets the
   hook to `FullText.ftPostConcat`. The selection is stored in the
   expression tree as `Expr.ext` nodes with tags `ft.*`. `declare
   ft-option` (a prolog setter) is stored under the pseudo-prefix `#ftopt`
   of the static namespaces and copied into each `ft.contains` node.
   Score variables are rewritten as §4.4 says: `for $x score $s in E`
   becomes a `let` of the score sequence of `E`, the `for` with a position
   variable, and a `let` of `$s`; `let score $s := E` becomes a `let` of
   the score of `E`.
2. **Resolution.** `XQuery4.Runtime.evalExt` gives an `ft.*` node to
   `FullText.evalFt`. The embedded expressions are evaluated once:
   FTWordsValue to `xs:string*`, ranges and window sizes to `xs:integer`,
   weights to `xs:double` (FTDY0016 above 1000 in absolute value). Stop
   word lists and thesauri are read from the resources of the dynamic
   context; an absent one is FTST0008 or FTST0018.
3. **Matching.** For each search context item, the item is tokenized and
   `evalSel` computes the AllMatches; `contains text` is true when a Match
   has no StringExclude (§4.3).

## Implementation-defined choices

- **Tokens:** maximal runs of characters of General Category L, M or N
  (the tables of the shared `Regex`). A Han, Hiragana or Katakana
  character is a token by itself (no spaces between words in these
  scripts), so `"网站"` matches `网站建置`.
- **Sentences** end after `.`, `!` or `?`. **Paragraphs** end at element
  boundaries (the qt4tests feature `fullText-units`: "element boundaries
  … treated as Full Text sentence and paragraph boundaries"); a boundary
  inside a token (`<b>p</b>rototypes`) does not split the token, because
  tokens come from the string value.
- **Comparison:** diacritics removed (NFD, non-spacing marks dropped)
  unless `diacritics sensitive`; case folded unless `case sensitive`;
  Porter stems with `stemming` and an English language. `lowercase` and
  `uppercase` also require the text token to be all lower or upper case.
- **Wildcards:** a query token with `.`, `.?`, `.*`, `.+`, `.{n,m}` and
  `\c` is translated to an XPath 4.0 regular expression and matched by the
  shared engine. A `?`, `*`, `+`, `{` or `}` that follows no `.` separates
  tokens; an escaped non-word character separates tokens too.
- **Stop words:** a query token in the list matches any one token. The
  default list (`stop words default`) and the default thesaurus are those
  of the W3C Full Text test suite (feature `fullText-defaults`).
- **Thesaurus:** the XQFTTS format; nested `synonym` elements are deeper
  levels; without a level range every level is used; the query phrase is
  always one of the alternatives.
- **Languages:** a tag whose primary subtag has 2 or 3 letters is
  supported (FTST0009 otherwise). Only English has a stemmer.
- **Scores:** 0 when the selection fails, else `1 - 1/(k+1)` for `k`
  successful Matches. A predicate selects the score of a `for` item.
- **Optional features:** all supported (mild not, unary not, every
  FTUnit and FTBigUnit, scope, times, content, stop word and language
  options, ignore option, negative weights). No FTST0001 to FTST0015
  restriction error is raised.

## Theorems (no `sorry`; `#print axioms`: propext, Classical.choice, Quot.sound)

- `succeeds_applyOr`, `succeeds_applyAnd`, `mem_applyAnd`: FTOr is the
  disjunction and FTAnd the conjunction of the match sets.
  `evalSel_or`, `evalSel_and`: `fts:evaluate` uses them.
  `unaryNot_fails`: `ftnot` of a successful operand fails.
- `contains_spaced`, `contains_eq_containsToken`: on a text of plain words
  separated by single spaces, `contains text "w"` (one word, no stop
  words, wildcards or thesaurus) is "some word has the comparison key of
  w"; with `case sensitive` and `diacritics sensitive` it is "some word
  equals w", which is `fn:contains-token` with the codepoint collation on
  that text. The tokenizer lemmas are proved on the fold that the
  tokenizer runs.
- `wildcardMatch_eq_regex`, `prepTok_wild`, `qtokMatch_wild`: a wildcard
  query token is matched by `Regex.XPath40.compile` and `Regex.isMatch`,
  the engine of `fn:matches`.
- `unaryNotHelper_eq_loop` (`@[csimp]`): the compiled code of
  `fts:UnaryNotHelper` is a loop.

## Runner changes (`Harness/Qt4Run.lean`)

- Features `fullText`, `fullText-ignore`, `fullText-units`,
  `fullText-defaults` are on; `ft` is a default family in XQuery mode.
- A resource whose file is absent is not given to the evaluator (the
  tests name absent stop word lists and thesauri to get FTST0008 and
  FTST0018).
- `assert-xml` for a result of more than one node: the whitespace-only
  text between the top-level nodes of the expected XML is layout, not
  part of the expected sequence.
- 10 `ft/` cases are excluded as defective test data
  (https://github.com/danbri/factoidal/issues/1173).
