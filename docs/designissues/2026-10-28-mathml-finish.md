# MathML: what "finish" means, model and rendering

Date: 2026-10-28. Status: design, no code. Tracking:
https://github.com/danbri/factoidal/issues/1165 (section "Front end: design
first", MathML). Earlier plan: `docs/designissues/2026-07-10-mathml-arbitrary-expression-rendering.md`
(F\*, waves 0 to 3).

## Result

Browsers render Presentation MathML natively (MathML Core in Chromium 109
and later, Firefox and Safari). So the front end needs no layout engine and
no JavaScript typesetting library: Factoidal gives Presentation MathML text,
and the page inserts it. "Finish" is model work in Lean: Content MathML
complete for the operators that the engine evaluates, the translation to
Strict Content MathML and its relation to OpenMath, Presentation output
that uses MathML Core only, Presentation input read into a tree, and the
MathML 4 `intent` attribute. Rendering is the browser's job and is checked
only by a browser sweep.

## 1. Target specifications (version-aware)

| Name in Lean | Specification | Use |
|---|---|---|
| `MathML3` | MathML 3.0, Second Edition, W3C Recommendation 2014-04-10 | the current modules cite it; stays the base for Content markup |
| `MathMLCore` | MathML Core, W3C Candidate Recommendation (pin the dated snapshot at stage 1) | the element and attribute set that the Presentation output is allowed to use |
| `MathML4` | MathML 4.0 (Full), W3C Working Draft or later (pin the dated version at stage 1) | Content markup changes, `intent` and `arg`, Strict Content |
| `OpenMath2` | OpenMath 2.0 standard and the content dictionaries (`arith1`, `relation1`, `linalg1`, `linalg2`, `integer1`, `minmax1`, `transc1`, `calculus1`, ...) | meaning of Strict Content symbols |

A theorem that holds for MathML 3 and MathML 4 is stated twice, or over a
parameter that names the version, so a MathML 4 change cannot silently alter
a MathML 3 result.

## 2. What exists

- `formal/lean4/L4Factoidal/MathML/Core.lean` (477 lines): Content `Expr`,
  exact rational evaluation, matrices through `Math/Matrix.lean`.
- `MathML/FromXml.lean`: Content MathML through the XML parser and
  `XML.NamespaceView` (`apply`, `ci`, `cn` with `integer`/`real`/`rational`,
  `matrix`, `vector`, `semantics`, `true`, `false`).
- `MathML/Present.lean`: `toPresentationMathML` (elements `math`, `mrow`,
  `mi`, `mn`, `mo`, `mfrac`, `msqrt`, `mroot`, `msup`, `mtable`, `mtr`, `mtd`,
  `mtext`, `merror`, with minimal parentheses by precedence) and
  `toContentMathML` (round trip with `FromXml`).
- `MathML/FromJson.lean` (the TOAN JSON shape), `Math/` (simplify,
  differentiate, substitute, series, matrices).
- Scores (`docs/web/hub/records/lean-scoreboard-2026-10-25.txt`): `l4mathml`
  81 pass, 0 fail (out of 81), authored from MathML 3 Chapter 4 with the REC
  section in each case (`third_party/testing/mathml/README.md`); `l4toan`
  parity battery 114 pass, 0 fail (out of 114), not a W3C suite.
- MathML in HTML: the HTML tree builder handles MathML foreign content and
  the MathML integration points (`HTML/TreeBuilder.lean`), and
  `XPath4/Html.lean` puts those elements in the MathML namespace. So MathML
  inside an HTML page reaches `FromXml` with no extra parser.

## 3. What "finish" means

| Part | Model or rendering | Done when |
|---|---|---|
| C1. Content MathML: every operator of the content dictionaries that `Math/` and `MathML/Core` evaluate, read and written | model | each operator has a case in the corpus, read and evaluated |
| C2. Non-strict to Strict Content translation (MathML 3 §4.6, MathML 4 equivalent) | model | a function `toStrict`, and theorem 1 |
| C3. Strict Content to and from OpenMath objects (XML encoding) | model | theorem 2 |
| P1. Presentation output in MathML Core only | model | theorem 3 and a vocabulary check |
| P2. Presentation input: read Presentation MathML (Core) into a tree, normalise `mrow`, serialise back | model | round-trip tests; no evaluation of Presentation, since it has no defined meaning |
| P3. Content to Presentation for the whole C1 vocabulary (MathML 4 Chapter on rendering of Content; the earlier "wave 1" list) | model | every C1 operator renders; browser sweep shows each |
| I1. `intent` (MathML 4): read the intent grammar, and emit `intent` on Presentation output from Content (so screen readers get the meaning) | model | intent parser tests from the MathML 4 examples; Presentation output carries an intent that parses and names the Content head |
| R1. Rendering | browser | a page in the hub shows each P3 case; `tests/web-demos` sweep with headless Chromium checks that each `math` element has a layout box with non-zero size |

Out of "finish": layout, fonts, line breaking, stretchy operators. Those are
the browser's MathML Core implementation.

## 4. Test suites

- **Own corpus**: `third_party/testing/mathml/` (exists; REC-cited). Add
  cases per C1 operator, with the MathML 4 section.
- **MathML 4 and MathML Core examples**: the specification sources
  (https://github.com/w3c/mathml, https://github.com/w3c/mathml-core) hold
  the examples. Stage 1 extracts the Content, Strict and `intent` examples as
  test inputs, with the commit in `PROVENANCE.md`. The expected results are
  the ones the text states (for example the Strict form of a non-strict
  example).
- **web-platform-tests `mathml/`** (https://github.com/web-platform-tests/wpt):
  mostly rendering reference tests, which test browsers, not Factoidal. The
  `mathml/relations/html5-tree/` parsing cases test the HTML parser's MathML
  foreign content; vendor those only, with provenance.
- **OpenMath**: the content dictionary files (`.ocd`) are the source for the
  symbol list of C1 and C3; vendor the ones used, with their licence.

## 5. Reuse

XML parser and namespace view; HTML parser for MathML in HTML; XML
serialisation; `Math/` for evaluation and simplification; the exact rationals
of `MathML/Rat.lean`; XSD for `cn` lexical forms. No second expression type:
OpenMath objects map to the same `Expr`.

## 6. Theorems to aim for

1. **Strict translation keeps the value** (`MathML3`, and again for
   `MathML4`): `eval (toStrict e) = eval e` for every non-strict `e` that the
   evaluator defines.
2. **Strict Content and OpenMath are the same objects**:
   `ofOpenMath (toOpenMath s) = s` and the converse, for Strict Content `s`.
3. **Presentation output is MathML Core**: every element and attribute name in
   `toPresentationMathML e` is in the `MathMLCore` vocabulary list (a
   structural induction over `Expr`, with the list as a Lean value taken from
   the pinned snapshot).
4. **Round trip** (exists as tests; make it a theorem): reading
   `toContentMathML e` gives `e` up to `simplify`.
5. **Intent agrees with Content**: the intent that P3 emits, read by the
   intent parser, names the same head and argument order as the Content
   expression it came from.

## 7. Staged plan

| Stage | Work | Measure |
|---|---|---|
| 1 | Pin MathML Core and MathML 4 versions; vendor the example corpus and the WPT html5-tree cases with provenance; audit C1 (heads read, evaluated, rendered) as a table | ledger row per suite; the audit table in this record |
| 2 | Theorem 3 and the `MathMLCore` vocabulary list (no code change expected: the current output uses only Core elements) | theorem builds |
| 3 | `toStrict` and theorem 1 | example corpus score |
| 4 | P3 for every C1 head; the hub page; browser sweep | sweep result |
| 5 | OpenMath encoding and theorem 2 | OpenMath round-trip tests |
| 6 | `intent` parser and emission; theorem 5 | MathML 4 intent examples |
| 7 | P2 Presentation input | round-trip tests |

## 8. Decisions recorded here (coordinator, not owner)

- The front end gets serialisation only; no JavaScript math library, as the
  hub rule already says (no third-party code from a CDN).
- Presentation MathML has no evaluation semantics in Factoidal. A meaning
  comes from Content markup or from `intent`.
