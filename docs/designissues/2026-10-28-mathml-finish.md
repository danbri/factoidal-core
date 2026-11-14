# MathML: what "finish" means, model and rendering

Date: 2026-10-28. Status (2026-11-14): parts C2 and C3 and theorems 1 to 3 have code and
proofs, with the limits stated in section 9; P2, P3, I1, R1 and theorems 4 and 5 are open. Tracking:
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

## 9. State on 2026-11-14

Stages 2, 3 and 5 of the plan have code and theorems. Stage 1 is done for the versions (below), not
for vendoring: the new cases are authored from the specifications' examples, and no `.ocd` file or WPT
case is vendored. Stage 6 has the reader and writer of the `intent` grammar only. Stages 4 and 7 are
not started.

### Versions read

| Name | Version read |
|---|---|
| `MathML3` | MathML 3.0 Second Edition, W3C Recommendation 2014-04-10, chapter 4 (https://www.w3.org/TR/MathML3/chapter4.html) |
| `MathML4` | MathML 4.0, W3C Working Draft 2026-11-12 (https://www.w3.org/TR/2026/WD-mathml4-20261112/), appendix F "The Strict Content MathML Transformation" |
| `MathMLCore` | MathML Core, W3C Candidate Recommendation Snapshot 2025-06-24 (https://www.w3.org/TR/2025/CR-mathml-core-20250624/), section 2.1 |
| `OpenMath2` | The OpenMath Standard 2.0 revision 3, 2019-07-01 (https://openmath.org/standard/om20-2019-07-01/omstd20.html), sections 2.1 and 3.1 |

MathML 4 moves the transformation from section 4.6 to appendix F. For the constructs below its rules
are the same as MathML 3's (F.2.5 roots, F.4.2 vectors and matrices, F.5.1 n-ary/unary operators,
F.6.2 predicate on list, F.7.1 numbers, F.8.1 minus), so one `toStrict` serves both and the theorems
are not stated twice. Both specifications print `cd="reln1"` in the n-ary relation example; the code
uses `relation1`, the dictionary the operator's syntax table and OpenMath name.

### Decision: `toStrict : Expr → Expr`

`Expr` carries both forms, so the transformation is a function on `Expr` and its theorems are
structural inductions with no XML parser in them. An application `app key args` has a key: the MathML
element name of an operator (`plus`, `rem`), or `cd:name` for an OpenMath symbol that has no MathML
element with the same application shape (`arith1:unary_minus`, `arith1:root`, `nums1:rational`,
`set1:set`, `list1:list`, `fns2:predicate_on_list`, `linalg2:matrix`, `linalg2:matrixrow`,
`linalg2:vector`, `linalg1:matrix_selector`, `linalg1:vector_selector`). Whether `plus` is written
`<plus/>` or `<csymbol cd="arith1">plus</csymbol>` is concrete syntax, decided by the writer, from the
table of 45 keys in `MathML/Symbols.lean`. A key outside the table is an identifier head
(`<apply><ci>f</ci>...`, OpenMath `OMV`).

`Expr` has no constructor for a symbol that is not applied. The one rule that needs one (the relation
handed to `fns2:predicate_on_list`) writes it `app "csymbol" [sym key]`. A constructor would change
every match over `Expr` in `Math/`, `Wasm/Ops` and the labs, which this branch did not build.

### What `toStrict` does (`MathML/Strict.lean`)

| Construct | Rule | Strict form |
|---|---|---|
| `minus` with one argument | MathML 3 §4.4.2.6, MathML 4 F.8.1 | `arith1:unary_minus` |
| `root` | §4.4.2.11, F.2.5 | `arith1:root(x, degree)`, degree 2 when absent |
| relation with other than two arguments | §4.3.4.3.2 "Rewrite: n-ary relations", F.6.2 | `fns2:predicate_on_list(relation, list1:list(...))` |
| `max`, `min` with no argument or two or more | §4.3.4.4.2 "Rewrite: n-ary unary set", F.5.1 | applied to `set1:set(...)` |
| `max`, `min` with one argument | §4.3.4.4.2 "Rewrite: n-ary unary single" | unchanged |
| `rat` (`cn type="rational"`) | §4.2.1.3 "Rewrite: cn sep", F.7.1 | `nums1:rational(n, d)` |
| `vec`, `mat` | §4.4.9.1 to §4.4.9.3, F.4.2 | `linalg2:vector`, `linalg2:matrix` of `linalg2:matrixrow` |
| `selector` | §4.4.9.6 and §4.6 step 8 | `linalg1:matrix_selector(i, j, M)` for three arguments, `linalg1:vector_selector(i, V)` for two |
| every other operator | "Rewrite: element" | unchanged key; the strict writer gives the `csymbol` |

Not covered, because the reader does not read them: qualifiers (`bvar`, `condition`,
`domainofapplication`, `lowlimit`, `uplimit`, `logbase`, `momentabout`), `bind`, `lambda`, `piecewise`,
`interval`, `set` and `list` as containers, `cn` of type `e-notation`, `complex-cartesian`,
`complex-polar` and `constant`, `type` and `definitionURL` attributes, `semantics` annotations (the
reader keeps the first child). A decimal `cn` is read as an exact rational, so it becomes
`nums1:rational`, not a strict `cn type="real"`. With two arguments `selector` always becomes
`vector_selector`: §4.6 says the symbol depends on the type of the argument, and `Expr` has no types.

### C1 audit: the keys `Core.eval` evaluates

Counted on 2026-11-14 in the inputs of `manifest.json` and `matrix-manifest.json` (81 cases). "Symbol" is
the entry of `MathML/Symbols.lean`; "Presentation" is the branch of `Present.pres`.

| Key | Evaluation cases | Presentation | Symbol |
|---|---|---|---|
| `plus`, `times` | 10, 11 | infix | `arith1:plus`, `arith1:times` |
| `minus` | 4 | prefix (one argument), infix (two) | `arith1:unary_minus`, `arith1:minus` |
| `divide` | 4 | `mfrac` | `arith1:divide` |
| `power` | 6 | `msup` | `arith1:power` |
| `root` | 4 | `msqrt`, `mroot` | `arith1:root` |
| `abs` | 2 | bars | `arith1:abs` |
| `quotient`, `rem` | 2, 1 | function form | `integer1:quotient`, `integer1:remainder` |
| `factorial` | 2 | postfix `!` | `integer1:factorial` |
| `gcd` | 2 | function form | `arith1:gcd` |
| `max`, `min` | 2, 1 | function form | `minmax1:max`, `minmax1:min` |
| `eq`, `neq`, `lt`, `gt`, `leq`, `geq` | 3, 1, 2, 1, 1, 1 | infix | `relation1` |
| `determinant`, `transpose` | 5, 2 | function form | `linalg1` |
| `scalarproduct`, `vectorproduct`, `outerproduct` | 2, 2, 1 | function form | `linalg1` |
| `selector` | 3 | function form | `linalg1:matrix_selector`, `linalg1:vector_selector` |
| `matrix`, `vector` literals | 25, 12 | fenced `mtable` | `linalg2:matrix`, `linalg2:matrixrow`, `linalg2:vector` |
| `true`, `false` | 0 (one strict case) | `mi` | `logic1:true`, `logic1:false` |

So every operator `eval` gives a value to has an evaluation case, and the truth values have none.
In the table and read, but refused by `eval` (no exact rational value, or no logic in the evaluator):
`exp`, `ln`, `sin`, `cos`, `tan`, `lcm`, `and`, `or`, `xor`, `not`, `implies`. Any other element name is
read as a key, refused by `eval`, written in function form, and is an identifier head in strict form
and OpenMath. P3 (a Presentation form for each of these beyond function form) is open.

### Evaluation and theorem 1

`Core.eval` is a `partial def`, so no theorem can unfold it. Strict content is evaluated by translating
it back: `unstrict : Expr → Expr` rewrites the strict forms into the forms `eval` reads, and
`evalStrict env e = eval env (unstrict e)`.

### Proved

`#print axioms` on this tree: `propext`, `Classical.choice`, `Quot.sound` for each theorem below, except
the two table theorems of `Symbols`, which rest on `propext` and `Quot.sound` only.

| Theorem | Module | Says |
|---|---|---|
| `toStrict_isStrict` | `Strict` | `isStrict (toStrict e)` for every `e` |
| `toStrict_of_isStrict` | `Strict` | a strict expression is a fixed point of `toStrict` |
| `toStrict_idempotent` | `Strict` | `toStrict (toStrict e) = toStrict e` |
| `isStrict_iff_toStrict_eq` | `Strict` | `isStrict e = true` exactly when `toStrict e = e` |
| `unstrict_toStrict` | `Strict` | `unstrict (toStrict e) = unstrict e` for every `e` |
| `evalStrict_toStrict` (theorem 1) | `Strict` | `evalStrict env (toStrict e) = evalStrict env e` for every `e` and `env`, defined or not |
| `evalStrict_of_native` (theorem 1) | `Strict` | if `unstrict e = e` then `evalStrict env (toStrict e) = eval env e` |
| `keyOf_of_symbolOf`, `symbolOf_of_keyOf` | `Symbols` | the key and symbol columns of the table are inverse |
| `ofOM_toOM` (theorem 2) | `OpenMath` | `ofOM (toOM s) = some s` for strict `s` |
| `ofOpenMath_toOpenMath` (theorem 2) | `OpenMath` | `ofOpenMath (toOpenMath e) = some (toStrict e)` for every `e` |
| `toOM_ofOM_image` (theorem 2, converse on the image) | `OpenMath` | what the object of a strict `s` reads back as writes to the same object |
| `presTree_core`, `presentationTree_core` (theorem 3) | `CoreVocabulary` | every element name in the tree `presTree e`, and in the `math` document tree, is in the MathML Core list |

`isStrict` is a `Bool` function, so it is decidable. Each theorem's doc comment has its "Says" and
"Does not say" lines.

### Tested only

- `lake exe l4mathml` on this tree (2026-11-14): content-mathml evaluation 81 pass, 0 fail, 0 markup-not-read
  (out of 81), the same as before this work; evaluation cases through their strict form 81 pass, 0 fail
  (out of 81); strict content transformation 20 pass, 0 fail (out of 20); OpenMath 17 pass, 0 fail
  (out of 17). The last three lines are new: `third_party/testing/mathml/strict-manifest.json` and
  `openmath-manifest.json`, authored from the examples of the specifications.
- `lake exe l4toan` on this tree, run because `Present.contentOp` and `FromXml.exprOf` changed: TOAN (Lean)
  114 pass, 0 fail (out of 114), the count of the 2026-10-25 scoreboard.
- `#guard` checks, all passing at build: 28 in `MathML/StrictTests.lean` and 35 in
  `MathML/OpenMathTests.lean` (the specifications' examples; OpenMath XML read, and written then read, on
  seven objects; refusals); 31 in `MathML/CoreVocabulary.lean` that the tree serialises to the string
  `Present.pres` writes, at least one per branch of `pres`; 39 in `MathML/Intent.lean` on the `intent`
  values of the MathML 4 examples; 5 in `MathML/Symbols.lean`.
- That `evalStrict` and `eval` agree on an expression with `unstrict e ≠ e`: only the corpus run above.

### Open

- Theorem 1 over `Core.eval` itself: needs `eval` as a total function (structural over `Expr`, with the
  operator dispatch split out), which would also remove a `partial def`. Until then `evalStrict` and
  `eval` are proved equal only where `unstrict e = e`.
- `ofOM o = some e → isStrict e`, and `toOM e = o` for every `o` that `ofOM` reads: not proved (needs
  an induction principle for `OMObj`; one counterexample to the second is named at `toOM_ofOM_image`).
- XML round trip `parseOpenMath (writeOpenMath o) = some o`: tested on the corpus objects, not proved.
  It goes through the XML parser, and through `toString` and `String.toInt?` for `OMI`.
- OpenMath: `OMB`, `OME`, `OMFOREIGN`, `OMR`, `cdbase` other than the default, `id` and sharing are not
  modelled. `OMF`, `OMSTR`, `OMBIND`, `OMATTR` are read and written but have no `Expr` counterpart.
  Symbols outside the 45-entry table are not read as application heads. No `.ocd` file is vendored.
- Theorem 3 on the string: `serializeList (presTree e) "" = pres e` is a `#guard` per branch of `pres`,
  not a theorem. Found while writing it: a vector renders `mtd` directly under `mtable`, with no `mtr`.
- Theorem 4 (reading `toContentMathML e` gives back `e`): not proved. What blocks it: the reader
  `FromXml.exprOf` is a `partial def`, which no proof can unfold, and the statement goes through the
  XML parser (`parseNamespaceView`), for which there is no parse-of-serialise theorem to use. The
  statement also needs hypotheses: `rat n 0` is written and not read back, and a `sym` or key with
  outer white space is trimmed by the reader. With `exprOf` made fuel-bounded or structural, a
  tree-level version (reader of the writer's tree, no parser) is the reachable first step. It stays a
  test (`#guard` in `FromJson.lean`, `OpenMathTests.lean`).
- `intent` (I1): `MathML/Intent.lean` reads and writes the grammar of MathML 4 section 5.1
  (`parseIntent`, fuel-bounded). Nothing emits `intent` on the Presentation output yet, so theorem 5 is
  not stated, and there is no theorem about the reader (a write-then-read theorem is the next step).
- Recursion: the new recursive declarations are bounded by the nesting of the expression (operand
  lists are loops with an accumulator) or are specification only; each has its line in
  `tools/lean-tail-recursion-allow.txt`. `tools/lean-tail-recursion-audit.py --gate` was run on a
  partial build (the modules of `l4mathml`, `l4toan` and the XML runners): it names no MathML
  declaration (the one it names, `Harness_Xslt4Run_filesBelow`, is not touched by this work). The
  full-build gate is CI's.
- Presentation input (P2), the Content to Presentation audit (P3) and the browser sweep (R1): not
  started.
- Built here: the import closures of `l4mathml` and `l4toan` and the new modules. `Wasm/Ops` and the
  labs, which also use `Expr`, `toContentMathML` and `parseMathML`, were not built locally.
