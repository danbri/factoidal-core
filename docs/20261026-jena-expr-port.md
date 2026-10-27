# Jena ARQ expression tests and manifests on Factoidal (stages 0 and 0b)

Date: 2026-10-26. Plan: stages 0 and 0b of
`docs/designissues/2026-10-25-jena-style-facade-feasibility.md` (§6).
Owner approval: "Jena - port them sure" (2026-10-26).

Inputs (measured):

- Apache Jena at commit `a1164c5dc5c9e1a9c58d94766c13d870e0a8ba98`, shallow
  fetch into a scratch directory outside the repository. Only test sources
  and manifest data are read. Jena and Maven are not run.
- `@factoidal/core` 0.16.0 web release (wasm from core `0069da82e`,
  `wasmSha256 1b10444e…`), installed by `tools/fetch-builds.sh`. No wasm build.
- The SPARQL texts: SPARQL 1.1 Query (REC) and SPARQL 1.2 Query
  (W3C Working Draft 25 October 2026), XPath F&O 3.1.

## Stage 0: the one-line expression tests

### What is ported

A one-line test is a line `@Test public void NAME() { BODY }` in
`jena-arq/src/test/java/org/apache/jena/sparql/expr/*.java`.

| | count |
|---|---|
| one-line declarations (regex `^\s*@Test\s+public void \w+\(\)\s*\{.*\}\s*$`) | 1,070 |
| ported to SPARQL | 996 |
| not ported (no SPARQL-observable result) | 74 |

The study gave 918 one-line declarations; its count method is not recorded
and gives a different number from this regex. 1,070 is the measured count.

Not ported, with the reason in `cases.json`: 27 `testSafeEquality`
(Jena optimizer API), 22 expression-transform tests (Java API), 11 `testVar`
(Java parser API), 8 SSE algebra syntax (`testSSE`, `evalExpr`), 6
`afn:sprintf` time-zone tests (the result depends on the JVM default time zone).

`tools/jena-facade-study/extract.py` reads each Java call, resolves the class
constants (`dateTime1`, `XSDDatatype.XSDtime.getURI()`, …) and writes a SPARQL
expression plus a check kind that is the Jena helper's assertion:
`sameTerm` (TestSPARQLKeywordFunctions, TestCastXSD: lexical form exact),
`sameValueSameDatatype` (LibTestExpr), `boolean`/`integer`/`decimal`/`double`
(Jena `isBoolean`/`isInteger`/`isDecimal`/`isDouble`), `ebv`, `evalError`,
`parseError`, and others. The prefixes and base of each Jena test class are
kept (TestExpressions has its own `Query` with base `http://base/`). The
binding `env` of TestExpressions and the SSE bindings of TestExpressions3 become
`VALUES` and `BIND(BNODE() …)`.

Port problems found and fixed in the port (class c): `isDouble`/`isDecimal`
are true for every numeric in Jena (`NodeValueInteger.isDouble()`); the global
prefix map needs a base for `<x>`; `testURI("ex:a.")` uses `parseAny`, so the
final `.` is not part of the name; `ExprUtils.parse` compiles a constant regex,
so an invalid pattern fails at parse time in Jena and at evaluation time in SPARQL.

### Suite

`npm/factoidal/test/jena-arq-expr.test.mjs`, data in
`npm/factoidal/test/fixtures/jena-arq-expr/` (`cases.json` 292 KB, derived
from Jena, Apache-2.0, notice in `test/fixtures/NOTICE`; `verdicts.json`).
Each case is one SELECT; the engine computes `?r` and the check `?ok`; JS
reads `?ok` only.

It is in the package suite, not in `tests/`: it runs in about 3 to 6 s, the
fixtures are not in the npm tarball (`files` in `package.json`), and in the
package suite the `web-gates` job runs it on each built wasm. A fix of one of
the defects below then turns its expected failures into unexpected passes on
the build of that fix, and the fix must update `verdicts.json` in the same PR.

Result, `cd npm/factoidal && node --test test/jena-arq-expr.test.mjs`
(0.16.0 wasm): 997 tests, 997 pass, 0 fail, 0 skipped. Of the 996 ported cases:

| verdict | cases |
|---|---|
| Jena's expectation holds (plain assertion) | 620 |
| defect (expected failure, open issue) | 107 |
| divergence (Jena extension or Jena differs from the specification) | 269 |

The 997th test checks the counts and that each unported case has a reason.
A native cross-check (`l4factoidal query --sparql12`, same queries) agrees
with the wasm on all 930 cases that parse.

### Defects (class a)

| group | cases | issue | specification |
|---|---|---|---|
| `string-arg-types-1036` | 37 | https://github.com/danbri/factoidal/issues/1036 | SPARQL 1.1 §17.4.3.1.1-§17.4.3.1.4, §17.4.6 |
| `substr-fn-substring-1036` | 7 | https://github.com/danbri/factoidal/issues/1036 | SPARQL 1.1 §17.4.3.3, F&O 3.1 §5.4.3 |
| `xsd-constructor-relabels` | 49 | https://github.com/danbri/factoidal/issues/1041 (new) | SPARQL 1.1 §17.5, F&O 3.1 §19 |
| `dir-lang-string-functions` | 13 | https://github.com/danbri/factoidal/issues/1042 (new) | SPARQL 1.2 WD §17.4.3, §17.4.3.8, §17.4.3.9 |
| `iriref-digit-573` | 1 | https://github.com/danbri/factoidal/issues/573 (open; the Lean lexer has it too) | SPARQL 1.1 §19.8 [139] |

The two 1036 groups are the cases that
https://github.com/danbri/factoidal-core/pull/126 fixes. Measured: the same
queries on a native `l4factoidal` built from the PR head `7053f548` (in a
separate worktree) meet the Jena expectation in exactly these 44 cases and in
no other case. When PR 126 and this suite are both on main, the two groups
must leave `verdicts.json` (their cases become plain assertions), or the
`web-gates` run of that build fails on 44 unexpected passes.

### Divergences (class b), not failures

| group | cases | specification |
|---|---|---|
| `ext-function-iri` (afn:, lfn:, math:, fn:numeric-*, op:*, sparql:*) | 90 | SPARQL 1.1 §17.6 |
| `ext-syntax` (IDIV, MOD, `idiv`/`mod` infix, EBV(), CALL(), sameValue()) | 52 | SPARQL 1.1 §19.8; SPARQL 1.2 WD §17.4.2.2 |
| `datetime-accessors` (YEAR … SECONDS on xsd:date, xsd:time, xsd:g*, xsd:duration) | 45 | SPARQL 1.1 §17.4.5.2-§17.4.5.7 |
| `lexical-form` (same value and datatype, other lexical form) | 24 | SPARQL 1.1 §17.1 |
| `operator-table` (`<` on xsd:time, xsd:gYear, durations, xsd:dateTimeStamp) | 20 | SPARQL 1.1 §17.3 |
| `equality-of-other-terms` (`'2' = 2`, `1 = true`, durations, gYear) | 15 | SPARQL 1.1 §17.4.1.7; SPARQL 1.2 WD §17.4.2.2 |
| `replace-empty-match` | 6 | F&O 3.1 §5.6.4 FORX0003 |
| `cast-double-to-decimal` | 4 | F&O 3.1 §19.1.2.3 |
| `cast-whitespace` | 4 | F&O 3.1 §19.2 |
| `substr-non-integer` | 3 | SPARQL 1.1 §17.4.3.3 |
| `cast-date-to-datetime` | 3 | SPARQL 1.1 §17.5 |
| `iri-of-blank-node` | 1 | SPARQL 1.1 §17.4.2.8 |
| `lang-tag-case` | 1 | RDF 1.1 Concepts §3.3 |
| `plus-on-strings` | 1 | SPARQL 1.1 §17.3 |

A divergence case fails if Jena's expectation starts to hold, so that the
verdict is read again.

Note for the owner: `equality-of-other-terms` follows SPARQL 1.1 (type
error). SPARQL 1.2 WD §17.4.2.2 `sameValue` lets a processor answer `false`
for `'2' = 2` when it "can determine that their values are not equal".
Factoidal in 1.2 mode still gives the 1.1 error. This is permitted, not a
defect; a choice to answer `false` would change these 15 cases.

## Stage 0b: Jena's own manifests

Runner: `l4w3c` (the hub scoreboard runner, `tools/lean-scoreboard.sh`), built
at core `ba9e7be5`. Script: `bash tools/jena-facade-study/run-manifests.sh <jena root>`.

| manifest | pass | fail | skip | unsupported | total |
|---|---|---|---|---|---|
| `ARQ/manifest-arq.ttl` (9 sub-manifests) | 13 | 58 | 0 | 237 | 308 |
| `ARQ/Scripting/manifest.ttl` (not in manifest-arq) | 0 | 4 | 0 | 0 | 4 |
| `SPARQL-CDTs/manifest-all.ttl` | 104 | 551 | 0 | 0 | 655 |

ARQ, by sub-manifest and class:

- `Syntax-ARQ` 53 and `Syntax-Lateral` 13 unsupported: test types
  `mfx:PositiveSyntaxTestARQ`/`NegativeSyntaxTestARQ` are ARQ syntax, not
  SPARQL (b).
- `Serialization` 165 unsupported: Jena query-serialization round trips,
  a Jena API (b).
- `PropertyFunctions` 5 pass, 43 fail: `list:`, `apf:` property functions are
  Jena extensions (b, SPARQL 1.1 §17.6 does not define property functions).
- `Lateral` 6 pass, 1 fail: LATERAL is not in the SPARQL 1.2 WD (Jena
  extension). The failing case `lateral-1` takes `LIMIT 2` of three labels
  ordered by `?s` only, so which two is not defined (SPARQL 1.1 §15.1, §15.5) (b).
- `EngineMain` 1, `EngineRef` 1, `Extra` 4 unsupported: test type
  `mfx:TestQuery`, which l4w3c does not read (c). Run as
  `mf:QueryEvaluationTest` in a copy: 4 pass, 2 fail. `EngineMain` uses a
  property function (b). `Extra/expr-triple-term` uses a SPARQL 1.2 triple
  term expression and the manifest does not declare SPARQL 1.2; with
  `version: '1.2'` the npm engine answers it (c, runner).
- `ValueTesting` 2 pass, 14 fail: the expected results are `.n3` files, which
  l4w3c does not read ("unknown result format") (c). With the `.n3` files
  renamed `.ttl` in a copy: 16 pass, 0 fail.
- `Scripting` 4 fail: `js:` functions run JavaScript, a Jena extension (b).

SPARQL-CDTs (composite datatypes `cdt:List`, `cdt:Map`, the `cdt:` functions,
FOLD and UNFOLD) is a Jena extension (b). 479 fails are ASK results where a
`cdt:` function is an error; 72 are parse errors on FOLD/UNFOLD. CDT datatypes
were not added (owner has not asked).

No engine defect was found in stage 0b.

## Follow-ups (not done here)

- l4w3c: read `.n3` result files as Turtle, and `mfx:TestQuery` as a query
  evaluation test. That is a harness change; it adds 14 + 4 passes.
- Stage 1 (Graph/Model API) needs the Lean ops in the study's §6.
