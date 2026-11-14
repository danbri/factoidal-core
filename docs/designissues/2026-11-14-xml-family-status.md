# The XML family: what is implemented and what the suites measure (2026-11-14)

Date: 2026-11-14. Branch `wip/xml-specs` (https://github.com/danbri/factoidal-core/pull/432).

This record gives, for each XML-related specification in the tree, the suite that measures it, the counts
measured on 2026-11-14 on origin/main 19fb349c1, and what is open. Every number in the column "measured" was
run that day with binaries built from that commit (`lake build l4qt4 l4xsd11 l4xslt4 l4mathml l4xsd-datatypes
l4relaxng l4schematron l4xinclude l4c14n l4xmlconf l4xml-namespaces l4xslt`, `ulimit -s 65520`); a number
marked "record" was not run again and its record is named. An unsupported case is never a pass. The changes
made on the branch after the measurement are in the last section.

## Summary table

| Specification | Suite | Measured today (pass / fail / unsupported, of total) | Last record before today |
|---|---|---|---|
| XSD 1.1 Part 2 Datatypes | W3C xsdtests 7bc3365c, instance tests whose question is a Part 2 one (`l4xsd-datatypes`) | 16,135 / 0 of 16,135 scored; 2,925 more are "unreadable-pattern" and not scored | 18,955 / 0 of 18,955 scored, 105 unreadable-pattern (2026-10-10, `docs/designissues/2026-09-07-xml-schema-datatypes.md`) |
| XSD 1.1 Part 1 Structures | W3C xsdtests 7bc3365c, all of `suite.xml` (`l4xsd11`) | 41,089 / 485 / 94 of 41,668 (98.6%); 67 not applicable (XSD 1.0 only) | 41,086 / 479 / 103 (2026-10-28, PR 206 comment) |
| XPath 4.0 + F&O 4.0 | qt4tests b1616b79 (`l4qt4 --isolate 60`) | 29,478 / 51 / 9,145 of 38,674; 5 excluded as defective data | 28,331 / 695 / 9,633 of 38,659 (2026-10-28) |
| XQuery 4.0 (+ Update, Full Text, EXPath) | qt4tests b1616b79 (`l4qt4 --lang xquery --isolate 60`) | 46,023 / 539 / 904 of 47,466; 11 excluded | 42,305 / 1,735 / 1,906 of 45,946 (2026-10-28) |
| XSLT 4.0 (includes the 3.0 tests) | qt4cg/xslt40-test 91328fbf, vendored subset, 257 of the catalog's 278 test sets (`l4xslt4 --isolate 60`) | 11,687 / 703 / 1,400 of 13,790; 12 excluded as defective data | none found in a record |
| EXPath Binary 4.0, File 4.0 | qt4tests `bin/`, `file/` (`l4qt4 --lang xquery --family bin --family file`) | bin 649 / 0 / 0 of 649 (23 excluded as defective data); file 270 / 0 / 0 of 270 | bin 647 / 0 / 2 of 649; file 265 / 2 / 3 of 270 (2026-10-28) |
| Serialization 4.0 | qt4tests `ser/` (`--family ser`) | 434 / 17 / 56 of 507; 1 excluded | — |
| XSD types in XPath | qt4tests `xs/` (`--family xs`) | 219 / 1 / 12 of 232 | — |
| XSLT 1.0 slice | 88-test pin (`l4xslt`; cloud `xslt` row) | 87 / 0 of 87 decided, 1 refused | cloud 2026-11-14 25c3a4510: 87 of 88 |
| XForms | none vendored until today | no suite run exists; 24 `#guard`s in `XForms/BindTests.lean` and one npm test | same |
| Content MathML (evaluation) | own corpus of 81 cases written from MathML 3 chapter 4 (not a W3C suite) (`l4mathml`) | 81 / 0 of 81 | cloud `mathml` row 2026-11-14 25c3a4510: 81 of 81 |
| MathML in the browser | WPT `mathml/` | not run for this record | 445 of Chrome's 4,321 subtests, 10.3% (full run of main 19fb349c1, Linux, 2026-11-14 03:14 UTC) |
| RELAX NG | James Clark's spectest + compacttest (`l4relaxng`) | 965 / 0 of 965; compact 87 / 0 of 87; 1 expected failure, 0 stale | same (2026-10-29) |
| Schematron | own corpus of 8 (`l4schematron`) | 8 / 0 of 8 decided | cloud 2026-11-14: 8 of 8 |
| XInclude | W3C XInclude suite 2006-09-27 (`l4xinclude`) | 166 / 0 of 174, 8 expected failures, 0 stale | — |
| Canonical XML 1.0, 1.1, Exclusive | W3C/interop vectors (`l4c14n`) | 141 / 0 of 141; 2 excluded as defective data | — |
| XML 1.0/1.1 + Namespaces (Lean) | W3C xmlconf (`l4xmlconf`) | plain 1,861 / 0 of 1,861; namespaces 56 / 0; encodings 65 / 0; XML 1.1 258 / 0; validating 2,184 / 0 of 2,184; output 46 / 0; local 51 / 0 + 1 expected failure | same (2026-10-10) |
| XML (F\* runner, cloud) | W3C xmlconf (`xml_runner`) | not run for this record | cloud 2026-11-14 25c3a4510: 1,447 pass, 1,138 skip of 2,585 |
| Namespaces in XML | `eduni/namespaces` (`l4xml-namespaces`) | 54 / 0 of 54 scored; 3 optional, 2 non-UTF-8 | — |
| xml:id, XML Base | no suite of their own; 52 local fixtures inside `l4xmlconf` ("xml-local") cover xml:lang / xml:id / xml:base | 51 / 0 + 1 expected failure of 52 | — |
| XProc 3.1 | xproc-test-suite (`l4xproc`) | not run today (71 more modules to build; disk) | 2,243 / 125 / 995 of 3,363 (2026-10-29, `2026-10-29-xproc31-progress.md`, thirteenth run) |
| XML Signature 1.1 | xmldsig11 interop + merlin vectors (`l4xmldsig`) | not run today (95 more modules to build; disk) | 15 / 0 of 15 (2026-11-01, `2026-11-01-xml-signature-11.md`) |
| DOM XPath in the browser | WPT `domxpath/` | not run for this record | 2 of 1,171 (0.2%), full run of main 19fb349c1 |
| DOM Parsing in the browser | WPT `domparsing/` | not run for this record | 265 of 3,731 (7.1%), same run |
| XML in the browser | WPT `xml/` | not run for this record | 46 of 242 (19.0%), same run |

## XML Schema: was it ever completed?

**Datatypes (Part 2): complete on what it scores, but the scored set had shrunk.** `l4xsd-datatypes` on main:
16,135 pass, 0 fail (out of 16,135 scored). The record of 2026-10-10 had 18,955 of 18,955 with 105 tests in the
"unreadable-pattern" bucket; today that bucket has 2,925. Cause: since commit
62d7be16e (2026-10-22) `XSD.patternMatches` compiles patterns with the shared profile `Regex.Profiles.compileXsd11`,
which refuses `\d`, `\D`, `\w`, `\W`, category escapes and class subtraction, and a pattern it cannot read makes
its group vacuous. So 2,820 pattern tests left the score without a failure showing, and the Part 2 validator
`XSD.validate` accepts a value that breaks such a pattern. The Part 1 engine does not have this gap: `XSD11/Pattern.lean`
falls back to the F&O 4.0 parser. Fixed on the branch (last section).

**Structures 1.1 (Part 1): 98.6%, not complete.** `l4xsd11` today: schema tests 14,999 pass, 295 fail, 60
unsupported; instance tests 26,090 pass, 190 fail, 34 unsupported; total 41,089 pass, 485 fail, 94 unsupported
(out of 41,668); 67 not applicable (XSD 1.0 only). By contributor (pass / fail / unsupported of total):
NIST 23,170 / 0 / 0 of 23,170; Microsoft 14,171 / 240 / 6 of 14,417; Sun 1,594 / 13 / 3 of 1,610; Saxonica
1,193 / 182 / 0 of 1,375; IBM 787 / 47 / 85 of 919; Boeing 18 of 18; Oracle 26 of 26; WG 39 / 2 of 41; common
91 / 1 of 92. Largest failing sets: `msMeta/Regex` 52 fail of 4,021; `msMeta/DataTypes` 46 of 3,434;
`saxonMeta/Wild` 40 of 284; `msMeta/Schema` 33 (+3 unsupported) of 156; `saxonMeta/Id` 32 of 121;
`saxonMeta/Simple` 32 of 108; `saxonMeta/CTA` 30 of 113; `ibmMeta/idIDREF` 13 fail + 46 unsupported of 134;
`ibmMeta/constraintsOnAttribute` 22 unsupported of 22; `msMeta/Additional` 20 (+3); `msMeta/IdentityConstraint`
16 of 1,064; `msMeta/Particles` 15 of 1,370; `saxonMeta/Open` 15 of 165; `saxonMeta/All` 12 of 110.
XSD 1.0 has no separate score: the 67 "1.0 only" cases are not run.

Open, precisely:
1. Part 2 pattern reader: 2,925 pattern tests unscored (above).
2. The 485 failures and 94 unsupported listed by set above.
3. Issue list of https://github.com/danbri/factoidal/issues/1152 (open, no comments): `fn:node-type-annotation`
   / `fn:atomic-type-annotation`; user-defined atomic types in XDM values (`instance of my:type`, `cast as my:type`);
   assertion context element should be parentless (§3.13.4.1); the theorem that `XPath4.castFromString` accepts
   every literal `XSD.valueOf` accepts is not proved; restriction and UPA checks explore at most 400 residual
   states; one finding in the suite's schema for schema documents is ignored; `use-xsi-schema-location`;
   `xsl:import-schema` and the `validation` attributes of XSLT are not wired to the hook.
4. Theorems proved (record): `validateElement_erase`, `assessRoot_erase`, `validateSimple_ok`,
   `xsdPatternRe_shared`, `patternOk11_shared`, `valueOf_builtin`, `shacl_datatype_is_xsd`. Not proved: that
   validation agrees with the content-model derivative as a stated theorem; determinism holds by construction
   (a pure function) but is not stated.

## QT4

Vendored copy: `third_party/testing/qt4tests` at qt4cg/qt4tests b1616b79 (2026-10-28). Upstream head today is
69636709 (2026-11-13): the copy is **78 commits behind, 128 files changed** (largest: `fn/update.xml` +1,059 −358,
`prod/NamedRecordTypeDecl.xml` +797, `app/fo-spec-examples.xml` rewritten, `file/file.xml` +334,
`fn/load-xquery-module.xml`, `fn/matches.re.xml` +272, `prod/CastableExpr.xml` +251, new `prod/CoerceExpr.xml`,
new `app/atomic-set.xml`, six new `app/Demos`). Not updated yet (it needs a provenance entry and a re-baseline).
`third_party/testing/xslt40-test` is at qt4cg/xslt40-test 91328fbf, which is still upstream head (0 behind).

**XPath 4.0 mode** (families prod, op, fn, map, array, math): 29,478 pass, 51 fail, 9,145 unsupported (out of
38,674). Unsupported by cause:

| Cause | Cases |
|---|---|
| The test is for XQuery only (`spec=XQ10+`, `XQ30+`, `XQ31+`, `XQ40+`, …): not an XPath test | 8,748 |
| The test is for versions before 4.0 only (XP20/XP30/XP31/XQ.. lists that exclude 4.0) | 376 |
| Source document not valid or not loadable (IDREF with no ID 5; 3 files) | 8 |
| `fn-format-integer-CLDR` 4, `unicode-version=7.0` 2, `!FULLY-NORMALIZED` 2, `xsd-version=1.0` 2, `directory-as-collection-uri` 1, `format-integer-sequence=一` 1, `!infoset-dtd` 1 | 13 |

So of the 29,550 cases that apply to XPath 4.0 (38,674 − 8,748 − 376), 29,478 pass: **99.76%**; counting every
unsupported case as not done it is 29,478 of 38,674 = 76.2%, but 9,124 of those 9,145 are tests of another
language or version, not missing features. Real gaps: 51 fails + 21 unsupported = 72 cases. The 51 fails:
`butWith` 8, record casts (`cast`/`castable` composite) 7, `fn:location` + `retain-location` 6, decimal division
last digit 4, `fold-left/right` range limit 4, `fn:transform` 4, type annotation functions 4, built-in record
types 3, regex quantifier limit 2, others 9.

**XQuery 4.0 mode** (adds app, misc, ft, upd): 46,023 pass, 539 fail, 904 unsupported (out of 47,466). By family
(pass / fail / unsupported of total): prod 14,156 / 401 / 391 of 14,948; fn 17,478 / 84 / 300 of 17,862; op
4,672 / 20 / 97 of 4,789; misc 4,127 / 16 / 89 of 4,232; app 3,018 / 17 / 21 of 3,056; array 533 / 1 / 3;
map 358 / 0 / 3; math 181 / 0 / 0; **ft (Full Text) 675 / 0 / 0 of 675; upd (Update) 825 / 0 / 0 of 825**.
Unsupported by cause: versions before 4.0 only 684 (376 mixed lists + 308 old XQuery only); XPath only 108;
`xsd-version=1.0` 59; source not valid or loadable 31; `fn-format-integer-CLDR` 4; `schema-location-hint` 3;
Unicode version pins 5; `!FULLY-NORMALIZED` 2; XML 1.0 4th edition 2; collection 2; others 4. Of the 46,674 cases
that apply to XQuery 4.0, 46,023 pass: **98.6%**; with every unsupported case as not done, 46,023 of 47,466 =
97.0%. Fails by cause (largest first): user-defined schema simple types not known to `cast`/`castable`/
`instance of` ("unknown type s:myUnionType" and the like: `prod-CastableExpr` 103, `prod-CastExpr.schema` 68,
`prod-SchemaImport` 27, `prod-InstanceofExpr` 11: about 200); `prod-NamedRecordTypeDecl` 43; `prod-FunctionCall`
16; `prod-ValidateExpr` 16; `prod-CastExpr` 15; `fn-xsd-validator` 12; `fn-deep-equal` 10; then sets of 8 or fewer.

Share done per specification, unsupported counted as not done, on the suites as vendored:

| Specification | Share |
|---|---|
| XPath 4.0 + F&O 4.0 (cases that apply to XPath 4.0) | 99.76% (29,478 of 29,550) |
| XQuery 4.0 (cases that apply) | 98.6% (46,023 of 46,674) |
| XQuery Update (upd family) | 100% (825 of 825) |
| XQuery and XPath Full Text (ft family) | 100% (675 of 675) |
| EXPath Binary 4.0 | 100% (649 of 649) |
| EXPath File 4.0 | 100% (270 of 270) |
| Serialization 4.0 (`ser/`; 49 of the 56 unsupported are tests for older versions only) | 94.8% of the cases that apply (434 of 458); 85.6% of all 507 |
| XSLT 4.0 (cases that apply; see below) | 93.0% (11,687 of 12,567); 84.8% of all 13,790 |

Caveat: these are against the copy of 2026-10-28; upstream has 78 newer commits.

## XSLT

The 88-test corpus is a pin (87 pass, 1 refused today). The real suite is vendored: `third_party/testing/xslt40-test`
(the QT4 fork of w3c/xslt30-test, so it holds the XSLT 3.0 tests plus the 4.0 ones; `tests/misc/docbook`,
`tests/misc/unicode-90`, `tests/fn/json-to-xml` and one streaming data file are left out for size) with the runner
`l4xslt4`. w3c/xslt30-test itself (head fddf1cf9) is not vendored; the QT4 fork carries its tests with their
`spec` dependencies, so the runner marks the 2.0-only and 3.0-only ones.

`l4xslt4 --isolate 60` today (25 minutes): **11,687 pass, 703 fail, 1,400 unsupported (out of 13,790)**; 12
excluded as defective data; 257 of the 278 test sets of the catalog are in the vendored copy. By directory
(pass / fail / unsupported of total): attr 1,449 / 130 / 50 of 1,629; decl 1,305 / 145 / 45 of 1,495; expr
698 / 32 / 9 of 739; fn 1,147 / 74 / 57 of 1,278; insn 1,752 / 144 / 98 of 1,994; misc 1,932 / 74 / 1,112 of
3,118; **strm (streaming) 2,505 / 59 / 0 of 2,564**; type 899 / 45 / 29 of 973.

Unsupported by cause: tests for XSLT 2.0 only 1,079, 3.0 only 59, 2.0 and 3.0 only 49, 1.0/2.0 only 20, with a
second dependency 16 (1,223 tests that no 4.0 processor runs); `xsl-stylesheet-processing-instruction` 23;
"not schema-aware" variants 21; collections 20; streaming fallback 7; not backwards compatible 6; no
disable-output-escaping 5; `xslt40-not-yet-agreed` 5; not XSD 1.1 5; implementation-defined choices (year
range, normalisation forms, package version resolution, decimal digits, calendars, encodings, numbering
languages) about 60. So 12,567 cases apply to XSLT 4.0 and 11,687 pass: **93.0%**; with every unsupported case
as not done, 84.8%.

Fails by test set (703): import-schema 47, error 40, evaluate 31, merge 24, as 20, validation 16, match 15,
number 14, notation 14, document 12, mode.enclosing 12, unparsed-entity-uri 12, accumulator 11,
higher-order-functions 11, static 11, catalog 10, include 10, mode 10, then sets of 9 or fewer. By message:
an expected static error not raised (XTSE…) 47 + 5, expected dynamic error not raised (XTDE…) 29, expected type
error not raised (XTTE…) 14, schema types unknown to `as` ("invalid sequence type 'my:partNumberType'") 14, 10
did not finish in 60 s, 6 stale exclusions (tests listed as defective now pass: the list needs pruning).

## XForms

Exists: `formal/lean4/L4Factoidal/XForms/Bind.lean` (339 lines; binds addressed by element name over `XML.Node`,
XPath 1.0, six model item properties, Kahn's algorithm, `recalculate`, `applyEdit`), `BindTests.lean` (24 `#guard`s),
the F\* original `formal/fstar/XForms.Bind.fst`, the Wasm op `xformsRecalc` and `npm/factoidal/test/xforms.test.js`.
`docs/designissues/2026-10-28-xforms-model-engine.md` is a design with status "design, no code". No instance
XDM, no node-set binds, no events, actions, submission or controls. **The W3C XForms 1.1 test suite had never been
run and was not vendored.** The archive (TestCases11.zip, 544,185 bytes, SHA-256
c577ad19645f7b664a4c9ac9eace96646c4169ec33040d26c5522ed27805024b, 810 files, chapters 2 to 11 plus appendix and
driver pages) is vendored on branch `wip/xml-specs-xforms`. Every case is an XHTML+XForms page whose pass
condition is a sentence for a person; that branch classifies the cases (model, view model, submission, needs a
human reader) and builds the engine and a runner: `docs/designissues/2026-11-14-xforms-engine.md`.

## MathML

- Content MathML: 81 pass, 0 fail (out of 81), but the corpus is this project's own (cases written from MathML 3
  chapter 4), not a W3C suite. `docs/designissues/2026-10-28-mathml-finish.md` is a design with status "no code":
  Strict Content translation, OpenMath, the MathML Core vocabulary theorem, Presentation input and `intent` are
  all open; work on them is on branch `wip/xml-specs-mathml-model`.
- Browser: WPT `mathml/` 445 of 4,321 (10.3%); 218 names: 173 OK, 16 ERROR, 29 TIMEOUT. The engine has no MathML
  layout at all. By sub-directory (Chrome counts at the older commit of `chrome.json`, sum 4,222):
  relations/css-styling 119 of 1,774; relations/html5-tree 293 of 1,529; presentation-markup/operators 9 of 338;
  mrow 1 of 221; scripts 8 of 95; idlharness 11 of 77; spaces 1 of 52; fractions 0 of 49; mpadded 3 of 37;
  tables 0 of 30; radicals 0 of 11; tokens 0 of 5. 78% of the subtests are DOM and CSS relations
  (`MathMLElement`, event handler attributes, tabindex, presentational attributes, box geometry), not glyph
  layout. Work on it is on branch `wip/xml-specs-mathml`
  (`docs/designissues/2026-11-14-mathml-core-layout.md`).

## Changes on the branch (after the measurement)

Measured with the same commands on `wip/xml-specs`; "before" is origin/main 19fb349c1.

| Commit | Change | Before | After |
|---|---|---|---|
| e7f8d6e96 | One reader for the XSD `pattern` facet, `Regex.Profiles.xsd11Re` (restricted profile, then the F&O 4.0 parser with its additions refused), used by Part 2 validation, Part 1 assessment and the RELAX NG XSD datatype library | `l4xsd-datatypes` 16135 pass, 0 fail (out of 16135 scored), 2925 unread patterns; `l4xsd11` 41089 pass, 485 fail, 94 unsupported (out of 41668) | 19060 pass, 0 fail (out of 19060 scored), 0 unread patterns; 41090 pass, 484 fail, 94 unsupported |
| 6de2416dd, 52818bcde | XPath 4.0 and XQuery 4.0: the simple types of the in-scope schema as type names: `cast as`, `castable as`, `instance of`, constructor functions, map key types (`XPath4/SchemaSimple.lean`, `IType.schemaType`, `SchemaSimpleUse`); `op:numeric-divide` on integers and decimals rounded to nearest at 18 digits (`Fn.Numeric.decDivNearest?`) | XQuery mode 46023 pass, 539 fail, 904 unsupported (out of 47466); XPath mode 29478 pass, 51 fail, 9145 unsupported (out of 38674) | XQuery mode 46251 pass, 311 fail, 904 unsupported; XPath mode 29483 pass, 46 fail, 9145 unsupported. No test set has fewer passes |

How a schema simple type is read. The schema hook gives the XSD 1.1 Part 2 body of a named simple type
(`SchemaTypeInfo.body`, an `XSD.SimpleType`). `SchemaHook.simpleUse` classifies the name for the parser: a pure
union of built-in types is the choice of those types (so the existing rules for choice types decide
subtyping, `instance of` and casting); another generalized atomic type (an atomic type with facets, a pure
union with such a member) is `IType.schemaType`; a list type or a union with facets of its own is allowed
only as the target of `cast` and `castable`, XPST0051 elsewhere (XPath 4.0 §3.2.7, §4.19.2). Casting follows
F&O 4.0 §23.3 over the body, with `XSD.valueOf` as the one validator.

Limit, stated: an atomic value carries a built-in type only (`Atomic.ty`), so a cast to a derived atomic type
gives a value of the built-in base, and `instance of` such a type is decided by value (the value's type
derives from the base and its lexical form is valid for the type). A value of the base type that lies in the
value space is therefore an instance here; the specification says that only of a value labelled with the
type. https://github.com/danbri/factoidal/issues/1152 item 2 stays open for the annotation.

## Proved, tested only, open

Proved (no `sorry`; axioms propext, Classical.choice, Quot.sound):

- `XSD11.patternOk11_eq`: the Part 1 and Part 2 `pattern` tests are equal for every list of pattern groups
  and every literal (`patternOk11_shared`, the earlier conditional statement, is kept and follows).
- `Regex.Profiles.xsd11Re_of_compileXsd11`: a pattern the restricted profile reads gets the same regex as
  before; `xsd11Re_none_of_refused`: a pattern both stages refuse has no regex.
- `XPath4.atomInBody_atomic_sound`, `atomInBody_union_sound`, `atomInBody_list`: the by-value instance test is
  sound against `XSD.valueOf`; no atomic value is an instance of a list type.
- `XPath4.castToBody_atomic_sound`: a successful cast to a derived atomic type is the cast to its built-in
  base, and the lexical form satisfies the facets. `castToBody_list_needs_lexical`: a typed value is never
  cast to a list type (XPTY0004). `castToBody_union_keeps`: a value of a member type is kept.
  `firstCast_mem`.
- `Fn.Numeric.divNearestEven_exact`, `decDivNearest_eq_decDiv_of_exact`, `decDivNearest_none_iff`: rounding
  to nearest agrees with truncation when the division is exact, and refuses exactly a zero divisor.

Tested only: the suite runs above; `#guard`s in `XSD/DatatypesTests.lean`, `RelaxNG/Datatypes.lean`,
`XPath4/SchemaSimple.lean` and `Fn/Numeric.lean`.

Open:

- That `xsd11Re` accepts exactly the XSD 1.1 Appendix G language.
- The half-unit error bound of `divNearestEven` when the division is not exact.
- Type annotations of user-defined atomic types on values (issue 1152 item 2); `castFromString` against
  `XSD.valueOf` (item 4).
- `prod-NamedRecordTypeDecl` (42 fails): labelled record types; upstream changed that test set by 797 lines
  after the vendored commit, so the copy is to be refreshed first (with a `PROVENANCE.md` entry and a new
  baseline) before the feature is written.
- The remaining failures and unsupported cases listed per suite above.

## Measured after the merges of 2026-11-14 morning

Runner binaries built from the merged sources; W3C xsdtests 7bc3365c, qt4tests b1616b79, xslt40-test 91328fbf.
Before = main 19fb349c1 (the XML modules did not change on main between it and d799500c7).

| Suite | Before | After |
|---|---|---|
| `l4xsd-datatypes` (Part 2 instance tests) | 16,135 pass, 0 fail (out of 16,135 scored; 2,925 unread patterns) | 19,060 pass, 0 fail (out of 19,060 scored; 0 unread) |
| `l4xsd11` (Part 1) | 41,089 pass, 485 fail, 94 unsupported (out of 41,668) | 41,090 / 484 / 94 |
| `l4qt4` XPath 4.0 | 29,478 / 51 / 9,145 (out of 38,674) | 29,483 / 46 / 9,145 |
| `l4qt4` XQuery 4.0 | 46,023 / 539 / 904 (out of 47,466) | 46,264 / 298 / 904 |
| `l4xslt4` | 11,687 / 703 / 1,400 (out of 13,790) | 11,728 / 662 / 1,400 |
| `l4xforms` (W3C XForms 1.1) | no engine | model 212 / 6 / 31 (of 249); view model 42 / 5 / 36 (of 83); submission 0 / 0 / 100 (of 100); 29 need a human reader |
| WPT domxpath / xml/xslt / xml | 2 of 1,171 / 0 of 187 / 46 of 55 | 1,164 / 183 / 53 (branch checks 43563531377, 43574629255) |

Proved in this round (beyond the list above): `XPath4` loops `castTokens` and `leavesAll` replace `mapM` inside the
fuel-bounded type walks (the four walks are on the tail-recursion allow list with their bound, fuel 16);
`DOM.XPathDom.elemPrefix_xmlNS`, `attrPrefix_xmlNS` (the XPath projection writes a node of the XML namespace with
the prefix `xml`); the DOM XPath theorems now compile with the engine build.
