# QT4 Unicode reuse and namespace lookup agreement

Date: 2026-10-29. Tracking:
https://github.com/danbri/factoidal/issues/1101,
https://github.com/danbri/factoidal/issues/1195,
https://github.com/danbri/factoidal/issues/1181.

## Unicode adapter

The final combined candidate uses shared Unicode 18.0.0 normalization while
XPath `fn:graphemes` retains its exact prior Unicode 15.1 implementation and
tables. The obsolete XPath normalization tables and generator are removed.
`hexVal`, `ccc`, `decompChar` and `decompose` remain available to
collations. XPath still handles form names, errors and FULLY-NORMALIZED;
the low-character shortcut preserves the existing serialization theorem.
WHATWG IDNA and Full Text receive the shared normalization transitively.

`UnicodeBridgeTests.lean`, imported by the existing `FeatureTests` build root,
checks public XPath calls, the compatibility APIs, composing characters with
combining class zero, Hangul, and the retained Unicode 15.1 cluster boundaries.
It also contrasts the shared Unicode 18 segmentation with XPath 15.1 on the
same input. The shared Unicode 18 module is unchanged.

The XPath grapheme migration remains open under
https://github.com/danbri/factoidal/issues/1195. The final candidate defers
that behavior change; it does not alter fixtures, exclude cases, or claim
selectable Unicode versions. Future migration must account for the version
differences below.

## Four explicit version differences in the prior candidate

The older QT4 grapheme fixture describes Unicode 15.1, without per-case
Unicode-version dependencies. Unicode 18 UAX #29 revision 49 changes GB9c
to `Linker Extend* × Consonant`, removing the initial consonant requirement:
https://www.unicode.org/reports/tr29/tr29-49.html#GB9c.

| QT4 case | Code points | Unicode 18 conformance line |
| --- | --- | --- |
| graphemes-1045 | 094D 0915 | GraphemeBreakTest.txt:179 |
| graphemes-1046 | 094D 0308 0915 | GraphemeBreakTest.txt:180 |
| graphemes-1187 | 0061 094D 0924 | GraphemeBreakTest.txt:859 |
| graphemes-1188 | 003F 094D 0924 | GraphemeBreakTest.txt:860 |

Unicode 18 expects one cluster for each row; QT4 expects two. The prior
Unicode 18 XPath candidate reported all four as failures, not exclusions.
The final candidate restores the two-cluster XPath outputs for all four.
The runner and upstream fixtures are unchanged.

[F&O 4.0](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-graphemes)
defines graphemes by UAX #29 and makes the supported Unicode version
implementation-defined. Both versions can conform to that rule. Retaining
XPath 15.1 preserves the pinned QT4 behavior; shared segmentation remains
explicitly Unicode 18.

## Namespace proof

`Doc.namespaceScope` factors the exact original fold out of `buildNode`.
`namespaceScope_eq_original` is proved by `rfl`; existing `DocTheorems2`
proofs still pass. No namespace-construction behavior changes.

The original proposed equality of scope lists is false: the builder prepends
declarations using a left fold, while `XML.applyDeclarations` retains their
source order. `NamespaceBridge.lean` proves equality of prefix lookups under
three explicit premises: local lexical recognition agrees, recognized
declaration prefixes are distinct, and `applyDeclarations` succeeds.
`namespaceScope_lookup_of_inherited` also admits inherited scopes that agree
only on lookups, so declaration order need not agree between tree levels.

`nsNodesOf_sound_lookup` and `nsNodesOf_complete_lookup` replace the old
representation-equality premise with lookup agreement. Completeness retains
the actual scope-length bound required by the namespace-slot representation.
Old theorem APIs remain intact. The new module is imported by `L4Factoidal`;
printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.

Still open: derive lexical recognition agreement from general valid QName
inputs, and carry the namespace invariant through the full stateful
`buildNode`/document construction. This increment does not close
https://github.com/danbri/factoidal/issues/1181.

## Prior Unicode 18 candidate validation

Measured locally on macOS ARM64. Baseline is the pre-Unicode-adapter source
with the definition-preserving namespace helper; the runner was freshly built.
Testing fixtures were restored from an existing populated checkout with APFS
clones, and `tools/ensure-test-env.sh --check` passed before testing.

| Check | Before | Prior Unicode 18 XPath candidate |
| --- | --- | --- |
| QT4 fn-normalize-unicode | 44 pass, 0 fail, 6 unsupported / 50 | unchanged |
| QT4 fn-graphemes | 1189 pass, 0 fail / 1189 | 1185 pass, 4 fail / 1189; cases above |
| QT4 fn-collation | not separately measured | 89 pass, 0 fail / 89 |
| QT4 fn-collation-key | not separately measured | 37 pass, 0 fail / 37 |
| QT4 fn-compare | not separately measured | 234 pass, 0 fail, 1 unsupported / 235 |
| Unicode 18 NormalizationTest | not rerun for baseline | 20172 pass, 0 fail / 20172 |
| Unicode 18 GraphemeBreakTest | not rerun for baseline | 853 pass, 0 fail / 853 |
| WPT URL | not rerun for baseline | 4570 pass, 0 fail / 4570 |
| QT4 Full Text, XQuery mode | not rerun for baseline | 675 pass, 0 fail / 675; 10 existing defective-data exclusions |

Commands (Lean commands run with `formal/lean4` as the working directory):

```sh
lake build l4qt4 l4unicode l4whatwg-url L4Factoidal.XPath4.NamespaceBridge L4Factoidal.XPath4.SerializeTheorems
lake build L4Factoidal.XPath4.UnicodeBridgeTests
.lake/build/bin/l4qt4 --set fn-normalize-unicode --list-fails
.lake/build/bin/l4qt4 --set fn-graphemes --list-fails
.lake/build/bin/l4qt4 --set fn-collation --list-fails
.lake/build/bin/l4qt4 --set fn-collation-key --list-fails
.lake/build/bin/l4qt4 --set fn-compare --list-fails
.lake/build/bin/l4qt4 --lang xquery --family ft --list-fails
.lake/build/bin/l4unicode norm ../../third_party/testing/unicode-18.0.0/NormalizationTest.txt
.lake/build/bin/l4unicode grapheme ../../third_party/testing/unicode-18.0.0/GraphemeBreakTest.txt
```

From the repository root, Node 22:

```sh
node tests/whatwg-url/run.mjs formal/lean4/.lake/build/bin/l4whatwg-url
```

The native targets and named proof/test modules passed. These are targeted
checks, not a full-library build, full QT4 score, or WASM/web-gates result.
The source reachability gate reports one existing unrelated gap,
`L4Factoidal.XProc31.UtilitySteps`. The same gate reports the same gap in
the unchanged Lean baseline checkout; the new bridge and regression modules
are reachable. The obsolescence sweep found one historical statement about
Unicode 16 assigning characters left unassigned by older versions; it remains
true and was retained.
The existing Full Text exclusions are tracked in
https://github.com/danbri/factoidal/issues/1173.

## Final combined candidate validation

After restoring the exact `origin/main` XPath grapheme source and tables,
the following named targets passed from `formal/lean4`:

```sh
lake build L4Factoidal.XPath4.UnicodeBridgeTests l4qt4
lake build L4Factoidal.XSLT4.QtFnTransformTests
.lake/build/bin/l4qt4 --set fn-graphemes --list-fails
.lake/build/bin/l4qt4 --set fn-normalize-unicode --list-fails
```

The final grapheme result is **1189 pass, 0 fail, 0 unsupported (1189 total)**.
Normalization remains **44 pass, 0 fail, 6 unsupported (50 total)**. The
normalization unsupported cases remain work to be handled through genuine
processor configuration; they are not new exclusions. The QName and assertion
regression target also includes the direct XSLT assertion controls.

The final build logs are `/private/tmp/qt4-grapheme-retained-build.log` and
`/private/tmp/qt4-transform-final-direct-tests.log`; the corpus logs are
`/private/tmp/qt4-graphemes-retained-after.log` and
`/private/tmp/qt4-normalize-retained-after.log`. These local checks do not
replace full-library CI or the exact-head `web-gates` required before merge.
