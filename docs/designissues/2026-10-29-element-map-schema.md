# Schema-aware element-to-map conversion

Date: 2026-10-29. Tracking:
https://github.com/danbri/factoidal/issues/1101 (QT4 implementation).

## Behavior

The XPath converter previously inferred layouts from the attributes and
children present in each instance. That gave the wrong result for validated
elements whose schema allows absent attributes, repeated children, mixed
content, or a different scalar type from lexical inference.

`SchemaHook.contentInfo` now supplies component facts by annotation QName:
content variety, list/zero-length status, permitted attributes, wildcard/open
content, and maximum child occurrences per expanded name. The default hook
returns no metadata. `XSD11.Load` derives the facts from the existing schema
components and effective facets, including inherited restrictions. A
worklist traverses particles: sequence/all add maxima, choice takes maxima,
and nested groups multiply them. `none` denotes unbounded occurrences; zero
times unbounded remains zero. The worklist has no fixed nesting cap and
adds no native recursive call cycle.

`XPath4.ElemMap` selects layouts in the specified order: explicit element
plan, schema-derived layout, wildcard fallback, then instance inference.
Explicit-layout failure retains its fallback behavior. Untyped conversion
keeps its existing lexical conversion path.

Validated nodes use their PSVI atomized values. List types produce arrays
even with zero or one item; dates and floats retain their types unless an
explicit conversion plan requests a cast. Schema inference is not itself
such a cast. This distinction also applies to attributes and to a host that
supplies typed values without component metadata. Explicit cast failures
use FOJS0010, or preserve the original value when `liberal` is true. Nilled
elements use each layout's null-marker representation.

Rules: [schema-based conversion](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#id-schema-based-conversion),
[layout selection](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#id-selecting-element-layout),
and [element and attribute content](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#element-and-attribute-content),
F&O 4.0 editor's draft dated 2026-10-28. The deployed content section
explicitly permits plan-requested casts of validated atomic values; an
older cached XML rendering omitted that paragraph. The deployed rule is
used here, while automatic schema-to-family casts are deliberately avoided.

No AType, IType, Item, Harness, FeatureSettings, Regex, dependency filter,
or fixture behavior changed. The new tests are imported by the library root.

## Validation

Measured locally on macOS ARM64 in `claude/qt4-element-map-schema`, based on
`108139c94a2fa69bd9c082e0acc6e6c1aba90eb9`. Before/after figures below are
for individual test sets in XQuery mode, not the whole QT4 catalog.

| Test set | Before pass/fail/unsupported | After pass/fail/unsupported |
| --- | --- | --- |
| fn-element-to-map | 186 / 35 / 0 (221 total) | 219 / 2 / 0 (221 total) |
| fn-element-to-map-plan | 21 / 0 / 0 | 21 / 0 / 0 |
| fn-map-to-element | 232 / 1 / 0 | 232 / 1 / 0 |
| fn-node-type-annotation | 6 / 1 / 0 | 6 / 1 / 0 |
| fn-atomic-type-annotation | 3 / 3 / 0 | 3 / 3 / 0 |
| fn-schema-type | 12 / 2 / 0 | 12 / 2 / 0 |
| prod-SchemaImport | 98 / 27 / 20 | 98 / 27 / 20 |

The focused public-query regressions cover schema-vs-instance distinctions,
typed booleans/dates/floats, list arrays and attributes, nested multiplicity,
wildcards, zero-length restrictions, explicit layouts and fallback, nilled
records, and typed/untyped cast failures. Controls distinguish an inferred
float value from an explicit plan conversion to double. The initial focused
test module failed before the implementation; its mixed-content query was
then made explicit about preserving boundary whitespace, as the official
test does.

Commands use `formal/lean4` as the explicit working directory:

```sh
lake build L4Factoidal.XSD11.ElementMapTests l4qt4
.lake/build/bin/l4qt4 --lang xquery --set fn-element-to-map --list-fails --isolate 60
```

The six control sets use the same runner flags. Their before measurements
use the frozen `42531712` runner; the target set was also measured before
the patch with the current runner. The named build and compiled-C recursion
and csimp-reach gates pass for the three changed production modules. The
first recursive particle traversal was replaced by the worklist after the
compiled audit found its foldl call cycle; no allow-list entries were added.

Local evidence: `/private/tmp/qt4-e2m-schema-before.log`,
`/private/tmp/qt4-e2m-schema-red.log`,
`/private/tmp/qt4-e2m-schema-final-targets.log`,
`/private/tmp/qt4-e2m-final-*.log`, and
`/private/tmp/qt4-e2m-{tail,csimp}-audit.log`.
These are targeted checks, not a full-library, WASM, or complete-catalog run.

## Two remaining fixture disagreements

`element-to-map-334` and `element-to-map-335` expect an empty sequence as
the `#content` value of a nilled record. The
[record-layout rule](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#id-record-layout)
requires the singleton null marker `#fn:null`. The implementation and focused
guards use that marker. Both official cases remain visible as failures;
no assertion, fixture, exclusion, or dependency was changed to hide them.

Fixture provenance is qt4tests `b1616b79c7300167c79a8b0790ba79b5e0b7080d`,
recorded in `third_party/testing/qt4tests/PROVENANCE.md`. An upstream
specification/test reconciliation is still needed for those two cases.

The metadata traversal and the layout selection have executable tests, not
a theorem relating the complete implementation to an independent statement
of F&O conversion semantics. Named schema atomic-value identity and labeled
XQuery record types remain separate work.
