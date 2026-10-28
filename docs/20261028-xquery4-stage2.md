# XQuery 4.0 in Lean, stage 2: toward all qt4tests

Date: 28 October 2026. Issue: https://github.com/danbri/factoidal/issues/1101
(QT4). Stage 1: [`20261028-xquery4-stage1.md`](20261028-xquery4-stage1.md).
PR: https://github.com/danbri/factoidal-core/pull/214. Test data: qt4tests
`b1616b79` (`third_party/testing/qt4tests/PROVENANCE.md`).

## How to measure

From `formal/lean4/`, with `ulimit -s 65520`:

    lake build l4qt4
    .lake/build/bin/l4qt4 --isolate 60 --lang xquery --family F    # XQuery mode
    .lake/build/bin/l4qt4 --isolate 60 --family F                  # XPath mode

for each family F of `prod fn op misc app ser map array math bin file xs`.
Add `--list-fails` for the failing and unsupported cases, `--set NAME` for
one test set.

## Results

Last full measurement (commit `d7ee4f24e`, before the `fn` schemas, the
`fn:id` change and the namespace work; a newer run follows in the PR):

| Mode | Pass | Fail | Unsupported | Total |
| --- | ---: | ---: | ---: | ---: |
| XQuery, start of stage 2 | 45040 | 1187 | 1397 | 47624 |
| XQuery, `d7ee4f24e` | 45690 | 786 | 1148 | 47624 |
| XPath, start of stage 2 | 32928 | 106 | 14587 | 47621 |
| XPath, `d7ee4f24e` | 32955 | 105 | 14561 | 47621 |

25 tests are excluded in XQuery mode (defective test data). One set,
`fn-system-properties`, has one pass fewer: with the feature `infoset-dtd`
its case for processors without that feature is not applicable.

## What changed

FLWOR (`XQuery4/Grammar.lean`, `XQuery4/Runtime.lean`):

- the 4.0 `trace` clause (a `let` of `fn:trace`);
- `for key $k as T value $v as U`: both types are checked; a sequence of
  maps (or of arrays for `for member`) is iterated in turn (PR 2715);
- XQST0089: two variables of one `for` binding with one name;
- `group by $v := E` is `let $v := E` before the grouping (§4.13.7), so a
  later spec sees the binding; a grouping variable without `:=` must be
  bound by the FLWOR (XQST0094); the declared type is checked against the
  atomized key; `collation` is used;
- `order by ... collation`: the collation is used, an unknown one is
  XQST0076; without one the default collation is used; with `empty
  greatest` NaN sorts after the other values and before the empty key;
- `allowing empty` checks the declared type of the empty binding.

`try`/`catch`: `fn:error` keeps the error value (atomic items; other
items atomized) and the prefix of the code, and a code in no namespace;
`$err:value` and `$err:map?value` give them. A `finally` clause that gives
a value is XQTY0153.

Constructors and namespaces (subagent work, merged): XQST0118 for end
tags, whitespace rules in tags, the 4.0 pragma syntax (`(#` is a pragma
only when `#)` follows), name test unions, references in braced URIs,
XQST0070, reserved operator names after `element`/`attribute`, prefixes of
namespaced computed attributes, the namespace axis is XPST0003 in XQuery;
in-scope namespaces of nested direct constructors, `xmlns=""`
undeclarations, namespaces in scope for casts in constructor content.

Prolog and modules (subagent work, merged): item types across `import
module`, `%public`/`%private`, annotation values, `declare default
collation` with any collation of `XPath4.collationOf`, `declare default
order empty`, decimal-format checks (XQST0097, XQST0098), context value
declarations, `fn:function-lookup`, `fn:function-annotations` and
`fn:function-name` for prolog functions (closure entries `#xqn`, `#xqa`),
parameter defaults in the focus of the call.

Functions and types, small changes in `XPath4/`:

- subtyping (§3.3.2): name-test subsumption in `element()`/`attribute()`
  tests, type names, `item()`, `node()`, `xnode()` and
  `document-node(a|b)` covered part by part by a choice, records and maps
  as functions with the value type made optional;
- `xs:float` to `xs:string`: the 1e-6..1e6 range is tested on the value of
  the shortest digits (so `xs:float(0.000001)` is `0.000001`);
- `fn:id`, `fn:element-with-id`, `fn:idref`: schema-typed ID and IDREF
  attributes and elements (is-id, is-idrefs);
- the F&O 4.0 schemas of the `fn` namespace (`XSD11/FnSchemas.lean`) are
  in every in-scope schema: `import schema` of the `fn` namespace,
  `fn:analyze-string` results typed, `fn:json-to-xml` with `validate`;
- `fn:json-doc` gives non-XML characters to the JSON parser (FOJS0001).

Runner (`Harness/Qt4Run.lean`): EXPath file tests in XQuery mode (a main
module with an empty prolog is given to the file evaluator); resource
names with `+`; the features `moduleImport` (XQuery) and `infoset-dtd`;
XML 1.0 fifth edition only (`1.0:4-` is not claimed); `assert-xml` with
expected XML written with indentation is also compared by deep-equal
without whitespace-only text nodes (the catalog allows a deep-equal
comparison). Test data: the 11 `upd/TestSources` documents that
`fn/update.xml` reads.

## Theorems

No `sorry`, no new axiom; `#print axioms` gives `propext`,
`Classical.choice`, `Quot.sound`.

- `XQuery4/FlworTheorems.lean`: `flwor_stream_nested`: for `for`, `let`
  and `where` clauses, the tuple-stream FLWOR (`ext "flwor"`, each clause
  over the whole stream) gives a value `r` exactly when the nested reading
  (each clause tuple by tuple, as the XPath 4.0 `for`/`let`/`if`) gives
  `r`; only the error may differ (§2.3.4). With `step_for`, `step_let`,
  `step_where`, `run_basic`, `flatMapE_bind_ok`. `runClauses` is now a fold
  of `stepClause`, with the same behaviour.
- `XQuery4/Theorems.lean`:
  - `validate_xsd11`, `validate_xsd11_error`, `schemaHookOf_validateIn`:
    `validate` is `XSD11.validateNodeIn` of the in-scope schema;
  - `flwor_forKeyValue`, `eval_flwor_forKeyValue`, `flwor_forMember`;
  - `nameOf_ncname`: a computed node name given as a string has an NCName
    local part; `isNCName_xsd_xml`: `XSD.isNCName` implies
    `XML.isValidNCName`; `parseQNameLex_local`;
  - `tokenize_shared`, `replace_shared`, `compileRe4_shared`: the regex
    functions are the XPath 4.0 entries over the shared `Regex` profile
    `compileXPath40` (with `XPath4.matches_shared` for `fn:matches`).

Open: equality of `nestT` with `XPath4.eval` of `flworToXPath` needs a
fuel-monotonicity lemma for `XPath4.eval`; well-formedness of every
constructed tree (https://github.com/danbri/factoidal/issues/1146).

## Not done

- User-defined atomic and union types from an imported schema (about 300
  fails in `prod-CastableExpr`, `prod-CastExpr.schema`, `prod-SchemaImport`,
  `prod-InstanceofExpr`, ...): item 2 of
  https://github.com/danbri/factoidal/issues/1152 (the XSD 1.1 work).
- Labeled record types (`prod-NamedRecordTypeDecl` and others):
  https://github.com/danbri/factoidal/issues/1153; it needs a label on the
  shared XDM map item.
- Identity and order of constructed nodes:
  https://github.com/danbri/factoidal/issues/1145.
- UCA tailorings (`orderBy69`, `group-025`):
  https://github.com/danbri/factoidal/issues/1144.
