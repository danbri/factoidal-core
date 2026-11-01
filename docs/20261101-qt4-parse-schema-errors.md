# XML parsing: schema errors in their calling context

F&O 4.0 reserves FODC0007 for DTD validity, uses FODC0014 for invalid
XSD content, and FODC0008 for an invalid `xsd-validation` option or unknown
requested type. Primary normative source:
https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-parse-xml
The locally inspected snapshot `/private/tmp/qt4-fo4-unicode-policy.html`
has SHA256 `60cbc78c30be60ad2b7c2bd34153891c1527d554863d57e3110c1c9e96a21bba`.

`XSD11.Load.validateXmlFor` now adapts the shared validator for the XML
parsing hook. XQuery `validateIn`, XProc's direct `validateFor`, and schema
unavailable FODC0009 remain separate contracts. No schemas, unsupported
features, tests, or skips were removed. This does not implement additional
prefix-based EQName resolution: unsupported/unknown requested types are
refused with the correct parsing error.

The kernel checks `validateXmlFor_ok_iff`: successful document values are
exactly those of the existing validator. `XPathBridge.parseXml_validate`
continues to establish PSVI construction and erasure to the parsed root.
Both audited proofs use only `propext`, `Classical.choice`, `Quot.sound`.
Nine executable guards check invalid types/content, the unchanged shared
error codes, successful integer validation, and missing-schema refusal.

## Measured validation

Lean 4.33.1 checked Load, XPathBridge and XmlParseErrorTests individually.
A targeted native runner replaced only current XmlParse and Load objects
in the existing October 30 `factoidal-qt4` native object graph. This is
targeted native evidence, not a whole-current-HEAD build or npm/WASM release.
No generated files entered the repository. Runner:
`/private/tmp/l4qt4-xsd-errors`, SHA256
`26beb07d6624392b180fdddbcb04b5abfd135a3544f15cd6d37f678a6fcbe531`.

Unmodified official QT4CG fixtures at commit
`18728a6943589f8341d67f94af154e3c68917bbb`:

| Set | Before: pass/fail/unsupported | After |
|---|---|---|
| fn-parse-xml | 50 / 4 / 3 | 53 / 1 / 3 |
| fn-parse-xml-fragment | 40 / 0 / 1 | 40 / 0 / 1 |
| fn-doc | 75 / 1 / 3 | 75 / 1 / 3 |
| prod-ValidateExpr | 74 / 16 / 2 | 74 / 16 / 2 |

Cases 434, 438, 439 now pass. Remaining parse-xml case 436 concerns
whitespace stripping before schema validation. Existing fn-doc and XQuery
failures remain visible; this change does not claim full conformance.

Reproduce from `formal/lean4` (change family/set for the other rows):

```sh
/private/tmp/l4qt4-xsd-errors \
  --root ../../../factoidal-qt4/third_party/testing/qt4tests \
  --family fn --set fn-parse-xml --lang xquery --list-fails
```

The harness can exit zero with failures; inspect the printed totals.
