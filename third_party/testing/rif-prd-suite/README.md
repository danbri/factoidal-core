# Vendored W3C RIF Test Cases — PRD dialect

The Approved RIF PRD test cases, as the RIF Working Group published them,
unmodified. Driven by `lake exe l4rif --prd` (`formal/lean4/Harness/RifRun.lean`,
engine `formal/lean4/L4Factoidal/RIF/Prd.lean`, XML reader
`formal/lean4/L4Factoidal/RIF/PrdXml.lean`) through `tests/rif-prd/run.sh`.

## Source

- Zip archive: <https://www.w3.org/2005/rules/test/repository/zips/PRD_v1.22.zip>
  (unpacked here as `PRD_v1.22/`; `VERSION.txt` says `1.22`)
- Manifest: <https://www.w3.org/2005/rules/test/repository/PRDTests.xml>
  (vendored as `PRDTests.xml`)
- Format: [RIF Test Cases (Second Edition)](https://www.w3.org/TR/rif-test/)
- Specification: [RIF Production Rule Dialect (Second Edition)](https://www.w3.org/TR/2013/REC-rif-prd-20130205/),
  W3C Recommendation 2013-02-05
- Fetched: 2026-10-29
- sha256:
  - `PRD_v1.22.zip`: `16fe5437b06ff6492c60b5c41588745a7870311347ca1f1d85f8876cb41c5e36`
  - `PRDTests.xml`: `0e3c62e33dfb80ac6769aa29d0ce9d14db63d2ca98b1a479f7b2eaa3b5f54b61`

## Inventory

`PRDTests.xml` lists 53 Approved cases: 34 PositiveEntailmentTest,
7 NegativeEntailmentTest, 3 PositiveSyntaxTest, 3 NegativeSyntaxTest,
6 ImportRejectionTest. 46 of them are also RIF Core cases; their files are
the ones vendored in `../rif-core-suite/Core_v1.22/` (the runner reads them
from there). `PRD_v1.22/` holds the other 7 (Assert, AssertRetract,
AssertRetract2, Modify, Modify_loop, Retract, RDF_Combination_SubClass_5)
and 3 that repeat Core cases (Core_NonSafeness, Core_NonSafeness_2,
No_free_variables); the runner reads each case once.

## Syntax used

The 6 PRD-only cases are read from their RIF/XML files (RIF PRD §8, the
normative syntax). Their presentation-syntax files are informative, and 3
of them do not agree with the XML:

- `AssertRetract-premise.rifps` asserts `"unkown"`; the XML and the
  conclusion say `"unknown"`.
- `AssertRetract2-premise.rifps` has `Retract (?X[ex:discount -> "10")`
  (no `]`).
- `Modify_loop-premise.rifps` writes `pred:numeric-greater-than` and
  `func:numeric-subtract` without `External`; the XML has `External`.

## License

W3C documents, distributed under the
[W3C Document License](https://www.w3.org/Consortium/Legal/2002/copyright-documents-20021231).
No file under `PRD_v1.22/` is modified.
