# Vendored W3C RIF Test Cases — BLD dialect

The Approved RIF BLD test cases, as the RIF Working Group published them,
unmodified. Driven by `lake exe l4rif --bld` (`formal/lean4/Harness/RifRun.lean`,
engine `formal/lean4/L4Factoidal/RIF/Bld.lean`) through `tests/rif-bld/run.sh`.

## Source

- Zip archive: <https://www.w3.org/2005/rules/test/repository/zips/BLD_v1.22.zip>
  (unpacked here as `BLD_v1.22/`; `VERSION.txt` says `1.22`)
- Manifest: <https://www.w3.org/2005/rules/test/repository/BLDTests.xml>
  (vendored as `BLDTests.xml`)
- Format: [RIF Test Cases (Second Edition)](https://www.w3.org/TR/rif-test/)
- Specification: [RIF Basic Logic Dialect (Second Edition)](https://www.w3.org/TR/2013/REC-rif-bld-20130205/),
  W3C Recommendation 2013-02-05
- Fetched: 2026-10-29
- sha256:
  - `BLD_v1.22.zip`: `d32541d91ef612e7dbf145a03bea386273d974500eef926c41f21d3062841721`
  - `BLDTests.xml`: `84d61dbcbadeb73adad2ac6f4e79e382763130853ce447a3a65544acfbd865b6`

## Inventory

32 cases: 26 PositiveEntailmentTest, 5 NegativeEntailmentTest,
1 NegativeSyntaxTest.

## Defective test data

`IRI_from_IRI`, `Multiple_IRIs_from_String` and `Multiple_Strings_from_IRI`
write the built-in `pred:iri-string` as an ordinary atom, without
`External`, in both the XML and the presentation syntax:
https://github.com/danbri/factoidal/issues/1186. They are reported as
excluded; corrected copies are in `tests/rif-bld-local/`.

## License

W3C documents, distributed under the
[W3C Document License](https://www.w3.org/Consortium/Legal/2002/copyright-documents-20021231).
No file under `BLD_v1.22/` is modified.
