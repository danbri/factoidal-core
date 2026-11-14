# W3C XForms 1.1 Test Suite: provenance

* **Path**: `third_party/testing/xforms11/Test/XForms1.1/Edition1/`
* **Source**: <https://www.w3.org/MarkUp/Forms/Test/XForms1.1/Edition1/zip/TestCases11.zip>
  (the archive offered by the suite's own index page,
  <https://www.w3.org/MarkUp/Forms/Test/XForms1.1/Edition1/>).
* **Retrieved**: 2026-11-14.
* **Archive**: `TestCases11.zip`, 544,185 bytes, SHA-256
  `c577ad19645f7b664a4c9ac9eace96646c4169ec33040d26c5522ed27805024b`.
  The archive lists 810 entries: 567 files (2,259,783 bytes) and 243
  directories.
* **What was copied**: every file of the archive, unchanged, with the
  archive's own directory layout (`Test/XForms1.1/Edition1/` holding
  `Chapt02` to `Chapt11`, `Appendix` and `driverPages`). 460 of the files
  are test documents (XHTML with XForms); the rest are the driver pages
  (`driverPages/xml/XF11TestSuite*.xml` list 500 test case entries with
  their specification section and whether they are normative; the
  chapter 1 list repeats 43 cases of other chapters), result templates,
  style sheets, and the data files, schemas and images the cases load.
  Nothing is edited here: classifications and machine-checkable
  expectations are kept outside this directory, in `tests/xforms11/`.
* **Licence**: the suite's index pages (`driverPages/html/index.html`
  and `driverPages/forms/index.xhtml`) state:

  > Distributed under both the W3C Test Suite License
  > (http://www.w3.org/Consortium/Legal/2008/04-testsuite-license) and
  > the W3C 3-clause BSD License
  > (http://www.w3.org/Consortium/Legal/2008/03-bsd-license).

  The W3C Test Suite License permits copying and distribution of the
  unmodified suite; the W3C 3-clause BSD License permits redistribution
  and use with or without modification, with the copyright notice kept.
  Copyright is held by the W3C (MIT, ERCIM, Keio) and the contributors
  to the suite.
* **Consumer**: `lake exe l4xforms` (`formal/lean4/Harness/XFormsRun.lean`),
  which reads the suite read-only, with `tests/xforms11/classification.json`
  and `tests/xforms11/expect/`.
* **Untrusted data**: the files are test inputs. Nothing in them is run
  as code; the scripts inside two cases (4.8.1.a, 4.8.1.b) are not
  executed.
