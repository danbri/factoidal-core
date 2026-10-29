# RELAX NG test suites (vendored)

Vendored 2026-10-29 for `lake exe l4relaxng`
(`formal/lean4/Harness/RelaxNGRun.lean`), the runner of the RELAX NG modules
`formal/lean4/L4Factoidal/RelaxNG/`. Tracking:
https://github.com/danbri/factoidal/issues/1165 (track B, item 3).

- Source: https://github.com/relaxng/jing-trang, commit
  `a6bc0041035988325dfbfe7823ef2c098fc56597` (HEAD of the default branch on
  2026-10-29). Each file is unchanged.
- `spectest.xml` (from `mod/rng-validate/test/spectest.xml`): James Clark's
  RELAX NG test suite for the OASIS RELAX NG Specification (2001-12-03,
  which ISO/IEC 19757-2 restates). 385 test cases: an incorrect schema, or a
  correct schema with valid and invalid instance documents. Some cases carry
  `resource` and `dir` elements, the files that `externalRef` and `include`
  load.
- `compacttest.xml` (from `mod/rng-schema/test/compacttest.xml`): 90 test
  cases for the RELAX NG compact syntax, each a compact schema with its XML
  syntax equivalent, or an incorrect compact schema.
- `xsdtest.xml` (from `mod/xsd-datatype/test/xsdtest.xml`): tests of the W3C
  XML Schema datatype library as Jing implements it.
- `testSuite.rng` (from `eg/testSuite.rng`): the RELAX NG schema of the test
  suite format.
- `copying.txt`: the licence of jing-trang (BSD-style, Thai Open Source
  Software Center Ltd, 2001-2003).

sha256:

```
3812289f941d4a1aa8ad0ab0f5e16f85f59d912eec710feb86b6b14a6e942a96  spectest.xml
3d541771f488d6a4efe0c788df98e16f152550d7b06ba081097a5d123d7fbe52  compacttest.xml
555fdc11b79c4a165594123e7dc08e431f9fe80cd98c06a91b1209344f455e37  xsdtest.xml
92ebfec92d9e2dcc08107bbcc03fc6d01ad0078e17f2f0422dccc3fdc8641b40  testSuite.rng
37e32425b814d4e69c2ac82d793966d8085ce2fee5501597999a713e61c4ae7f  copying.txt
```
