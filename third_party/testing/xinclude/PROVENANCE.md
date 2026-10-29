# XInclude test suite (vendored)

Vendored 2026-10-29 for `lake exe l4xpointer`
(`formal/lean4/Harness/XPointerRun.lean`), the runner of
`formal/lean4/L4Factoidal/XML/XPointer.lean` (XPointer Framework, element(),
xmlns()) and `XML/XPointerXPath.lean` (xpointer()). Later it is the suite of
the XInclude processor. Tracking: https://github.com/danbri/factoidal/issues/1165
(track B, item 2).

- Source: https://www.w3.org/XML/Test/XInclude/XIncl20060927.zip, the W3C
  XInclude test suite of the W3C XML Core Working Group, release of
  2006-09-27, fetched 2026-10-29. sha256 of the zip:
  `1e5519a7e14a096c70645f1d2bcb1d84d01b5788a9cc5acdb4d007967c5527ce`.
- `XIncl20060927/` is the content of the zip, unchanged, except that the
  `CVS/` directories (CVS client metadata, 29 directories) are removed.
- `testdescr.xml` lists 175 test cases from five contributors (Red Hat,
  Fourthought, NIST, LTG Edinburgh University, Elliotte Rusty Harold):
  111 `success`, 64 `error`. 98 `xi:include` elements in the
  test documents carry an `xpointer` attribute.
- Licence: W3C test suite, published by the W3C under the W3C Software and
  Document Notice and License,
  https://www.w3.org/copyright/software-license-2023/ . `README.cvs` gives the
  feedback list.
