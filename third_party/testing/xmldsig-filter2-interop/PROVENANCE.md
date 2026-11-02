# XML Signature XPath Filter 2.0 interop vectors (vendored)

Vendored 2026-11-01 for `lake exe l4xmldsig` (`formal/lean4/Harness/XmlDsigRun.lean`),
the runner of `formal/lean4/L4Factoidal/XML/DSigFilter2.lean` (XML-Signature
XPath Filter 2.0, W3C Recommendation 08 November 2002,
https://www.w3.org/TR/2002/REC-xmldsig-filter2-20021108/). Tracking:
https://github.com/danbri/factoidal/issues/1165 (track B, item 4) and
https://github.com/danbri/factoidal/issues/1225.

- Source: `02-merlin-xpath-filter2-three.tar.gz`, attached by Merlin Hughes
  (Baltimore Technologies) to
  http://lists.w3.org/Archives/Public/w3c-ietf-xmldsig/2002AprJun/0306.html,
  fetched from
  https://lists.w3.org/Archives/Public/w3c-ietf-xmldsig/2002AprJun/att-0306/02-merlin-xpath-filter2-three.tar.gz
  on 2026-11-01 (tarball sha256
  `5635f741ff26802adfcc1061cb40504de62e4d2d3a82808fce31c018a6d66e7b`). The
  XPath Filter 2.0 interop report
  (https://www.w3.org/Signature/2002/05/xmldsig-filter2-interop.html) links
  it. Every file was extracted unchanged (mode set to 0644).
- These vectors use the algorithm URI of the Recommendation,
  `http://www.w3.org/2002/06/xmldsig-filter2`. The earlier set
  (`merlin-xpath-filter2-two`) uses the draft URI
  `http://www.w3.org/2002/04/xmldsig-filter2` and is not vendored.
- `Readme.txt`: `sign-*-c14n-N.txt` is the canonical output of reference N
  (and, for the last N of `sign-spec`, of `ds:SignedInfo`).
- The signatures are DSA (`dsa-sha1`); the runner checks reference
  validation (the octets and the digests). The signature value is an
  expected failure that names https://github.com/danbri/factoidal/issues/1224
  (DSA).
- `SHA256SUMS`: the sha256 of each file as vendored.
- Copyright: the author's test material, distributed through the W3C public
  list archive of the XML Signature Working Group.
