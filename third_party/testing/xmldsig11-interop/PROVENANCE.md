# XML Signature 1.1 interop test vectors (vendored)

Vendored 2026-11-01 for `lake exe l4xmldsig` (`formal/lean4/Harness/XmlDsigRun.lean`),
the runner of `formal/lean4/L4Factoidal/XML/DSig11.lean` (XML Signature Syntax
and Processing Version 1.1, W3C Recommendation 11 April 2013). Tracking:
https://github.com/danbri/factoidal/issues/1165 (track B, item 4).

- Source: the test file directory of "XML Signature 1.1 Interop Test Report",
  W3C Working Group Note 13 November 2012,
  https://www.w3.org/TR/2012/NOTE-xmldsig-core1-interop-20121113/ (fetched as
  https://www.w3.org/TR/xmldsig-core1-interop/interop/xmldsig11/oracle/), on
  2026-11-01. Every file of the directory listing was copied unchanged (45
  signatures and `README.txt`). The `keys` subdirectory that `README.txt`
  names is not in the published listing.
- These are Oracle's vectors. The report also names test vectors of Microsoft
  and Sun; the W3C site does not publish them.
- `README.txt`: "HMAC key is "testkey"".
- The report, section 6.2: `signature-enveloping-hmac-sha1-truncated40.xml`
  "should be rejected" (HMACOutputLength 40, below the minimum of §6.3.1);
  every other file is a valid signature.
- `SHA256SUMS`: the sha256 of each file as vendored.
- Copyright: W3C. Test material of a W3C Working Group Note, used under the
  W3C document licence (https://www.w3.org/Consortium/Legal/copyright-documents).
