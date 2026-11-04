# XML Signature interop vectors of 2001 (vendored)

Vendored 2026-11-01 for `lake exe l4xmldsig` (`formal/lean4/Harness/XmlDsigRun.lean`),
the runner of `formal/lean4/L4Factoidal/XML/DSig11.lean` (XML Signature Syntax
and Processing Version 1.1, W3C Recommendation 11 April 2013). Tracking:
https://github.com/danbri/factoidal/issues/1165 (track B, item 4) and
https://github.com/danbri/factoidal/issues/1225 (the XSLT transform).

- Source: `01-merlin-xmldsig-twenty-three.tar.gz`, attached by Merlin Hughes
  (Baltimore Technologies) to the XML Signature Working Group list, fetched from
  https://lists.w3.org/Archives/Public/w3c-ietf-xmldsig/2002AprJun/att-0016/01-merlin-xmldsig-twenty-three.tar.gz
  on 2026-11-01 (tarball sha256
  `781be470bb2d2b6805a2de4936443f815c4dd6fa5b1aa196d6f15c30f0b76081`). The
  XML Signature interop report
  (https://www.w3.org/Signature/2001/04/05-xmldsig-interop.html) links it.
  Every file was extracted unchanged into `merlin-xmldsig-twenty-three/`
  (mode set to 0644).
- `xml-stylesheet.b64`: fetched from
  https://www.w3.org/Signature/2002/04/xml-stylesheet.b64 on 2026-11-01,
  unchanged. Two references of the vectors name it, and its decoded octets
  are the text that `http://www.w3.org/TR/xml-stylesheet` served in 2001
  (SHA-1 `60NvZvtdTB+7UnlLp/H24p7h4bs=`, the DigestValue of those
  references). The page at that URI has changed since then, so the runner
  gives these octets for it and never reads the network.
- `Readme.txt` of the set: the HMAC key is `secret`; `signature.xml` has
  references of the forms `""`, `#xpointer(/)`, `#foo` and
  `#xpointer(id('foo'))`, manifests, an XPath with `here()`, an XSLT
  transform and a RetrievalMethod; `signature-*-c14n-*.txt` are the
  intermediate canonical forms.
- The signatures are DSA (`dsa-sha1`) except the two HMAC-SHA1 ones and
  `signature-enveloping-rsa.xml` (RSA with a 1024-bit key). The runner checks
  reference validation of every reference and core validation of each
  signature; DSA and the 1024-bit key are expected failures that name
  https://github.com/danbri/factoidal/issues/1224 and
  https://github.com/danbri/factoidal/issues/1227.
  `signature-enveloping-hmac-sha1-40.xml` (HMACOutputLength 40) was valid
  under XML Signature 1.0 of 2002; XML Signature 1.1 §6.3.1 requires its
  refusal, and the runner requires the refusal.
- `SHA256SUMS`: the sha256 of each file of `merlin-xmldsig-twenty-three/`
  as vendored.
- Copyright: the author's test material, distributed through the W3C public
  list archive of the XML Signature Working Group; `xml-stylesheet.b64` is
  the base64 form of a W3C Recommendation, under the W3C document licence
  (https://www.w3.org/Consortium/Legal/copyright-documents).
