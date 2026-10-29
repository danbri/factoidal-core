# XML canonicalization test cases (vendored)

Vendored 2026-10-28 for `lake exe l4c14n` (`formal/lean4/Harness/C14nRun.lean`),
the runner of `formal/lean4/L4Factoidal/XML/C14n.lean` (Canonical XML 1.0 and
1.1, Exclusive XML Canonicalization 1.0). Tracking:
https://github.com/danbri/factoidal/issues/1165 (track B, item 1).

## `interop-c14n11/`: the Canonical XML 1.1 interoperability test cases

- Source: https://www.w3.org/2007/xmlsec/interop/xmldsig/c14n11/ (directory
  listing of the XML Security Specifications Maintenance Working Group),
  fetched 2026-10-28, every file of the listing copied unchanged (173 files).
- `testcases` lists the 20 cases. For case `C`: `C-template.xml` is the XML
  Signature template (a reference with an XPath Filtering transform and a
  Canonical XML 1.1 transform); `C-IAIK-ref0.digestinput` is the octet stream
  that the IAIK implementation digested; the other `C-*.xml` files are the
  signatures of IAIK, IBM, ORCL, SUN and UPC. `report.html` is the
  implementation report (Thomas Roessler, 2008-01-22): "All five
  implementations submitted identical canonicalization results for all test
  cases."
- The runner takes the expected octets from `C-IAIK-ref0.digestinput`, and for
  `xmlbase-c14n11spec3-103`, which has no IAIK digest input, from
  `C-UPC.output`.

## `rec-c14n10/`, `rec-c14n11/`: the examples of the Recommendations

- Canonical XML Version 1.0, W3C Recommendation 15 March 2001,
  https://www.w3.org/TR/2001/REC-xml-c14n-20010315, section 3 (examples 3.1 to
  3.7). Copy of the page: `rec-c14n10/REC-xml-c14n-20010315.html`, sha256
  `09c02ef3bc0f8364b00b16fb06092637c08e8f38cf223d47a5862eacc2956bc0`.
- Canonical XML Version 1.1, W3C Recommendation 2 May 2008,
  https://www.w3.org/TR/2008/REC-xml-c14n11-20080502/, section 3 (examples 3.1
  to 3.8) and the Appendix table of the modified Remove Dot Segments algorithm.
  Copy of the page: `rec-c14n11/REC-xml-c14n11-20080502.html`, sha256
  `d91a016ac03391255c64bd5f90035b292f1ee97c3ad4076ea8b33ef11fd9673f`.
- The files `exN-input.xml`, `exN-c14n*.xml` and `exN-subset.xpath` are the
  `<code>` blocks of the example tables, extracted from those copies by
  rendering them as a browser does (HTML white space collapsed, `<br/>` a line
  feed, `&nbsp;` a space, entity references replaced). `exN-c14n.xml` is the
  "Canonical Form" of an example; `-uncommented` and `-commented` are the two
  forms where the table gives both. No trailing line feed is added.
- `remove-dot-segments.tsv`: the Appendix table, input and output, one row per
  line, separated by a tab.
- `world.txt`: example 3.5 says "Let world.txt contain "world" (excluding the
  quotes)"; the file holds those five characters.

## `interop-exc-c14n/`: the Exclusive XML Canonicalization interop test vectors

- Source: the test vectors Y1, Y3 and Y4 of the Exclusive Canonicalization
  Implementation and Interoperability Report of the IETF/W3C XML Signature
  Working Group (https://www.w3.org/Signature/2002/02/01-exc-c14n-interop.html,
  Joseph Reagle, revision 1.33 of 2003-05-06), fetched 2026-10-29. Each is an
  attachment to the w3c-ietf-xmldsig mailing list by Merlin Hughes (Baltimore
  Technologies); the archives were unpacked and every file copied unchanged:
  - `merlin-exc-c14n-one/` (Y1, 2002-01-14):
    https://lists.w3.org/Archives/Public/w3c-ietf-xmldsig/2002JanMar/att-0032/01-merlin-exc-c14n-one.tgz,
    sha256 `7011f7bba301f0c27b85920d133ed45c34fe4b5594ad955aec7682c9b1770302`.
  - `merlin-iaikTests-two/` (Y3, 2002-04-18, Gregor Karlinger's examples in a
    signature):
    https://lists.w3.org/Archives/Public/w3c-ietf-xmldsig/2002AprJun/att-0056/01-merlin-iaikTests-two.tar.gz,
    sha256 `0156857e3790362100a57afa48f286eb35a69ef61a0d16ea521cdda25f31e015`.
  - `merlin-c14n-three/` (Y4, 2002-05-31, XPath transforms that select parts
    of the namespace axis, each canonicalized by Canonical XML 1.0, by
    Exclusive XML Canonicalization, and by Exclusive XML Canonicalization with
    an InclusiveNamespaces PrefixList):
    https://lists.w3.org/Archives/Public/w3c-ietf-xmldsig/2002AprJun/att-0228/01-merlin-c14n-three.tar.gz,
    sha256 `6081bcd691295d5f6da0804c939013c6f45bb51146cba426f40a731259e5d24f`.
- In each directory, `c14n-K.txt` is the octet stream that the signature's
  K-th `Reference` (from 0, in document order) gave to its digest, and the
  file with the next number is the canonical form of `SignedInfo`. The report
  lists eight implementations (Apache, Baltimore, IAIK, IBM, Phaos, XMLsec,
  NEC, Datapower) as interoperable on these vectors.
- Y2 (reagle-1) of the report has no archive link and is not vendored.
