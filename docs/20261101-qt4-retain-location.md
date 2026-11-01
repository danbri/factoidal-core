# XML parsing retain-location option

The shared `XPath4.XmlParse.parseOpts` now accepts `retain-location` and
validates it with `optBool`. It does not retain or fabricate location metadata.

## Specification and official cases

[F&O 4.0 fn:parse-xml-fragment](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-parse-xml-fragment)
(and the option tables for `fn:parse-xml` and `fn:doc`) defines the option as
`xs:boolean`, default false. The implementation may ignore a true request.
The existing official snapshot `/private/tmp/qt4-fo4-unicode-policy.html`
contains these tables at lines 71587, 71305 and 68937 respectively; SHA-256
`60cbc78c30be60ad2b7c2bd34153891c1527d554863d57e3110c1c9e96a21bba`.
Direct web-tool retrieval on 2026-11-01 exceeded its response-size limit;
this check used that existing snapshot, not a newly fetched specification.

Unmodified QT4 fixtures in sibling checkout
`source/factoidal-qt4/third_party/testing/qt4tests/fn/parse-xml-fragment.xml`
(lines 443–469) contain `parse-xml-fragment-505` (true), `506` (false),
and `507` (string `yes`, requiring XPTY0004). These carry `covers-40="PR2839"`.
Simply adding the key without type validation would incorrectly admit case 507.

## Evidence and boundary

Fresh replay of the frozen October 29 runner `/private/tmp/l4qt4-42531712`
(SHA-256 `cbce4b4c9ef20be1886ad1e9322fe030d1dc2f4155a3362bc20d1acda0ab7dca`)
reported 38 pass, 2 fail, 1 unsupported for the official fragment set. Cases
505 and 506 failed with unknown-option XPTY0004. This is an older-artifact
measurement, not a current-head measurement. Its exit status was zero despite
the two failures; counts must be inspected.

`XmlParseOptionTests.lean` has 13 closed kernel-checked `by decide` examples
and one executable `#guard`. Before the edit, the true/false kernel examples
failed against the existing overlay. After the edit, checking the current
`XmlParse.lean` and all 14 cases succeeded. Other cases preserve wrong-type,
unknown-key, strip-space, XSD-mode, external-trust and unavailable DTD/XInclude
checks. The XSD-mode check uses `#guard` because kernel reduction stalls on its
string-prefix primitive; it is not presented as a theorem.

The focused commands ran from `source/factoidal-routing/formal/lean4`:

```sh
LEAN_PATH=/private/tmp/qt4-retain-location-check lean \
  -o /private/tmp/qt4-retain-location-check/L4Factoidal/XPath4/XmlParse.olean \
  L4Factoidal/XPath4/XmlParse.lean
LEAN_PATH=/private/tmp/qt4-retain-location-check lean \
  L4Factoidal/XPath4/XmlParseOptionTests.lean
```

The isolated prefix uses symbolic links to existing checked dependencies from
`/private/tmp/srx-routing-overlay`, replacing only XmlParse with the fresh output.
The coordinator then imported the test module in `L4Factoidal.lean` and ran
`lake build L4Factoidal.XPath4.XmlParseOptionTests` from the Lean project.
The normal Lake build completed successfully (55 jobs), including all 14
checks. No full corpus build, download or binary copy was performed.
Source admission checks do not establish rebuilt public API or package behavior.
The official runner is absent from this checkout and still needs rebuilding.

After that rebuild, run the unchanged official fragment set and the related
`fn-parse-xml` and `fn-doc` sets. The correct fixture-root argument from the Lean
working directory is `../../../factoidal-qt4/third_party/testing/qt4tests`.
No fixture expectation or unsupported classification was changed.
