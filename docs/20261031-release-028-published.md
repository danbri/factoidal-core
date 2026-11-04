# Published 0.28.0 and hub pin

Published from core `e5057984e388be6534fef19cdbb869b5b5652a17` through
https://github.com/danbri/factoidal-builds/actions/runs/41176153022.
The exact build passed 1976 package tests and seven comparison tests, with
zero failures or skips:
https://github.com/danbri/factoidal-builds/actions/runs/41154673265.

The registry tarball SHA-256 is
`f158022cda51b601106264fbe4e3f2957f1f634dbaeae79a6bf504326fdacbf7`,
identical to the publishing workflow output. The downloaded registry package
passed 22 installed consumer tests covering QT4 API/node/CLI, HTML parsing,
LWS path/header/redirect boundaries, release stamp and generated-sequence/date
regressions. The release browser and strict-CSP checks pass; their stale
streaming expectation was corrected separately in PR284. Published CDN Chrome
smoke returned version0.28.0, XPath node result `1`, `proved:false`, and an RDF
parse of one triple. Ordinary npm install resolves the registry tarball after
initial registry/CDN propagation delay.

Hub release data now selects0.28.0. Twenty focused hub surface/composition tests
pass against the installed official artifact. The compositor retains its own
explicit0.27.0 pin and source proof references. No claim is made that all hub
notebook tests or native WebDAV tests pass. No new native executable release
is included. StaticTyping, QName, SERVICE and graphics work remain separate.

npm signed publication and SLSA provenance attestations are available; the
publication transparency record is
https://search.sigstore.dev/?logIndex=3611308852.
The statement names the builds repository workflow, while the engine stamp
names the core commit. A downloaded statement alone is not cryptographic
verification; the independent npm signature audit result is recorded in the
release issue: https://github.com/danbri/factoidal/issues/1211.
