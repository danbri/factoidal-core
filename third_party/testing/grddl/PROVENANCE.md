# Vendored W3C GRDDL test suite — provenance

Offline copy of the W3C GRDDL ("Gleaning Resource Descriptions from
Dialects of Languages") test cases, so Factoidal's GRDDL Stage 1 runner
(`bin/grddl-runner/grddl_runner.ml`) can discover transformations,
apply them, and compare result graphs **without any network access**.

There is no upstream git repository for this suite (unlike the other
suites under `third_party/testing/`, which are git submodules). The
files are served as plain documents under
`https://www.w3.org/2001/sw/grddl-wg/td/`, so they are vendored here as
a plain directory tree mirroring the source URL paths.

## What was retrieved

- **Retrieved:** 2026-07-09, via `curl -sS -L` through the session's
  configured HTTPS proxy.
- **Spec:** GRDDL, W3C Recommendation 11 September 2007
  (<https://www.w3.org/TR/grddl/>).
- **Test-cases document:** <https://www.w3.org/TR/grddl-tests/>;
  manifest data root <https://www.w3.org/2001/sw/grddl-wg/td/>.

### Manifest

- `grddl-tests-normative.rdf` — the normative test manifest (RDF/XML).
  - Source: `https://www.w3.org/2001/sw/grddl-wg/td/grddl-tests-normative.rdf`
  - SHA-256: `bb7ddcd379fce93d4128e95f2e97bf065a55f45da3cfc1dd91222ef245e524a4`
- `grddl-tests-normative.n3` — the same manifest in Turtle/N3 (kept for
  human reference; the runner parses the RDF/XML copy).
  - Source: `https://www.w3.org/2001/sw/grddl-wg/td/grddl-tests-normative.n3`
  - SHA-256: `70dba2618dbb5c7eff8e46ae687ad50c585261496e2b6a3838e1dfe69cefdcd6`

The manifest uses the rdfcore test-schema vocabulary
(`http://www.w3.org/2000/10/rdf-tests/rdfcore/testSchema#`) plus the
GRDDL-specific extension vocabulary
(`http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#`), which
adds `exercisesRule`, `alternative`, and the `NetworkedTest` class that
flags tests requiring live HTTP.

### Document tree — `docroot/`

`docroot/` is a URL mirror the runner maps absolute test-suite IRIs
into (`iri_to_local`):

- `docroot/td/`  ← `http://www.w3.org/2001/sw/grddl-wg/td/`
  (input documents, transformation stylesheets, expected-output RDF/XML,
  and the `base/` subdirectory for the xml:base tests).
- `docroot/g/`  ← `http(s)://www.w3.org/2003/g/`
  (the shared GRDDL transformation stylesheets `embeddedRDF.xsl`,
  `inline-rdf.xsl`, and the `glean-profile` profile document).

Every input document, transformation stylesheet, and expected-output
file referenced by the normative manifest was fetched (all HTTP 200).
Extension-less content-negotiated URLs (e.g. `td/hcard`,
`td/four-transforms`) were saved under their basename; these belong to
the networked namespace/profile-document tests (Stage 2, skipped by the
Stage 1 runner) and are vendored for completeness.

## Licence

The W3C GRDDL specification, its test cases, and the served test
documents are published by the W3C and made available under the **W3C
Document Licence** and the **W3C Software and Document Notice and
Licence**
(<https://www.w3.org/copyright/software-license-2023/> and
<https://www.w3.org/copyright/document-license-2023/>). These vendored
copies are byte-identical to the upstream documents; they are
reproduced here unmodified solely to let the offline GRDDL Stage 1
runner exercise the suite without a network fetch. No warranty; see the
W3C licences for terms.

## 2026-10-10: additions and corrections

Issue: <https://github.com/danbri/factoidal/issues/668> (GRDDL item:
"vendor the fetched documents into the fixture set (with licence) so the
tests decide offline, and fix the rest"). All files below are W3C
documents served from `www.w3.org`; the W3C Document Licence and the W3C
Software and Document Notice and Licence (links above) apply. Every
document was fetched once with `curl -sS -L` through the session proxy.
The runner makes no network request.

### Documents added (retrieved 2026-10-10)

The namespace documents (GRDDL section 3), profile documents (section 5)
and stylesheets the normative tests need, which the 2026-07-09 copy did
not carry. Fetched from the `http` IRI with
`Accept: application/rdf+xml, application/xhtml+xml;q=0.9,
application/xslt+xml;q=0.9, application/xml;q=0.8, text/xml;q=0.8,
text/html;q=0.5, */*;q=0.1`; each answered after one redirection from
`http` to the same path under `https`.

| Path | Source IRI | Content-Type served | SHA-256 |
|---|---|---|---|
| `g/xml-attributes` | <http://www.w3.org/2003/g/xml-attributes> | `application/xslt+xml` | `9074c072e2323b3231b631fd2cc2a6baa5ec0f2b503ddfb37bbc0810d07b8dd5` |
| `td/base/whichdir.xsl` | <http://www.w3.org/2001/sw/grddl-wg/td/base/whichdir.xsl> | `application/xslt+xml` | `ca7efdbc73f244bb84f083241d27955b67c97e6fba3eb17c02c5c3570169f846` |
| `td/erdf` | <http://www.w3.org/2001/sw/grddl-wg/td/erdf> | `text/html; charset=utf-8` | `4aad0c757a956bf3628ac1e0309f6232ee22bbed6b6d6122d5f767fdcdc38639` |
| `td/extract-rdf.xsl` | <http://www.w3.org/2001/sw/grddl-wg/td/extract-rdf.xsl> | `application/xslt+xml` | `b911b46585997c1542ee8e5c5b2bf9fdc41a396da147d74e7924597224946639` |
| `td/fnd` | <http://www.w3.org/2001/sw/grddl-wg/td/fnd> | `application/rdf+xml; charset=utf-8` | `70a3b32bb686c96c0e5213859bbea4aa276b7fb373790bbe44337bc6db3b718f` |
| `td/grddlProfile.html` | <http://www.w3.org/2001/sw/grddl-wg/td/grddlProfile.html> | `text/html; charset=utf-8` | `acd2fa56680e4d2b7d2211fb04191f198fd38624afafbb900af7c7cc8fec6827` |
| `td/hcarda-prof` | <http://www.w3.org/2001/sw/grddl-wg/td/hcarda-prof> | `application/rdf+xml; charset=utf-8` | `25ac9a3d4c62b692c29bcd3b944d44184edd1c52bf4c0d790361490861b36b28` |
| `td/loop-ns-b` | <http://www.w3.org/2001/sw/grddl-wg/td/loop-ns-b> | `application/xml; qs=0.9` | `8afcd00d741d29e574cec38fdb1b8c8c2f9a4da9a1f57ce4ff6e169aa90a355f` |
| `td/ns-fnd` | <http://www.w3.org/2001/sw/grddl-wg/td/ns-fnd> | `application/xml` | `b45dd023d14022279921c105228ca57b773e62dc95336e2a1f63e9f00efccad3` |
| `td/ns-pf-ns-fnd` | <http://www.w3.org/2001/sw/grddl-wg/td/ns-pf-ns-fnd> | `application/xml` | `7988e2fc7ed199bf392a5e48067af17bc9ea9fb3b0af9cd19e3a1d6581607188` |
| `td/ns-pf-pf-fnd` | <http://www.w3.org/2001/sw/grddl-wg/td/ns-pf-pf-fnd> | `application/xml` | `fbcb452fc71a390f72eda7c463ff8e1d04026c4aeef7c46d081001910b4a10c1` |
| `td/one` | <http://www.w3.org/2001/sw/grddl-wg/td/one> | `application/xslt+xml (Accept: application/xslt+xml)` | `db88c2c9cf0b2319560d5f268cdd5c42230bf3950994882d4d85d715f3044552` |
| `td/pf-fnd` | <http://www.w3.org/2001/sw/grddl-wg/td/pf-fnd> | `text/html` | served `d83b5af56f696a4a29a4839ce74c59acf6c31349e46b641025695fcffb3c7e83`; stored `20ccc888ace04ad7ebf153ca1edaf8e780b2cc39de715bfaf0d3b169df8f90e2` (redacted, see below) |
| `td/pf-ns-fnd` | <http://www.w3.org/2001/sw/grddl-wg/td/pf-ns-fnd> | `text/html` | served `e18040962007d6975586570901feecb16c8fbe1c625327b700ea8370029b4f29`; stored `b4827841a6f44682264057d48740b9446f96a1c47c2a0ed891699df87294a45c` (redacted, see below) |
| `td/pf-ns-pf-ns-fnd` | <http://www.w3.org/2001/sw/grddl-wg/td/pf-ns-pf-ns-fnd> | `text/html` | served `32686077058dc4e1442133c3ceaf6a206989528eeb37321d7352f30dd93ad4a0`; stored `85a152def49f29fac2083b1bde45b6902ffce9f6858b160504a0fc3fed98550a` (redacted, see below) |
| `td/pf-pf-fnd` | <http://www.w3.org/2001/sw/grddl-wg/td/pf-pf-fnd> | `text/html` | served `55e5937edbd4ef91682c93116bcbc71a5b6ef0ee1dbf1334118e89a7ecb66430`; stored `309fcc4d8649621329d6441000384418c676bf38e4039459ea84ef0d8453b419` (redacted, see below) |
| `td/pf-pf-ns-fnd` | <http://www.w3.org/2001/sw/grddl-wg/td/pf-pf-ns-fnd> | `text/html` | served `26aa378ade840209a5d2df8ac32fa25160f11e816624a98b410e153b1300dd1e`; stored `d0f8bc24bb9c80854e0e177000400657543d36cb3dcc3ca82c4d4e289bf73319` (redacted, see below) |
| `td/sq1ns` | <http://www.w3.org/2001/sw/grddl-wg/td/sq1ns> | `application/xml; qs=0.9` | `4d98fceab506e0ef27801b1438112ce0896eee565a72a87e10c7bbd0bb9b24bc` |
| `td/sq2ns` | <http://www.w3.org/2001/sw/grddl-wg/td/sq2ns> | `application/rdf+xml; charset=utf-8` | `948eaf9e620ce3abab7dd30dfbae88ba358cc8ef17c0eed2098be547d4dd1d72` |
| `td/two-transforms-ns` | <http://www.w3.org/2001/sw/grddl-wg/td/two-transforms-ns> | `application/rdf+xml; charset=utf-8` | `22517f05a6ea8a5d52898941cc0d8a90f2f2607f61f87bf0cd5f8831771a8b4e` |

`td/one` has two representations by content negotiation (`one.rdf` and
an XSLT stylesheet). The manifest uses it only as a transformation
(`two-transforms-ns`, `html-and-grddl-xform-attr`), so the stored copy
is the representation served for `Accept: application/xslt+xml`.

### Server environment removed from six SSI documents

`td/pf-fnd`, `td/pf-ns-fnd`, `td/pf-pf-fnd`, `td/pf-pf-ns-fnd`,
`td/pf-ns-pf-ns-fnd` and (already vendored on 2026-07-09)
`td/pf-pf-pf-ns-fnd` are generated by the server-side include
`pf.shtml`, which prints the request's CGI environment inside a `<p>`.
The served copies carry other visitors' IP addresses, user agents and
cookies (the CDN cached them). The lines of the form `NAME=value` were
removed and replaced with one XML comment. The `head/@profile` that the
layering tests read is unchanged. Served and stored SHA-256 are in the
table above; for `td/pf-pf-pf-ns-fnd`: served
`12e2f738d53ac6ff5ba59d94d761bd1dfea800b7e6d6088129d2068376654a0d`,
stored `da9092f3caf5d8f89d930ab6bca60b44bdff7bd795e4d6f548828dfd9ed7b405`.

### Local inputs restored to the 2007 Recommendation copies

After 2007 the W3C edited the served test inputs: `http://` links in
attribute values became `https://` (for example the MusicBrainz album
link in `titleauthor.html`, from which the expected output takes its
subject). The Recommendation's own deliverable, the archive
<https://www.w3.org/TR/2007/REC-grddl-tests-20070911/grddl-tests.zip>
(dated 2007-06-30, SHA-256
`9c2728320ff06e7ad4ed47cf1b4a83e257a06a8da5468797b621bb2c026f69d9`,
retrieved 2026-10-10), holds the local inputs as approved. These nine
files now carry the archive bytes:

| File | Served copy (2026-07-09) SHA-256 | Archive copy SHA-256 (stored) |
|---|---|---|
| `td/baseURI.html` | `23ae5bb1efe4e69816c6bdac79d5ae3478e9b742169f59ed0eb84b716d368cff` | `b5d2eccf3b7f266604e60a64d18984d2db43b08af2886de30bbeebdfe49f8b40` |
| `td/titleauthor.html` | `1c7d39a1274b72dfa67c86322227dc28ec14e3869878fe3f35bf3be0823cc298` | `d9b2c149b6baf3b5c13efb3b6c21dfdeb3bc4a0ce007736bf7ceb5ad3d9bab1d` |
| `td/xhtmlWithGrddlEnabledProfileAndADisabledInBodyTransform.html` | `263bec7210f2a3209c4b5d262ff1403bfe7120c6e018680a7ce5386e319a72e0` | `041dc7d408754d007b31c8e940e9e7aca582b6fa85eb49fb2ce92e87e8630929` |
| `td/xhtmlWithGrddlEnabledProfileAndInBodyTransform.html` | `14b45a5bdf577746380348fc012969d6b811d060ab110e0af287da597b7b5923` | `8bfe71227daa7a7ce8e40a47f42ff412c72722fdbe1a85d704f50e349d30404d` |
| `td/xhtmlWithGrddlProfile.html` | `b0891ee063126557f469227a75141b965f8328ca24eff0ee43c4764869703734` | `ca454447c49555efe849be7b5f768c696bc8e74868fa914bf29ef889cba647e3` |
| `td/xhtmlWithGrddlTransformationInBody.html` | `b7485c40d2e31daef4efbce9cb7684866656dc268a7e6bbc294b0f5245571dbd` | `eac20d7110e0dd5275af8206112f5d25d2c6f9b97dcb4e25d8f2c8316c7de77e` |
| `td/xhtmlWithMoreThanOneGrddlTransformation.html` | `cba4798cc334a958eff7c22ce1e2ddb6a2fb6d9a6fb3618125b5f92c3c8972c7` | `1a2925657fc566db3f656bbbee8f8150b992e2a440120f62b7c421dca3bfbc73` |
| `td/xhtmlWithMoreThanOneProfile.html` | `52c7a6b3da85ab7551d6f029f2dee2e4f97771b1a13aca8515fa92469252cc0e` | `8fd79c5694b7e377375e2fbe27a6f2f68afa205ce9e4a7d5f35e420927b7673c` |
| `td/xinclude1.html` | `68bf85d5919793aceb3e2ed1fafc2bc93678e56a2f7cb71cc36e8750801469d7` | `49eca98a5be09589dd982fdc1d22269bb8a32e0b8661f656a706ce0658500282` |

The other local inputs in the archive are byte-identical to the served
copies. The archive does not contain the networked inputs; the edited
networked inputs (`td/grddlProfileWithBaseElement`,
`td/base/xhtmlWithBaseElement`, `td/conneg.html` and others) stay as
served, and the runner reports the cases that depend on them as
failures that differ only by the URI scheme. An unedited copy is not
reachable from here: `web.archive.org` refuses the proxy connection and
`cvsweb.w3.org` asks for a W3C login.

### Redirections recorded, copies removed

Five suite IRIs answer with a redirection to a copy under `td/base/`
(the base-URI tests depend on it). They are in `docroot/redirects.tsv`
with status and `Location`; the runner follows them, so the retrieval
URI is the redirection target. The five copies the 2026-07-09 fetch had
saved under the source names (`td/grddlProfileWithBaseElement`,
`td/xhtmlWithBaseElement`, `td/xhtmlWithoutBaseElement`,
`td/xmlWithBase`, `td/xmlWithoutBase`, byte-identical to the targets)
were removed.

### Not vendored

- `td/spaces-in-rel.sxsl?only|first|last|middle|duplicate`,
  `td/profile-has-spaces-in-rel.sxsl?...`, `td/layering-namespace?` and
  `td/layering-profile?`: server-side stylesheets. Each now answers 303
  to `https://auth.w3.org/` (W3C login). Tests `spaces-in-rel`,
  `glean-profile`, `ns-ns-pf-pf`, `ns-pf-ns-pf-ns` and `pf-pf-pf-ns`
  need them and stay UNAVAILABLE with the IRI named.
- `http://www.w3.org/1999/xhtml` (the XHTML namespace document). Since
  2008 it names a `grddl:namespaceTransformation` to
  `https://www.w3.org/2008/07/rdfa-xslt`, which the 2007 expected
  outputs predate. Other namespace and profile documents outside the two
  suite trees (the RDF and SVG namespaces, `http://www.example.org/...`)
  are not vendored either; the runner names them per case.
