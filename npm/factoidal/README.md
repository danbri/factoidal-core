# @factoidal/core

An RDF, SPARQL, reasoning and validation library for Node 22.12+, Deno 2 and
browsers: the Lean 4 library `L4Factoidal` compiled to one WebAssembly module,
with JavaScript glue. The package contains no F\* code.

## Install and use

```bash
npm install @factoidal/core
```

```js
import { parse, query, canonicalize } from "@factoidal/core";
const ds = await parse('<http://x/a> <http://x/n> "A" .', { format: "ntriples" });
const rows = await query(ds, "SELECT ?n WHERE { ?s <http://x/n> ?n }");
console.log(rows[0].get("n").value);      // A
console.log(await canonicalize(ds));       // RDFC-1.0 canonical N-Quads
```

Full API: [API.md](https://github.com/danbri/factoidal-core/blob/main/npm/factoidal/API.md).
Changes: [CHANGELOG.md](CHANGELOG.md).

## JavaScript API

All functions return a Promise. Datasets are `Dataset` values or
`DatasetHandle`s; other inputs and outputs are strings, objects or
`Uint8Array`.

- RDF: `parse`, `serialize`, `graphs`, `dataFactory`, `openDataset` (handle), `jsonldToRdf`, `jsonldFromRdf`, `normalizeNQuads`
- SPARQL: `query`, `update`, `queryRaw`, `queryHdt`, `registerExtensionFunction`, `unregisterExtensionFunction`, `clearExtensionFunctions`, `registerServiceEndpoint`, `clearServiceEndpoints`
- Canonicalization: `canonicalize`, `canonicalizeNQuads`, `canonicalHash`
- Reasoning: `rhoDfClosure`, `rhoDfFragmentCheck`, `coreRdfsClosure`, `coreRdfsCheck`, `rdfsPlusClosure`, `owlClosure`, `owlEntails`, `owlIsConsistent`, `tableauDlInconsistent`, `tableauMaterialise`, `rifEval`
- Validation and mapping: `shaclValidate`, `shexValidate`, `rmlMap`, `csvwToRdf`, `jsonSchemaValidate`, `schematronValidate`
- XML: `xmlWellformed`, `xpathEval`, `xsltTransform`, `xformsRecalc`
- Store: `openStore`, `queryStore`, `listStores`, `Store`; `serveStore(root, {port})` gives `{url, port, close()}`, a SPARQL 1.1 Protocol server (Node only); `deltaLogOpen`, `deltaLogAppend`, `deltaLogInspect`, `deltaLogMerge`, `deltaLogReadAllHex`, `deltaLogDestroy`
- Credentials and crypto: `vcCheckCredential`, `vcCheckCredentialSubject`, `vcCheckNoDataLoss`, `vcCheckRelatedResourceDigests`, `vcEddsaCreateFromCanonical`, `vcEddsaVerifyFromCanonical`, `vcEd25519Sign`, `vcEd25519Verify`, `vcEd25519SecretToPublic`, `vcSha256Hex`, `didKeyResolve`, `aeadSeal`, `aeadOpen` (ChaCha20-Poly1305), `hpkeSeal`, `hpkeOpen` (RFC 9180), `proofCheck`, `proofInspect`
- Mathematics: `mathmlEval`, `clParse`, `clSerialize`, `clNormalize`, `clAlphaNorm`, `toanSimplify`, `toanDiff`, `toanSubst`, `toanSummation`, `toanProduct`, `matrix*`, `sigmoid*`
- Engine: `capabilities`, `version`, `engine`, `loadEngine` (raw `call(op, args)` for every op)
- Subpaths: `@factoidal/core/core` (smaller wasm, no store ops), `/rdfjs`, `/api`, `/fn`; `lws/`, `solid/`, `xmpp/` hosts

## Command line

`npx factoidal <command>`:

- `pack INPUT STORE/gen-N`, `activate STORE gen-N`: build and activate a store from an RDF file
- `query STORE QUERY`, `inspect STORE`; `update` and `compact` exit 3 (https://github.com/danbri/factoidal/issues/641); updates work through `serve`
- `serve --file DATA /ds` (the `fuseki-server --file` form) or `serve STORE --port N`: SPARQL 1.1 Protocol at `/sparql`, Graph Store Protocol at `/data`, Service Description. W3C protocol tests against this server: 50 pass, 0 fail (out of 50) [P]
- `lws-serve DIR`, `solid-serve DIR`, `solid-client OP URL`: Linked Web Storage 1.0 and Solid Protocol
- `version`, `sample-store`

Replacing Apache Jena Fuseki: [docs/fuseki-replacement.md](https://github.com/danbri/factoidal-core/blob/main/npm/factoidal/docs/fuseki-replacement.md).

## Specifications covered, with test scores

Scores are from the W3C (or other named) test suites, run by the native
build of the same Lean library on 2026-10-09 [B]. Rows marked [S] are from the
speed record of 2026-10-13.

- SPARQL 1.1 Query, Update, Protocol (manifest-all): 631 pass, 0 fail (out of 631) [B]
- SPARQL 1.2 (triple terms, reifiers): 254 pass, 0 fail (out of 254) [B]
- RDF 1.1 N-Triples 70/0/70, N-Quads 87/0/87, Turtle 313/0/313, TriG 356/0/356, RDF/XML 166/0/166 (pass/fail/total) [B]
- RDF 1.1 Semantics (rdf-mt): 39 pass, 0 fail (out of 39) [B]
- RDF 1.2 syntax suites (N-Triples, N-Quads, Turtle, TriG, RDF/XML): all pass, 0 fail [B]
- RDF 1.2 Semantics: 40 pass, 7 fail (out of 47) [B]
- JSON-LD 1.1 toRdf 467/0/467, expand 385/0/385, compact 245/0/246 (1 not run), flatten 58/0/58, fromRdf 53/0/54 (1 not run) [B]
- JSON-LD 1.1 Framing: 29 pass, 63 fail (out of 92) [B]
- RDFC-1.0 canonicalization: 86 pass, 0 fail (out of 86) [B]
- OWL 2 RL profile tests: 126 pass, 0 fail (out of 126) [B]
- OWL 2 DL regime, type-inconsistency: 116 pass, 11 fail, 1 other (out of 128) [B]
- OWL 2 DL regime, positive entailment: 169 pass, 35 fail, 2 other (out of 206) [B]
- SHACL 1.0 Core 98/0/98, SHACL-SPARQL 22/0/22 [B]
- SHACL 1.2 Core: 103 pass, 30 fail (out of 133); SHACL 1.2 SPARQL 22/3/25 [B]
- ShEx 2 (ShExJ validation): 1182 pass, 0 fail (out of 1182); ShExC parser 442/0/442 [B]
- CSVW csv2rdf 270/0/270, csv2json 270/0/270, validation 281/1/282 [B]
- RIF Core: 43 pass, 0 fail, 3 undecided (out of 46) [B]
- RML Core: 60 pass, 0 fail, 16 not attempted (out of 76) [B]
- XML 1.0 (xmlconf): 1861 pass, 0 fail, 516 not run [B]
- XSD 1.1 datatypes (W3C instance tests): 18951 pass, 5 fail (out of 18956) [B]
- XPath 1.0 (repository battery, not a W3C suite): 100 pass, 0 fail (out of 100) [B]
- XSLT 1.0: 84 pass, 3 fail, 1 refused (out of 88) [B]
- JSON Schema draft-07: 770 pass, 0 fail (out of 770) [B]
- VC Data Integrity eddsa-rdfc-2022, did:key, Ed25519 (RFC 8032): 58 pass, 0 fail (out of 58) [B]
- A persisted store (Shardborough generations, read and query; SHA-256 per block) and RDF/JS DataFactory and DatasetCore

[B] https://github.com/danbri/factoidal-core/blob/03e2e6deee8146ce7e6fdc3f8f34b8245af5ab54/docs/designissues/2026-10-09-lean-conformance-baseline.md

[P] https://github.com/danbri/factoidal-core/blob/9a4045f1572a032b53ccb867f8395fe0c8d97bb9/docs/designissues/2026-10-10-store-serve.md

[S] https://github.com/danbri/factoidal-core/blob/06f79fd3a3f434c7d1a6ffd2bd0b0bbc0044203c/docs/designissues/2026-10-12-sota-reference.md

## Strengths

- One engine on every surface. Node, Deno and the browser load the same
  `.wasm`; the parsers, SPARQL evaluator, reasoners and validators are Lean
  code, and the JavaScript only moves arguments and results.
- The Lean library contains no `sorry`, no user axioms and no `native_decide`
  (`l4-assets/version.json`, member `claims`).
- No failures on the W3C SPARQL 1.1, SPARQL 1.2, RDF 1.1 syntax, RDFC-1.0,
  JSON-LD toRdf/expand, ShEx and SHACL 1.0 suites (scores above, [B]).
- OWL 2 RL closure on nine real ontologies: 0.04 to 1.6 times the time of Jena
  OWL Micro and 0.06 to 0.72 times its peak memory [S] section 1.
- OWL 2 DL consistency on SKOS, FOAF, PROV-O, BFO and Pizza: 0.07 to 1.1 times
  the time of HermiT, 0.3 to 0.5 times its memory [S].
- Streaming N-Triples and Turtle parse holds 24 MB at 400,000 triples
  (native build) [S].
- No dependencies on other npm packages.

## Weaknesses and known gaps

- Size: the tarball is about 3.8 MB packed, 19 MB unpacked. It carries two
  wasm modules (11.2 MB full, 6.1 MB `./core` subset).
- Parse speed: N-Triples 4.4 times and Turtle 3.0 times the time of Serd;
  RDF/XML 6.2 times the time of Oxigraph and 9.5 times its memory [S].
  RDF/XML memory per document byte: https://github.com/danbri/factoidal/issues/771 (open).
- SPARQL in memory, 346,100 triples: 3.4 to 4.1 times the time of Oxigraph [S].
  Remaining costs: https://github.com/danbri/factoidal/issues/827 (open).
- RDFC-1.0: 1.5 to 2.0 times the time of Oxigraph on ordinary inputs [S].
- OWL 2 DL consistency: wine 8.8, QUDT 8.6 times the time of HermiT; QUDT
  uses 2.9 times its memory [S].
- CLI query peak memory 9 times the F\* engine at 80,000 paragraphs:
  https://github.com/danbri/factoidal/issues/729 (open).
- Four equalities of the chunked strict parser are tested, not proved:
  https://github.com/danbri/factoidal/issues/826 (open).
- JSON-LD Framing: 63 of 92 tests fail. SHACL 1.2 Core: 30 of 133 fail.
  RDF 1.2 Semantics: 7 of 47 fail [B].
- `factoidal update` and `factoidal compact` exit 3: https://github.com/danbri/factoidal/issues/641 (open).
- As a Fuseki replacement: no administration API, one dataset per process, no authentication, and TDB2 databases are served read only (`serve --tdb2`, https://github.com/danbri/factoidal/issues/834): https://github.com/danbri/factoidal/issues/831 to https://github.com/danbri/factoidal/issues/833 (open).
- Node's default stack can raise a `RangeError` in the wasm on some
  row-at-a-time queries over large results; `node --stack-size=4000` or Deno
  clears it (`skills/npm-release/SKILL.md`, trap 11).
- The API can change before 1.0.

## Licence

Apache-2.0. See `LICENSE` and `NOTICE`.
