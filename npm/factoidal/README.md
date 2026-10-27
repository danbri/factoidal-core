# @factoidal/core

> ⚠️ **EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.**
>
> This covers the whole core library and every command line tool. Treat
> every security component as under-reviewed and risky: the servers and
> clients (SPARQL Protocol, LWS and its authorization server, Solid, WebDAV,
> XMPP), authentication, bearer tokens and session keys, JOSE, XML
> Signature and SAML, Verifiable Credentials Data Integrity, did:key,
> signatures, hashes and the crypto bindings. They have had little
> independent security review. Some of them use well-known primitives
> (HACL\*, WebCrypto), but the code that combines and exposes those
> primitives is new. A correct primitive does not make a protocol or a
> server safe. Do not use these components to protect real data or real
> accounts, and do not expose the servers to networks you do not trust.
> Report security problems at https://github.com/danbri/factoidal/issues.

RDF, SPARQL, reasoning, validation and Linked Data servers in one package.
Runs in Node 22.12+, Deno 2 and browsers. No dependencies.



```bash
npm install @factoidal/core
```

```js
import { parse, csvwToRdf, canonicalHash } from "@factoidal/core";

const ds = await parse('<http://x/a> <http://x/n> "A" .', { format: "ntriples" });
const rows = await ds.query("SELECT ?n WHERE { ?s <http://x/n> ?n }");
console.log(rows[0].get("n").value);              // A
console.log(ds.toString("turtle"));
console.log(await ds.serialize({ format: "rdfxml" }));
console.log(await ds.canonicalize());              // RDFC-1.0 canonical N-Quads
console.log(await canonicalHash(ds));              // its SHA-256, 64 hex digits

const table = await csvwToRdf("id,name\n1,a\n", "", { mode: "minimal", url: "http://x/t.csv" });
console.log(table.size);                           // 2

ds.dispose();
table.dispose();
```

A `Dataset` keeps its data inside the engine. Every producer returns one and
every consumer accepts one, so a pipeline does not re-parse between steps.
An unknown option key throws. With no `format`, the format is inferred and
reported in `dataset.format`; an explicit `format` is never overridden.
RDF 1.2 input uses `turtle12`, `ntriples12`, `nquads12` or `trig12`.
RDF 1.2 in JSON-LD (JSON-LD-star: `@triple`, `@reifies`, `@annotation`,
`@direction`) needs the option `rdfstar`: `jsonldToRdf(text, { rdfstar: true })`
and `dataset.serialize({ format: 'jsonld', rdfstar: true })`.

## What it does

- Syntaxes: N-Triples, N-Quads, Turtle, TriG, RDF/XML, JSON-LD; RDF 1.1 and 1.2
  (RDF 1.2 in JSON-LD through the JSON-LD-star draft, option `rdfstar`)
- SPARQL 1.1 and 1.2 query and update; GeoSPARQL functions, text search,
  JavaScript extension functions, SERVICE
- Reasoning: RDFS, OWL 2 RL closure, restricted checked OWL consistency,
  experimental OWL entailment, RIF Core
- Validation: SHACL, ShEx, JSON Schema, Schematron
- Mapping: CSVW, RML, JSON-LD
- Canonicalization: RDFC-1.0; Verifiable Credentials Data Integrity (eddsa-rdfc-2022), did:key
- XML: XML 1.0, XPath 1.0, XSLT 1.0, XForms
- Servers: SPARQL 1.1 Protocol and Graph Store (Fuseki-compatible paths,
  Jena TDB2 read only), Linked Web Storage 1.0, WebDAV for file
  browsers, Solid, an OAuth 2.0
  authorization server (token exchange for OpenID Connect ID tokens,
  self-issued CID credentials and SAML 2.0 assertions)
- Security: JWS/JWT (ES256, RS256, EdDSA), XML Signature verification in the
  SAML Core profile (Exclusive XML Canonicalization 1.0, rsa-sha256), with
  HACL\* primitives. XML Encryption and JWE are not implemented yet:
  https://github.com/danbri/factoidal/issues/1081
- A persisted store with a delta log for updates (early stage)
- Terms: a JavaScript extension function can answer with an exact term
  (`{value: "007", datatype: XSD + "integer"}`, an RDF/JS term, a triple
  term); the engine keeps the lexical form and the datatype IRI as given.
  A term given as a string is one N-Triples term everywhere (`<http://…>`
  is an IRI, `_:b` a blank node). See API.md, "Custom extension functions" and
  "Terms given as strings".
- RDF/JS DataFactory and DatasetCore (`/rdfjs`), a functional API (`/fn`)

## What is new

Releases: https://github.com/danbri/factoidal-core/releases. All changes:
[CHANGELOG.md](https://github.com/danbri/factoidal-core/blob/main/npm/factoidal/CHANGELOG.md).
Live examples: https://danbri.github.io/factoidal/web/hub/.

**0.18.0** (2026-10-27, [release](https://github.com/danbri/factoidal-core/releases/tag/v0.18.0)):

- SPARQL: the XSD constructor functions (`xsd:byte`, `xsd:date`, `xsd:g*`,
  durations, ...) cast as XPath F&O 3.1 §19 says; an invalid value is an
  error, not an ill-typed literal (https://github.com/danbri/factoidal-core/pull/142).
- SPARQL 1.2: STRSTARTS, STRENDS, CONTAINS, STRBEFORE and STRAFTER compare
  the base direction; `STRBEFORE("abc"@en--ltr, "b")` is `"a"@en--ltr`
  (https://github.com/danbri/factoidal-core/pull/136).
- JSON-LD-star: RDF 1.2 triple terms, reifiers and annotations in JSON-LD
  with the option `rdfstar` (https://github.com/danbri/factoidal-core/pull/134,
  https://github.com/danbri/factoidal-core/pull/140). Hub page:
  https://danbri.github.io/factoidal/web/hub/jsonld-star/.
- `factoidal webdav-serve CONFIGDIR` serves LWS storages to file browsers
  over WebDAV (RFC 4918 classes 1 and 2). litmus 0.13: 208 pass, 0 fail
  (out of 208) (https://github.com/danbri/factoidal/issues/1066).
- LWS client: range and conditional reads, trusted storages for
  notifications, one-page search, linksets, Ed25519 session keys, bearer
  tokens (https://github.com/danbri/factoidal/issues/1065).
- Store open: a scoped `openStoreHandle` on the londat store takes 198 ms,
  not 305 ms (median of 9) (https://github.com/danbri/factoidal-core/pull/141).

**0.17.0** (2026-10-27, [release](https://github.com/danbri/factoidal-core/releases/tag/v0.17.0)):

- **Breaking:** `canonicalHash(graph)` returns the SHA-256 (64 hex digits)
  of the RDFC-1.0 canonical N-Quads; use `canonicalize()` for the text
  (https://github.com/danbri/factoidal-core/pull/127).
- SPARQL string functions take the argument types of SPARQL 1.1 §17.4.3;
  `SUBSTR("12345", 0, 3)` is `"12"` (https://github.com/danbri/factoidal-core/pull/126).
- `factoidal pack --layout sbm11` writes an SBM11 store, the same files as
  `l4sbm11-pack` byte for byte (605 of 605 W3C census inputs); `activate`,
  `inspect` and `query` read it (https://github.com/danbri/factoidal-core/pull/131).
- Store open in Node: 562 ms, not 1,485 ms, on the londat store (142,314
  quads; median of 7) (https://github.com/danbri/factoidal-core/pull/135).
- `factoidal lws-serve DIR --authz ASDIR`: the storage and an authorization
  server on one port; well-known paths also work behind a reverse proxy
  with a path prefix.
- Fixes in the chunked Turtle reader (https://github.com/danbri/factoidal-core/pull/128)
  and RML (https://github.com/danbri/factoidal-core/pull/129); 996 Apache
  Jena ARQ expression tests run on the package (https://github.com/danbri/factoidal-core/pull/132);
  no npm test skips when the wasm lacks an op
  (https://github.com/danbri/factoidal-core/pull/124, https://github.com/danbri/factoidal-core/pull/125).

**Next release** (not published): fixes for 16 defects that the echo test
ports (below) found: 7 in SPARQL, 9 in the readers and writers
(https://github.com/danbri/factoidal-core/pull/148).

## Checked pipelines

Each component kind has one interface type whose contract against the W3C
specifications is part of the type: readers, stores, the SPARQL evaluator,
writers, reasoners, validators and the proof checker. A contract that is not
proved yet is a named assumption; CI fails when the list of assumptions grows
without a stated reason. A theorem states that the SPARQL answer agrees with
the SPARQL 1.1 semantics for data from any source (a parsed document, an
edited Dataset, an update, a reasoner's output, a union of stores), given the
listed assumptions. No new command-line verbs. Status:
https://github.com/danbri/factoidal/issues/975.

The same components are nodes you can compose. A value on a wire is
`{graph, evidence}`; each node adds one evidence record; the result lists the
union of the named assumptions of the nodes, so a pipeline says exactly what
its answer depends on.
`pipe()` and `run()` get the type check and that union from the engine
(op `pipelineCheck`); the theorem `Pipeline.guarantee_sound` gives the
guarantee of every well-typed pipeline, and `run()` refuses one that is not
well typed unless `{ unchecked: true }`.

```js
import { stages, node, pipe, run } from "@factoidal/core";

const sources = `@prefix ex: <http://example.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:alice ex:worksFor ex:acme .
ex:worksFor rdfs:domain ex:Employee .
ex:Employee rdfs:subClassOf ex:Person .`;
const description = `@prefix ex: <http://example.org/> .
_:x a ex:Person . _:x ex:worksFor ex:acme .`;

console.log((await stages()).length);  // registered components, each with status and contract
const p = pipe(
  await node("turtleDocumentReader"),
  await node("rdfsReasoner"),
  await node("rdfsExplainGraphStage", { description }),
);
const r = await run(p, sources);
console.log(r.evidence.map((e) => e.stage)); // one record per node
console.log(r.evidence[2].artefact.entailed); // true, with a checked derivation
console.log(r.assumptions, r.proved);       // what the answer depends on
```

`run(p, input, { unchecked: true })` also runs components that are not proved,
and marks those steps in the evidence. Details: API.md, "Stages as nodes" and
"Explaining an entailment" (`explain()` is the same check as one call).

Formats (generated from `formats()`):

<!-- formats-table:start (generated by test/formats-table.test.mjs) -->
| format | read RDF 1.1 | read RDF 1.2 | write RDF 1.1 | write RDF 1.2 | engine |
|---|---|---|---|---|---|
| nquads | yes | yes | yes | yes | core |
| ntriples | yes | yes | yes | yes | core |
| turtle | yes | yes | yes | yes | core |
| trig | yes | yes | yes | yes | core |
| rdfxml | yes | no | yes | no | core |
| jsonld | yes | no | yes | no | full |
| rdfc | no | no | yes | no | core |
| sparql-results-json | no | no | yes | yes | core |
| sparql-results-xml | no | no | yes | yes | core |
| sparql-results-csv | no | no | yes | yes | core |
| sparql-results-tsv | no | no | yes | yes | core |
<!-- formats-table:end -->

Missing writers (HDT, N3, RDFa): https://github.com/danbri/factoidal/issues/883.

## Errors

Every function rejects with one class, `FactoidalError`, except that an
argument of the wrong JavaScript type is a `TypeError`. The engine decides
three fields: `code` (below), `position` (`{line, column, offset,
byteOffset}` where the input defines one: `offset` is a UTF-16 index into
your string, `byteOffset` counts UTF-8 bytes) and `spec` (the specification
section of the condition). `cause` holds the underlying error of `host.io`.

```js
import { parse, FactoidalError } from '@factoidal/core';
try { await parse('<http://e/a> <http://e/p> .', 'turtle'); }
catch (e) { if (e instanceof FactoidalError) console.log(e.code, e.position.line, e.spec); }
```

Codes (generated from `engineTables().errorCodes`):

<!-- errors-table:start (generated by test/errors.test.mjs) -->
| code | specification | meaning |
|---|---|---|
| `parse.syntax` | <https://www.w3.org/TR/rdf12-turtle/#sec-grammar> | The input text does not match the grammar of its RDF syntax. |
| `parse.rdf12-required` | <https://www.w3.org/TR/rdf12-concepts/#section-triple-terms> | The text uses an RDF 1.2 form (triple term, reified triple, base direction) and was read as RDF 1.1. |
| `term.invalid-iri` | <https://www.w3.org/TR/rdf12-concepts/#section-IRIs> | A term that must be an IRI is not one. |
| `term.invalid-langtag` | <https://www.w3.org/TR/rdf12-concepts/#section-Graph-Literal> | A language tag is not well-formed (BCP 47). |
| `term.invalid` | <https://www.w3.org/TR/sparql11-results-json/#select-encode-terms> | A term or quad given as JSON is not an RDF term or quad. |
| `query.syntax` | <https://www.w3.org/TR/sparql11-query/#grammar> | The SPARQL query does not match the SPARQL grammar. |
| `query.failed` | <https://www.w3.org/TR/sparql11-query/#sparqlDefinition> | The SPARQL query parsed but its evaluation was refused. |
| `update.syntax` | <https://www.w3.org/TR/sparql11-update/#grammar> | The SPARQL update does not match the SPARQL Update grammar. |
| `update.failed` | <https://www.w3.org/TR/sparql11-update/#updateLanguage> | The SPARQL update parsed but was refused. |
| `format.unknown` | - | The format name is not one the engine reads or writes. |
| `serialize.unsupported-rdf12` | <https://www.w3.org/TR/rdf12-concepts/#section-triple-terms> | The data holds an RDF 1.2 term and the requested RDF 1.1 output has no form for it. |
| `serialize.failed` | - | The writer refused the data. |
| `canon.unsupported-rdf12` | <https://www.w3.org/TR/rdf-canon/#canon-algorithm> | RDFC-1.0 defines no canonical labelling for RDF 1.2 triple terms or directional strings. |
| `canon.failed` | <https://www.w3.org/TR/rdf-canon/#canon-algorithm> | Canonicalization was refused. |
| `owl.unsupported-rdf12` | <https://www.w3.org/TR/owl2-mapping-to-rdf/#Mapping_from_RDF_Graphs_to_the_Structural_Specification> | OWL 2 Direct Semantics has no rule for RDF 1.2 triple terms or directional strings. |
| `reason.failed` | - | A closure or entailment check was refused. |
| `regime.refused` | <https://www.w3.org/TR/sparql11-entailment/> | The entailment regime is not implemented. |
| `validate.failed` | - | A validation (SHACL, ShEx, JSON Schema, Schematron) could not run on its inputs. |
| `xml.failed` | <https://www.w3.org/TR/xml/#sec-well-formed> | An XML, XPath, XSLT, MathML or XForms input was refused. |
| `crypto.failed` | - | A cryptographic or Verifiable Credentials operation refused its inputs. |
| `store.failed` | - | A persisted-store, pack or HDT operation was refused. |
| `registry.failed` | <https://www.w3.org/TR/sparql11-query/#extensionFunctions> | An extension-function or SERVICE registration was refused. |
| `handle.unknown` | - | The handle was never issued by this engine. |
| `handle.disposed` | - | The handle was issued and then closed. |
| `option.unknown` | - | The options object has a key the function does not take. |
| `option.invalid-value` | - | An option or mode argument has a value outside its table. |
| `option.conflict` | - | Two options were given that cannot be combined. |
| `capacity.exceeded` | - | The input is above a fixed size limit of the engine. |
| `call.arity` | - | The op was called with the wrong number of arguments. |
| `call.arguments` | - | The arguments document is not a JSON array of strings. |
| `op.unknown` | - | The loaded engine has no op of this name. |
| `op.failed` | - | Any other refusal of an op. |
| `host.io` | - | The host could not read or write a file, a store or a log (no engine decision). |
<!-- errors-table:end -->

Full API: [API.md](https://github.com/danbri/factoidal-core/blob/main/npm/factoidal/API.md).
Changes: [CHANGELOG.md](CHANGELOG.md).

## Command line

```console
$ npx factoidal serve --file data.ttl /ds          # SPARQL endpoint at /ds/sparql
$ npx factoidal serve --tdb2 DIR /ds               # serve a Jena TDB2 database
$ npx factoidal pack data.ttl store/gen-1 && npx factoidal activate store gen-1   # IBK5 quad blocks
$ npx factoidal query store 'SELECT * WHERE { ?s ?p ?o } LIMIT 5'
$ npx factoidal query "$(npx factoidal sample-store)" 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
$ npx factoidal lws-serve DIR --issuer IRI         # Linked Web Storage
$ npx factoidal solid-serve DIR                    # Solid Protocol
$ npx factoidal authz-serve DIR --resource IRI --saml-idp idp.json   # OAuth 2.0 authorization server
```

`npx factoidal --help` lists every command. Replacing Apache Jena Fuseki:
[docs/fuseki-replacement.md](https://github.com/danbri/factoidal-core/blob/main/npm/factoidal/docs/fuseki-replacement.md).

## Test results

Official test suites, pass / fail / total, 2026-10-09 [B] unless marked.

The OWL DL rows below are historical measurements of the legacy harness;
they do not measure the current `owlIsConsistent` API. That API checks only
an admitted fragment of the default graph (atomic classes,
`owl:someValuesFrom`, `owl:TransitiveProperty`, and annotations, axiom
annotations included). It returns `true` for a checked finite model, `false`
for a checked contradiction and `null` for unsupported input, exhausted
`fuel` or an incomplete check. Other restrictions, negative property
assertions, imports and equivalentClass are unsupported. `owlEntails`
answers `false` only with a checked countermodel; its positive verdicts use a
separate legacy path that does not have this source-to-verdict proof. See the
[OWL API contract](https://github.com/danbri/factoidal-core/blob/main/npm/factoidal/API.md)
and the [assurance record](https://github.com/danbri/factoidal-core/blob/main/docs/20261022-owl-pr-reconciliation.md).

| Suite | Result |
|---|---|
| SPARQL 1.1 Query, Update, Protocol | 631 / 0 / 631 |
| SPARQL 1.2 | 254 / 0 / 254 |
| SPARQL Protocol, Graph Store, Service Description against `serve` | 50 / 0 / 50 [P] |
| Linked Web Storage 1.0, Touchstone (another implementer's harness), `lws-serve` | 215 / 0 / 221 (6 not applicable) [L] |
| RDF 1.1 N-Triples, N-Quads, Turtle, TriG, RDF/XML | 992 / 0 / 992 |
| RDF 1.2 syntax suites | all pass |
| RDF 1.1 Semantics | 39 / 0 / 39 |
| RDF 1.2 Semantics | 29 / 0 / 29 [S] |
| JSON-LD 1.1 toRdf, expand, flatten | 910 / 0 / 910 |
| JSON-LD 1.1 compact, fromRdf | 298 / 0 / 300 (2 not run) |
| JSON-LD 1.1 Framing | 29 / 63 / 92 |
| JSON-LD-star draft (RDF 1.2), option `rdfstar` | 168 / 1 / 171 (2 local override; 170 of 171 with them) [J] |
| RDF 1.2 eval tests written as JSON-LD-star and read back | 140 / 0 / 140 [J] |
| RDFC-1.0 | 86 / 0 / 86 |
| OWL 2 RL | 126 / 0 / 126 |
| OWL 2 DL type-inconsistency | 116 / 11 / 128 (1 other) |
| OWL 2 DL positive entailment | 169 / 35 / 206 (2 other) |
| SHACL 1.0 Core, SHACL-SPARQL | 120 / 0 / 120 |
| SHACL 1.2 Core | 103 / 30 / 133 |
| ShEx 2 validation, ShExC | 1624 / 0 / 1624 |
| CSVW | 821 / 0 / 821 (1 defective W3C test excluded) [C] |
| RIF Core | 43 / 0 / 46 (3 undecided) |
| RML Core | 60 / 0 / 76 (16 not attempted) |
| XML 1.0 (xmlconf) | 1861 / 0 (516 not run) |
| XSD 1.1 datatypes | 18951 / 5 / 18956 |
| XSLT 1.0 | 84 / 3 / 88 (1 refused) |
| JSON Schema draft-07 | 770 / 0 / 770 |
| VC Data Integrity, did:key, Ed25519 | 58 / 0 / 58 |
| XPath 1.0 (own battery) | 100 / 0 / 100 [X] |

[B] https://github.com/danbri/factoidal-core/blob/03e2e6deee8146ce7e6fdc3f8f34b8245af5ab54/docs/designissues/2026-10-09-lean-conformance-baseline.md
[P] https://github.com/danbri/factoidal-core/blob/9a4045f1572a032b53ccb867f8395fe0c8d97bb9/docs/designissues/2026-10-10-store-serve.md
[X] https://github.com/danbri/factoidal-core/blob/cb871c2de8354362ae6226eb57fb6c549624ea1a/docs/designissues/2026-10-10-xml-profile-widened.md
[L] 2026-10-22, https://github.com/danbri/factoidal-core/blob/2b9d2e39af53be31ed92463b58d3e132e65c4fe4/docs/designissues/2026-10-21-lws-touchstone-run.md (with server options, 220 of 221 pass in at least one configuration)
[S] 2026-10-21, the current W3C manifest (29 active tests), https://github.com/danbri/factoidal-core/blob/2b9d2e39af53be31ed92463b58d3e132e65c4fe4/docs/claude-rules/current-state.md
[C] 2026-10-21, validation test308, https://github.com/danbri/factoidal/issues/700
[J] 2026-10-27, tests of https://github.com/json-ld/json-ld-star/pull/61; the fail is a defective fixture (fromRdf tst07), https://github.com/danbri/factoidal-core/blob/2a656d7bfb4af329d77669afb5e62eb00625bd15/docs/designissues/2026-10-26-jsonld-star.md

## Limits

- Size: 2.9 MB packed, 14.0 MB unpacked; one 13.2 MB wasm module.
- `factoidal update` and `compact` exit 3; updates work through `serve`
  (https://github.com/danbri/factoidal/issues/641).
- Fuseki: read-only administration API, one dataset per process, no
  configuration file, no authentication, no JSON-LD from Graph Store GET
  (https://github.com/danbri/factoidal/issues/829 to 834).
- Large result sets can exceed Node's default stack; use
  `node --stack-size=4000` or Deno.
- The API can change before 1.0.

## Tested against other libraries' test suites

[echochamber](https://github.com/danbri/echochamber) gives the API of four
RDF libraries over this package and ports each library's own tests. Where
this package and the library disagree, the specification decides: a
Factoidal defect (an issue in https://github.com/danbri/factoidal), a
divergence of the library from the specification, or a gap in the echo.
Counts on 0.18.0 (echochamber main 5760a33, 2026-10-27,
https://github.com/danbri/echochamber/pull/8):

| echo | in the style of | ported | pass | defect | divergence | gap |
|---|---|---:|---:|---:|---:|---:|
| leana | Apache Jena | 748 | 317 | 1 | 15 | 415 |
| Hardylib | RDFLib | 1,438 | 511 | 8 | 919 | 0 |
| Enthie | N3.js and RDF/JS | 1,460 | 1,071 | 29 | 124 | 236 |
| MoonForge | Eclipse RDF4J | 2,801 | 2,201 | 300 | 300 | 0 |

MoonForge passed 2,124 cases on 0.16.0, 2,150 on 0.17.0
(https://github.com/danbri/echochamber/pull/5) and 2,201 on 0.18.0
(https://github.com/danbri/echochamber/pull/6). Details per echo:
`docs/<echo>/feasibility.md` and `conformance/<echo>/` in echochamber.

## Licence

Apache-2.0. See `LICENSE` and `NOTICE`.
