---
title: Factoidal hub
layout: hub.njk
---

# Factoidal

<p class="warning"><strong>⚠️ EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.</strong> This covers the whole core
library and every command line tool, and in particular all protocol,
authentication and security code.</p>

Factoidal is an RDF engine written in Lean 4 and compiled to WebAssembly
and to native code. It reads and writes the RDF 1.1 and RDF 1.2 syntaxes,
answers SPARQL 1.1 and 1.2, reasons with RDFS and OWL 2, validates with
SHACL and ShEx, imports CSV, JSON and XML, canonicalises and signs RDF,
serves data over HTTP, and keeps it on disk.

The pages below run their examples in this page with the npm package
`@factoidal/core` {{ factoidalRelease.version }}, the published release
(loaded from `{{ factoidalRelease.base }}`): edit a cell and press Run. The engine and the data stay
in your browser.

## Pages

<ul class="post-series">
  <li><a href="./rdf-syntaxes/">RDF syntaxes</a> — Turtle, N-Triples, N-Quads, TriG, RDF/XML, JSON-LD; RDF 1.2 triple terms, reifiers, annotations and base direction; error positions</li>
  <li><a href="./jsonld-star/">JSON-LD-star and JSON-LD 1.3</a> — RDF 1.2 triple terms, reifiers, annotations and base direction in JSON-LD (<code>@triple</code>, <code>@reifies</code>, <code>@annotation</code>, option <code>rdfstar</code>); the draft, the choices made, scores, and the plan towards JSON-LD 1.3</li>
  <li><a href="./rdf12-jsonld-usecases/">RDF 1.2 use cases in JSON-LD-star</a> — provenance, facts with several occurrences, edge properties, claims that are not asserted, one reifier for several triples, annotations on annotations; SPARQL 1.2 annotation queries</li>
  <li><a href="./sparql/">SPARQL</a> — query and update, property paths, aggregates, GeoSPARQL functions, <code>text:query</code>, extension functions in JavaScript and WebAssembly, SERVICE, SPARQL 1.2 triple patterns</li>
  <li><a href="./importers/">Data importers and integration</a> — CSVW, RML, JSON-LD and a GRDDL-style XSLT step, four independent sources merged into one dataset, each in its own named graph, one query across them</li>
  <li><a href="./inference/">Inference</a> — RDFS and OWL 2 RL closure over pipeline output, derived triples in their own graph, OWL 2 DL consistency and entailment</li>
  <li><a href="./canary-wharf-pipeline/">A Canary Wharf pipeline</a> — Turtle and CSVW sources through checked nodes, merged into named graphs, one query across them, N-Quads for an SBM11 store, and the pipeline's record queried as RDF</li>
  <li><a href="./checked-pipelines/">Checked pipelines</a> — readers, reasoners, the SPARQL evaluator and writers as nodes; per-step status and contract, entailment explanations, and the list of what is proved and what is assumed</li>
  <li><a href="./validation/">SHACL and ShEx</a> — validation reports as RDF, SHACL-SPARQL, ShExC schemas</li>
  <li><a href="./canonical-and-credentials/">Canonical form and credentials</a> — RDFC-1.0, <code>canonicalHash</code> (SHA-256, graph names kept), eddsa-rdfc-2022 proofs, did:key</li>
  <li><a href="./servers/">Servers</a> — SPARQL Protocol and Graph Store with Fuseki paths, read-only Jena TDB2, Linked Web Storage with its authorization server, Solid, XMPP (commands and recorded output)</li>
  <li><a href="./webdav/">WebDAV</a> — serve local and remote Linked Web Storage to Finder, Windows Explorer, GNOME Files and other WebDAV clients; did:key login to an LWS server, HTTPS through a proxy, Tailscale and SSH from behind NAT</li>
  <li><a href="./shardborough/">Shardborough (early stage)</a> — the persisted store: pack (IBK5 or SBM11), activate, query, update through a delta log, compact; store-open times</li>
</ul>

## What is new

- **0.18.0** ([release](https://github.com/danbri/factoidal-core/releases/tag/v0.18.0)):
  XSD constructor casts as XPath F&O 3.1 §19 says
  ([SPARQL](./sparql/#string-functions-casts-and-base-direction));
  base direction in the SPARQL string functions; JSON-LD-star with the
  option `rdfstar`
  ([JSON-LD-star and JSON-LD 1.3](https://danbri.github.io/factoidal/web/hub/jsonld-star/)); a WebDAV
  server for file browsers and a larger LWS client ([servers](./servers/));
  a faster store open ([Shardborough](./shardborough/#opening-a-store-from-node)).
- **0.17.0** ([release](https://github.com/danbri/factoidal-core/releases/tag/v0.17.0)):
  **breaking**, `canonicalHash` gives the SHA-256 of the canonical form
  ([canonical form](./canonical-and-credentials/)); SPARQL string-function
  argument types; `factoidal pack --layout sbm11`
  ([Shardborough](./shardborough/#the-sbm11-layout-layout-sbm11)); store open
  2.6 times faster on the londat store; `lws-serve --authz`, an authorization server on the
  storage's port ([servers](./servers/#linked-web-storage-10)); release
  checks (no test skips when the wasm lacks an op).

All changes: [CHANGELOG](https://github.com/danbri/factoidal-core/blob/main/npm/factoidal/CHANGELOG.md),
[releases](https://github.com/danbri/factoidal-core/releases).

## Tested against other libraries' test suites

[echochamber](https://github.com/danbri/echochamber) gives the API of four
RDF libraries over `@factoidal/core` and ports each library's own tests.
Where Factoidal and the library disagree, the specification decides: a
Factoidal defect (an issue), a divergence of the library from the
specification, or a gap in the echo. Counts on 0.18.0 (echochamber main 5760a33,
https://github.com/danbri/echochamber/pull/8):

| echo | in the style of | ported | pass | defect | divergence | gap |
|---|---|---:|---:|---:|---:|---:|
| leana | Apache Jena | 748 | 317 | 1 | 15 | 415 |
| Hardylib | RDFLib | 1,438 | 511 | 8 | 919 | 0 |
| Enthie | N3.js and RDF/JS | 1,460 | 1,071 | 29 | 124 | 236 |
| MoonForge | Eclipse RDF4J | 2,801 | 2,201 | 300 | 300 | 0 |

MoonForge passed 2,124 cases on 0.16.0, 2,150 on 0.17.0 and 2,201 on
0.18.0 ([echochamber PR 5](https://github.com/danbri/echochamber/pull/5),
[PR 6](https://github.com/danbri/echochamber/pull/6)). Fixes for 16 more
defects that the echoes found are in the next release
(https://github.com/danbri/factoidal-core/pull/148).

## The API in one cell

```observable-js
example = {
  const ds = await Factoidal.parse('<http://example.org/a> <http://example.org/p> "hello" .', { format: 'ntriples' });
  const rows = await ds.query('SELECT ?o WHERE { ?s ?p ?o }');
  return rows[0].get('o').value;
}
```

`Factoidal` is the module `@factoidal/core` (in a page:
`import * as Factoidal from 'https://cdn.jsdelivr.net/npm/@factoidal/core/browser.js'`;
in Node: `import * as Factoidal from '@factoidal/core'`). `parse`,
`csvwToRdf`, `rmlMap`, `jsonldToRdf`, the closures and CONSTRUCT return a
`Dataset`: a handle to data held inside the engine, with `query`,
`update`, `serialize`, `closure`, `validateShacl`, `validateShex` and
`canonicalize`.

## Standards support

Each row is one conformance runner of the Lean 4 tree, run over the test
suite named in the second column. The numbers are read from the record
below when the site is built; none is written by hand.

Record: [{{ hubStandards.file }}](./records/{{ hubStandards.file }})
(plain table: [{{ hubStandards.textFile }}](./records/{{ hubStandards.textFile }})),
measured {{ hubStandards.generated }} with `tools/lean-scoreboard.sh`.
{{ hubStandards.binaries }}

<div class="standards-table">
<table>
<thead><tr><th>Specification area</th><th>Suite (runner: fixture)</th><th>Score</th></tr></thead>
<tbody>
{%- for row in hubStandards.rows %}
<tr><td>{{ row.area }}</td><td><code>{{ row.suite }}</code></td><td>{{ row.text }}</td></tr>
{%- endfor %}
</tbody>
</table>
</div>

OWL 2 rows by regime. The **RL closure regime** applies the OWL 2 RL rules
(OWL 2 Profiles §4.3) and nothing else. Those rules are complete only for
ontologies in the OWL 2 RL profile, so on the full catalogs
(`type-positive-entailment.rdf`, `type-inconsistency.rdf`, `syntax-dl.rdf`
and others) the cases that need OWL 2 DL reasoning are fails of that
regime by design. Its "Approved, in scope" rows are the cases that the RL
rules can decide. The **DL regime** (RL closure, then a tableau refuter)
and the **RDF-Based regime** run the same catalogs and are the measures for
the other cases.

"Other" counts cases that are neither a pass nor a fail: skipped,
unsupported, undecided, not attempted, or a local override named by an
open issue. The notes of the record say which.

## Older notebooks

The [historical F\* notebooks](../historical-fstar-notebooks/) are the 54
hub posts written before 2026-10-20, most of them for the F\* engine. They
are kept unchanged as a record.
