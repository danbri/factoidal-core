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

## Web platform

Foafnaut is a web browser with its own built-in engine, BubblePopKit: it parses HTML,
computes CSS, lays out text and boxes, runs page scripts with BubblePopJS and draws with
WebGPU. Textnaut is the same engine in a text terminal. [Web platform](./web-platform/) has all their pages.

<ul class="post-series">
  <li><a href="./foafnaut/">Foafnaut</a> — the browser in a page: tabs, an address bar for URLs, searches and commands, view source, XML with XSLT, drawn by the built-in engine with WebGPU. It works at phone width.</li>
  <li><a href="./epub/">EPUB reader</a> — open an unencrypted EPUB 3 file in your browser.</li>
  <li><a href="./textnaut/">Textnaut</a> — the text-mode browser in a page: the built-in engine lays out a page and Textnaut shows it as a grid of characters with numbered links, as in a terminal. The terminal program: <code>npx @foafos/textnaut</code>.</li>
  <li><a href="./foafnaut/pages/start.html">Start page</a> — the page Foafnaut and Textnaut open with: sites on the web to try, grouped, each with a note on how well it works today, and copies of some openly licensed pages that open inside Foafnaut on the Hub.</li>
  <li><a href="./foafnaut/pages/index.html">Demo pages</a> — pages that show what the engine draws: scripts, WebGPU and WebGL, SVG, text, XML and XSLT. Open them in <a href="./foafnaut/">Foafnaut</a> or <a href="./textnaut/">Textnaut</a>.</li>
  <li><a href="./foafnaut/pages/stress.html">Stress tests</a> — heavy pages kept apart, such as the Spinal Tap page and the shader gallery, with what makes each one heavy.</li>
  <li><a href="./foafnaut/pages/settings.html">Settings</a> — the page script engine (BubblePopJS or QuickJS-NG), text size, theme and the other choices; in Foafnaut it is the gear at the right of the toolbar, or <code>:settings</code>.</li>
  <li><a href="./notebook/">Notebook: cells drawn by the built-in engine</a> — notebook cells whose output the engine draws: a page in a canvas, a Foafnaut view with scripts, and Textnaut's text, from one engine, with each cell's timings.</li>
  <li><a href="./conformance/">Conformance</a> — how much of Test262, the JavaScript conformance suite, and of the Web Platform Tests Foafnaut passes, from full measured runs, next to other browsers, with the history of every run.</li>
  <li><a href="./specs/">Data and documents conformance</a> — RDF, SPARQL, OWL 2, SHACL, ShEx, JSON-LD, CSVW, RML, RIF, Verifiable Credentials, XML, XSLT, Schematron, JSON Schema and MathML: one row per technology family, then each specification, version and test population, with the history of every recorded run.</li>
  <li><a href="./web-platform/foafnaut/notes/">Foafnaut notes</a> — short dated notes on what the browser can do, newest first, with links that open each demo in Foafnaut.</li>
  <li><a href="./foafnaut2525-status/">Project status</a> — where the engine stands, suite by suite; the engine renders this note too.</li>
  <li><a href="./html-webgpu/">HTML and CSS in the built-in engine</a> — editable HTML/CSS, block and inline layout, shared vector geometry, WebGPU pixels and clickable source-mapped links.</li>
  <li><a href="./render-scores/">Rendering and font scores</a> — the score of each rendering and font suite by commit, and the largest failure groups: the next fixes.</li>
  <li><a href="./render-scores/#svg-tiny-pixels">SVG Tiny 1.2 test suite results</a> — each W3C SVG Tiny 1.2 test drawn by the engine and compared with its reference image.</li>
</ul>

## Parallel compute

<ul class="post-series">
  <li><a href="./gssl/">GDSL graph workbench</a> — one shared typed dataflow language across signal, font, motion, image and numeric examples; JS graph builders and S-expressions both run through the same CPU/WebGPU graph checker. The page also includes an experimental general-purpose GPU device lab: two actual compute passes, persistent intermediate buffers, upload reuse, bounded buffer inspection and a draft language specification. This is not the assured SPARQL accelerator.</li>
  <li><a href="./paralliverse/">Paralleliverse</a> — typed parallel-computation Studio: a real RDF/SPARQL BGP evaluated independently by Lean/Wasm and two WebGPU join plans, with lexical triples, intermediate GPU relations, solution-bag comparisons and source-scoped evidence; plus word-map and packing experiments.</li>
</ul>

## Pages

<ul class="post-series">
  <li><a href="./data-compositor/">Data Compositor</a> — a visual studio roster pipeline: CSVW, RDF inference, named graphs, SPARQL and XSLT, with editable inputs, component evidence, portable pipeline files and FOAF pod storage</li>
  <li><a href="./rdf-syntaxes/">RDF syntaxes</a> — Turtle, N-Triples, N-Quads, TriG, RDF/XML, JSON-LD; RDF 1.2 triple terms, reifiers, annotations and base direction; error positions</li>
  <li><a href="./jsonld-star/">JSON-LD-star and JSON-LD 1.3</a> — RDF 1.2 triple terms, reifiers, annotations and base direction in JSON-LD (<code>@triple</code>, <code>@reifies</code>, <code>@annotation</code>, option <code>rdfstar</code>); the draft, the choices made, scores, and the plan towards JSON-LD 1.3</li>
  <li><a href="./rdf12-jsonld-usecases/">RDF 1.2 use cases in JSON-LD-star</a> — provenance, facts with several occurrences, edge properties, claims that are not asserted, one reifier for several triples, annotations on annotations; SPARQL 1.2 annotation queries</li>
  <li><a href="./sparql/">SPARQL</a> — query and update, property paths, aggregates, GeoSPARQL functions, <code>text:query</code>, extension functions in JavaScript and WebAssembly, SERVICE, SPARQL 1.2 triple patterns</li>
  <li><a href="./ethereum-wasm-sparql/">Ethereum bytecode → WASM → SPARQL</a> — interactive full-uint256 EVM bytecode compilation, seven-condition eligibility policy, editable RDF/SPARQL, bytecode mutation and provenance hashes</li>
  <li><a href="./importers/">Data importers and integration</a> — CSVW, RML, JSON-LD and a GRDDL-style XSLT step, four independent sources merged into one dataset, each in its own named graph, one query across them</li>
  <li><a href="./inference/">Inference</a> — RDFS and OWL 2 RL closure over pipeline output, derived triples in their own graph, OWL 2 DL consistency and entailment</li>
  <li><a href="./sparql-rl/">SPARQL-RL</a> — SPARQL 1.2 RL rules (W3C editor's draft) with data blocks, NOT, SET, GROUP, stratification and run-once rules; OWL 2 RL as SPARQL-RL rules; the semi-naive and BGP theorems; comparison with RIF, SWRL, SPIN, SHACL rules, N3, Datalog and OWL 2 RL</li>
  <li><a href="./canary-wharf-pipeline/">A Canary Wharf pipeline</a> — Turtle and CSVW sources through checked nodes, merged into named graphs, one query across them, N-Quads for an SBM11 store, and the pipeline's record queried as RDF</li>
  <li><a href="./checked-pipelines/">Checked pipelines</a> — readers, reasoners, the SPARQL evaluator and writers as nodes; per-step status and contract, entailment explanations, and the list of what is proved and what is assumed</li>
  <li><a href="./validation/">SHACL and ShEx</a> — validation reports as RDF, SHACL-SPARQL, ShExC schemas</li>
  <li><a href="./canonical-and-credentials/">Canonical form and credentials</a> — RDFC-1.0, graph hashes, eddsa-rdfc-2022 proofs, did:key</li>
  <li><a href="./servers/">Servers</a> — SPARQL Protocol and Graph Store with Fuseki paths, read-only Jena TDB2, Linked Web Storage, Solid, XMPP (commands and recorded output)</li>
  <li><a href="./webdav/">WebDAV</a> — serve local and remote Linked Web Storage to Finder, Windows Explorer, GNOME Files and other WebDAV clients; did:key login to an LWS server, HTTPS through a proxy, Tailscale and SSH from behind NAT</li>
  <li><a href="./webdav-lws-design/">WebDAV, LWS and custodians</a> — design note: what the 0.21.0 WebDAV and LWS theorems say and do not say, one custodian per privileged resource, careful read-write LWS mounts, and read-only projections of SPARQL, SKOS, feeds and public pods</li>
  <li><a href="./pods-and-bots/">Pods, bots and access control</a> — one LWS pod owned by a did:key agent, a read-write and a read-only bot through a Web Access Control ACL; which identity is checked where, one read-only WebDAV mount per bot in 0.21.0, and what each sees in a mounted volume</li>
  <li><a href="./shardborough/">Shardborough (early stage)</a> — the persisted store: pack, activate, query, update through a delta log, compact</li>
</ul>

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
