---
title: Factoidal hub
layout: hub.njk
---

# Factoidal

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
  <li><a href="./sparql/">SPARQL</a> — query and update, property paths, aggregates, GeoSPARQL functions, <code>text:query</code>, extension functions in JavaScript and WebAssembly, SERVICE, SPARQL 1.2 triple patterns</li>
  <li><a href="./importers/">Data importers and integration</a> — CSVW, RML, JSON-LD and a GRDDL-style XSLT step, four independent sources merged into one dataset, each in its own named graph, one query across them</li>
  <li><a href="./inference/">Inference</a> — RDFS and OWL 2 RL closure over pipeline output, derived triples in their own graph, OWL 2 DL consistency and entailment</li>
  <li><a href="./canary-wharf-pipeline/">A Canary Wharf pipeline</a> — Turtle and CSVW sources through checked nodes, merged into named graphs, one query across them, N-Quads for an SBM11 store, and the pipeline's record queried as RDF</li>
  <li><a href="./checked-pipelines/">Checked pipelines</a> — readers, reasoners, the SPARQL evaluator and writers as nodes; per-step status and contract, entailment explanations, and the list of what is proved and what is assumed</li>
  <li><a href="./validation/">SHACL and ShEx</a> — validation reports as RDF, SHACL-SPARQL, ShExC schemas</li>
  <li><a href="./canonical-and-credentials/">Canonical form and credentials</a> — RDFC-1.0, graph hashes, eddsa-rdfc-2022 proofs, did:key</li>
  <li><a href="./servers/">Servers</a> — SPARQL Protocol and Graph Store with Fuseki paths, read-only Jena TDB2, Linked Web Storage, Solid, XMPP (commands and recorded output)</li>
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
