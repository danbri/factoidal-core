---
title: A Canary Wharf pipeline
description: Turtle and CSVW sources about Canary Wharf, each transformed by checked pipeline nodes, merged into named graphs, queried across graphs, written as N-Quads for an SBM11 store, and the pipeline's own record queried as RDF.
layout: hub.njk
tests: tests/hub/hub_canary-wharf-pipeline_test.mjs
---

# A Canary Wharf pipeline

[Hub](../) · Turtle, CSVW, nodes and evidence, named graphs, SPARQL, N-Quads, SBM11

The cells on this page run `@factoidal/core` {{ factoidalRelease.version }}
from the npm registry ([npm]({{ factoidalRelease.npmUrl }})).

The question: which tall buildings at Canary Wharf are near a busy station
with step-free access, and which steps of the pipeline does each answer
depend on?

Two sources answer it. A Turtle document describes the buildings and a
small schema. A CSV table with CSVW metadata describes the stations. Each
source goes through its own pipeline: the output of each node is the input
of the next node (`pipe`), and each node adds an evidence record. The two
results then go into one dataset, one named graph per source, and one query
joins them. The figures are illustrative sample data, not published
statistics.

```observable-js
release = Factoidal.version
```

## Source 1: buildings, in Turtle

`st:` abbreviates the station IRIs. A Turtle prefixed name cannot contain
`/`, so `cw:station/cw-jubilee` is a syntax error and the engine refuses it.
Newfoundland has no `rdf:type`; the schema gives it one.

```observable-js
CW = 'https://example.org/canary-wharf/'
```

```observable-js
buildingsTtl = `@prefix cw: <${CW}> .
@prefix st: <${CW}station/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
cw:Skyscraper rdfs:subClassOf cw:Building .
cw:heightMetres rdfs:domain cw:Building .
cw:oneCanadaSquare a cw:Skyscraper ; rdfs:label "One Canada Square" ;
  cw:heightMetres 235 ; cw:nearStation st:cw-jubilee , st:cw-dlr .
cw:eightCanadaSquare a cw:Skyscraper ; rdfs:label "8 Canada Square" ;
  cw:heightMetres 200 ; cw:nearStation st:cw-elizabeth , st:cw-jubilee .
cw:newfoundland rdfs:label "Newfoundland" ;
  cw:heightMetres 220 ; cw:nearStation st:heron-quays .
cw:crossrailPlace a cw:Building ; rdfs:label "Crossrail Place" ;
  cw:heightMetres 30 ; cw:nearStation st:cw-elizabeth .`
```

The pipeline reads the Turtle, computes the RDFS closure (Newfoundland is a
`cw:Building` by `rdfs:domain`, One Canada Square by `rdfs:subClassOf`), and
transforms the closure with a SPARQL CONSTRUCT: it keeps the buildings and
adds a height band.

```observable-js
buildingsPipeline = Factoidal.pipe(
  await Factoidal.node('turtleDocumentReader'),
  await Factoidal.node('rdfsReasoner'),
  await Factoidal.node('shippedEvaluator', { query: `PREFIX cw: <${CW}>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
CONSTRUCT { ?b a cw:Building ; rdfs:label ?l ; cw:heightMetres ?h ;
              cw:heightBand ?band ; cw:nearStation ?s }
WHERE { ?b a cw:Building ; rdfs:label ?l ; cw:heightMetres ?h ; cw:nearStation ?s
        BIND(IF(?h >= 200, "tall", "low") AS ?band) }` }),
)
```

`pipe()` checks the types of the wires before anything runs. Each
conversion is one the engine allows between a node's output and the next
node's input:

```observable-js
buildingsCheck = ({ wellTyped: buildingsPipeline.wellTyped, conversions: buildingsPipeline.check.conversions })
```

```observable-js
buildingsRun = Factoidal.run(buildingsPipeline, buildingsTtl)
```

```observable-js
buildingsEvidence = pretty(buildingsRun.evidence.map((e) => ({ stage: e.stage, status: e.status, contract: e.contract })))
```

## Source 2: stations, in CSV with CSVW metadata

```observable-js
stationsCsv = `id,name,line,stepFree,entriesMillions
cw-jubilee,Canary Wharf,Jubilee,true,38.2
cw-elizabeth,Canary Wharf,Elizabeth,true,26.4
cw-dlr,Canary Wharf,DLR,true,14.9
heron-quays,Heron Quays,DLR,false,6.1`
```

```observable-js
stationsMetadata = JSON.stringify({
  '@context': 'http://www.w3.org/ns/csvw',
  url: 'stations.csv',
  tableSchema: {
    aboutUrl: `${CW}station/{id}`,
    columns: [
      { name: 'id', titles: 'id', suppressOutput: true },
      { name: 'name', titles: 'name', propertyUrl: 'http://www.w3.org/2000/01/rdf-schema#label' },
      { name: 'line', titles: 'line', propertyUrl: `${CW}line`, valueUrl: `${CW}line/{line}` },
      { name: 'stepFree', titles: 'stepFree', propertyUrl: `${CW}stepFree`, datatype: 'boolean' },
      { name: 'entriesMillions', titles: 'entriesMillions', propertyUrl: `${CW}entriesMillions`, datatype: 'decimal' },
    ],
  },
})
```

The CSVW conversion is the function `csvwToRdf`. It is not a pipeline node:
the stage registry lists CSVW with status `missing` (no contract and no
test suite in the registry), so it adds no evidence record. The last
section shows what that does to the pipeline's record.

```observable-js
fromCsvw = Factoidal.csvwToRdf(stationsCsv, stationsMetadata, { base: CW, mode: 'minimal' })
```

```observable-js
csvwStage = {
  const s = (await Factoidal.stages()).find((x) => x.name === 'CSVW (tabular data to RDF)');
  return ({ name: s.name, status: s.status, bound: s.bound, runnable: s.runnable });
}
```

The CSVW output goes into a one-node pipeline: a CONSTRUCT that types each
station and marks a station as busy above 20 million entries.

```observable-js
stationsPipeline = Factoidal.pipe(await Factoidal.node('shippedEvaluator', { query: `PREFIX cw: <${CW}>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
CONSTRUCT { ?s a cw:Station ; rdfs:label ?n ; cw:line ?line ; cw:stepFree ?sf ;
              cw:entriesMillions ?e ; cw:busy ?busy }
WHERE { ?s rdfs:label ?n ; cw:line ?line ; cw:stepFree ?sf ; cw:entriesMillions ?e
        BIND(?e > 20 AS ?busy) }` }))
```

```observable-js
stationsRun = Factoidal.run(stationsPipeline, fromCsvw)
```

## One dataset, one named graph per source

`Dataset` is an RDF/JS `DatasetCore`. Each pipeline's output graph goes into
a graph named after its source.

```observable-js
merged = {
  const { namedNode, quad } = Factoidal.dataFactory;
  const all = await Factoidal.parse('', { format: 'nquads' });
  for (const [name, run] of Object.entries({ buildings: buildingsRun, stations: stationsRun })) {
    const g = namedNode(`${CW}graph/${name}`);
    for (const q of run.graph) all.add(quad(q.subject, q.predicate, q.object, g));
  }
  return all;
}
```

```observable-js
perGraph = merged.query(`SELECT ?g (COUNT(*) AS ?triples) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g ORDER BY ?g`)
```

## The query across the graphs

Tall buildings near a station that is step-free and busy, with the lines and
the total entries of those stations, kept when the total is above 30
million. The join variable `?st` binds an IRI from the Turtle source in one
graph and the same IRI from the CSV source in the other. Newfoundland is
tall, but its station is not step-free; Crossrail Place is near a busy
step-free station, but it is low.

The query runs as a pipeline node too, so the answer graph has an evidence
record. The CONSTRUCT writes the answer as triples.

```observable-js
answerRun = Factoidal.run(Factoidal.pipe(await Factoidal.node('shippedEvaluator', { query: `PREFIX cw: <${CW}>
PREFIX g: <${CW}graph/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
CONSTRUCT { ?b cw:answerTo cw:question ; cw:viaStation ?st ; cw:viaLine ?line }
WHERE {
  GRAPH g:buildings { ?b cw:heightBand "tall" ; cw:nearStation ?st }
  GRAPH g:stations  { ?st cw:stepFree true ; cw:busy true ; cw:line ?line }
}` })), merged)
```

The same join as a table, with the aggregate and the HAVING filter:

```observable-js
answer = merged.query(`PREFIX cw: <${CW}>
PREFIX g: <${CW}graph/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?building ?height (GROUP_CONCAT(DISTINCT ?lineName; separator=", ") AS ?lines) (SUM(?e) AS ?entries)
WHERE {
  GRAPH g:buildings { ?b rdfs:label ?building ; cw:heightMetres ?height ;
                      cw:heightBand "tall" ; cw:nearStation ?st }
  GRAPH g:stations  { ?st cw:stepFree true ; cw:busy true ; cw:line ?line ;
                      cw:entriesMillions ?e
                      BIND(STRAFTER(STR(?line), "line/") AS ?lineName) }
}
GROUP BY ?building ?height
HAVING (SUM(?e) > 30)
ORDER BY DESC(?height)`)
```

## The pipeline's record, as RDF

Every evidence record above is a JavaScript object. To query the record
with the data, the next cell writes it as triples in a named graph
`g:provenance`, with [PROV-O](https://www.w3.org/TR/prov-o/) for the
structure: each run and each CSVW call is a `prov:Activity` that
`prov:used` its input and `prov:generated` its output graph, and each step
has its stage, status and contract. The cell only copies fields; the
engine does not yet give this graph itself
([issue 563](https://github.com/danbri/factoidal/issues/563), the evidence
graph profile). The CSVW call has no evidence record, so its step comes
from the registry entry above.

```observable-js
provenance = {
  const { namedNode, literal, quad } = Factoidal.dataFactory;
  const PROV = 'http://www.w3.org/ns/prov#';
  const RDF_TYPE = namedNode('http://www.w3.org/1999/02/22-rdf-syntax-ns#type');
  const XSD_INT = namedNode('http://www.w3.org/2001/XMLSchema#integer');
  const gp = namedNode(`${CW}graph/provenance`);
  const n = (local) => namedNode(CW + local);
  const ds = await Factoidal.parse('', { format: 'nquads' });
  for (const q of merged) ds.add(q);
  for (const q of answerRun.graph) ds.add(quad(q.subject, q.predicate, q.object, n('graph/answer')));
  const add = (s, p, o) => ds.add(quad(s, p, o, gp));
  const activity = (name, used, generated, steps) => {
    const a = n(`activity/${name}`);
    add(a, RDF_TYPE, namedNode(PROV + 'Activity'));
    for (const u of used) add(a, namedNode(PROV + 'used'), u);
    add(a, namedNode(PROV + 'generated'), generated);
    steps.forEach((s, i) => {
      const step = n(`activity/${name}/step/${i}`);
      add(step, n('partOf'), a);
      add(step, n('order'), literal(String(i), XSD_INT));
      add(step, n('stage'), literal(s.stage));
      add(step, n('status'), literal(s.status));
      if (s.contract) add(step, n('contract'), literal(s.contract));
      for (const x of s.assumptions || []) add(step, n('assumption'), literal(x));
    });
  };
  activity('buildings', [n('source/buildings.ttl')], n('graph/buildings'), buildingsRun.evidence);
  activity('csvw', [n('source/stations.csv')], n('data/csvw-output'), [{ stage: csvwStage.name, status: csvwStage.status }]);
  activity('stations', [n('data/csvw-output')], n('graph/stations'), stationsRun.evidence);
  activity('answer', [n('graph/buildings'), n('graph/stations')], n('graph/answer'), answerRun.evidence);
  return ds;
}
```

Which steps made each graph, in order:

```observable-js
stepsPerGraph = provenance.query(`PREFIX cw: <${CW}>
PREFIX g: <${CW}graph/>
PREFIX prov: <http://www.w3.org/ns/prov#>
SELECT ?graph ?order ?stage ?status WHERE {
  GRAPH g:provenance { ?a prov:generated ?graph . ?step cw:partOf ?a ;
                       cw:order ?order ; cw:stage ?stage ; cw:status ?status }
} ORDER BY ?graph ?order`)
```

The whole lineage of the answer graph, by following the data: the property
path `(prov:used/^prov:generated)*` walks from the activity that made a
graph to the activities that made its inputs, to any depth.

```observable-js
answerLineage = provenance.query(`PREFIX cw: <${CW}>
PREFIX g: <${CW}graph/>
PREFIX prov: <http://www.w3.org/ns/prov#>
SELECT ?activity ?stage ?status WHERE {
  GRAPH g:provenance {
    ?made prov:generated g:answer .
    ?made (prov:used/^prov:generated)* ?activity .
    ?step cw:partOf ?activity ; cw:order ?order ; cw:stage ?stage ; cw:status ?status }
} ORDER BY ?activity ?order`)
```

For each data graph: is every step in its lineage `proved`? `NOT EXISTS`
looks for one that is not.

```observable-js
allProved = provenance.query(`PREFIX cw: <${CW}>
PREFIX g: <${CW}graph/>
PREFIX prov: <http://www.w3.org/ns/prov#>
SELECT ?graph ?allProved WHERE {
  VALUES ?graph { g:buildings g:stations g:answer }
  BIND(NOT EXISTS { GRAPH g:provenance {
    ?made prov:generated ?graph . ?made (prov:used/^prov:generated)* ?a .
    ?step cw:partOf ?a ; cw:status ?s FILTER(?s != "proved") } } AS ?allProved)
} ORDER BY ?graph`)
```

Data and record in one query: each building in the answer, with each
step upstream of it that is not `proved`.

```observable-js
answerCaveats = provenance.query(`PREFIX cw: <${CW}>
PREFIX g: <${CW}graph/>
PREFIX prov: <http://www.w3.org/ns/prov#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT DISTINCT ?building ?stage ?status WHERE {
  GRAPH g:answer { ?b cw:answerTo cw:question }
  GRAPH g:buildings { ?b rdfs:label ?building }
  GRAPH g:provenance {
    ?made prov:generated g:answer . ?made (prov:used/^prov:generated)* ?a .
    ?step cw:partOf ?a ; cw:stage ?stage ; cw:status ?status FILTER(?status != "proved") }
} ORDER BY ?building`)
```

So the record can be followed as data: named graphs say which source a fact
came from, and the provenance graph says which steps made that graph. The
same computation is stated in Lean: the guarantee of a well-typed path is
the composition of its stages' contracts plus the union of their named
assumptions (`Dataflow.query_sound` and the source table in
[docs/2026-10-25-composition.md](https://github.com/danbri/factoidal-core/blob/main/docs/2026-10-25-composition.md)). Two
parts of it still come from the JavaScript side: this page copies the
evidence objects into triples (the engine should give that graph,
[issue 563](https://github.com/danbri/factoidal/issues/563)), and the CSVW
step has no evidence record because CSVW is not a registered stage with a
contract ([issue 975](https://github.com/danbri/factoidal/issues/975),
component contracts).

## Writing the dataset for a persistent store

The N-Quads writer node (status `proved`) writes all five named graphs:
buildings, stations, answer and provenance, with the default graph empty.

```observable-js
nquadsRun = Factoidal.run(Factoidal.pipe(await Factoidal.node('nquadsDocumentWriter')), provenance)
```

```observable-js
nquadsSummary = {
  const text = nquadsRun.evidence[0].artefact.text;
  const lines = text.split('\n').filter((l) => l.length > 0);
  const graphs = [...new Set(lines.map((l) => (l.match(/<([^>]*)> \.$/) || [])[1]))].sort();
  return ({ quads: lines.length, graphs, proved: nquadsRun.proved });
}
```

An SBM11 generation (the Shardborough store) holds such a dataset on disk,
with its named graphs. In @factoidal/core {{ factoidalRelease.version }} the
package can open and query an SBM11 generation (`openSbm11`), but it cannot
pack one: packing SBM11 from npm is
[issue 1009](https://github.com/danbri/factoidal/issues/1009), with its
stages in
[docs/designissues/2026-10-24-sbm11-in-npm.md](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-10-24-sbm11-in-npm.md)
(its first user named there is the Docklands app,
<https://danbri.github.io/londat/docklands/>). Today the native tools pack
the text above:

```
l4sbm11-pack canary-wharf.nq store/gen-1 && l4sbm11 activate store gen-1
l4sbm11 query store --file answer.rq
```

Measured 2026-10-25 with those commands on this page's N-Quads (96 quads,
5,533 bytes on disk): the store answers the query of the table above with
the same two rows, and the "data and record in one query" above with the
same two rows, both on its id path (`path=ids`).

```observable-js
sbm11PackInNpm = Object.keys(Factoidal).filter((k) => /pack/i.test(k) && /sbm11/i.test(k))
```
