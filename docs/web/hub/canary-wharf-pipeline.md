---
title: A Canary Wharf pipeline
description: Real Canary Wharf buildings from the kgx knowledge graph (Turtle) and a CSVW table of station lines, each transformed by checked pipeline nodes, merged into named graphs, joined by walking distance, written as N-Quads for an SBM11 store, and the pipeline's own record queried as RDF.
layout: hub.njk
tests: tests/hub/hub_canary-wharf-pipeline_test.mjs
---

# A Canary Wharf pipeline

[Hub](../) · Turtle, CSVW, nodes and evidence, named graphs, SPARQL, N-Quads, SBM11

The cells on this page run `@factoidal/core` {{ factoidalRelease.version }}
from the npm registry ([npm]({{ factoidalRelease.npmUrl }})).

The question: which of the tall buildings at Canary Wharf have a station
entrance of each line within 300 metres, and which steps of the pipeline
does each answer depend on?

Two sources answer it.

- The buildings come from **kgx**, the Canary Wharf knowledge graph of
  [danbri/londat](https://github.com/danbri/londat/tree/main/kgx) (search
  page: <https://danbri.github.io/londat/cwplans/kg/>). The Turtle below is
  an extract of its `buildings` graph, version
  `https://kgx.foaf.tv/id/graphbuildings41263dc7cc077db2` (RDFC-1.0 SHA-256
  `41263dc7…9876`): names, heights, levels and positions of 8 towers and 6
  station buildings. Licence of that graph: derived from OpenStreetMap
  (© OpenStreetMap contributors, [ODbL 1.0](https://www.openstreetmap.org/copyright)),
  Wikidata (CC0) and OS Open identifiers (OGL). kgx is scoping data, not
  reviewed for production.
- The lines that serve each station building are a CSV table with CSVW
  metadata.

Each source goes through its own pipeline: the output of each node is the
input of the next node (`pipe`), and each node adds an evidence record. The
two results then go into one dataset, one named graph per source, and one
query joins them.

```observable-js
release = Factoidal.version
```

## Source 1: buildings, in Turtle (an extract of kgx)

```observable-js
CW = 'https://example.org/canary-wharf/'
```

```observable-js
KGX_VERSION = 'https://kgx.foaf.tv/id/graphbuildings41263dc7cc077db2'
```

```observable-js
buildingsTtl = `# Extract of the kgx graph version <https://kgx.foaf.tv/id/graphbuildings41263dc7cc077db2>
# (danbri/londat, kgx/graphs/buildings/41263dc7cc077db2.nq.gz), triples copied unchanged.
# Derived from OpenStreetMap (c) OpenStreetMap contributors, ODbL 1.0,
# https://www.openstreetmap.org/copyright ; Wikidata (CC0); OS Open UPRN/USRN/TOID ids (OGL).
@prefix id: <https://kgx.foaf.tv/id/> .
@prefix cwk: <https://kgx.foaf.tv/vocab#> .
@prefix s: <https://schema.org/> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
id:cwb0413 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "commercial" ;
  cwk:heightMetres "235"^^xsd:integer ;
  cwk:levels "50"^^xsd:integer ;
  s:latitude "51.504938"^^xsd:decimal ;
  s:longitude "-0.019519"^^xsd:decimal ;
  s:name "One Canada Square" ;
  s:sameAs <https://www.openstreetmap.org/way/5986754> .
id:cwb0417 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "office" ;
  cwk:heightMetres "199.5"^^xsd:decimal ;
  cwk:levels "45"^^xsd:integer ;
  s:alternateName "HSBC UK" ;
  s:latitude "51.505434"^^xsd:decimal ;
  s:longitude "-0.017438"^^xsd:decimal ;
  s:name "8 Canada Square" ;
  s:sameAs <https://www.openstreetmap.org/way/5986805> .
id:cwb0414 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "office" ;
  cwk:heightMetres "87.7"^^xsd:decimal ;
  cwk:levels "15"^^xsd:integer ;
  s:alternateName "Bank of America" ;
  s:latitude "51.505589"^^xsd:decimal ;
  s:longitude "-0.018536"^^xsd:decimal ;
  s:name "5 Canada Square" ;
  s:sameAs <https://www.openstreetmap.org/way/175512094> .
id:cwb0465 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "office" ;
  cwk:heightMetres "70.95"^^xsd:decimal ;
  cwk:levels "20"^^xsd:integer ;
  s:alternateName "McGraw Hill" ;
  s:latitude "51.504111"^^xsd:decimal ;
  s:longitude "-0.016936"^^xsd:decimal ;
  s:name "20 Canada Square" ;
  s:sameAs <https://www.openstreetmap.org/way/177143626> .
id:cwb0451 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "apartments" ;
  cwk:levels "58"^^xsd:integer ;
  s:alternateName "Newfoundland Quay" ;
  s:latitude "51.504273"^^xsd:decimal ;
  s:longitude "-0.02509"^^xsd:decimal ;
  s:name "Newfoundland" ;
  s:sameAs <https://www.openstreetmap.org/way/532616070> .
id:cwb0590 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "apartments" ;
  cwk:heightMetres "205"^^xsd:integer ;
  cwk:levels "57"^^xsd:integer ;
  s:latitude "51.502269"^^xsd:decimal ;
  s:longitude "-0.015032"^^xsd:decimal ;
  s:name "One Park Drive" ;
  s:sameAs <https://www.openstreetmap.org/way/534219763> .
id:cwb0577 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "apartments" ;
  cwk:levels "75"^^xsd:integer ;
  s:latitude "51.502761"^^xsd:decimal ;
  s:longitude "-0.02551"^^xsd:decimal ;
  s:name "Landmark Pinnacle" ;
  s:sameAs <https://www.openstreetmap.org/way/365809822> .
id:cwb0358 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "retail" ;
  cwk:heightMetres "28"^^xsd:integer ;
  s:latitude "51.506054"^^xsd:decimal ;
  s:longitude "-0.018017"^^xsd:decimal ;
  s:name "Crossrail Place" ;
  s:sameAs <https://www.openstreetmap.org/way/281015404> .
id:cwb0409 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "train_station" ;
  cwk:levels "3"^^xsd:integer ;
  s:alternateName "Canary Wharf DLR" ;
  s:latitude "51.505024"^^xsd:decimal ;
  s:longitude "-0.020972"^^xsd:decimal ;
  s:name "Canary Wharf" ;
  s:sameAs <https://www.openstreetmap.org/way/140138785> .
id:cwb0519 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "train_station" ;
  cwk:levels "2"^^xsd:integer ;
  s:latitude "51.503581"^^xsd:decimal ;
  s:longitude "-0.019458"^^xsd:decimal ;
  s:name "Canary Wharf Station West Entrance" ;
  s:sameAs <https://www.openstreetmap.org/way/140132570> .
id:cwb0521 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "train_station" ;
  cwk:levels "1"^^xsd:integer ;
  s:latitude "51.503416"^^xsd:decimal ;
  s:longitude "-0.017825"^^xsd:decimal ;
  s:name "East Entrance" ;
  s:sameAs <https://www.openstreetmap.org/way/140132633> .
id:cwb0522 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "train_station" ;
  cwk:levels "1"^^xsd:integer ;
  s:latitude "51.503263"^^xsd:decimal ;
  s:longitude "-0.017085"^^xsd:decimal ;
  s:name "Fosterito Entrance" ;
  s:sameAs <https://www.openstreetmap.org/way/140235068> .
id:cwb0075 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "train_station" ;
  cwk:levels "3"^^xsd:integer ;
  s:latitude "51.509427"^^xsd:decimal ;
  s:longitude "-0.026662"^^xsd:decimal ;
  s:name "Westferry" ;
  s:sameAs <https://www.openstreetmap.org/way/543109625> .
id:cwb0806 a cwk:Building ;
  a s:Place ;
  cwk:buildingTag "roof" ;
  cwk:levels "2.5"^^xsd:decimal ;
  s:latitude "51.499979"^^xsd:decimal ;
  s:longitude "-0.016293"^^xsd:decimal ;
  s:name "South Quay DLR station" ;
  s:sameAs <https://www.openstreetmap.org/way/170221187> .`
```

Not every building has a height: Newfoundland and Landmark Pinnacle have
only a number of levels. The first pipeline reads the Turtle and runs a
CONSTRUCT node that gives every building a height: the measured value, or
3.5 metres per level, marked as an estimate.

```observable-js
heightsQuery = `PREFIX cwk: <https://kgx.foaf.tv/vocab#>
PREFIX s: <https://schema.org/>
PREFIX cw: <${CW}>
CONSTRUCT { ?b s:name ?n ; s:latitude ?lat ; s:longitude ?lon ; cwk:buildingTag ?tag ;
              cw:height ?h ; cw:heightEstimated ?est }
WHERE { ?b a cwk:Building ; s:name ?n ; s:latitude ?lat ; s:longitude ?lon
        OPTIONAL { ?b cwk:buildingTag ?tag }
        OPTIONAL { ?b cwk:heightMetres ?m }
        OPTIONAL { ?b cwk:levels ?l }
        BIND(COALESCE(?m, ?l * 3.5) AS ?h)
        BIND(!BOUND(?m) AS ?est) }`
```

```observable-js
buildingsPipeline = Factoidal.pipe(
  await Factoidal.node('turtleDocumentReader'),
  await Factoidal.node('shippedEvaluator', { query: heightsQuery }),
)
```

`pipe()` checks the types of the wires before anything runs:

```observable-js
buildingsCheck = ({ wellTyped: buildingsPipeline.wellTyped, conversions: buildingsPipeline.check.conversions })
```

```observable-js
buildingsRun = Factoidal.run(buildingsPipeline, buildingsTtl)
```

```observable-js
buildingsEvidence = pretty(buildingsRun.evidence.map((e) => ({ stage: e.stage, status: e.status, contract: e.contract })))
```

The second transformation classifies: a building of 150 metres or more is
a tower. Station buildings are not classified from kgx's `buildingTag`:
kgx tags the South Quay DLR station building `roof`, and Crossrail Place,
which holds the Elizabeth line station, `retail`. The lines table of
source 2 says which buildings are stations, and the query joins on it. This
step reads the
first CONSTRUCT's output, so the natural pipeline puts it after the first
one. The type check refuses that pipeline: the evaluator's output wire is
`Answer` for every query form, and no stage reads `Answer`, although the
answer of a CONSTRUCT is a graph
([issue 1026](https://github.com/danbri/factoidal/issues/1026)):

```observable-js
classifyQuery = `PREFIX cwk: <https://kgx.foaf.tv/vocab#>
PREFIX s: <https://schema.org/>
PREFIX cw: <${CW}>
CONSTRUCT { ?b a ?kind ; s:name ?n ; s:latitude ?lat ; s:longitude ?lon ;
              cw:height ?h ; cw:heightEstimated ?est }
WHERE { ?b s:name ?n ; s:latitude ?lat ; s:longitude ?lon
        OPTIONAL { ?b cw:height ?h ; cw:heightEstimated ?est }
        BIND(IF(?h >= 150, cw:Tower, cw:OtherBuilding) AS ?kind) }`
```

```observable-js
chainedCheck = {
  const p = Factoidal.pipe(
    await Factoidal.node('turtleDocumentReader'),
    await Factoidal.node('shippedEvaluator', { query: heightsQuery }),
    await Factoidal.node('shippedEvaluator', { query: classifyQuery }),
  );
  return ({ wellTyped: p.wellTyped, mismatch: p.check.mismatch });
}
```

So the second step runs as its own one-node pipeline on the first run's
output graph. Each run has its own evidence, and the record section below
joins them by the graph that one generated and the other used.

```observable-js
classifyRun = Factoidal.run(Factoidal.pipe(await Factoidal.node('shippedEvaluator', { query: classifyQuery })), buildingsRun.graph)
```

```observable-js
towers = {
  const ds = await Factoidal.parse('', { format: 'nquads' });
  for (const q of classifyRun.graph) ds.add(q);
  return ds.query(`PREFIX s: <https://schema.org/>
PREFIX cw: <${CW}>
SELECT ?name ?height ?estimated WHERE { ?b a cw:Tower ; s:name ?name ; cw:height ?height ; cw:heightEstimated ?estimated }
ORDER BY DESC(?height)`);
}
```

## Source 2: station lines, in CSV with CSVW metadata

One row per station building of kgx, keyed by its kgx identifier. The
Jubilee line station has three entrance buildings in kgx, and the Elizabeth
line station is inside Crossrail Place.

```observable-js
linesCsv = `kgxId,line
cwb0409,DLR
cwb0075,DLR
cwb0806,DLR
cwb0519,Jubilee
cwb0521,Jubilee
cwb0522,Jubilee
cwb0358,Elizabeth`
```

```observable-js
linesMetadata = JSON.stringify({
  '@context': 'http://www.w3.org/ns/csvw',
  url: 'station-lines.csv',
  tableSchema: {
    aboutUrl: 'https://kgx.foaf.tv/id/{kgxId}',
    columns: [
      { name: 'kgxId', titles: 'kgxId', suppressOutput: true },
      { name: 'line', titles: 'line', propertyUrl: `${CW}line`, valueUrl: `${CW}line/{line}` },
    ],
  },
})
```

The CSVW conversion is the function `csvwToRdf`. It is not a pipeline node:
the stage registry lists CSVW with status `missing` (no contract and no
test suite in the registry), so it adds no evidence record. The record
section below shows what that does to the pipeline's record.

```observable-js
fromCsvw = Factoidal.csvwToRdf(linesCsv, linesMetadata, { base: CW, mode: 'minimal' })
```

```observable-js
csvwStage = {
  const s = (await Factoidal.stages()).find((x) => x.name === 'CSVW (tabular data to RDF)');
  return ({ name: s.name, status: s.status, bound: s.bound, runnable: s.runnable });
}
```

The CSVW output goes into a one-node pipeline: a CONSTRUCT that writes
`cw:servedBy` and gives each line a label.

```observable-js
linesPipeline = Factoidal.pipe(await Factoidal.node('shippedEvaluator', { query: `PREFIX cw: <${CW}>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
CONSTRUCT { ?b cw:servedBy ?line . ?line a cw:Line ; rdfs:label ?name }
WHERE { ?b cw:line ?line BIND(STRAFTER(STR(?line), "line/") AS ?name) }` }))
```

```observable-js
linesRun = Factoidal.run(linesPipeline, fromCsvw)
```

## One dataset, one named graph per source

`Dataset` is an RDF/JS `DatasetCore`. Each pipeline's output graph goes into
a graph named after its source.

```observable-js
merged = {
  const { namedNode, quad } = Factoidal.dataFactory;
  const all = await Factoidal.parse('', { format: 'nquads' });
  for (const [name, run] of Object.entries({ buildings: classifyRun, lines: linesRun })) {
    const g = namedNode(`${CW}graph/${name}`);
    for (const q of run.graph) all.add(quad(q.subject, q.predicate, q.object, g));
  }
  return all;
}
```

```observable-js
perGraph = merged.query(`SELECT ?g (COUNT(*) AS ?triples) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g ORDER BY ?g`)
```

## The query across the graphs: towers and the lines within 300 metres

The towers and every building's position are in the buildings graph; which
buildings are stations, and of which line, is in the lines graph. The distance is the equirectangular
approximation (metres per degree: 111,320 north–south, 69,300 east–west at
latitude 51.5°), compared squared, because SPARQL 1.1 has no square root.

The query runs as a pipeline node, so the answer graph has an evidence
record. The CONSTRUCT writes the answer as triples.

```observable-js
answerRun = Factoidal.run(Factoidal.pipe(await Factoidal.node('shippedEvaluator', { query: `PREFIX s: <https://schema.org/>
PREFIX cw: <${CW}>
PREFIX g: <${CW}graph/>
CONSTRUCT { ?t cw:answerTo cw:question ; cw:lineWithin300m ?line }
WHERE {
  GRAPH g:buildings { ?t a cw:Tower ; s:latitude ?tlat ; s:longitude ?tlon .
                      ?st s:latitude ?slat ; s:longitude ?slon }
  GRAPH g:lines { ?st cw:servedBy ?line }
  BIND((?slat - ?tlat) * 111320 AS ?dy)
  BIND((?slon - ?tlon) * 69300 AS ?dx)
  FILTER(?dx * ?dx + ?dy * ?dy <= 90000)
}` })), merged)
```

The same join as a table, one row per tower, with the lines and the number
of entrance buildings in reach:

```observable-js
answer = merged.query(`PREFIX s: <https://schema.org/>
PREFIX cw: <${CW}>
PREFIX g: <${CW}graph/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?tower ?height ?estimated (GROUP_CONCAT(DISTINCT ?lineName; separator=", ") AS ?lines)
       (COUNT(DISTINCT ?st) AS ?entrances)
WHERE {
  GRAPH g:buildings { ?t a cw:Tower ; s:name ?tower ; cw:height ?height ; cw:heightEstimated ?estimated ;
                        s:latitude ?tlat ; s:longitude ?tlon .
                      ?st s:latitude ?slat ; s:longitude ?slon }
  GRAPH g:lines { ?st cw:servedBy ?line . ?line rdfs:label ?lineName }
  BIND((?slat - ?tlat) * 111320 AS ?dy)
  BIND((?slon - ?tlon) * 69300 AS ?dx)
  FILTER(?dx * ?dx + ?dy * ?dy <= 90000)
}
GROUP BY ?tower ?height ?estimated
ORDER BY DESC(?height)`)
```

Landmark Pinnacle is a tower by its estimated height, but no station
building of this extract is within 300 metres of it (Heron Quays, its
nearest DLR station, is not in the extract), so it has no row.

## The pipeline's record, as RDF

Every evidence record above is a JavaScript object. To query the record
with the data, the next cell writes it as triples in a named graph
`g:provenance`. It uses [PROV-O](https://www.w3.org/TR/prov-o/), as kgx does
for its own runs: each run is a `prov:Activity` that `prov:used` its input
and `prov:generated` its output graph, and each step has its stage
(`cwp:tool`, the kgx pipeline vocabulary), status and contract. The
Turtle source `prov:wasDerivedFrom` the kgx graph version, so the lineage
continues into kgx's own record. The cell only copies fields; the engine
does not yet give this graph itself
([issue 563](https://github.com/danbri/factoidal/issues/563), the evidence
graph profile). The CSVW call has no evidence record, so its step comes
from the registry entry above.

```observable-js
provenance = {
  const { namedNode, literal, quad } = Factoidal.dataFactory;
  const PROV = 'http://www.w3.org/ns/prov#';
  const CWP = 'https://kgx.foaf.tv/pipeline#';
  const RDF_TYPE = namedNode('http://www.w3.org/1999/02/22-rdf-syntax-ns#type');
  const XSD_INT = namedNode('http://www.w3.org/2001/XMLSchema#integer');
  const gp = namedNode(`${CW}graph/provenance`);
  const n = (local) => namedNode(CW + local);
  const ds = await Factoidal.parse('', { format: 'nquads' });
  for (const q of merged) ds.add(q);
  for (const q of answerRun.graph) ds.add(quad(q.subject, q.predicate, q.object, n('graph/answer')));
  const add = (s, p, o) => ds.add(quad(s, p, o, gp));
  add(n('source/buildings.ttl'), namedNode(PROV + 'wasDerivedFrom'), namedNode(KGX_VERSION));
  const activity = (name, used, generated, steps) => {
    const a = n(`activity/${name}`);
    add(a, RDF_TYPE, namedNode(PROV + 'Activity'));
    for (const u of used) add(a, namedNode(PROV + 'used'), u);
    add(a, namedNode(PROV + 'generated'), generated);
    steps.forEach((s, i) => {
      const step = n(`activity/${name}/step/${i}`);
      add(step, n('partOf'), a);
      add(step, n('order'), literal(String(i), XSD_INT));
      add(step, namedNode(CWP + 'tool'), literal(s.stage));
      add(step, n('status'), literal(s.status));
      if (s.contract) add(step, n('contract'), literal(s.contract));
      for (const x of s.assumptions || []) add(step, n('assumption'), literal(x));
    });
  };
  activity('heights', [n('source/buildings.ttl')], n('data/heights'), buildingsRun.evidence);
  activity('classify', [n('data/heights')], n('graph/buildings'), classifyRun.evidence);
  activity('csvw', [n('source/station-lines.csv')], n('data/csvw-output'), [{ stage: csvwStage.name, status: csvwStage.status }]);
  activity('lines', [n('data/csvw-output')], n('graph/lines'), linesRun.evidence);
  activity('answer', [n('graph/buildings'), n('graph/lines')], n('graph/answer'), answerRun.evidence);
  return ds;
}
```

Which steps made each graph, in order:

```observable-js
stepsPerGraph = provenance.query(`PREFIX cw: <${CW}>
PREFIX cwp: <https://kgx.foaf.tv/pipeline#>
PREFIX g: <${CW}graph/>
PREFIX prov: <http://www.w3.org/ns/prov#>
SELECT ?graph ?order ?stage ?status WHERE {
  GRAPH g:provenance { ?a prov:generated ?graph . ?step cw:partOf ?a ;
                       cw:order ?order ; cwp:tool ?stage ; cw:status ?status }
} ORDER BY ?graph ?order`)
```

The whole lineage of the answer graph, by following the data: the property
path `(prov:used/^prov:generated)*` walks from the activity that made a
graph to the activities that made its inputs, to any depth, and
`prov:wasDerivedFrom` names the kgx graph version at the start.

```observable-js
answerLineage = provenance.query(`PREFIX cw: <${CW}>
PREFIX cwp: <https://kgx.foaf.tv/pipeline#>
PREFIX g: <${CW}graph/>
PREFIX prov: <http://www.w3.org/ns/prov#>
SELECT ?activity ?stage ?status WHERE {
  GRAPH g:provenance {
    ?made prov:generated g:answer .
    ?made (prov:used/^prov:generated)* ?activity .
    ?step cw:partOf ?activity ; cw:order ?order ; cwp:tool ?stage ; cw:status ?status }
} ORDER BY ?activity ?order`)
```

```observable-js
answerSources = provenance.query(`PREFIX g: <${CW}graph/>
PREFIX prov: <http://www.w3.org/ns/prov#>
SELECT DISTINCT ?source ?derivedFrom WHERE {
  GRAPH g:provenance {
    ?made prov:generated g:answer .
    ?made (prov:used/^prov:generated)* ?a .
    ?a prov:used ?source FILTER NOT EXISTS { ?other prov:generated ?source }
    OPTIONAL { ?source prov:wasDerivedFrom ?derivedFrom } }
} ORDER BY ?source`)
```

For each data graph: is every step in its lineage `proved`? `NOT EXISTS`
looks for one that is not.

```observable-js
allProved = provenance.query(`PREFIX cw: <${CW}>
PREFIX g: <${CW}graph/>
PREFIX prov: <http://www.w3.org/ns/prov#>
SELECT ?graph ?allProved WHERE {
  VALUES ?graph { g:buildings g:lines g:answer }
  BIND(NOT EXISTS { GRAPH g:provenance {
    ?made prov:generated ?graph . ?made (prov:used/^prov:generated)* ?a .
    ?step cw:partOf ?a ; cw:status ?s FILTER(?s != "proved") } } AS ?allProved)
} ORDER BY ?graph`)
```

Data and record in one query: each tower in the answer, with each step
upstream of it that is not `proved`.

```observable-js
answerCaveats = provenance.query(`PREFIX cw: <${CW}>
PREFIX cwp: <https://kgx.foaf.tv/pipeline#>
PREFIX g: <${CW}graph/>
PREFIX prov: <http://www.w3.org/ns/prov#>
PREFIX s: <https://schema.org/>
SELECT DISTINCT ?tower ?stage ?status WHERE {
  GRAPH g:answer { ?t cw:answerTo cw:question }
  GRAPH g:buildings { ?t s:name ?tower }
  GRAPH g:provenance {
    ?made prov:generated g:answer . ?made (prov:used/^prov:generated)* ?a .
    ?step cw:partOf ?a ; cwp:tool ?stage ; cw:status ?status FILTER(?status != "proved") }
} ORDER BY ?tower`)
```

So the record can be followed as data: named graphs say which source a fact
came from, the provenance graph says which steps made that graph, and the
start of the chain is a kgx graph version with its own record. The same
computation is stated in Lean: the guarantee of a well-typed path is the
composition of its stages' contracts plus the union of their named
assumptions (`Dataflow.query_sound` and the source table in
[docs/2026-10-25-composition.md](https://github.com/danbri/factoidal-core/blob/main/docs/2026-10-25-composition.md)).
Two parts of it still come from the JavaScript side: this page copies the
evidence objects into triples (the engine should give that graph,
[issue 563](https://github.com/danbri/factoidal/issues/563)), and the CSVW
step has no evidence record because CSVW is not a registered stage with a
contract ([issue 975](https://github.com/danbri/factoidal/issues/975),
component contracts).

## Writing the dataset for a persistent store

The N-Quads writer node (status `proved`) writes all four named graphs:
buildings, lines, answer and provenance, with the default graph empty.

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
with its named graphs; kgx itself is served from a Shardborough store. In
@factoidal/core {{ factoidalRelease.version }} the package can open and
query an SBM11 generation (`openSbm11`), but it cannot pack one: packing
SBM11 from npm is
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

Measured 2026-10-25 with those commands on this page's N-Quads (156 quads,
7,161 bytes on disk): the store answers the query of the table above with
the same four rows, and the "data and record in one query" above with the
same four rows, both on its id path (`path=ids`).

```observable-js
sbm11PackInNpm = Object.keys(Factoidal).filter((k) => /pack/i.test(k) && /sbm11/i.test(k))
```
