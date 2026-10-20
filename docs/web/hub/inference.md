---
title: Inference
description: RDFS and OWL 2 RL closure, and OWL DL consistency and entailment, applied to the output of an import pipeline, with the derived triples kept in their own named graph.
layout: hub.njk
tests: tests/hub/hub_inference_test.mjs
---

# Inference

[Hub](../) · RDFS, OWL 2 RL, OWL 2 DL

`ds.closure(regime)` returns a new `Dataset` that holds the input and every
triple the regime derives. The regimes are `'rdfs'`, `'owl-rl'`,
`'rho-df'` (the six-rule core of RDFS) and `'rdfs-plus'`.
`Factoidal.owlIsConsistent` and `Factoidal.owlEntails` decide OWL 2 DL
questions with a tableau.

## Pipeline output

Two import steps, as on the [importers page](../importers/): a CSV file
through CSVW and a JSON file through RML. The steps go into named graphs.

```observable-js
stations = Factoidal.csvwToRdf(`id,name
pad,Paddington
kgx,King's Cross`, JSON.stringify({
  '@context': 'http://www.w3.org/ns/csvw', url: 'stations.csv',
  tableSchema: { aboutUrl: 'http://example.org/station/{id}', columns: [
    { name: 'id', titles: 'id', suppressOutput: true },
    { name: 'name', titles: 'name', propertyUrl: 'http://www.w3.org/2000/01/rdf-schema#label' } ] },
}), { mode: 'minimal' })
```

```observable-js
lines = Factoidal.rmlMap(`@prefix rml: <http://w3id.org/rml/> .
@prefix ex: <http://example.org/> .
ex:M a rml:TriplesMap ;
  rml:logicalSource [ a rml:LogicalSource ; rml:iterator "$[*]" ; rml:referenceFormulation rml:JSONPath ;
    rml:source [ a rml:RelativePathSource ; rml:root rml:MappingDirectory ; rml:path "lines.json" ] ] ;
  rml:subjectMap [ rml:template "http://example.org/line/{$.code}" ] ;
  rml:predicateObjectMap [ rml:predicate ex:serves ;
    rml:objectMap [ rml:template "http://example.org/station/{$.at}" ; rml:termType rml:IRI ] ] .`,
  JSON.stringify([{ code: 'eli', at: 'pad' }, { code: 'vic', at: 'kgx' }]), 'json')
```

The vocabulary, also a step of its own:

```observable-js
ontology = Factoidal.parse(`@prefix ex: <http://example.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
ex:serves rdfs:domain ex:Line ; rdfs:range ex:Station .
ex:Station rdfs:subClassOf ex:Place .
ex:servedBy owl:inverseOf ex:serves .
ex:Line owl:disjointWith ex:Place .`, { format: 'turtle' })
```

```observable-js
pipeline = {
  const { namedNode, quad } = Factoidal.dataFactory;
  const all = await Factoidal.parse('', { format: 'nquads' });
  for (const [step, data] of Object.entries({ csvw: stations, rml: lines, vocabulary: ontology })) {
    const g = namedNode(`http://example.org/step/${step}`);
    for (const q of data) all.add(quad(q.subject, q.predicate, q.object, g));
  }
  return all;
}
```

The closures read the default graph, so the next cell merges the step
graphs into one default graph:

```observable-js
merged = pipeline.query('CONSTRUCT { ?s ?p ?o } WHERE { GRAPH ?g { ?s ?p ?o } }')
```

## RDFS closure

```observable-js
rdfs = merged.closure('rdfs')
```

```observable-js
rdfsTypes = rdfs.query(`PREFIX ex: <http://example.org/>
SELECT ?thing ?type WHERE { ?thing a ?type . FILTER(STRSTARTS(STR(?type), STR(ex:))) } ORDER BY ?thing ?type`)
```

```observable-js
pretty(rdfsTypes)
```

## OWL 2 RL closure

`owl:inverseOf` is outside RDFS. The OWL 2 RL closure derives the
`ex:servedBy` triples:

```observable-js
owlRl = merged.closure('owl-rl')
```

```observable-js
servedBy = owlRl.query(`PREFIX ex: <http://example.org/>
SELECT ?station ?line WHERE { ?station ex:servedBy ?line } ORDER BY ?station`)
```

```observable-js
pretty(servedBy)
```

A query can also ask for the closure itself, with the `entail` option:

```observable-js
entailedAsk = merged.query('ASK { <http://example.org/station/pad> a <http://example.org/Place> }', { entail: 'RDFS' })
```

## The derived triples in their own named graph

Every triple of the OWL 2 RL closure that is not in the input, and whose
terms are IRIs or literals, goes into the graph `step/owl-rl`, so a query
can tell asserted facts from derived facts.

```observable-js
withInferences = {
  const { namedNode, quad } = Factoidal.dataFactory;
  const out = pipeline.clone();
  const g = namedNode('http://example.org/step/owl-rl');
  const key = (q) => [q.subject, q.predicate, q.object].map((t) => `${t.termType}:${t.value}`).join(' ');
  const asserted = new Set(merged.toArray().map(key));
  for (const q of owlRl) {
    const named = [q.subject, q.object].every((t) => t.termType !== 'BlankNode');
    if (named && !asserted.has(key(q))) out.add(quad(q.subject, q.predicate, q.object, g));
  }
  return out;
}
```

```observable-js
padFacts = withInferences.query(`PREFIX ex: <http://example.org/>
SELECT ?p ?o ?g WHERE { GRAPH ?g { <http://example.org/station/pad> ?p ?o } } ORDER BY ?g ?p ?o`)
```

```observable-js
pretty(padFacts)
```

## OWL 2 DL: consistency and entailment

`owlIsConsistent` answers `true`, `false` or `null` (the tableau ran out
of its step budget, with a `reason`). The pipeline is consistent:

```observable-js
consistent = Factoidal.owlIsConsistent(merged)
```

A source that types a line as a station contradicts
`ex:Line owl:disjointWith ex:Place`, through the range and subclass axioms:

```observable-js
inconsistent = {
  const bad = merged.clone();
  await bad.update('INSERT DATA { <http://example.org/line/eli> a <http://example.org/Station> }');
  return Factoidal.owlIsConsistent(bad);
}
```

`owlEntails` decides an entailment that needs an OWL class expression,
here an existential restriction (`owl:someValuesFrom`), which the OWL 2 RL
rules do not derive on the left-hand side of a subclass axiom:

```observable-js
entails = Factoidal.owlEntails(`@prefix ex: <http://example.org/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
[ a owl:Restriction ; owl:onProperty ex:serves ; owl:someValuesFrom ex:Station ] rdfs:subClassOf ex:RailLine .
ex:eli ex:serves ex:pad . ex:pad a ex:Station .`,
`@prefix ex: <http://example.org/> . ex:eli a ex:RailLine .`, { format: 'turtle' })
```

## Limits

- The OWL DL functions (`owlIsConsistent`, `owlEntails`) and RDFC-1.0
  refuse a dataset with an RDF 1.2 triple term (the closures accept it):
  <https://github.com/danbri/factoidal/issues/873>. Expected-failure test:
  `tests/hub/hub_inference_test.mjs`.
- The closures and the OWL DL functions read the default graph only.
- There is no OWL 2 EL, QL or RL profile checker:
  <https://github.com/danbri/factoidal/issues/773>.
- Some OWL DL refutations cannot yet be certified (datatypes, counting,
  nominals): <https://github.com/danbri/factoidal/issues/764>. The OWL
  scores are in the [standards table](../#standards-support).
