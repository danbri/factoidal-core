---
title: RDF 1.2 use cases in JSON-LD-star
description: Provenance, time-bound facts with several occurrences, edge properties, claims that are not asserted, one reifier for several triples, and annotations on annotations — each written in JSON-LD-star, read as RDF 1.2 and queried with SPARQL 1.2 annotation syntax.
layout: hub.njk
tests: tests/hub/hub_rdf12-jsonld-usecases_test.mjs
---

# RDF 1.2 use cases in JSON-LD-star

[Hub](../) · [JSON-LD-star and JSON-LD 1.3](../jsonld-star/) · statements about statements

RDF 1.2 gives three ways to say something about a triple:

| RDF 1.2 | What it is | Asserted? | JSON-LD-star | Turtle 1.2 |
|---|---|---|---|---|
| triple term | the triple itself, as a value; the same subject, predicate and object give the same term | no | `{"@triple": node}` | `<<( s p o )>>` |
| reifier | a resource that `rdf:reifies` a triple term: one occurrence, claim, event or source of it | no | `{"@id": r, "@reifies": node}` | `<< s p o ~ r >>` |
| annotation | the asserted triple and a reifier of it, in one step | yes | `"p": {"@id": o, "@annotation": {...}}` | `s p o ~ r {\| ... \|}` |

A triple term is the statement; a reifier is something that has that
statement as its content. One triple term can have many reifiers, and one
reifier can reify many triple terms (RDF 1.2 Concepts, section 3.8,
"Triple Terms and Reification"). The keywords and the options are on the
[JSON-LD-star page](../jsonld-star/). This page shows the use cases with one
document and runs every query on it.

JSON-LD-star is a draft (https://github.com/json-ld/json-ld-star/pull/61),
read and written by Factoidal with the option `rdfstar` (`@factoidal/core`
0.18.0 and later). Its syntax can change.

## One document, six use cases

```observable-js
ctx = ({ '@vocab': 'http://example.org/', ex: 'http://example.org/',
         xsd: 'http://www.w3.org/2001/XMLSchema#' })
```

```observable-js
doc = JSON.stringify({ '@context': ctx, '@graph': [
  // 1. Provenance: where an asserted value comes from, and when that source was read.
  { '@id': 'ex:bob', age: { '@value': 23, '@annotation': { '@id': 'ex:claim1',
      source: { '@id': 'ex:census', '@annotation': { retrieved: { '@value': '2026-10-27', '@type': 'xsd:date' } } } } } },
  // 2. One fact, two occurrences, each with its own time.
  { '@id': 'ex:liz', spouse: { '@id': 'ex:richard', '@annotation': [
      { '@id': 'ex:m1', start: { '@value': '1964', '@type': 'xsd:gYear' }, end: { '@value': '1974', '@type': 'xsd:gYear' } },
      { '@id': 'ex:m2', start: { '@value': '1975', '@type': 'xsd:gYear' }, end: { '@value': '1976', '@type': 'xsd:gYear' } } ] } },
  // 3. Edge properties, as in a property graph; the reifier is a blank node.
  { '@id': 'ex:alice', knows: { '@id': 'ex:bob', '@annotation': { since: 2019, weight: 0.8 } } },
  // 4a. A claim that is not asserted, and who made it.
  { '@id': 'ex:claim2', '@reifies': { '@id': 'ex:bob', likes: { '@id': 'ex:coffee' } }, claimedBy: { '@id': 'ex:carol' } },
  // 4b. A statement as the object of another statement (a quotation).
  { '@id': 'ex:dave', said: { '@triple': { '@id': 'ex:bob', likes: { '@id': 'ex:tea' } } } },
  // 5. One reifier for two triples: one observation event.
  { '@id': 'ex:obs1', '@reifies': [ { '@id': 'ex:sensor', temp: 21 }, { '@id': 'ex:sensor', humidity: 40 } ],
    at: { '@value': '2026-10-27T10:00:00Z', '@type': 'xsd:dateTime' } },
]}, null, 2)
```

```observable-js
ds = Factoidal.jsonldToRdf(doc, { rdfstar: true })
```

The RDF 1.2 dataset, in N-Quads 1.2:

```observable-js
nquads = ds.serialize({ format: 'nquads' })
```

A helper for the queries below: SPARQL 1.2 (option `sparql12`), each row as
plain values.

```observable-js
select = async (data, q) => (await data.query(`PREFIX ex: <http://example.org/>
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
${q}`, { sparql12: true })).map((row) => Object.fromEntries([...row.keys()].map((v) => [v, row.get(v).value])))
```

## 1. Provenance of a value

`ex:bob ex:age 23` is asserted. Its reifier `ex:claim1` names the source,
and the triple `ex:claim1 ex:source ex:census` has its own annotation: the
date the census was read (an annotation on an annotation). SPARQL 1.2 reads
both levels with the same `{| ... |}` syntax as Turtle 1.2:

```observable-js
provenance = select(ds, `SELECT ?age ?src ?when WHERE {
  ex:bob ex:age ?age {| ex:source ?src {| ex:retrieved ?when |} |} }`)
```

## 2. One fact, many occurrences

`ex:liz ex:spouse ex:richard` is one triple, asserted once (an RDF graph is
a set). The two marriages are two reifiers of the same triple term, each
with its own start and end. Without reifiers the two date ranges could not
be told apart. `~ ?m` binds the reifier:

```observable-js
marriages = select(ds, `SELECT ?m ?start ?end WHERE {
  ex:liz ex:spouse ex:richard ~ ?m {| ex:start ?start ; ex:end ?end |} } ORDER BY ?start`)
```

```observable-js
counts = select(ds, `SELECT (COUNT(*) AS ?asserted) (SUM(?n) AS ?reifiers) WHERE {
  ex:liz ex:spouse ex:richard .
  { SELECT (COUNT(?r) AS ?n) WHERE { ?r rdf:reifies <<( ex:liz ex:spouse ex:richard )>> } } }`)
```

## 3. Edge properties

A property graph keeps properties on an edge. In RDF 1.2 the edge is the
asserted triple and its properties go on a reifier. With no `@id` in the
`@annotation`, the reifier is a new blank node. The JSON number `0.8` is an
`xsd:double` (JSON-LD 1.1 Processing Algorithms, "Object to RDF
Conversion"); write `{"@value": "0.8", "@type": "xsd:decimal"}` for a
decimal.

```observable-js
edge = select(ds, `SELECT ?since ?weight WHERE {
  ex:alice ex:knows ex:bob {| ex:since ?since ; ex:weight ?weight |} }`)
```

## 4. Statements that are not asserted

`@reifies` and `@triple` do not assert the triple. Carol claims that Bob
likes coffee, and Dave said that Bob likes tea; neither triple is in the
graph:

```observable-js
claims = ({
  claimedBy: await select(ds, `SELECT ?who WHERE { ?c rdf:reifies <<( ex:bob ex:likes ex:coffee )>> ; ex:claimedBy ?who }`),
  said: await select(ds, `SELECT ?who ?what WHERE { ?who ex:said <<( ex:bob ex:likes ?what )>> }`),
  coffeeAsserted: await ds.query('ASK { <http://example.org/bob> <http://example.org/likes> <http://example.org/coffee> }'),
  teaAsserted: await ds.query('ASK { <http://example.org/bob> <http://example.org/likes> <http://example.org/tea> }'),
})
```

Use `@reifies` when the statement has properties of its own (who claims
it, when, how sure); use `@triple` when the statement is a value of another
property, as in `ex:said`.

## 5. One reifier for several triples

An observation gives two values at one time. `ex:obs1` reifies both triple
terms, so the time is said once:

```observable-js
observation = select(ds, `SELECT ?p ?o ?at WHERE {
  ex:obs1 rdf:reifies <<( ex:sensor ?p ?o )>> ; ex:at ?at } ORDER BY ?p`)
```

## 6. Back to JSON-LD-star

The writer gives `@annotation` for a reifier of an asserted triple and
`@reifies` for the others. Here is the JSON-LD for the marriages:

```observable-js
written = {
  const nodes = JSON.parse(await ds.serialize({ format: 'jsonld', rdfstar: true }));
  return nodes.find((n) => n['@id'] === 'http://example.org/liz');
}
```

When a reifier is itself annotated (`ex:claim1` in use case 1), the writer
gives it as a node with `@reifies` and puts the nested annotation on its
property; the RDF is the same.

## Meaning: a triple term names the statement, through its IRIs

RDF 1.2 Semantics interprets the IRIs in a triple term as it interprets them
anywhere else. If `ex:bob owl:sameAs ex:robert`, then Dave also said that
Robert likes tea. The OWL 2 RL closure gives that triple
(https://github.com/danbri/factoidal/issues/873, the W3C test
`opaque-iri`):

```observable-js
sameAs = {
  const data = await Factoidal.parse(`VERSION "1.2"
PREFIX ex: <http://example.org/>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
ex:dave ex:said <<( ex:bob ex:likes ex:tea )>> .
ex:bob owl:sameAs ex:robert .`, { format: 'turtle12' });
  const closed = await data.closure('owl-rl');
  return select(closed, 'SELECT ?who WHERE { ?who ex:said <<( ex:robert ex:likes ex:tea )>> }');
}
```

A reifier is a resource, so two reifiers of one triple term are not the same
resource unless something says so (use case 2). A triple term entails
nothing about the asserted graph: `rdf:reifies` does not assert its object
(use case 4).

## Limits

* JSON-LD-star is a draft; Factoidal follows RDF 1.2 where the draft and
  RDF 1.2 Turtle disagree. The choices are listed on the
  [JSON-LD-star page](../jsonld-star/).
* `entail` with `sparql12` in one `query` call needs a release after 0.20.0
  (https://github.com/danbri/factoidal/issues/1109). With 0.19.0 and 0.20.0,
  take the closure first (as above), then query it.