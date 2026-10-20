---
title: SPARQL
description: SPARQL 1.1 and 1.2 query and update over a Dataset, with GeoSPARQL functions, text:query, extension functions written in JavaScript or WebAssembly, and SERVICE.
layout: hub.njk
tests: tests/hub/hub_sparql_test.mjs
---

# SPARQL

[Hub](../) · SPARQL 1.1, SPARQL 1.2, GeoSPARQL, text search, extension functions, SERVICE

`ds.query(text)` answers a SELECT with an array of `Map`s (variable name
to RDF/JS term), an ASK with a boolean, and a CONSTRUCT or DESCRIBE with a
new `Dataset`. `ds.update(text)` applies SPARQL 1.1 Update in place.

## The data

```observable-js
places = Factoidal.parse(`@prefix ex: <http://example.org/> .
@prefix geo: <http://www.opengis.net/ont/geosparql#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:park a ex:Place ; rdfs:label "Hyde Park, a large royal park" ;
  geo:hasGeometry [ geo:asWKT "POLYGON((0 0, 4 0, 4 3, 0 3, 0 0))"^^geo:wktLiteral ] .
ex:cafe a ex:Place ; rdfs:label "Serpentine cafe by the lake" ; ex:partOf ex:park ;
  geo:hasGeometry [ geo:asWKT "POINT(1 1)"^^geo:wktLiteral ] .
ex:station a ex:Place ; rdfs:label "Paddington station" ;
  geo:hasGeometry [ geo:asWKT "POINT(7 5)"^^geo:wktLiteral ] .
ex:kiosk a ex:Place ; rdfs:label "Kiosk" ; ex:partOf ex:cafe .`, { format: 'turtle' })
```

## SELECT, property paths, aggregates

```observable-js
partOf = places.query(`PREFIX ex: <http://example.org/>
SELECT ?part ?whole WHERE { ?part ex:partOf+ ?whole } ORDER BY ?part ?whole`)
```

```observable-js
counted = places.query(`PREFIX ex: <http://example.org/>
SELECT ?whole (COUNT(?part) AS ?n) WHERE { ?part ex:partOf+ ?whole } GROUP BY ?whole ORDER BY DESC(?n)`)
```

A result can also come back as a SPARQL results document:

```observable-js
return places.query('SELECT ?s WHERE { ?s a <http://example.org/Place> } ORDER BY ?s LIMIT 2', { output: 'csv' })
```

## ASK, CONSTRUCT and Update

```observable-js
hasKiosk = places.query('ASK { <http://example.org/kiosk> <http://example.org/partOf> ?x }')
```

```observable-js
constructed = places.query(`PREFIX ex: <http://example.org/>
CONSTRUCT { ?whole ex:hasPart ?part } WHERE { ?part ex:partOf ?whole }`)
```

`update` changes the dataset in place, so this cell works on a copy:

```observable-js
updated = {
  const copy = places.clone();
  await copy.update(`PREFIX ex: <http://example.org/>
DELETE { ?k ex:partOf ?c } INSERT { ?k ex:partOf ex:park } WHERE { ?k ex:partOf ?c . FILTER(?k = ex:kiosk) }`);
  const rows = await copy.query('SELECT ?w WHERE { <http://example.org/kiosk> <http://example.org/partOf> ?w }');
  return rows.map((r) => r.get('w').value);
}
```

## GeoSPARQL functions

`geof:sfWithin`, `geof:sfIntersects`, `geof:distance` and the other
Simple Features functions are evaluated over WKT literals with exact
rational arithmetic.

```observable-js
inPark = places.query(`PREFIX geo: <http://www.opengis.net/ont/geosparql#>
PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
PREFIX ex: <http://example.org/>
SELECT ?place ?inside ?distance WHERE {
  ex:park geo:hasGeometry/geo:asWKT ?area .
  ?place geo:hasGeometry/geo:asWKT ?wkt .
  FILTER(?place != ex:park)
  BIND(geof:sfWithin(?wkt, ?area) AS ?inside)
  BIND(geof:distance(?wkt, "POINT(4 3)"^^geo:wktLiteral) AS ?distance)
} ORDER BY ?place`)
```

## Text search with text:query

The `text:query` property function of Apache Jena text search matches
literals that hold every token of the search string.

```observable-js
textHits = places.query(`PREFIX text: <http://jena.apache.org/text#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?s ?label WHERE { ?s text:query (rdfs:label "park") ; rdfs:label ?label } ORDER BY ?s`)
```

## Extension functions in JavaScript and WebAssembly

A function registered by IRI (SPARQL 1.1 section 17.6) can be called from
any expression. This one is JavaScript:

```observable-js
jsFunction = {
  await Factoidal.registerExtensionFunction('http://example.org/fn/initials',
    ([label]) => label.value.split(/\s+/).map((w) => w[0]).join(''));
  return places.query(`PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?label (<http://example.org/fn/initials>(?label) AS ?initials)
WHERE { ?s rdfs:label ?label } ORDER BY ?label`);
}
```

This one calls a WebAssembly module. The 41 bytes below are a complete
module that exports `add(i32, i32) -> i32`:

```observable-js
wasmAdd = {
  const bytes = new Uint8Array([0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 127, 127, 1, 127,
    3, 2, 1, 0, 7, 7, 1, 3, 97, 100, 100, 0, 0, 10, 9, 1, 7, 0, 32, 0, 32, 1, 106, 11]);
  const { instance } = await WebAssembly.instantiate(bytes);
  await Factoidal.registerExtensionFunction('http://example.org/fn/add',
    ([a, b]) => instance.exports.add(Number(a.value), Number(b.value)));
  const rows = await places.query('SELECT (<http://example.org/fn/add>(40, 2) AS ?sum) WHERE { }');
  return rows[0].get('sum').value;
}
```

## SERVICE

`registerServiceEndpoint` binds an endpoint IRI to a dataset in the page.
A `SERVICE` clause naming that IRI is answered from it. A `SERVICE` IRI
with no registration answers no solutions; the page makes no network
request.

```observable-js
federated = {
  const timetable = await Factoidal.parse(`@prefix ex: <http://example.org/> .
ex:station ex:trainsPerHour 24 .`, { format: 'turtle' });
  await Factoidal.registerServiceEndpoint('http://example.org/timetable/sparql', timetable);
  return places.query(`PREFIX ex: <http://example.org/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?label ?perHour WHERE {
  ?s rdfs:label ?label .
  SERVICE <http://example.org/timetable/sparql> { ?s ex:trainsPerHour ?perHour }
}`);
}
```

## SPARQL 1.2: triple terms, reifiers, annotations

The SPARQL 1.2 grammar is read when the call passes `sparql12: true`.

```observable-js
claims = Factoidal.parse(`VERSION "1.2"
@prefix ex: <http://example.org/> .
ex:alice ex:said <<( ex:bob ex:likes ex:tea )>> .
ex:carol ex:said <<( ex:bob ex:likes ex:coffee )>> .
ex:bob ex:likes ex:tea ~ ex:claim1 {| ex:source ex:diary |} .`, { format: 'turtle12' })
```

```observable-js
whoSaidWhat = claims.query(`PREFIX ex: <http://example.org/>
SELECT ?who ?drink WHERE { ?who ex:said <<( ex:bob ex:likes ?drink )>> } ORDER BY ?who`, { sparql12: true })
```

```observable-js
tripleFunctions = claims.query(`PREFIX ex: <http://example.org/>
SELECT ?t (isTRIPLE(?t) AS ?isTriple) (SUBJECT(?t) AS ?s) (OBJECT(?t) AS ?o)
WHERE { ex:alice ex:said ?t }`, { sparql12: true })
```

A reifier (`~`) and an annotation block (`{| |}`) in a query pattern:

```observable-js
annotations = claims.query(`PREFIX ex: <http://example.org/>
SELECT ?reifier ?source WHERE { ex:bob ex:likes ex:tea ~ ?reifier {| ex:source ?source |} }`, { sparql12: true })
```

## Limits

- `geof:distance` computes the Euclidean distance in the units of the
  coordinates; it has no geodesic distance in metres for CRS84 points:
  <https://github.com/danbri/factoidal/issues/772>. Expected-failure test:
  `tests/hub/hub_sparql_test.mjs`.
- `SERVICE` in the npm package reaches only endpoints registered in the
  page. The SPARQL client for remote endpoints is in the
  [servers](../servers/) page's command-line tools.
