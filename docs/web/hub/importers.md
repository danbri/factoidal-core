---
title: Data importers and pipelines
description: Turn CSV, JSON, JSON-LD and XHTML into RDF with CSVW, RML, JSON-LD and a GRDDL-style XSLT step, keep each step's output in its own named graph, and query across the steps.
layout: hub.njk
tests: tests/hub/hub_importers_test.mjs
---

# Data importers and pipelines

[Hub](../) · CSVW, RML, JSON-LD, GRDDL, the RDF parsers

Each importer returns a `Dataset`. This page converts four sources about
the same railway stations, writes each result into its own named graph,
and queries across the graphs. The named graph of a triple then records
which step produced it.

## Step 1: CSV with CSVW metadata

[CSV on the Web](https://www.w3.org/TR/csv2rdf/): the metadata document
names each column and how a cell becomes an RDF term.

```observable-js
stationsCsv = `id,name,opened
pad,Paddington,1854
kgx,King's Cross,1852`
```

```observable-js
stationsMetadata = JSON.stringify({
  '@context': 'http://www.w3.org/ns/csvw',
  url: 'stations.csv',
  tableSchema: {
    aboutUrl: 'http://example.org/station/{id}',
    columns: [
      { name: 'id', titles: 'id', suppressOutput: true },
      { name: 'name', titles: 'name', propertyUrl: 'http://www.w3.org/2000/01/rdf-schema#label' },
      { name: 'opened', titles: 'opened', propertyUrl: 'http://example.org/opened', datatype: 'gYear' },
    ],
  },
})
```

```observable-js
fromCsvw = Factoidal.csvwToRdf(stationsCsv, stationsMetadata, { base: 'http://example.org/', mode: 'minimal' })
```

```observable-js
pretty(fromCsvw)
```

## Step 2: JSON with an RML mapping

[RML](https://kg-construct.github.io/rml-core/spec/docs/): a triples map
iterates over the JSON with JSONPath and builds one subject per item.

```observable-js
linesJson = JSON.stringify({ lines: [
  { code: 'eli', name: 'Elizabeth line', stations: ['pad'] },
  { code: 'vic', name: 'Victoria line', stations: ['kgx'] },
] })
```

```observable-js
linesMapping = `@prefix rml: <http://w3id.org/rml/> .
@prefix ex: <http://example.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:LinesMap a rml:TriplesMap ;
  rml:logicalSource [ a rml:LogicalSource ;
    rml:iterator "$.lines[*]" ; rml:referenceFormulation rml:JSONPath ;
    rml:source [ a rml:RelativePathSource ; rml:root rml:MappingDirectory ; rml:path "lines.json" ] ] ;
  rml:subjectMap [ rml:template "http://example.org/line/{$.code}" ; rml:class ex:Line ] ;
  rml:predicateObjectMap [ rml:predicate rdfs:label ; rml:objectMap [ rml:reference "$.name" ] ] ;
  rml:predicateObjectMap [ rml:predicate ex:serves ;
    rml:objectMap [ rml:template "http://example.org/station/{$.stations[*]}" ; rml:termType rml:IRI ] ] .`
```

```observable-js
fromRml = Factoidal.rmlMap(linesMapping, linesJson, 'json')
```

```observable-js
pretty(fromRml)
```

## Step 3: JSON-LD

```observable-js
fromJsonLd = Factoidal.jsonldToRdf(JSON.stringify({
  '@context': { ex: 'http://example.org/', step: { '@id': 'ex:stepFreeAccess', '@type': 'http://www.w3.org/2001/XMLSchema#boolean' } },
  '@graph': [
    { '@id': 'ex:station/pad', step: 'true' },
    { '@id': 'ex:station/kgx', step: 'false' },
  ],
}))
```

```observable-js
pretty(fromJsonLd)
```

## Step 4: XHTML through XSLT, as GRDDL does

[GRDDL](https://www.w3.org/TR/grddl/) names an XSLT transformation in an
XHTML document and reads the RDF/XML it produces. This cell runs the two
steps of that mechanism with the package's XSLT 1.0 processor and RDF/XML
parser.

```observable-js
noticeXhtml = `<html xmlns="http://www.w3.org/1999/xhtml">
<head profile="http://www.w3.org/2003/g/data-view"><title>Notices</title></head>
<body><ul>
<li class="notice" id="pad">Lift out of service at Paddington</li>
</ul></body></html>`
```

```observable-js
noticeXslt = `<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:h="http://www.w3.org/1999/xhtml" xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
  xmlns:ex="http://example.org/">
<xsl:template match="/">
  <rdf:RDF>
    <xsl:for-each select="//h:li[@class='notice']">
      <rdf:Description rdf:about="http://example.org/station/{@id}">
        <ex:notice><xsl:value-of select="."/></ex:notice>
      </rdf:Description>
    </xsl:for-each>
  </rdf:RDF>
</xsl:template>
</xsl:stylesheet>`
```

```observable-js
fromXhtml = Factoidal.parse(await Factoidal.xsltTransform(noticeXslt, noticeXhtml), { format: 'rdfxml' })
```

```observable-js
pretty(fromXhtml)
```

## One dataset, one named graph per step

`Dataset` is an RDF/JS `DatasetCore`, so `add` puts a quad into it. Each
step's triples go into a graph named after the step.

```observable-js
pipeline = {
  const { namedNode, quad } = Factoidal.dataFactory;
  const all = await Factoidal.parse('', { format: 'nquads' });
  const steps = { csvw: fromCsvw, rml: fromRml, jsonld: fromJsonLd, grddl: fromXhtml };
  for (const [step, data] of Object.entries(steps)) {
    const g = namedNode(`http://example.org/step/${step}`);
    for (const q of data) all.add(quad(q.subject, q.predicate, q.object, g));
  }
  return all;
}
```

```observable-js
perGraph = pipeline.query(`SELECT ?g (COUNT(*) AS ?triples) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g ORDER BY ?g`)
```

```observable-js
pretty(perGraph)
```

A query that joins facts from four steps, and reports the graph of each
fact:

```observable-js
joined = pipeline.query(`PREFIX ex: <http://example.org/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?station ?line ?stepFree ?notice ?nameFrom ?lineFrom WHERE {
  GRAPH ?nameFrom { ?s rdfs:label ?station }
  GRAPH ?lineFrom { ?l ex:serves ?s ; rdfs:label ?line }
  OPTIONAL { GRAPH <http://example.org/step/jsonld> { ?s ex:stepFreeAccess ?stepFree } }
  OPTIONAL { GRAPH <http://example.org/step/grddl> { ?s ex:notice ?notice } }
} ORDER BY ?station`)
```

```observable-js
pretty(joined)
```

The whole pipeline as TriG:

```observable-js
pipeline.serialize({ format: 'trig' })
```

The [inference page](../inference/) runs RDFS and OWL reasoning over a
pipeline of this shape.

## The parsers

Every importer above ends in the same RDF dataset model as `parse`, which
reads Turtle, N-Triples, N-Quads, TriG, RDF/XML and JSON-LD, each in RDF
1.1 and RDF 1.2 forms. See [RDF syntaxes](../rdf-syntaxes/).

## Limits

- The npm package has no GRDDL processor: nothing finds the
  transformation that an XHTML profile or `grddl:transformation` names,
  or fetches it. The step above names the stylesheet by hand. GRDDL
  conformance is measured by the native runner `l4grddl` (see the
  [standards table](../#standards-support)); its open cases:
  <https://github.com/danbri/factoidal/issues/730> and
  <https://github.com/danbri/factoidal/issues/668>.
- `rmlMap` reads one logical source per call; joins across two sources
  are not supported in this entry point, and relational database sources
  are not supported: <https://github.com/danbri/factoidal/issues/707>.
- There is no option to write a producer's output straight into a named
  graph; the page copies quads with `add`.
- A remote JSON-LD `@context` is not fetched:
  <https://github.com/danbri/factoidal/issues/667>.
