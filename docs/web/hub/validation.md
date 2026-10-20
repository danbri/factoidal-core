---
title: SHACL and ShEx
description: Validate a Dataset against SHACL shapes, query the validation report as RDF, and check focus nodes against a ShEx schema.
layout: hub.njk
tests: tests/hub/hub_validation_test.mjs
---

# SHACL and ShEx

[Hub](../) · SHACL Core, SHACL-SPARQL, ShEx 2

## The data

```observable-js
people = Factoidal.parse(`@prefix ex: <http://example.org/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:age 30 ; foaf:knows ex:bob .
ex:bob a foaf:Person ; foaf:age "old" ; foaf:knows ex:carol .
ex:carol a foaf:Document .`, { format: 'turtle' })
```

## SHACL

```observable-js
shapes = `@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex: <http://example.org/> .
ex:PersonShape a sh:NodeShape ;
  sh:targetClass foaf:Person ;
  sh:property [ sh:path foaf:name ; sh:minCount 1 ; sh:datatype xsd:string ] ;
  sh:property [ sh:path foaf:age ; sh:maxCount 1 ; sh:datatype xsd:integer ] ;
  sh:property [ sh:path foaf:knows ; sh:class foaf:Person ] .`
```

`validateShacl` answers `{ conforms, report }`:

```observable-js
conforms = people.validateShacl(shapes, { format: 'turtle' }).then((r) => r.conforms)
```

The report is a `Dataset` that holds one `sh:ValidationReport`, so it can
be queried:

```observable-js
report = people.validateShacl(shapes, { format: 'turtle' }).then((r) => r.report)
```

```observable-js
violations = report.query(`PREFIX sh: <http://www.w3.org/ns/shacl#>
SELECT ?focus ?path ?component WHERE {
  ?r a sh:ValidationResult ; sh:focusNode ?focus ; sh:sourceConstraintComponent ?component .
  OPTIONAL { ?r sh:resultPath ?path }
} ORDER BY ?focus ?component`)
```

SHACL-SPARQL: a constraint written as a SPARQL SELECT query.

```observable-js
sparqlConstraint = people.validateShacl(`@prefix sh: <http://www.w3.org/ns/shacl#> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex: <http://example.org/> .
ex:NoSelfKnows a sh:NodeShape ; sh:targetClass foaf:Person ;
  sh:sparql [ sh:select """PREFIX foaf: <http://xmlns.com/foaf/0.1/>
    SELECT $this WHERE { $this foaf:knows ?other . ?other foaf:knows ?third . FILTER NOT EXISTS { ?third a foaf:Person } }""" ] .`,
  { format: 'turtle' }).then((r) => r.conforms)
```

## ShEx

A ShEx schema in the compact syntax (ShExC). `validateShex` answers
whether one focus node conforms to one shape.

```observable-js
shex = `PREFIX foaf: <http://xmlns.com/foaf/0.1/>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
PREFIX ex: <http://example.org/>
ex:Person { foaf:name xsd:string ; foaf:age xsd:integer ? ; foaf:knows @ex:Person * }`
```

```observable-js
shexResults = {
  const out = {};
  for (const who of ['alice', 'bob', 'carol']) {
    out[who] = await people.validateShex(shex, { focus: `http://example.org/${who}`, shape: 'http://example.org/Person' });
  }
  return out;
}
```

No node conforms: Bob has no `foaf:name` and his age is not an
`xsd:integer`; Carol has no name; Alice knows Bob, and `@ex:Person`
requires Bob to conform.

## Conformance

The W3C SHACL and ShEx suite scores are in the
[standards table](../#standards-support).
