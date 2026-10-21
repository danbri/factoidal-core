---
title: RDF syntaxes
description: Read and write Turtle, N-Triples, N-Quads, TriG, RDF/XML and JSON-LD, in RDF 1.1 and RDF 1.2, with one Dataset that stays inside the engine.
layout: hub.njk
tests: tests/hub/hub_rdf_syntaxes_test.mjs
---

# RDF syntaxes

[Hub](../) · RDF 1.1 and RDF 1.2 concrete syntaxes

`Factoidal.parse(text, options)` reads one document into a `Dataset`.
The parsed dataset stays in the WebAssembly memory of the engine. Each
method call (`serialize`, `query`, `canonicalize`) sends the handle of the
dataset, not the data.

Conformance of each syntax: see the [standards table](../#standards-support).

## Read a Turtle document

```observable-js
turtle = `@prefix ex: <http://example.org/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
ex:bob a foaf:Person ; foaf:name "Bob"@en .`
```

```observable-js
ds = Factoidal.parse(turtle, { format: 'turtle' })
```

```observable-js
summary = ({ quads: ds.size, format: ds.format, prefixes: ds.prefixes })
```

## Write it in each syntax

```observable-js
written = {
  const out = {};
  for (const format of ['ntriples', 'nquads', 'turtle', 'trig', 'rdfxml', 'jsonld']) {
    out[format] = await ds.serialize({ format });
  }
  return out;
}
```

```observable-js
return written.rdfxml
```

Read the RDF/XML back and compare the two datasets by their RDFC-1.0
canonical form:

```observable-js
sameAfterRdfXml = {
  const back = await Factoidal.parse(written.rdfxml, { format: 'rdfxml' });
  return (await back.canonicalize()) === (await ds.canonicalize());
}
```

```observable-js
sameAfterJsonLd = {
  const back = await Factoidal.parse(written.jsonld, { format: 'jsonld' });
  return (await back.canonicalize()) === (await ds.canonicalize());
}
```

## A syntax error has a position

Parsing is strict by default. The error is a `FactoidalError` with a code,
a position (line and column) and the grammar section it breaks.

```observable-js
syntaxError = {
  try {
    await Factoidal.parse('@prefix ex: <http://example.org/> .\nex:a ex:b .', { format: 'turtle' });
    return 'accepted';
  } catch (e) {
    return ({ name: e.name, code: e.code, line: e.position.line, column: e.position.column, spec: e.spec });
  }
}
```

With `lenient: true` the parser skips each bad statement, keeps the
good ones, and records one diagnostic per skipped statement:

```observable-js
lenient = {
  const d = await Factoidal.parse('<http://e/a> <http://e/p> 1 .\n<http://e/b> <http://e/p> .\n<http://e/c> <http://e/p> 3 .',
    { format: 'turtle', lenient: true });
  return ({ quads: d.size, diagnostics: d.diagnostics.map((x) => `${x.line}:${x.column} ${x.class}`) });
}
```

## RDF 1.2: triple terms, reifiers, annotations, base direction

The `*12` format names read the RDF 1.2 grammar. The RDF 1.1 names
refuse RDF 1.2 syntax.

```observable-js
turtle12 = `VERSION "1.2"
@prefix ex: <http://example.org/> .
ex:alice ex:said <<( ex:bob ex:likes ex:tea )>> .
ex:bob ex:likes ex:tea ~ ex:claim1 {| ex:source ex:diary |} .
ex:note ex:text "hello"@en--ltr .`
```

```observable-js
ds12 = Factoidal.parse(turtle12, { format: 'turtle12' })
```

```observable-js
return ds12.serialize({ format: 'nquads' })
```

```observable-js
refusedAs11 = {
  try {
    await Factoidal.parse(turtle12, { format: 'turtle' });
    return 'accepted';
  } catch (e) {
    return e.message.slice(0, 120);
  }
}
```

## What each writer supports

```observable-js
formatTable = Factoidal.formats()
```

## Limits

- No HDT, N3 or RDFa writer, and no RDF 1.2 output in RDF/XML or JSON-LD:
  <https://github.com/danbri/factoidal/issues/883>. Expected-failure test:
  `tests/hub/hub_rdf_syntaxes_test.mjs`.
- The npm package has no RDF/JS stream interfaces (parser and serializer
  streams); a document is read and written whole:
  <https://github.com/danbri/factoidal/issues/884>.
- RDFC-1.0 canonicalisation refuses a dataset with a triple term:
  <https://github.com/danbri/factoidal/issues/873>. See
  [canonical form and credentials](../canonical-and-credentials/).
