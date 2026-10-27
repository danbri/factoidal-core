---
title: JSON-LD-star and JSON-LD 1.3
description: RDF 1.2 triple terms, reifiers, annotations and base direction in JSON-LD, with the option rdfstar; what Factoidal implements of the JSON-LD-star draft and the plan towards JSON-LD 1.3.
layout: hub.njk
tests: tests/hub/hub_jsonld-star_test.mjs
---

# JSON-LD-star and JSON-LD 1.3

[Hub](../) · RDF 1.2 in JSON-LD

RDF 1.2 adds triple terms, reifiers, annotations and base direction to RDF.
JSON-LD 1.1 has no form for them. JSON-LD-star is the draft that adds three
keywords: `@triple`, `@reifies` and `@annotation`. Factoidal reads and writes
them since `@factoidal/core` 0.18.0, with the option `rdfstar`.

The draft is not a W3C specification. It is a set of tests
(https://github.com/json-ld/json-ld-star/pull/61, branch `1.2-tests`) and an
outline of the algorithm changes. Its syntax can change (see "Towards
JSON-LD 1.3" below). Without `rdfstar`, Factoidal
is a JSON-LD 1.1 processor, as before.

## The keywords

| JSON-LD-star | RDF 1.2 | Example |
|---|---|---|
| `{"@triple": node}` | a triple term; `node` must give exactly one triple | `{"@triple": {"@id": "ex:bob", "ex:likes": {"@id": "ex:tea"}}}` |
| `"@reifies": node` on a node object | `rdf:reifies` from the node to the triple term of each triple that `node` gives | `{"@id": "ex:claim1", "@reifies": {...}}` |
| `"@annotation": node` on a property value | a reifier of the asserted triple that the value makes; the reifier is the annotation's `@id`, or a new blank node | `"ex:likes": {"@id": "ex:tea", "@annotation": {"ex:source": ...}}` |
| `"@direction"` with `@language` | an `rdf:dirLangString` literal (`rdfDirection: "rdf-1.2"`, the default under `rdfstar`) | `{"@value": "hello", "@language": "en", "@direction": "ltr"}` |

## From Turtle 1.2 to JSON-LD-star

The same RDF 1.2 data as on the [RDF syntaxes](../rdf-syntaxes/) page: a
triple term, an annotation with a reifier `ex:claim1`, and a directional
language string.

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

With `rdfstar`, the JSON-LD writer gives the triple term as `@triple`, the
reifier of the asserted triple as `@annotation`, and the base direction as
`@direction`:

```observable-js
starJson = JSON.parse(await ds12.serialize({ format: 'jsonld', rdfstar: true }))
```

Without `rdfstar`, the writer refuses the triple term (JSON-LD 1.1 has no
form for it):

```observable-js
refusedWithout = {
  try {
    await ds12.serialize({ format: 'jsonld' });
    return 'accepted';
  } catch (e) {
    return e.code;
  }
}
```

## From JSON-LD-star to RDF

`jsonldToRdf(text, { rdfstar: true })` reads the three keywords. This
document uses each of them, with a context:

```observable-js
starDoc = JSON.stringify({
  '@context': { '@vocab': 'http://example.org/', ex: 'http://example.org/' },
  '@graph': [
    { '@id': 'ex:alice', said: { '@triple': { '@id': 'ex:bob', likes: { '@id': 'ex:tea' } } } },
    { '@id': 'ex:bob', likes: { '@id': 'ex:tea', '@annotation': { '@id': 'ex:claim1', source: { '@id': 'ex:diary' } } } },
    { '@id': 'ex:claim2', '@reifies': { '@id': 'ex:bob', likes: { '@id': 'ex:coffee' } }, source: { '@id': 'ex:rumour' } },
  ],
}, null, 2)
```

```observable-js
fromStar = Factoidal.jsonldToRdf(starDoc, { rdfstar: true })
```

```observable-js
return fromStar.serialize({ format: 'nquads' })
```

The `@annotation` gives both the asserted triple and its reifier. The
`@reifies` gives only the reifier: `ex:bob ex:likes ex:coffee` is not
asserted.

## Query it with SPARQL 1.2

A triple term in a SPARQL 1.2 pattern matches the reified triple (the
option `sparql12` selects the SPARQL 1.2 grammar):

```observable-js
sources = {
  const rows = await fromStar.query(`PREFIX ex: <http://example.org/>
    SELECT ?o ?source WHERE {
      ?r <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( ex:bob ex:likes ?o )>> ;
         ex:source ?source .
    } ORDER BY ?o`, { sparql12: true });
  return rows.map((row) => `${row.get('o').value} from ${row.get('source').value}`);
}
```

## A round trip

Turtle 1.2 to JSON-LD-star and back gives the same dataset. The data has no
blank nodes, so equal sorted N-Quads mean equal datasets. (RDFC-1.0, the
usual check, has no canonical form for triple terms:
https://github.com/danbri/factoidal/issues/873.)

```observable-js
roundTrip = {
  const back = await Factoidal.jsonldToRdf(await ds12.serialize({ format: 'jsonld', rdfstar: true }), { rdfstar: true });
  const lines = async (d) => (await d.serialize({ format: 'nquads' })).trim().split('\n').sort();
  const [a, b] = [await lines(ds12), await lines(back)];
  return { quads: a.length, same: a.join('\n') === b.join('\n') };
}
```

The same check runs in Lean over every positive evaluation test of the W3C
RDF 1.2 N-Triples, N-Quads, Turtle and TriG suites (`l4sbm11-w3c
jsonld-star-roundtrip`): 140 of 140 datasets, and 79 of 79 positive syntax
tests, are isomorphic after the round trip.

## Base direction

Under `rdfstar` the JSON-LD `@direction` maps to RDF 1.2 `rdf:dirLangString`
(`rdfDirection: "rdf-1.2"`, proposed for JSON-LD 1.2 in
https://github.com/w3c/json-ld-syntax/issues/488). Without it, JSON-LD 1.1
keeps its own modes (`i18n-datatype`, `compound-literal`) and the default
drops the direction (https://github.com/danbri/factoidal/issues/984).

```observable-js
direction = {
  const doc = JSON.stringify({ '@id': 'http://example.org/note',
    'http://example.org/text': { '@value': 'مرحبا', '@language': 'ar', '@direction': 'rtl' } });
  const star = await Factoidal.jsonldToRdf(doc, { rdfstar: true });
  const plain = await Factoidal.jsonldToRdf(doc);
  return { rdfstar: (await star.serialize({ format: 'nquads' })).trim(),
           jsonld11: (await plain.serialize({ format: 'nquads' })).trim() };
}
```

## Choices where the draft is silent or old

The owner's rule (2026-10-27): "Go for whatever is closer to RDF 1.2
direction." RDF 1.2 Turtle is the reference: in `s p o ~ r {| ... |}` the
reifier `r` can be an IRI or a blank node, and other triples can refer to it.

1. An `@annotation` can have an IRI `@id`: the reifier. Two draft fixtures
   (expand and toRdf `tst23`) keep the older rule that makes this an error;
   they are counted as local overrides, not passes.
2. Writing JSON-LD-star, every reifier of an asserted triple becomes an
   `@annotation`, IRI or blank node, referenced elsewhere or not.
3. `rdfDirection: "rdf-1.2"` is the default under `rdfstar`.

Record: [`docs/designissues/2026-10-26-jsonld-star.md`](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-10-26-jsonld-star.md).

## Conformance

| Suite | Result |
|---|---|
| JSON-LD-star draft tests (json-ld-star PR 61, `l4jsonld-api --star`) | 168 pass, 1 fail, 2 local override (out of 171): expand 46 + 1, toRdf 46 + 1, fromRdf 20 of 21, compact 17 of 17, flatten 39 of 39 |
| W3C JSON-LD 1.1 API (no `rdfstar`; unchanged) | 791 pass, 0 fail, 2 local override (out of 793) |
| W3C RDF 1.2 eval tests through JSON-LD-star and back | 140 of 140 |
| W3C RDF 1.2 positive syntax tests through JSON-LD-star and back | 79 of 79 |

The one fail, fromRdf `tst07`, is a defect in the test data: its expected
output has `"@type": "ex:Type"` as a string inside `@triple`, where expanded
form needs an array (the suite's own expand `st07-out.jsonld` has the array).
The harness counts a local override apart from a pass. The 0.18.0 changelog
adds them: 168 pass + 2 local override = 170 of 171.
The [standards table](../#standards-support) has the current numbers.

## Towards JSON-LD 1.3

There is no JSON-LD 1.3 specification text yet (October 2026). The work is
in four places:

- https://github.com/json-ld/json-ld-star/pull/61 (JSON-LD-star tests for
  RDF 1.2, branch `1.2-tests`): the tests Factoidal runs. They are expected
  to move to https://github.com/w3c/json-ld-api as the JSON-LD 1.3 tests.
- https://github.com/json-ld/json-ld-star/issues/49 (syntax for triple
  terms and reifiers): a proposal of 2026-10-18 to use one keyword `@quote`
  in place of `@triple` and `@reifies`.
- https://github.com/niklasl/trld/pull/6 (TRLD, a JSON-LD processor that
  targets JSON-LD 1.3): a second implementation.
- https://github.com/w3c/json-ld-syntax/issues/488 (JSON-LD 1.2 as "RDF 1.2
  basic"): base direction as `rdf:dirLangString`, with triple terms left to
  1.3.

What Factoidal will do as these change:

1. **JSON-LD 1.2, "RDF 1.2 basic".** `rdfDirection: "rdf-1.2"` exists now.
   When JSON-LD 1.2 is published, it becomes available without `rdfstar`,
   with the 1.2 processing mode.
2. **The tests move to w3c/json-ld-api.** We copy them in place of the
   json-ld-star copy (`third_party/testing/json-ld-star/`) and score them
   in the same runner. Each fixture that disagrees with our choices above
   is reported upstream, not changed here.
3. **`@quote` or another syntax change.** The keywords are aliases in one
   table of the Lean JSON-LD processor (`L4Factoidal/JSONLD/Context.lean`).
   A new keyword is added next to the old ones; the old ones stay readable
   while the drafts disagree.
4. **A 1.3 processing mode.** When the specification names one, it selects
   what `rdfstar` selects now, and `rdfstar` stays as its alias.

Tracking the gaps that stay in JSON-LD 1.1: https://github.com/danbri/factoidal/issues/883
(RDF 1.2 output in RDF/XML and JSON-LD) and https://github.com/danbri/factoidal/issues/984
(JSON-LD and RDF 1.2).

## Limits

- `parse(text, { format: 'jsonld', rdfstar: true })` is refused
  (`option.unknown`) in 0.18.0 and 0.19.0 (fixed for 0.20.0 by https://github.com/danbri/factoidal-core/pull/152); use `jsonldToRdf(text, { rdfstar: true })`.
  The 0.18.0 changelog says `parse` takes the option. Expected-failure
  test: `tests/hub/hub_jsonld-star_test.mjs`.
- `formats()` lists JSON-LD as RDF 1.1 only (`read12`, `write12` false); it
  does not know the option `rdfstar`.
- Without `rdfstar`, the reader ignores `@triple`, `@reifies` and
  `@annotation` as JSON-LD 1.1 says for unknown keywords: their triples are
  lost without an error.
- Framing (`jsonldFrame`) and the F\* JSON-LD tree have no JSON-LD-star.
