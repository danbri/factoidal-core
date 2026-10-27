# JSON-LD-star in the Lean tree (2026-10-26)

Owner, 2026-10-26, verbatim: "Ok so implement JSON-LD-star: JSON-LD-star is
SOTA. It will likely change a bit, but let's start there first." and "Try to
reuse as much of our JSON and JSON-LD code as possible (and RDF 1.2, SPARQL
1.2, *obviously*)".

## Target

The JSON-LD-star tests of https://github.com/json-ld/json-ld-star/pull/61
(branch `1.2-tests`, commit `6142c6ff`), copied to
`third_party/testing/json-ld-star/` (provenance:
`third_party/testing/json-ld-star-PROVENANCE.md`). This is the RDF 1.2 form of
JSON-LD-star: triple terms and reifiers, not the RDF-star quoted triples of the
2021 Community Group report. There is no specification text for it. The
algorithm changes are the pull-request comment of 2025-05-19, copied below.

Keywords, active only when the option `rdfstar` is true (otherwise they are
ignored as unknown `@`-keywords):

- `@triple`: an object `{"@triple": node}` is an RDF 1.2 triple term. `node`
  must give exactly one triple.
- `@reifies`: on a node object, `rdf:reifies` to the triple term of each triple
  that its value gives (one or more).
- `@annotation`: on a value object or node object that is the value of a
  property, a reifier (blank node, or the annotation's `@id`) of the triple
  that the value makes, with the annotation's own properties.

Later syntax change is likely: the `@quote` proposal in
https://github.com/json-ld/json-ld-star/issues/49 (2026-10-18), and a move of
these tests to w3c/json-ld-api as JSON-LD 1.3.

## Where it lives

Lean 4 only (owner, 2026-10-21: test failures and scores are Lean 4 only).
The F\* JSON-LD tree has no JSON-LD-star; it keeps refusing triple terms.

- Option: `ContextCore.rdfstar` (`L4Factoidal/JSONLD/Context.lean`), set by the
  `rdfstar` argument of `expandDocument`, `parseJsonLd`, `compactDocument`,
  `flattenDocument` (also `createAnnotations`) and `FromRdf.Options.rdfstar`.
- RDF side: `Term.tripleTerm` of `L4Factoidal.RDF` (RDF 1.2 Concepts); fixtures
  are read with the RDF 1.2 N-Quads reader (`Mode.rdf12`).
- Score: `formal/lean4/.lake/build/bin/l4jsonld-api --star`, run from the
  repository root; scoreboard job `l4jsonld-api-star`
  (`tools/lean-scoreboard.sh`). 2026-10-27: 170 pass, 1 fail (out of 171):
  expand 47/47, toRdf 47/47, fromRdf 20/21, compact 17/17, flatten 39/39.

## Rules taken from the fixtures (2026-10-26/27)

The outline below is incomplete and in one place contradicts the fixtures.
Where they differ, the fixtures decide; each case is listed here.

Expansion (`Expand.lean`, `Context.lean`):

- `@triple`: the value expands with a null active property. It must give
  exactly one node object with no `@reverse` and no `@triple`, and that node
  must make exactly one triple. One triple is counted for each value of each
  property, of `@type`, of `@reifies` and of each reverse property. The object
  that holds `@triple` may have only `@triple` and `@annotation`. Error:
  "invalid triple term" (tst11 to tst14).
- `@reifies`: each value must be a node object that makes AT LEAST one triple.
  The outline says "no more than one statement"; the fixtures say otherwise
  (tst12a, tst13a, tst14a make two triples and are valid; tst11a makes none and
  is "invalid reification").
- `@annotation`: each value must be a node object whose `@id`, if present, is a
  blank node (tst23, tst24, tst24a). It is valid only on a value object or node
  object that is a property value, forward or reverse (tst34, tst35). It is
  invalid at the top level (tst21), in `@graph` (tst22), in `@included` (tst27),
  on a `@list` item (tst26), inside `@triple` (tst27a) or a `@reifies` value,
  and directly inside another annotation; it is valid inside an annotation's
  own property values (tst40). Error: "invalid annotation". On a list object
  the existing 1.1 error "invalid set or list object" applies (tst25).
- Aliases of the three keywords are terms whose definition is the keyword
  (tst36, tst37), recognised only under `rdfstar`.
- Two JSON-LD 1.1 corrections came with this work, both with the W3C suites
  unchanged: a value object ignores a key that expands to a keyword lookalike
  (API 5.1 step 13.2; json-ld-star tst03 with `rdfstar` false); and an embedded
  node object with `@reverse` is no longer refused with "invalid reverse
  property value" (that error is for value and list objects as reverse values;
  json-ld-star compact tst35).

Deserialize to RDF (`ToRdf.lean`, `RdfAcc.rdfstar`):

- `{"@triple": n}` gives `Term.tripleTerm s p o` for the one triple of `n`;
  the triple is not asserted.
- `r` with `@reifies` values gives `r rdf:reifies <<( t )>>` for each triple of
  each value; those triples are not asserted.
- `@annotation` on value `o` of property `p` of subject `s` gives, for each
  annotation node, reifier `r` (its `@id`, or a new blank node) with
  `r rdf:reifies <<( s p o )>>` and the annotation's own triples. For a reverse
  property the reified triple is the reversed one.

Serialize RDF as JSON-LD (`FromRdf.lean`, `FromRdf.Options.rdfstar`):

- A triple term becomes `{"@triple": node}`; nested triple terms are built by a
  tail-recursive walk and a left fold (no stack growth with depth; `#guard` at
  depth 3,000).
- `r rdf:reifies <<( t )>>` becomes a `@reifies` value of `r`.
- Annotation folding: a reifier becomes `@annotation` on the asserted value
  only when (1) it is a blank node, (2) it has exactly one `@reifies` value,
  (3) the reified triple is asserted in the same graph, and (4) it is not
  referenced anywhere else (not an object, not in a triple term, not a graph
  name). The annotation keeps the reifier's `@id`.
- `RDF/SinkJsonLd.lean`: `withJsonLdStar` writes triple terms; the default
  `withJsonLd` still refuses them. The stream writer does not fold
  annotations (folding needs the whole graph).

Compaction (`Compact.lean`): `@triple`, `@reifies` and `@annotation` values are
compacted as node objects with a null active property and written under the
keyword's alias; a value object with `@annotation` keeps its map form.

Flattening (`Flatten.lean`, `generateNodeMap (rdfstar := …)`):

- An `@annotation` on a value object, a `@triple` value or a node object
  (also under `@reverse`) becomes a reifier node with
  `@reifies: [{"@id": subject, property: [value]}]` and the annotation's own
  properties; `@triple` and `@reifies` values stay embedded.
- Blank-node labels follow the Ruby json-ld implementation, because the
  fixtures pin exact labels: under `rdfstar`, every blank `@id` is renamed in
  document order before node-map generation, and every annotation takes a
  fresh label. One correction the reference lacks: blank nodes inside
  embedded triples are mapped to their final labels after node-map
  generation (no fixture tests this).
- `createAnnotations` folds a reifier back into `@annotation` on the matching
  value, as the outline says, even when another node references the reifier
  (st35n). This is wider than the fromRdf folding rule above (which also
  needs the reifier to be unreferenced). The two rules are different on
  purpose for now: each follows its own fixtures. Record of the difference,
  not a decision; revisit when the syntax settles.

Source and sink layers: `Source.withJsonLdStar` and `Sink.withJsonLdStar`
read and write JSON-LD-star; `withJsonLd` stays JSON-LD 1.1 on both sides.
The `#guard`s in `RDF/SinkJsonLd.lean` check the round trip.

Test harness (`Harness/JsonLdApiProbe.lean`):

- `specVersion: "json-ld-star"` names the extension, not a processing mode;
  those tests run as JSON-LD 1.1.
- Star fixtures are read with the RDF 1.2 N-Quads reader. Before this, the
  RDF 1.1 reader dropped every triple-term line, and empty-against-empty
  comparisons gave 11 false passes.
- Star fromRdf and flatten results are compared with arrays unordered, except
  `@list`. The fixtures' top-level node order is the Ruby implementation's
  insertion order: neither sorted by `@id` (fromRdf st15, st16, st29) nor in
  input order (fromRdf st19, st20). 16 of 39 flatten fixtures differ from our
  sorted output only in that order.
- Every star compact entry names its expected output as `context`. When that
  document has no `@context`, the test compacts with an empty context. Only
  that case is affected; the W3C suites never name the output as the context.

Fixture defect: fromRdf `st07-out.jsonld` has `"@type": "ex:Type"` as a string
inside `@triple`; expanded form requires an array, and the suite's own
`expand/st07-out.jsonld` has `["ex:Type"]`. Our output is the array. This test
stays failing until it is reported upstream and classified (CLAUDE.md,
"Defective W3C test data is not our failure").

## Algorithm changes (Gregg Kellogg, json-ld-star PR 61 comment, 2025-05-19, verbatim)

Synopsis of algorithm updates:

## [Expansion Algorithm](https://json-ld.github.io/json-ld-star/#expansion-algorithm)

* If output object is a triple term (an object containing an `@triple` key) verify that the only keys in that object are `@triple` and `@annotation`.
* When processing each key/value in the input:
  * If expanded property is `@annotation`, the _expanded value_ is the result of expanding that value, using `@annotation` as the active property.
  * If _expanded property_ is `@reifies`:
    * expand value as an array called _rei nodes_, using `null` as active property.
    * for each _rei node_ in _rei nodes_, count the triples generated by calling the [Object to RDF Algorithm](https://json-ld.github.io/json-ld-star/#object-to-rdf-algorithm) on that node to verify the no more than one statement is generated.
    * The result is the expanded value as an array using `@reifies` as the _active property_.
  * If _expanded property_ is `@triple`:
    * expand value to _tt node_, using `null` as _active property_.
    * count the statements generated by calling the [Object to RDF Algorithm](https://json-ld.github.io/json-ld-star/#object-to-rdf-algorithm) on that node to verify the no more than one triple is generated.
    * _tt node_ must not include the `@reverse` or `@triple` keys.
    * The result _tt node_.
* Before processing nests, if the output object includes `@triple`, ensure that it includes no keys other than `@triple` and `@annotation`.

## [Compaction Algorithm](https://json-ld.github.io/json-ld-star/#compaction-algorithm)

* If _expanded property_ is `@id`, its value can no longer be an object, so text reverts to base JSON-LD 1.1
* Adds entry for _expanded property_ being `@triple`, which compacts the triple object and returns it.

## [Flattening Algorithm](https://json-ld.github.io/json-ld-star/#flattening-algorithms)

* If _element_ is a _value object_, see if it includes an `@annotation` key. If so:
  * Remove the `@annotation` key using the value as _annotation_
  * construct _reification_ as a new object with `@id` set to _active subject_, and _active property_ set to an array containing _element_.
  * For each annotation:
    * set _reifier_ to the `@id` key from that annotation, or a new blank node, if there is no such entry.
    * Add key entries for `@id` and `@reifier` taken from _reifier_ and _reification_, respectively.
    * Create an entry in _graph map_ using _active graph_, and _reifier_ for _active subject_
 * If _element_ is a _triple term_, see if it includes an `@annotation` key. If so:
  * Remove the `@annotation` key using the value as _annotation_
  * construct _reification_ as a new object with `@id` set to _active subject_, and _active property_ set to an array containing _element_.
  * For each annotation:
    * set _reifier_ to the `@id` key from that annotation, or a new blank node, if there is no such entry.
    * Add key entries for `@id` and `@reifier` taken from _reifier_ and _reification_, respectively.
    * Create an entry in _graph map_ using _active graph_, and _reifier_ for _active subject_
  * Use _add value_ to add _element_ as an _active property_ to _subject node_. (_element_ will only contain `@triple`).
* Otherwise, _element_ is a _node object_:
  * Process annotations as above, creating a `@reifies` entry in _node_, using _element_ without the `@reifies` key.

### [Create Annotations](https://json-ld.github.io/json-ld-star/#create-annotations)

* Foreach entry in _node map_ having a `@reifies` key, and for each such value _node_:
  * set _reif id_ do the value of `@id` in _node_.
  * set _reifs_ to the value of `@reifies` in _node_. (It **must** be an array).
  * Set _annotation_ to the a copy of _node_ excluding `@id` and `@reifies`.
  * For each _reif_ in _reifs_:
    * set _target id_ to the value of `@id` in _reif`.
    * set _target node_ to the entry in _node map_ for _target id_.
    * If there is no such node, continue to the next _reif_.
    * set _reif prop_ to the only key in _reif_ other than `@id` (error if not found)
    * set _reif values_ to the value of _reif key_ in _reif_, which must be an array with a single entry.
    * set _reif value_ to the only entry in _reif values_.
    * set _target values_ to the value of _reif prop_ in _target node_, continuing to the next _reif_ if there are no such values.
    * It is an error if _target values_ is not an array.
    * For each _target value_ in _target values_
      * Continue to the next _target value_ unless _target value_ exclusive of `@annotation` is equal to _reif value_
      * Use _add value_ to add a copy of _annotation_ with `@id` set to _reif id_ as an `@annotation` to _target value_.
      * remove _reif_ from `@reifies` in _node_.
  * If the value of `@reifies` in _node_ is empty, remove that entry from _node_.

## [Serialize RDF as JSON-LD Algorithm](https://json-ld.github.io/json-ld-star/#serialize-rdf-as-json-ld)

* if _predicate_ is `rdf:reifies` and _object_ is a _triple term_:
  * set _reifiecation_ to the JSON-LD representation of the _triple term_ and merge the resulting value of `@triple` into _node_ using the `@reifies` key.

## [Object to RDF Algorithm](https://json-ld.github.io/json-ld-star/#object-to-rdf-algorithm)

* If _item_ is a _triple term_, return the result of using this algorithm on the value of `@triple`
* When processing each _property_ and _value) in _item_:
  * If _proeprty_ is `@reifies`, call this algorithm recursively on each such value, where each resulting triple is treated as a _triple term_ resource.
