// Pins every code sample in
// docs/web/hub/03-schemas-that-infer-rdfs-owl.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runReactivePost } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '03-schemas-that-infer-rdfs-owl.md';

const RDFS_TTL = `
  @prefix schema: <https://schema.org/> .
  @prefix rdfs:   <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix ex:     <http://example.org/> .

  schema:Person rdfs:subClassOf schema:Thing .
  ex:alice a schema:Person .
`;

const Q = `SELECT ?type WHERE { <http://example.org/alice> a ?type }`;

test('post03: no entailment sees only the asserted type', async () => {
  const dataset = await factoidal.parse(RDFS_TTL);
  const rows = await factoidal.query(dataset, Q);
  const types = rows.map((r) => r.get('type').value);
  assert.deepEqual(types, ['https://schema.org/Person']);
});

test('post03: RDFS entailment adds schema:Thing via subClassOf', async () => {
  const dataset = await factoidal.parse(RDFS_TTL);
  const rows = await factoidal.query(dataset, Q, { entail: 'RDFS' });
  const types = rows.map((r) => r.get('type').value).sort();
  assert.deepEqual(types, [
    'http://www.w3.org/2000/01/rdf-schema#Resource',
    'https://schema.org/Person',
    'https://schema.org/Thing',
  ]);
});

const OWL_TTL = `
  @prefix schema: <https://schema.org/> .
  @prefix foaf:   <http://xmlns.com/foaf/0.1/> .
  @prefix owl:    <http://www.w3.org/2002/07/owl#> .
  @prefix ex:     <http://example.org/> .

  schema:Person owl:equivalentClass foaf:Person .
  ex:alice a schema:Person .
`;

test('post03: RDFS entailment does not know owl:equivalentClass', async () => {
  const dataset2 = await factoidal.parse(OWL_TTL);
  const rows = await factoidal.query(dataset2, Q, { entail: 'RDFS' });
  const types = rows.map((r) => r.get('type').value).sort();
  // rdfs:Resource is derived for every subject (rdfs4a/4b); the point
  // of this test is that owl:equivalentClass does NOT fire under RDFS,
  // i.e. no foaf:Person in the list.
  assert.deepEqual(types, [
    'http://www.w3.org/2000/01/rdf-schema#Resource',
    'https://schema.org/Person',
  ]);
});

// The OWL 2 RL/RDF rules (OWL 2 Profiles § 4.3, Tables 4-9) fix this
// set. cax-eqc1 (Table 7) gives foaf:Person. No row types an individual
// as owl:Thing: cls-thing (Table 6) has no premise and types owl:Thing
// itself as an owl:Class. rdfs:Resource comes from rdfs4a/rdfs4b, which
// are RDFS entailment rules (RDF 1.1 Semantics § 9.2.1), not OWL 2 RL
// rows. The F* engine added both through extension tables
// (owl_thing_axioms and its RDFS layer); see
// docs/designissues/2026-09-07-lean-owl-corpus-gap.md § 14.1.
const OWL_RL_TYPES = [
  'http://xmlns.com/foaf/0.1/Person',
  'https://schema.org/Person',
];

test('post03: OWL-RL entailment derives foaf:Person via equivalentClass (cax-eqc1), and no owl:Thing or rdfs:Resource typing', async () => {
  const dataset2 = await factoidal.parse(OWL_TTL);
  const rows = await factoidal.query(dataset2, Q, { entail: 'OWL-RL' });
  const types = rows.map((r) => r.get('type').value).sort();
  assert.deepEqual(types, OWL_RL_TYPES);
});

// ---------------------------------------------------------------------
// Cell-pinning tests: extract the exact ```observable-js source shipped
// on the page and execute it via the same new Function(...) construction
// docs/_includes/hub.njk's mountCell() uses, against the real
// npm/factoidal typed API (fn === factoidal here; the live page instead
// binds `fn` to the in-browser adapter — see docs/web/hub/README.md).
// ---------------------------------------------------------------------

const cells = extractObservableCells(POST_FILE);

test('post03: post has 4 live cells (the shared query hoisted into its own named cell)', () => {
  assert.equal(cells.length, 4, `expected 4 live cells, found ${cells.length}`);
});

test('post03: dependency inference wires all three query cells to the named q cell', () => {
  const post = runReactivePost(cells, { fn: factoidal });
  assert.equal(post.names[0], 'q');
  for (const i of [1, 2, 3]) {
    assert.ok(post.infos[i].refs.includes('q'), `cell ${i + 1} references q`);
  }
});

test('post03 cell 2 (RDFS toggle): schema:Thing appears only with entailment', async () => {
  const post = runReactivePost(cells, { fn: factoidal });
  const result = await post.value(post.names[1]);
  assert.deepEqual(result, {
    withoutEntailment: ['https://schema.org/Person'],
    withRDFS: [
      'http://www.w3.org/2000/01/rdf-schema#Resource',
      'https://schema.org/Person',
      'https://schema.org/Thing',
    ],
  });
});

test('post03 cell 3 (OWL-RL toggle): equivalentClass only fires under OWL-RL', async () => {
  const post = runReactivePost(cells, { fn: factoidal });
  const result = await post.value(post.names[2]);
  // The cell does not sort withRDFS, and a SELECT without ORDER BY has
  // no fixed solution order (SPARQL 1.1 Query § 15.1), so compare it as
  // a set.
  assert.deepEqual([...result.withRDFS].sort(), [
    'http://www.w3.org/2000/01/rdf-schema#Resource',
    'https://schema.org/Person',
  ]);
  assert.deepEqual(result.withOWLRL, OWL_RL_TYPES);
});

test('post03 cell 4 (mutual subClassOf): equivalence in pure RDFS', async () => {
  const post = runReactivePost(cells, { fn: factoidal });
  const result = await post.value(post.names[3]);
  assert.deepEqual(result, [
    'http://www.w3.org/2000/01/rdf-schema#Resource',
    'http://xmlns.com/foaf/0.1/Person',
    'https://schema.org/Person',
  ]);
});
