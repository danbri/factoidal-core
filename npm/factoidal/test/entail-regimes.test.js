// query()'s `entail` option: the engine closes the default graph under the
// regime and then answers the query (op queryRaw,
// formal/lean4/Wasm/Ops/QueryExtras.lean). And the x-ikl-* names, which are
// refused before they reach the engine (moved from select.test.js when
// select.js left the package).

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const factoidal = require('..');
const fn = require('../fn.js');

const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
const TTL = `
  @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
  @prefix owl:  <http://www.w3.org/2002/07/owl#> .
  @prefix : <http://e/> .
  :C rdfs:subClassOf :D .
  :a a :C .
  :p owl:inverseOf :q .
  :a :p :b .
`;
const ASK_D = `ASK { <http://e/a> <${RDF_TYPE}> <http://e/D> }`;
const ASK_INV = 'ASK { <http://e/b> <http://e/q> <http://e/a> }';

test('entail none: a subclass membership is not entailed', async () => {
  assert.equal(await factoidal.query(TTL, ASK_D), false);
});

for (const regime of ['RDFS', 'OWL-RL', 'x-rdfscore', 'x-rdfsplus']) {
  test(`entail ${regime}: a subclass membership (rdfs9) is entailed`, async () => {
    assert.equal(await factoidal.query(TTL, ASK_D, { entail: regime }), true);
  });
}

test('entail x-rdfsplus: owl:inverseOf is applied; x-rdfscore does not apply it', async () => {
  assert.equal(await factoidal.query(TTL, ASK_INV, { entail: 'x-rdfsplus' }), true);
  assert.equal(await factoidal.query(TTL, ASK_INV, { entail: 'x-rdfscore' }), false);
});

test('entail RDFS: SELECT answers Bindings over the closure', async () => {
  const rows = await factoidal.query(TTL,
    `SELECT ?c WHERE { <http://e/a> <${RDF_TYPE}> ?c } ORDER BY ?c`, { entail: 'RDFS' });
  const classes = rows.map((r) => r.get('c').value);
  assert.ok(classes.includes('http://e/C') && classes.includes('http://e/D'), classes.join(' '));
});

test('entail RDFS: CONSTRUCT answers a Dataset over the closure', async () => {
  const ds = await factoidal.query(TTL,
    `CONSTRUCT { ?s <${RDF_TYPE}> ?c } WHERE { ?s <${RDF_TYPE}> ?c }`, { entail: 'RDFS' });
  assert.ok(ds instanceof factoidal.Dataset);
  assert.ok([...ds].some((q) => q.object.value === 'http://e/D'));
});

test('an unknown regime is option.invalid-value', async () => {
  await assert.rejects(() => factoidal.query(TTL, ASK_D, { entail: 'x-none-such' }),
    (e) => e instanceof factoidal.FactoidalError && e.code === 'option.invalid-value');
});

test('query() rejects x-ikl-* entail regimes, case-insensitively', async () => {
  const ds = await factoidal.parse(TTL);
  await assert.rejects(
    () => factoidal.query(ds, 'SELECT * WHERE { ?s ?p ?o }', { entail: 'x-ikl-core' }),
    /x-ikl-\* entailment regimes are the owner's design/);
  await assert.rejects(
    () => factoidal.query(ds, 'SELECT * WHERE { ?s ?p ?o }', { entail: 'X-IKL-Whatever' }),
    /x-ikl-\* entailment regimes are the owner's design/);
});

test('fn.js entail() refuses x-ikl-* as not implemented, before it reaches the engine', async () => {
  const ds = await fn.parse(TTL);
  await assert.rejects(() => fn.entail(ds, 'x-ikl-foo'),
    /x-ikl-\* entailment regimes are the owner's design/);
});

test('fn.js entail(RDFS) materialises the closure as an FnDataset', async () => {
  const ds = await fn.parse(TTL);
  const closed = await fn.entail(ds, 'rdfs');
  assert.ok(closed.size > ds.size);
});
