// Pins every code sample in docs/web/historical-fstar-notebooks/07-json-ld-rdf-as-json.md.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, runReactivePost } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;
const POST_FILE = '07-json-ld-rdf-as-json.md';

const cells = extractObservableCells(POST_FILE);

// The cells call the package's typed jsonldToRdf / jsonldFromRdf through
// `fn`; the page binds `fn` and `Factoidal` to the same API
// (npm/factoidal/browser.js, issue 726).
const FactoidalNode = factoidal;

test('post07: post has 5 live cells (ALICE_JSONLD hoisted into its own named cell)', () => {
  assert.equal(cells.length, 5, `expected 5 live cells, found ${cells.length}`);
});

test('post07: dependency inference wires ALICE_JSONLD to the tryJsonldToRdf and round-trip cells', () => {
  const post = runReactivePost(cells, { fn: factoidal, Factoidal: FactoidalNode });
  assert.equal(post.names[1], 'ALICE_JSONLD');
  for (const i of [2, 3]) {
    assert.ok(post.infos[i].refs.includes('ALICE_JSONLD'), `cell ${i + 1} references ALICE_JSONLD`);
  }
});

test('post07 cell 1 (plain JSON, no @context): zero triples', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal, Factoidal: FactoidalNode });
  assert.deepEqual(result, { tripleCount: 0 });
});

test('post07 cell 3 (@context mapping): three triples, available', async () => {
  const post = runReactivePost(cells, { fn: factoidal, Factoidal: FactoidalNode });
  const result = await post.value(post.names[2]);
  assert.equal(result.available, true);
  const lines = result.nquads.trim().split('\n').sort();
  assert.deepEqual(lines, [
    '<http://example.org/alice> <http://schema.org/jobTitle> "Engineer" .',
    '<http://example.org/alice> <http://schema.org/name> "Alice" .',
    '<http://example.org/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://schema.org/Person> .',
  ]);
});

test('post07 cell 4 (round trip): JSON-LD -> N-Quads -> query returns Alice/Engineer', async () => {
  const post = runReactivePost(cells, { fn: factoidal, Factoidal: FactoidalNode });
  const result = await post.value(post.names[3]);
  assert.deepEqual(result, [{ name: 'Alice', title: 'Engineer' }]);
});

test('post07 cell 5 (fromRdf): N-Quads -> expanded JSON-LD node object', async () => {
  const result = await runObservableCell(cells[4], { fn: factoidal, Factoidal: FactoidalNode });
  assert.ok(Array.isArray(result), 'expanded form is an array of node objects');
  assert.equal(result.length, 1);
  const node = result[0];
  assert.equal(node['@id'], 'http://example.org/alice');
  assert.deepEqual(node['@type'], ['http://schema.org/Person']);
  assert.deepEqual(node['http://schema.org/name'], [{ '@value': 'Alice' }]);
  assert.deepEqual(node['http://schema.org/jobTitle'], [{ '@value': 'Engineer' }]);
});

// ---------------------------------------------------------------------
// Direct API checks, independent of the cell-extraction machinery above.
// ---------------------------------------------------------------------

test('post07: capabilities() reports JSON-LD support (grounds the "check first" cell pattern)', async () => {
  const caps = await factoidal.capabilities();
  assert.equal(caps.jsonld, true);
});

test('post07: jsonldToRdf resolves relative @id against an explicit base option', async () => {
  const jsonld = JSON.stringify({
    '@context': { foaf: 'http://xmlns.com/foaf/0.1/', name: 'foaf:name' },
    '@id': 'alice',
    name: 'Alice',
  });
  const ds = await factoidal.jsonldToRdf(jsonld, { base: 'http://example.org/' });
  assert.equal(ds.size, 1);
  assert.equal([...ds][0].subject.value, 'http://example.org/alice');
});
