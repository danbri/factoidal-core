// Review findings against 0.14.0-0.18.0, fixed in 0.20.0:
// 1. A well-typed reader -> writer -> reader pipeline failed at run time:
//    the writer left the input Dataset on its wire (wireOut String).
// 2. Settings could change after node() checked them, so the evidence
//    digest and the pipeline check described other settings than those run.
import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const TTL = '@prefix ex: <http://example.org/> . ex:a ex:p "x" ; ex:q ex:b .';
const SHAPES = `@prefix sh: <http://www.w3.org/ns/shacl#> . @prefix ex: <http://example.org/> .
  ex:S a sh:NodeShape ; sh:targetNode ex:a ; sh:property [ sh:path ex:p ; sh:minCount 1 ] .`;
const EXTRA_SHAPE = `@prefix sh: <http://www.w3.org/ns/shacl#> . @prefix ex: <http://example.org/> .
  ex:S sh:property [ sh:path ex:missing ; sh:minCount 1 ] .`;

test('reader -> writer -> reader: well typed, and it runs', async () => {
  for (const [w, r] of [['ntriplesDocumentWriter', 'ntriplesDocumentReader'],
    ['nquadsDocumentWriter', 'nquadsDocumentReader'],
    ['turtleDocumentWriter', 'turtleDocumentReader']]) {
    const p = f.pipe(await f.node('turtleDocumentReader'), await f.node(w), await f.node(r));
    assert.equal(p.wellTyped, true, w);
    const out = await f.run(p, TTL, { unchecked: true });
    assert.ok(out.graph instanceof f.Dataset, w);
    assert.equal(out.graph.size, 2, w);
    assert.ok(await f.isomorphic(out.graph, await f.parse(TTL)), w);
  }
});

test('each node puts a value of its output wire on the wire', async () => {
  const data = await f.parse(TTL);
  const one = async (name, params) => {
    const n = await f.node(name, params);
    return { n, r: await f.run(n, data, { unchecked: true }) };
  };
  let { n, r } = await one('ntriplesDocumentWriter');
  assert.equal(n.wireOut, 'String');
  assert.equal(typeof r.graph, 'string');
  assert.equal(r.graph, r.evidence[0].artefact.text);

  ({ n, r } = await one('shippedEvaluator', { query: 'SELECT ?o WHERE { ?s ?p ?o }' }));
  assert.equal(n.wireOut, 'Table');
  assert.ok(Array.isArray(r.graph));
  assert.equal(r.graph.length, 2);

  ({ n, r } = await one('shippedEvaluator', { query: 'ASK { ?s ?p "x" }' }));
  assert.equal(n.wireOut, 'Answer');
  assert.equal(r.graph, true);

  ({ n, r } = await one('shippedEvaluator', { query: 'CONSTRUCT WHERE { ?s ?p ?o }' }));
  assert.equal(n.wireOut, 'Dataset');
  assert.ok(r.graph instanceof f.Dataset);

  ({ n, r } = await one('rdfcStage'));
  assert.equal(n.wireOut, 'String × String');
  const [canonical, sha256] = r.graph;
  assert.equal(canonical, await f.canonicalize(data));
  assert.equal(sha256, await f.vcSha256Hex(canonical));

  ({ n, r } = await one('shaclValidator', { shapes: SHAPES }));
  assert.equal(n.wireOut, 'ValidationReport');
  assert.equal(r.graph.conforms, true);
});

test('rdfcStage takes text as well as a Dataset', async () => {
  const n = await f.node('rdfcStage', { format: 'turtle' });
  const r = await f.run(n, TTL, { unchecked: true });
  const ds = await f.parse(TTL);
  assert.deepEqual(r.graph, [await f.canonicalize(ds), await f.canonicalHash(ds)]);
});

test('a writer then a SPARQL evaluator is not well typed, and run() refuses it', async () => {
  const p = f.pipe(await f.node('turtleDocumentReader'), await f.node('turtleDocumentWriter'),
    await f.node('shippedEvaluator', { query: 'ASK {}' }));
  assert.equal(p.wellTyped, false);
  await assert.rejects(f.run(p, TTL), /not well typed/);
});

test('a change to the caller\'s Dataset after node() does not reach the node', async () => {
  const data = await f.parse(TTL);
  const shapes = await f.parse(SHAPES);
  const n = await f.node('shaclValidator', { shapes });
  const before = await f.run(n, data);
  for (const q of await f.parse(EXTRA_SHAPE)) shapes.add(q);
  const after = await f.run(n, data);
  assert.equal(before.graph.conforms, true);
  assert.equal(after.graph.conforms, true, 'the node validates with the shapes it was made with');
  assert.equal(after.evidence[0].settingsDigest, before.evidence[0].settingsDigest);
  // A new node with the changed shapes is a new digest and a new answer.
  const n2 = await f.node('shaclValidator', { shapes });
  assert.notEqual(n2.settingsDigest, n.settingsDigest);
  assert.equal((await f.run(n2, data)).graph.conforms, false);
});

test('a change through node.params is refused at run()', async () => {
  const data = await f.parse(TTL);
  const n = await f.node('shaclValidator', { shapes: await f.parse(SHAPES) });
  for (const q of await f.parse(EXTRA_SHAPE)) n.params.shapes.add(q);
  await assert.rejects(f.run(n, data), /changed after node\(\) checked them/);
});

test('settings are frozen at every depth', async () => {
  const opts = { prefixes: { ex: 'http://example.org/' }, list: [{ a: 1 }] };
  const n = await f.node('turtleDocumentWriter', opts);
  assert.ok(Object.isFrozen(n.params.prefixes));
  assert.ok(Object.isFrozen(n.params.list[0]));
  assert.throws(() => { n.params.prefixes.ex = 'http://other.example/'; }, TypeError);
  opts.prefixes.ex = 'http://other.example/';
  assert.equal(n.params.prefixes.ex, 'http://example.org/', 'the caller\'s object is not shared');
  assert.ok(Object.isFrozen(n.settingsWire.prefixes));
});
