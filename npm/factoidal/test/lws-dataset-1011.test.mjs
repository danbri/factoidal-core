// openLwsDataset (https://github.com/danbri/factoidal/issues/1011): this
// package's own LWS server on an ephemeral port, two Turtle resources and
// one text resource PUT by the LWS client, then the storage crawled and
// queried as a dataset. Skipped when the loaded wasm has no LWS server ops
// or no dataset-view ops (lwsViewPlan, lwsDatasetView).

import test from 'node:test';
import assert from 'node:assert/strict';
import { loadEngine } from '../bin/engine.mjs';

let skip = 'wasm engine not built';
let engine = null;
try {
  engine = await loadEngine();
  const { lwsOpsAvailable } = await import('../lws/server.mjs');
  const { lwsDatasetOpsAvailable } = await import('../lws/dataset.mjs');
  const server = await lwsOpsAvailable(engine);
  const view = await lwsDatasetOpsAvailable(engine);
  skip = !server.available ? server.reason : !view.available ? view.reason : false;
} catch (_err) { /* engine did not load: skip */ }

test('GRAPH ?g gives both resources; the evidence lists both ETags', { skip }, async () => {
  const { listen } = await import('../lws/server.mjs');
  const { createLwsClient } = await import('../lws/client.mjs');
  const { openLwsDataset } = await import('../lws/dataset.mjs');
  const running = await listen({ engine, port: 0, insecureNoAuth: true });
  try {
    const client = await createLwsClient({ engine });
    const root = `${running.origin}/`;
    const notes = (await client.create(root, { container: true, slug: 'notes' })).location;
    const a = (await client.create(notes, {
      slug: 'a.ttl', mediaType: 'text/turtle', body: '<#it> <http://e/p> "a" .' })).location;
    const b = (await client.create(root, {
      slug: 'b.ttl', mediaType: 'text/turtle', body: '<> <http://e/p> "b" .' })).location;
    await client.create(notes, { slug: 'c.txt', mediaType: 'text/plain', body: 'not RDF' });

    const lws = await openLwsDataset(root, { engine });
    try {
      assert.equal(lws.graphs, 2);
      const { result, evidence } = await lws.query(
        'SELECT DISTINCT ?g WHERE { GRAPH ?g { ?s ?p ?o } } ORDER BY ?g');
      assert.deepEqual(result.map((row) => row.get('g').value).sort(), [a, b].sort());
      assert.deepEqual(evidence.map((e) => e.resource).sort(), [a, b].sort());
      for (const e of evidence) assert.match(e.etag, /^(W\/)?"/);
      assert.equal(new Set(evidence.map((e) => e.etag)).size, 2);
      // the text resource is left out, with a reason
      assert.ok(lws.skipped.some((s) => /c\.txt$/.test(s.resource)));
      // containment is the default graph
      const contains = await lws.query(
        `ASK { <${notes}> <http://www.w3.org/ns/ldp#contains> <${a}> }`);
      assert.equal(contains.result, true);
      const inGraph = await lws.query(`ASK { GRAPH <${a}> { <${a}#it> <http://e/p> "a" } }`);
      assert.equal(inGraph.result, true);
    } finally {
      lws.dispose();
    }

    // a change: the new representation has a new ETag and the new triple
    await client.update(b, { mediaType: 'text/turtle', body: '<> <http://e/p> "b2" .' });
    const again = await openLwsDataset(root, { engine });
    try {
      const r = await again.query(`ASK { GRAPH <${b}> { <${b}> <http://e/p> "b2" } }`);
      assert.equal(r.result, true);
      const old = await again.query(`ASK { GRAPH <${b}> { <${b}> <http://e/p> "b" } }`);
      assert.equal(old.result, false);
    } finally {
      again.dispose();
    }
  } finally {
    await running.close();
  }
});

test('a storage root that is not a string is a TypeError', async () => {
  const { openLwsDataset } = await import('../lws/dataset.mjs');
  await assert.rejects(openLwsDataset(42), TypeError);
});
