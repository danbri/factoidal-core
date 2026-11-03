// openLwsDataset (https://github.com/danbri/factoidal/issues/1011, version 2):
// this package's own LWS server on an ephemeral port, two Turtle resources
// and one text resource PUT by the LWS client, then the storage crawled and
// queried as a dataset: the table-of-contents graph named by the storage
// description IRI, one graph per Turtle document, one graph per linkset.
// Skipped when the loaded wasm has no LWS server ops or no version 2
// dataset-view ops (lwsViewPlan with `metadata`, lwsDatasetView).

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

const LWS = 'https://www.w3.org/ns/lws#';
const IANA = 'http://www.iana.org/assignments/relation/';

test('the TOC, the documents and the linksets are graphs; the evidence lists every ETag', { skip }, async () => {
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
    const c = (await client.create(notes, { slug: 'c.txt', mediaType: 'text/plain', body: 'not RDF' })).location;

    const lws = await openLwsDataset(root, { engine });
    try {
      // the TOC is named by the storage description IRI
      assert.equal(lws.toc, `${running.origin}/.well-known/lws-storage`);
      // the TOC, two documents, the linksets of root, notes, a, b and c
      assert.equal(lws.graphs, 8);
      const { result, evidence } = await lws.query(
        'SELECT DISTINCT ?g WHERE { GRAPH ?g { ?s ?p ?o } } ORDER BY ?g');
      const names = result.map((row) => row.get('g').value);
      assert.equal(names.length, 8);
      assert.ok(names.includes(lws.toc));
      assert.ok(names.includes(a) && names.includes(b));
      // the text resource has no document graph
      assert.ok(!names.includes(c));
      const docs = evidence.filter((e) => e.lastModified !== undefined);
      const linksets = evidence.filter((e) => e.linkset !== undefined);
      assert.deepEqual(docs.map((e) => e.resource).sort(), [a, b].sort());
      for (const e of docs) assert.match(e.etag, /^(W\/)?"/);
      assert.equal(new Set(docs.map((e) => e.etag)).size, 2);
      assert.deepEqual(linksets.map((e) => e.resource).sort(), [root, notes, a, b, c].sort());
      // the text resource is not read, with a reason
      assert.ok(lws.skipped.some((s) => /c\.txt$/.test(s.resource)));
      // containment is lws:items in the TOC; the default graph is empty
      const contains = await lws.query(
        `ASK { GRAPH <${lws.toc}> { <${notes}> <${LWS}items> <${a}> } }`);
      assert.equal(contains.result, true);
      const dflt = await lws.query('ASK { ?s ?p ?o }');
      assert.equal(dflt.result, false);
      // the text resource is in the TOC, with its format, and has a linkset
      const typed = await lws.query(
        `ASK { GRAPH <${lws.toc}> { <${c}> a <${LWS}DataResource> ; <http://purl.org/dc/terms/format> ?f ;
           <${IANA}linkset> ?l } }`);
      assert.equal(typed.result, true);
      // the linkset graph of a: `up` is the IANA relation, `type` is rdf:type
      const up = await lws.query(
        `ASK { GRAPH ?l { <${a}> <${IANA}up> <${notes}> ; a <${LWS}DataResource> ;
           <${LWS}storage> <${lws.toc}> } }`);
      assert.equal(up.result, true);
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
