// Actual public API over the package's WASM. No query emulation/reference shim.
// Local tests against an older engine are expected red until it is rebuilt.
// SERVICE providers are in-process snapshots: this suite makes no network call.
import test, { before, after } from 'node:test';
import assert from 'node:assert/strict';
import * as core from '../index.mjs';

const local = '<urn:one> <urn:enabled> "yes" .';
const body = '{ ?s <urn:value> ?v }';
const service = `SERVICE ?endpoint ${body}`;
const values = 'VALUES ?endpoint { <urn:one> <urn:two> }';
const query = pattern => `SELECT ?v ?tag WHERE { ${pattern} } ORDER BY ?v`;
const projected = rows => rows.map(row => row.get('v')?.value ?? '<unbound>');
async function providers() {
  await core.clearServiceEndpoints();
  await core.registerServiceEndpoint('urn:one', '<urn:s> <urn:value> "one" .', {format:'ntriples'});
  await core.registerServiceEndpoint('urn:two', '<urn:s> <urn:value> "two" .', {format:'ntriples'});
  await core.registerServiceEndpoint('urn:outer', '', {format:'ntriples'});
}
async function evaluate(pattern, data='') {
  const dataset = await core.parse(data, {format:'ntriples'});
  try { return await core.query(dataset, query(pattern)); } finally { dataset.dispose(); }
}
before(providers);
after(() => core.clearServiceEndpoints());

test('SERVICE variables correlate VALUES in either join order and preserve bags', async () => {
  assert.deepEqual(projected(await evaluate(values + service)), ['one','two']);
  assert.deepEqual(projected(await evaluate(service + values)), ['one','two']);
  assert.deepEqual(projected(await evaluate('VALUES ?endpoint { <urn:one> <urn:one> <urn:two> }' + service)), ['one','one','two']);
  assert.deepEqual(projected(await evaluate('VALUES (?endpoint ?v) { (<urn:one> "wrong") (<urn:one> "one") }' + service)), ['one']);
});

test('SERVICE variables correlate BIND and triple bindings in either join order', async () => {
  assert.deepEqual(projected(await evaluate('BIND(<urn:one> AS ?endpoint)' + service)), ['one']);
  assert.deepEqual(projected(await evaluate(service + '{ BIND(<urn:one> AS ?endpoint) }')), ['one']);
  assert.deepEqual(projected(await evaluate('?endpoint <urn:enabled> ?tag .' + service, local)), ['one']);
  assert.deepEqual(projected(await evaluate(service + '?endpoint <urn:enabled> ?tag .', local)), ['one']);
  await assert.rejects(evaluate(service + 'BIND(<urn:one> AS ?endpoint)'), /BIND variable already in scope/);
});

test('SERVICE SILENT resolves known providers and preserves rows on failure', async () => {
  assert.deepEqual(projected(await evaluate('VALUES ?endpoint { <urn:one> } SERVICE SILENT ?endpoint ' + body)), ['one']);
  for (const endpoint of ['<urn:missing>', '42']) {
    const rows = await evaluate(`VALUES (?endpoint ?tag) { (${endpoint} "keep") } SERVICE SILENT ?endpoint ${body}`);
    assert.deepEqual(projected(rows), ['<unbound>']); assert.equal(rows[0].get('tag').value, 'keep');
  }
  await assert.rejects(evaluate('VALUES ?endpoint { <urn:missing> }' + service), /SERVICE|endpoint/i);
  assert.deepEqual(await evaluate('VALUES ?endpoint {}' + service), []);
});

test('nested variable SERVICE uses the same registered provider scope', async () => {
  assert.deepEqual(projected(await evaluate(`SERVICE <urn:outer> { VALUES ?endpoint { <urn:one> } ${service} }`)), ['one']);
});

test('Dataset, serialized output and registered node paths use corrected correlation', async () => {
  const dataset = await core.parse('', {format:'ntriples'}), sparql = query(values + service);
  try {
    assert.deepEqual(projected(await dataset.query(sparql)), ['one','two']);
    const result = await core.run(await core.node('shippedEvaluator', {query:sparql}), dataset);
    assert.deepEqual(projected(result.graph), ['one','two']);
    // Existing component metadata is retained; this is not a security certificate.
    assert.equal(result.evidence.at(-1).status, 'proved');
    const xml = await core.queryRaw('', sparql, {dataFormat:'ntriples',output:'xml'});
    assert.match(xml, /sparql-results#/); assert.match(xml, />one</); assert.match(xml, />two</);
    const stored = await core.query(dataset, sparql, {output:'xml'});
    assert.match(stored, />one</); assert.match(stored, />two</);
  } finally { dataset.dispose(); }
});

test('a provider absent from the operation scope stays denied, including SILENT', async () => {
  await core.clearServiceEndpoints();
  try {
    await assert.rejects(evaluate('VALUES ?endpoint { <urn:one> }' + service), /SERVICE|endpoint/i);
    assert.deepEqual(projected(await evaluate('VALUES ?endpoint { <urn:one> } SERVICE SILENT ?endpoint ' + body)), ['<unbound>']);
  } finally { await providers(); }
});
