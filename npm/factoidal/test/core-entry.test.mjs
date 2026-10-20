// '@factoidal/core/core' — the core engine (l4factoidal-core.wasm) against
// the full engine of '@factoidal/core' (l4factoidal.wasm).
// https://github.com/danbri/factoidal/issues/713 stage 4.
//
// The core module is the same Lean library with a dispatch table that
// reaches a subset (formal/lean4/Wasm/CoreDispatch.lean): parse and
// serialise the RDF syntaxes of Wasm/Ops/Parse.lean's table, SPARQL 1.1 and
// 1.2 query and update over text and handles, canonicalisation, the RDFS and
// OWL 2 RL closures, SHACL, the lenient parse. These cases check that
//   * the core entry gives the same answers as the full entry for those
//     functions (one positive and one negative case per family);
//   * every other function rejects with an error naming '@factoidal/core';
//   * capabilities() reports the module that is loaded;
//   * the core entry exports the same names as the full entry;
//   * the core module is smaller than the full module.
// Both engines load in this one process (two module instances).

import test from 'node:test';
import assert from 'node:assert/strict';
import { statSync } from 'node:fs';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';

import * as full from '../index.mjs';
import * as core from '../core.mjs';

const require = createRequire(import.meta.url);
const assetsDir = fileURLToPath(new URL('../l4-assets/', import.meta.url));

const TTL = `@prefix : <http://example.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
:a a :C ; :p "x" ; :q :b .
:C rdfs:subClassOf :D .
:b :p "y" .
`;
const SELECT = 'PREFIX : <http://example.org/> SELECT ?s ?o WHERE { ?s :p ?o } ORDER BY ?o';

const rowsText = (rows) => rows.map((m) => [...m].map(([k, v]) => `${k}=${v.value}`).join(' ')).join('\n');
const sortedLines = (nq) => nq.split('\n').filter(Boolean).sort().join('\n');

test('core entry: capabilities() reports the core module, full entry the full module', async () => {
  const c = await core.capabilities();
  const f = await full.capabilities();
  assert.equal(c.profile, 'core');
  assert.equal(f.profile, 'full');
  for (const k of ['shacl', 'owlClosure', 'entailment', 'datasetHandles', 'sparql12',
    'parseDiagnostics', 'turtlePrefixes']) {
    assert.equal(c[k], true, `core capabilities().${k}`);
    assert.equal(f[k], true, `full capabilities().${k}`);
  }
  for (const k of ['shex', 'tableau', 'rml', 'csvw', 'jsonld', 'xml', 'xpath', 'xslt',
    'rif', 'mathml', 'xforms', 'jsonSchema', 'schematron', 'toan', 'matrix', 'hdt',
    'vcCrypto', 'store', 'didKey']) {
    assert.equal(c[k], false, `core capabilities().${k}`);
    assert.equal(f[k], true, `full capabilities().${k}`);
  }
  assert.equal(core.engine, 'lean4-wasm-core');
  assert.equal(full.engine, 'lean4-wasm');
});

test('core entry: the ops reflection names the engine and what only the full engine serves', async () => {
  const ce = await core.loadEngine();
  const fe = await full.loadEngine();
  const cr = ce.call('ops', []);
  const fr = fe.call('ops', []);
  assert.equal(cr.engine, 'core');
  assert.equal(fr.engine, 'full');
  // Every core op is a full op; core ops and full-only ops are the full ops.
  for (const op of cr.ops) assert.ok(fr.ops.includes(op), `core op ${op} is in the full table`);
  const fullNames = new Set([...fr.ops, ...fr.blobIoOps].filter((o) => o !== 'ops'));
  const split = new Set([...cr.ops, ...cr.fullOnlyOps]);
  assert.deepEqual([...fullNames].filter((o) => !split.has(o)), []);
  assert.deepEqual([...split].filter((o) => !fullNames.has(o)), []);
  assert.deepEqual(cr.fullOnlyFormats, ['jsonld', 'json-ld', 'application/ld+json']);
});

test('core entry: parse, query, update and serialize answer as the full entry', async () => {
  for (const format of ['turtle', 'ntriples', 'nquads', 'trig']) {
    const text = format === 'turtle' || format === 'trig' ? TTL
      : (await full.serialize(await full.parse(TTL), { format: 'nquads' }));
    const dc = await core.parse(text, { format });
    const df = await full.parse(text, { format });
    assert.equal(dc.size, df.size, `${format}: same quad count`);
    assert.equal(rowsText(await core.query(dc, SELECT)), rowsText(await full.query(df, SELECT)));
  }
  const rdfxml = '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" ' +
    'xmlns:e="http://example.org/"><rdf:Description rdf:about="http://example.org/a">' +
    '<e:p>x</e:p></rdf:Description></rdf:RDF>';
  assert.equal((await core.parse(rdfxml, { format: 'rdfxml' })).size, 1);
  const dc = await core.parse(TTL);
  const df = await full.parse(TTL);
  const upd = 'PREFIX : <http://example.org/> INSERT DATA { :c :p "z" }';
  assert.equal(
    sortedLines(await core.serialize(await core.update(dc, upd), { format: 'nquads' })),
    sortedLines(await full.serialize(await full.update(df, upd), { format: 'nquads' })));
  assert.equal(await core.serialize(dc, { format: 'turtle' }),
    await full.serialize(df, { format: 'turtle' }));
});

test('core entry: a parse error and a query error reject as on the full entry', async () => {
  const bad = '@prefix : <http://example.org/> .\n:a :p .\n';
  const ce = await core.parse(bad).then(() => null, (e) => e);
  const fe = await full.parse(bad).then(() => null, (e) => e);
  assert.ok(ce instanceof core.ParseError, 'core: ParseError');
  assert.equal(ce.line, fe.line);
  assert.equal(ce.column, fe.column);
  await assert.rejects(core.query(await core.parse(TTL), 'SELECT WHERE'), /./);
});

test('core entry: dataset handles and SPARQL 1.2 answer as the full entry', async () => {
  const hc = await core.openDataset(TTL);
  const hf = await full.openDataset(TTL);
  assert.equal(rowsText(await hc.query(SELECT)), rowsText(await hf.query(SELECT)));
  const q12 = 'PREFIX : <http://example.org/> SELECT ?s WHERE { ?s :p ?o . FILTER(isLiteral(?o)) }';
  assert.equal(rowsText(await hc.query(q12, { sparql12: true })),
    rowsText(await hf.query(q12, { sparql12: true })));
  hc.dispose();
  hf.dispose();
});

test('core entry: canonicalize, the closures and SHACL answer as the full entry', async () => {
  const bn = '_:x <http://example.org/p> _:y .\n_:y <http://example.org/p> _:x .\n';
  assert.equal(await core.canonicalize(bn, { format: 'nquads' }),
    await full.canonicalize(bn, { format: 'nquads' }));
  for (const mode of ['RDFS', 'OWL-RL']) {
    const c = await core.owlClosure(TTL, mode);
    const f = await full.owlClosure(TTL, mode);
    assert.equal(sortedLines(c.toNQuads()), sortedLines(f.toNQuads()), mode);
  }
  await assert.rejects(core.owlClosure(TTL, 'no-such-mode'), /mode must be/);
  const shapes = `@prefix sh: <http://www.w3.org/ns/shacl#> . @prefix : <http://example.org/> .
:S a sh:NodeShape ; sh:targetClass :C ; sh:property [ sh:path :q ; sh:minCount 2 ] .`;
  const c = await core.shaclValidate(TTL, shapes);
  const f = await full.shaclValidate(TTL, shapes);
  assert.equal(c.conforms, false);
  assert.equal(c.conforms, f.conforms);
  assert.equal(c.report.size, f.report.size);
});

test('core entry: the lenient parse answers as the full entry', async () => {
  const text = '<http://x/a> <http://x/p> "1" .\n<http://x/b> <http://x/p> .\n';
  const c = await core.parse(text, { format: 'ntriples', lenient: true });
  const f = await full.parse(text, { format: 'ntriples', lenient: true });
  assert.equal(c.size, 1);
  assert.equal(c.size, f.size);
  assert.equal(c.diagnostics.length, f.diagnostics.length);
});

// Each function outside the core subset, with arguments the full engine
// accepts: the core entry rejects, naming '@factoidal/core'.
const FULL_ONLY_CALLS = [
  ['xmlWellformed', (api) => api.xmlWellformed('<a/>')],
  ['xpathEval', (api) => api.xpathEval('<a><b/></a>', 'count(//b)')],
  ['jsonldToRdf', (api) => api.jsonldToRdf('{"@id":"http://e/a","http://e/p":"v"}')],
  ['shexValidate', (api) => api.shexValidate('<http://e/a> <http://e/p> "v" .',
    'PREFIX e: <http://e/>\ne:S { e:p LITERAL }', 'http://e/a', 'http://e/S', { format: 'ntriples' })],
  ['owlIsConsistent', (api) => api.owlIsConsistent(TTL)],
  ['vcSha256Hex', (api) => api.vcSha256Hex('abc')],
  ['toanSimplify', (api) => api.toanSimplify({ kind: 'num', value: 1 })],
  ['clParse', (api) => api.clParse('(P a)')],
  ['matrixDeterminant', (api) => api.matrixDeterminant([[1, 0], [0, 1]])],
  ['didKeyResolve', (api) => api.didKeyResolve('did:key:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK')],
  ['openStore', (api) => api.openStore(() => new Uint8Array(0))],
  ['queryHdt', (api) => api.queryHdt(new Uint8Array(8), 'ASK { ?s ?p ?o }')],
];

for (const [name, call] of FULL_ONLY_CALLS) {
  test(`core entry: ${name} rejects naming '@factoidal/core'`, async () => {
    const err = await call(core).then(() => null, (e) => e);
    assert.ok(err instanceof Error, `${name} on the core entry must reject`);
    assert.match(err.message, /'@factoidal\/core'/, err.message);
    assert.match(err.message, /core engine/, err.message);
  });
}

test('core entry: the full entry serves the same calls (no core-only refusal there)', async () => {
  for (const [name, call] of FULL_ONLY_CALLS) {
    if (name === 'openStore' || name === 'queryHdt') continue; // need real store / HDT bytes
    const err = await call(full).then(() => null, (e) => e);
    if (err) assert.doesNotMatch(err.message, /core engine/, `${name}: ${err.message}`);
  }
});

test('core entry: JSON-LD text rejects naming the full entry; the full entry reads it', async () => {
  const jl = '{"@id":"http://e/a","http://e/p":"v"}';
  await assert.rejects(core.parse(jl, { format: 'jsonld' }), /'@factoidal\/core'/);
  assert.equal((await full.parse(jl, { format: 'jsonld' })).size, 1);
  // The raw dispatch answers the engine's own refusal, with servedBy "full".
  const eng = await core.loadEngine();
  const err = (() => { try { eng.call('xmlWellformed', ['<a/>']); return null; } catch (e) { return e; } })();
  assert.ok(err && err.envelope && err.envelope.servedBy === 'full', 'raw refusal has servedBy');
});

test('core entry: exports the same names as the full entry (Node and browser)', async () => {
  const names = (m) => Object.keys(m).filter((k) => k !== 'default').sort();
  assert.deepEqual(names(core), names(full));
  const cb = await import('../core-browser.js');
  const fb = await import('../browser.js');
  assert.deepEqual(names(cb), names(fb));
  const cjs = require('../core.js');
  assert.equal(typeof cjs.parse, 'function');
  assert.equal(cjs.parse, core.parse, 'require() and import share one module instance');
});

test('core entry: the core module is smaller than the full module', () => {
  const fullBytes = statSync(assetsDir + 'l4factoidal.wasm').size;
  const coreBytes = statSync(assetsDir + 'l4factoidal-core.wasm').size;
  // The bound is loose on purpose: it fails when a change makes the core
  // dispatch reach most of the library again, not on ordinary growth.
  assert.ok(coreBytes < 0.7 * fullBytes,
    `core ${coreBytes} bytes is not below 70% of full ${fullBytes} bytes`);
});
