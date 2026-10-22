// One error model for the package (https://github.com/danbri/factoidal/issues/882
// item 4, https://github.com/danbri/factoidal/issues/901 KR 3.1).
//
// The engine decides every code, spec section and position
// (formal/lean4/Wasm/Ops/ErrorModel.lean). This file checks:
//   1. each declared code is triggered through the public API, with its code,
//      position and spec;
//   2. every op of the engine's dispatch table (op `ops`) answers an error
//      only with a declared code (the list of ops and of codes come from the
//      engine, anti-pattern 30);
//   3. the README "Errors" table and the d.ts code union are the engine's
//      list. Run with UPDATE_ERRORS_TABLE=1 to rewrite the README block.

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import * as f from '../index.mjs';

const tables = await f.engineTables();
const CODES = tables.errorCodes.map((c) => c.code);
const SPEC = Object.fromEntries(tables.errorCodes.map((c) => [c.code, c.spec || null]));
const eng = await f.loadEngine();

const NT = '<http://e/a> <http://e/p> "x" .\n';
const TT = '<http://e/a> <http://e/p> <<( <http://e/a> <http://e/p> <http://e/o> )>> .\n';
const TURTLE_GRAMMAR = 'https://www.w3.org/TR/rdf12-turtle/#sec-grammar';
const NT_GRAMMAR = 'https://www.w3.org/TR/rdf12-n-triples/#n-triples-grammar';

// The FactoidalError a promise (or a function) rejects with.
async function rejection(fn) {
  try {
    await fn();
  } catch (err) {
    return err;
  }
  assert.fail('expected a rejection');
}

// The envelope of a raw engine call that refuses (the loadEngine() handle
// throws an Error whose `envelope` is the engine's answer).
function rawRefusal(op, args, blob) {
  try {
    if (blob) eng.callBlobIO(op, args, blob);
    else eng.call(op, args);
  } catch (err) {
    assert.ok(err.envelope, `${op}: a refusal carries the engine envelope`);
    return err.envelope;
  }
  assert.fail(`${op}: expected a refusal`);
}

function check(err, code, spec, position) {
  assert.ok(err instanceof f.FactoidalError, `a FactoidalError, got ${err && err.name}: ${err && err.message}`);
  assert.equal(err.name, 'FactoidalError');
  assert.equal(err.code, code, err.message);
  assert.ok(CODES.includes(err.code));
  assert.equal(err.spec, spec === undefined ? SPEC[code] : spec);
  if (position === null) assert.equal(err.position, null);
  else if (position) assert.deepEqual(err.position, position);
  assert.ok(err.message.length > 0);
}

function checkEnvelope(env, code) {
  assert.equal(env.ok, false);
  assert.equal(env.code, code, env.error);
  assert.equal(env.spec ?? null, SPEC[code]);
}

const covered = new Set();
function codeTest(code, name, fn) {
  covered.add(code);
  test(`${code}: ${name}`, fn);
}

const ds = await f.parse(NT, 'ntriples');
const tt = await f.parse(TT, 'turtle12');

codeTest('parse.syntax', 'Turtle, with line, column, offset, byteOffset', async () => {
  const err = await rejection(() => f.parse('<http://e/a> <http://e/p> .', 'turtle'));
  check(err, 'parse.syntax', TURTLE_GRAMMAR, { line: 1, column: 27, offset: 26, byteOffset: 26 });
  assert.equal(err.format, 'turtle');
});
test('parse.syntax: position offset is UTF-16, byteOffset UTF-8', async () => {
  const text = '<http://e/\u{1F600}> <http://e/p> .';
  const err = await rejection(() => f.parse(text, 'turtle'));
  check(err, 'parse.syntax', TURTLE_GRAMMAR);
  assert.equal(text.slice(err.position.offset), '.');
  assert.equal(err.position.byteOffset, new TextEncoder().encode(text.slice(0, err.position.offset)).length);
});
test('parse.syntax: missing RDF object is not an invalid IRI', async () => {
  const text = '<urn:s> <urn:p> .';
  for (const format of ['ntriples', 'ntriples12', 'nquads', 'nquads12']) {
    const err = await rejection(() => f.parse(text, { format }));
    const spec = format.startsWith('nquads')
      ? 'https://www.w3.org/TR/rdf12-n-quads/#sec-grammar' : NT_GRAMMAR;
    check(err, 'parse.syntax', spec, { line: 1, column: 17, offset: 16, byteOffset: 16 });
    assert.equal(err.format, format);
  }
});
test('parse.syntax: RDF/XML has the RDF/XML grammar and no position', async () => {
  const err = await rejection(() => f.parse('<rdf:RDF', 'rdfxml'));
  check(err, 'parse.syntax', 'https://www.w3.org/TR/rdf12-xml/#section-Infoset-Grammar', null);
});
codeTest('parse.rdf12-required', 'a triple term read as RDF 1.1 Turtle', async () => {
  const err = await rejection(() => f.parse(TT, 'turtle'));
  check(err, 'parse.rdf12-required', undefined, { line: 1, column: 27, offset: 26, byteOffset: 26 });
});
codeTest('term.invalid-iri', 'an IRIREF with a space', async () => {
  const err = await rejection(() => f.parse('<a b> <http://e/p> "x" .', 'ntriples'));
  check(err, 'term.invalid-iri', undefined, { line: 1, column: 3, offset: 2, byteOffset: 2 });
});
test('term.invalid-iri: an RDF/JS NamedNode that is not an IRI', async () => {
  const q = f.dataFactory.quad(f.dataFactory.namedNode('a b'), f.dataFactory.namedNode('http://e/p'),
    f.dataFactory.literal('x'));
  check(await rejection(() => f.fromQuads([q])), 'term.invalid-iri', undefined, null);
});
codeTest('term.invalid-langtag', 'a language tag that starts with a digit', async () => {
  const err = await rejection(() => f.parse('<http://e/a> <http://e/p> "x"@1-- .', 'ntriples'));
  check(err, 'term.invalid-langtag', undefined, { line: 1, column: 31, offset: 30, byteOffset: 30 });
});
codeTest('term.invalid', 'a literal in subject position', async () => {
  const q = f.dataFactory.quad(f.dataFactory.literal('s'), f.dataFactory.namedNode('http://e/p'),
    f.dataFactory.literal('x'));
  check(await rejection(() => f.fromQuads([q])), 'term.invalid', undefined, null);
});
codeTest('query.syntax', 'position counts into the query text', async () => {
  const err = await rejection(() => f.query(ds, 'SELECT *\nWHERE { ?s }'));
  check(err, 'query.syntax');
  assert.equal(err.position.line, 2);
  assert.equal(typeof err.position.byteOffset, 'number');
});
test('query.syntax: SPARQL 1.2 query names the SPARQL 1.2 grammar', async () => {
  const err = await rejection(() => f.query(ds, 'SELEC * {}', { version: '1.2' }));
  check(err, 'query.syntax', 'https://www.w3.org/TR/sparql12-query/#grammar');
});
codeTest('query.failed', 'an unregistered SERVICE endpoint', async () => {
  const err = await rejection(() => f.query(ds, 'SELECT * { SERVICE <http://unregistered.example/> { ?s ?p ?o } }'));
  check(err, 'query.failed');
});
codeTest('update.syntax', 'an unclosed INSERT DATA', async () => {
  const err = await rejection(() => f.update(ds, 'INSERT DATA { '));
  check(err, 'update.syntax');
  assert.equal(err.position.line, 1);
});
codeTest('update.failed', 'LOAD has no host to fetch from', async () => {
  const env = rawRefusal('updateDataset', [NT, 'LOAD <http://unreachable.example/x.ttl>']);
  checkEnvelope(env, 'update.failed');
});
codeTest('format.unknown', 'parse and serialize', async () => {
  check(await rejection(() => f.parse('x', 'bogus')), 'format.unknown');
  check(await rejection(() => f.serialize(ds, 'bogus')), 'format.unknown');
  check(await rejection(() => ds.serialize({ format: 'bogus' })), 'format.unknown');
});
codeTest('serialize.unsupported-rdf12', 'a triple term written as RDF 1.1 N-Triples', async () => {
  check(await rejection(() => f.serialize(tt, { format: 'ntriples', version: '1.1' })),
    'serialize.unsupported-rdf12');
});
codeTest('serialize.failed', 'N-Quads text the writer cannot read', async () => {
  checkEnvelope(rawRefusal('serializeTurtle', ['garbage']), 'serialize.failed');
});
codeTest('canon.unsupported-rdf12', 'RDFC-1.0 of a triple term', async () => {
  check(await rejection(() => f.canonicalize(tt)), 'canon.unsupported-rdf12');
});
codeTest('canon.failed', 'canonicalizeToNQuads of text that is not N-Quads', async () => {
  checkEnvelope(rawRefusal('canonicalizeToNQuads', ['garbage']), 'canon.failed');
});
codeTest('owl.unsupported-rdf12', 'OWL 2 DL consistency of a triple term', async () => {
  check(await rejection(() => f.owlIsConsistent(tt)), 'owl.unsupported-rdf12');
});
codeTest('reason.failed', 'owlClosure of text that is not N-Quads', async () => {
  checkEnvelope(rawRefusal('owlClosure', ['garbage', 'rdfs']), 'reason.failed');
});
codeTest('regime.refused', 'an x-ikl-* regime', async () => {
  check(await rejection(() => f.query(ds, 'ASK {}', { entail: 'x-ikl-test' })), 'regime.refused');
});
codeTest('validate.failed', 'SHACL with data that is not N-Quads', async () => {
  checkEnvelope(rawRefusal('shaclValidate', ['garbage', '']), 'validate.failed');
});
codeTest('xml.failed', 'an XPath expression the engine cannot read', async () => {
  check(await rejection(() => f.xpathEval('<a/>', '///')), 'xml.failed');
});
codeTest('crypto.failed', 'an Ed25519 secret key that is not hex', async () => {
  check(await rejection(() => f.vcEd25519SecretToPublic('zz')), 'crypto.failed');
});
codeTest('store.failed', 'a store manifest that is not hex', async () => {
  checkEnvelope(rawRefusal('storeManifestInspect', ['zz']), 'store.failed');
});
codeTest('registry.failed', 'a SERVICE endpoint whose data is not N-Quads', async () => {
  checkEnvelope(rawRefusal('registerServiceEndpoint', ['http://e/s', 'garbage']), 'registry.failed');
});
codeTest('handle.unknown', 'a handle the engine never issued', async () => {
  checkEnvelope(rawRefusal('datasetQuery', ['h999999999', 'ASK {}']), 'handle.unknown');
});
codeTest('handle.disposed', 'every method of a disposed Dataset', async () => {
  const d = await f.parse(NT, 'ntriples');
  d.dispose();
  check(await rejection(() => d.size), 'handle.disposed');
  check(await rejection(() => d.query('ASK {}')), 'handle.disposed');
  check(await rejection(() => f.query(d, 'ASK {}')), 'handle.disposed');
});
codeTest('option.unknown', 'a key parse() does not take', async () => {
  const err = await rejection(() => f.parse('x', { bogus: 1 }));
  check(err, 'option.unknown');
  assert.match(err.message, /bogus/);
  check(await rejection(() => ds.update('INSERT DATA {}', { bogus: 1 })), 'option.unknown');
});
codeTest('option.invalid-value', 'an output outside the table', async () => {
  check(await rejection(() => f.query(ds, 'ASK {}', { output: 'pdf' })), 'option.invalid-value');
  check(await rejection(() => f.owlClosure(ds, 'rho-df')), 'option.invalid-value');
  check(await rejection(() => ds.closure('no-such-regime')), 'option.invalid-value');
});
codeTest('option.conflict', 'SPARQL 1.2 with a results format', async () => {
  check(await rejection(() => f.query(ds, 'ASK {}', { version: '1.2', output: 'csv' })), 'option.conflict');
  check(await rejection(() => ds.serialize({ format: 'ntriples', prefixes: {} })), 'option.conflict');
});
codeTest('capacity.exceeded', 'a byte region above the engine limit', async () => {
  checkEnvelope(rawRefusal('blobEcho', ['999999999999'], new Uint8Array(0)), 'capacity.exceeded');
});
codeTest('call.arity', 'an op called with no arguments', async () => {
  checkEnvelope(rawRefusal('queryDataset', []), 'call.arity');
});
codeTest('call.arguments', 'an arguments document that is not an array', async () => {
  checkEnvelope(rawRefusal('queryDataset', { not: 'an array' }), 'call.arguments');
});
codeTest('op.unknown', 'an op the engine does not have', async () => {
  checkEnvelope(rawRefusal('noSuchOp', []), 'op.unknown');
});
codeTest('op.failed', 'a Common Logic text that does not parse', async () => {
  check(await rejection(() => f.clParse('(((')), 'op.failed');
});
codeTest('host.io', 'a store root with no CURRENT pointer', async () => {
  const err = await rejection(() => f.openStore('/nonexistent-factoidal-store-root'));
  check(err, 'host.io');
  assert.ok(err.cause);
});

test('a wrong JavaScript type is a TypeError', async () => {
  await assert.rejects(() => f.query(ds, 42), TypeError);
  await assert.rejects(() => f.parse('x', 7), TypeError);
});

test('every declared code has a test above', () => {
  assert.deepEqual(CODES.filter((c) => !covered.has(c)), []);
  assert.deepEqual([...covered].filter((c) => !CODES.includes(c)), []);
});

// Every op of the dispatch table, with 0 to 4 empty or junk arguments: an
// error answer always carries a declared code. The op list and the exempt
// list (LWS and Solid: HTTP status model) are the engine's.
test('every op error path of the dispatch table maps to a declared code', () => {
  const reflection = eng.call('ops', []);
  const exempt = new Set(tables.errorModelExemptOps);
  const blobIo = new Set(reflection.blobIoOps);
  const ops = reflection.ops.filter((op) => op !== 'ops' && !exempt.has(op));
  assert.ok(ops.length > 100, `the engine lists its ops (${ops.length})`);
  const argSets = [[], [''], ['', ''], ['x', 'y', 'z'], ['<a> <b> .', 'zz', '', '']];
  let errors = 0;
  for (const op of ops) {
    for (const args of argSets) {
      let env;
      try {
        env = blobIo.has(op) ? eng.callBlobIO(op, args, new Uint8Array(0)).envelope : eng.call(op, args);
      } catch (err) {
        env = err.envelope;
        assert.ok(env, `${op}(${JSON.stringify(args)}): a refusal carries an envelope: ${err.message}`);
      }
      if (env && env.ok === false) {
        errors += 1;
        assert.ok(CODES.includes(env.code), `${op}(${JSON.stringify(args)}) answered code ${env.code}: ${env.error}`);
        if (env.spec !== undefined) assert.equal(typeof env.spec, 'string');
      }
    }
  }
  assert.ok(errors > ops.length, `error paths exercised: ${errors}`);
});

function markdown(rows) {
  const lines = ['| code | specification | meaning |', '|---|---|---|'];
  for (const r of rows) {
    lines.push(`| \`${r.code}\` | ${r.spec ? `<${r.spec}>` : '-'} | ${r.summary} |`);
  }
  return lines.join('\n');
}

test('README errors table is the engine list', () => {
  const path = new URL('../README.md', import.meta.url);
  const readme = readFileSync(path, 'utf8');
  const start = '<!-- errors-table:start (generated by test/errors.test.mjs) -->';
  const end = '<!-- errors-table:end -->';
  const i = readme.indexOf(start);
  const j = readme.indexOf(end);
  assert.ok(i >= 0 && j > i, 'README.md has the errors-table markers');
  const want = `${start}\n${markdown(tables.errorCodes)}\n${end}`;
  const have = readme.slice(i, j + end.length);
  if (have !== want && process.env.UPDATE_ERRORS_TABLE === '1') {
    writeFileSync(path, readme.slice(0, i) + want + readme.slice(j + end.length));
    return;
  }
  assert.equal(have, want, 'run UPDATE_ERRORS_TABLE=1 npm test to regenerate');
});

test('index.d.ts FactoidalErrorCode is the engine list', () => {
  const dts = readFileSync(new URL('../index.d.ts', import.meta.url), 'utf8');
  const m = dts.match(/export type FactoidalErrorCode =([^;]*);/);
  assert.ok(m, 'index.d.ts declares FactoidalErrorCode');
  const declared = [...m[1].matchAll(/'([^']+)'/g)].map((x) => x[1]);
  assert.deepEqual(declared, CODES);
});
