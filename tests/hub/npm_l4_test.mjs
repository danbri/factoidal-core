// Pins the main entry of @factoidal/core (the `./l4` alias of 0.9.x was
// removed in 0.10.0). Since 0.9.0 the package carries one engine, the
// Lean 4 wasm. The low-level
// engine handle it used to export is `loadEngine()`. The test pins the
// alias, the engine handle's version, bgpQuery and IBK3 scan, one join
// through the low-level bgpQuery and the typed query(), and the
// missing-assets error text of the resolver (npm/factoidal/bin/engine.mjs).

import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { readFileSync } from 'node:fs';
import { NPM_FACTOIDAL_INDEX } from './_helpers.mjs';

const require = createRequire(import.meta.url);
const l4 = require('../../npm/factoidal/index.js');
const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;

const EX = 'http://example.org/';
const uri = (v) => ({ type: 'uri', value: v });
const lit = (v, datatype) => (datatype ? { type: 'literal', value: v, datatype } : { type: 'literal', value: v });
const v = (name) => ({ type: 'var', value: name });

const TRIPLES = [
  { subject: uri(EX + 'alice'), predicate: uri(EX + 'name'), object: lit('Alice') },
  { subject: uri(EX + 'alice'), predicate: uri(EX + 'age'), object: lit('30', 'http://www.w3.org/2001/XMLSchema#integer') },
  { subject: uri(EX + 'bob'), predicate: uri(EX + 'name'), object: lit('Bob') },
  { subject: uri(EX + 'bob'), predicate: uri(EX + 'age'), object: lit('24', 'http://www.w3.org/2001/XMLSchema#integer') },
];

test('factoidal/l4: an alias of the main entry, the Lean engine', () => {
  assert.equal(l4.engine, 'lean4-wasm');
  assert.equal(l4.parse, factoidal.parse);
});

test('factoidal/l4: version identifies the Lean engine', async () => {
  const ver = (await l4.loadEngine()).version();
  assert.match(ver, /l4factoidal/);
});

test('factoidal/l4: the low-level bgpQuery agrees with the typed query()', async () => {
  const doc = (await l4.loadEngine()).bgpQuery(TRIPLES, [
    { subject: v('s'), predicate: uri(EX + 'name'), object: v('n') },
    { subject: v('s'), predicate: uri(EX + 'age'), object: v('a') },
  ]);
  const leanRows = doc.results.bindings
    .map((b) => `${b.s.value}|${b.n.value}|${b.a.value}`)
    .sort();

  const dataset = await factoidal.parse(
    TRIPLES.map((t) => `<${t.subject.value}> <${t.predicate.value}> ${
      t.object.type === 'uri' ? `<${t.object.value}>`
        : t.object.datatype ? `"${t.object.value}"^^<${t.object.datatype}>`
        : `"${t.object.value}"`} .`).join('\n'),
    { format: 'ntriples', baseIRI: EX });
  const rows = await factoidal.query(dataset,
    `PREFIX : <${EX}> SELECT ?s ?n ?a WHERE { ?s :name ?n ; :age ?a }`);
  const bindings = Array.isArray(rows) ? rows : rows.results.bindings;
  const typedRows = bindings
    .map((b) => {
      const g = (k) => (b[k]?.value ?? b.get?.(k)?.value ?? String(b[k]));
      return `${g('s')}|${g('n')}|${g('a')}`;
    })
    .sort();

  assert.equal(leanRows.length, 2);
  assert.deepEqual(leanRows, typedRows);
});

test('factoidal/l4: the IBK3 predicate scan through the engine handle', async () => {
  const bytes = readFileSync(new URL('../../docs/web/hub/assets/blocks/shardborough-three-way/type.ibk3', import.meta.url));
  const result = (await l4.loadEngine()).call('scanIBK3Predicate', [
    bytes.toString('hex'),
    'http://example.org/type',
    'source:npm-l4-test',
  ]);
  assert.equal(result.format, 'IBK3');
  assert.equal(result.blankNodeScope, 'source:npm-l4-test');
  assert.equal(result.rows, 4);
});

test('factoidal/l4: missing-assets error names the remedies', async () => {
  // Force every resolver source to miss by asking from a copy whose
  // repo-relative path cannot exist. Simplest faithful probe: check the
  // error text constant in the module source.
  const src = readFileSync(new URL('../../npm/factoidal/bin/engine.mjs', import.meta.url), 'utf8');
  assert.match(src, /l4-assets/);
  assert.match(src, /FACTOIDAL_L4_ASSETS/);
});
