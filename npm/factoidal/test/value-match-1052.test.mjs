// https://github.com/danbri/factoidal/issues/1052: value-based matching of
// literals. sameValue() is SPARQL 1.1 `=` on two terms (sections 17.3 and
// 17.4.1.7), decided by the engine (L4Factoidal.SPARQL.sameValue); the
// Dataset option {match: 'value'} matches a literal object by it. Term matching
// stays the default.
//
// Companion Lean pins: the `#guard`s of
// formal/lean4/L4Factoidal/SPARQL/SameValue.lean (the relation, its symmetry on
// a matrix of 50 terms, the completeness of the index keys) and of
// formal/lean4/Wasm/Ops/Handles.lean (the options argument).
import './helpers.js';

import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
const { parse, ready, sameValue, dataFactory: f, FactoidalError } = require('..');

const XSD = 'http://www.w3.org/2001/XMLSchema#';
const lit = (lex, dt) => f.literal(lex, f.namedNode(XSD + dt));
const s = f.namedNode('http://e/s');
const p = f.namedNode('http://e/p');
const g = f.namedNode('http://e/g');

const NQ = `<http://e/s> <http://e/p> "01"^^<${XSD}integer> .
<http://e/s> <http://e/p> "2.50"^^<${XSD}decimal> .
<http://e/s> <http://e/p> "true"^^<${XSD}boolean> .
<http://e/s> <http://e/p> "abc"^^<${XSD}integer> .
<http://e/s> <http://e/p> "NaN"^^<${XSD}double> .
<http://e/s> <http://e/p> "2000-01-01T00:00:00Z"^^<${XSD}dateTime> .
<http://e/s> <http://e/p> "a"@en-gb .
<http://e/t> <http://e/p> "1"^^<${XSD}int> .
<http://e/s> <http://e/p> "1.0"^^<${XSD}decimal> <http://e/g> .
`;

test('sameValue: one value in several datatypes and spellings', async () => {
  await ready();
  assert.equal(sameValue(lit('01', 'integer'), lit('1', 'integer')), true);
  assert.equal(sameValue(lit('1', 'int'), lit('1.0', 'decimal')), true);
  assert.equal(sameValue(lit('1', 'integer'), lit('1e0', 'double')), true);
  assert.equal(sameValue(lit('true', 'boolean'), lit('1', 'boolean')), true);
  assert.equal(sameValue(lit('2000-01-01T00:00:00Z', 'dateTime'),
    lit('2000-01-01T01:00:00+01:00', 'dateTime')), true);
  assert.equal(sameValue(f.literal('a', 'en-GB'), f.literal('a', 'en-gb')), true);
});

test('sameValue: different values are false', async () => {
  await ready();
  assert.equal(sameValue(lit('1', 'integer'), lit('2', 'integer')), false);
  assert.equal(sameValue(f.literal('a'), f.literal('A')), false);
  assert.equal(sameValue(f.literal('a', 'en'), f.literal('a')), false);
  assert.equal(sameValue(f.namedNode('http://e/a'), f.namedNode('http://e/b')), false);
  assert.equal(sameValue(f.namedNode('http://e/a'), f.literal('a')), false);
  // F&O op:numeric-equal: NaN is not equal to itself.
  assert.equal(sameValue(lit('NaN', 'double'), lit('NaN', 'double')), false);
});

test('sameValue: incomparable is null, distinct from false', async () => {
  await ready();
  assert.equal(sameValue('"a"^^<http://e/dt>', '"b"^^<http://e/dt>'), null);
  assert.equal(sameValue(lit('abc', 'integer'), lit('1', 'integer')), null);
  assert.equal(sameValue(lit('1', 'integer'), lit('true', 'boolean')), null);
  assert.equal(sameValue(lit('2000-01-01T00:00:00', 'dateTime'),
    lit('2000-01-01T00:00:00Z', 'dateTime')), null);
  // The same term is the same value, also for an unknown datatype or an
  // ill-typed literal.
  assert.equal(sameValue('"a"^^<http://e/dt>', '"a"^^<http://e/dt>'), true);
  assert.equal(sameValue(lit('abc', 'integer'), lit('abc', 'integer')), true);
});

test('sameValue: symmetric on every pair of a sample', async () => {
  await ready();
  const terms = [lit('1', 'integer'), lit('1.0', 'decimal'), lit('1', 'float'), lit('0.1', 'float'),
    lit('0.1', 'decimal'), lit('NaN', 'float'), lit('x', 'integer'), lit('1', 'boolean'),
    f.literal('1'), f.literal('1', 'en'), f.namedNode('http://e/a'), f.blankNode('b')];
  for (const a of terms) {
    for (const b of terms) {
      assert.equal(sameValue(a, b), sameValue(b, a), `${a.value} ${b.value}`);
    }
  }
});

test('sameValue: a term that is not a term is a FactoidalError', async () => {
  await ready();
  assert.throws(() => sameValue('not a term', lit('1', 'integer')),
    (e) => e instanceof FactoidalError && e.code === 'term.invalid');
});

test('Dataset.has: term match by default, value match with {match: "value"}', async () => {
  const ds = await parse(NQ, { format: 'nquads' });
  const q = f.quad(s, p, lit('1', 'integer'));
  assert.equal(ds.has(q), false);
  assert.equal(ds.has(q, { match: 'term' }), false);
  assert.equal(ds.has(q, { match: 'value' }), true);
  assert.equal(ds.has(f.quad(s, p, lit('2.5', 'decimal')), { match: 'value' }), true);
  assert.equal(ds.has(f.quad(s, p, lit('2.5', 'double')), { match: 'value' }), true);
  assert.equal(ds.has(f.quad(s, p, lit('1', 'boolean')), { match: 'value' }), true);
  assert.equal(ds.has(f.quad(s, p, lit('2000-01-01T05:00:00+05:00', 'dateTime')), { match: 'value' }), true);
  assert.equal(ds.has(f.quad(s, p, f.literal('a', 'EN-GB')), { match: 'value' }), true);
  assert.equal(ds.has(f.quad(s, p, lit('3', 'integer')), { match: 'value' }), false);
  // The same term is a match also where `=` is false (NaN) or incomparable.
  assert.equal(ds.has(f.quad(s, p, lit('NaN', 'double')), { match: 'value' }), true);
  assert.equal(ds.has(f.quad(s, p, lit('abc', 'integer')), { match: 'value' }), true);
  // The subject and graph positions match by term.
  assert.equal(ds.has(f.quad(f.namedNode('http://e/x'), p, lit('1', 'integer')), { match: 'value' }), false);
  ds.dispose();
});

test('Dataset.match: value match over all graphs and subjects', async () => {
  const ds = await parse(NQ, { format: 'nquads' });
  const one = lit('1', 'integer');
  assert.equal(ds.match(null, null, one).size, 0);
  const m = ds.match(null, null, one, null, { match: 'value' });
  // "01"^^xsd:integer, "1"^^xsd:int (another subject), "1.0"^^xsd:decimal (graph g)
  assert.equal(m.size, 3);
  const objs = [...m].map((q) => `${q.object.value}^^${q.object.datatype.value.slice(XSD.length)}`).sort();
  assert.deepEqual(objs, ['01^^integer', '1.0^^decimal', '1^^int']);
  assert.equal(ds.match(null, null, one, g, { match: 'value' }).size, 1);
  assert.equal(ds.match(null, null, one, f.defaultGraph(), { match: 'value' }).size, 2);
  assert.equal(ds.match(f.namedNode('http://e/t'), null, lit('1.0', 'double'), null, { match: 'value' }).size, 1);
  // A pattern with no literal object is the term match.
  assert.equal(ds.match(s, null, null, null, { match: 'value' }).size, ds.match(s).size);
  for (const d of [m]) d.dispose();
  ds.dispose();
});

test('Dataset.delete: value delete removes every quad of the same value', async () => {
  const ds = await parse(NQ, { format: 'nquads' });
  const before = ds.size;
  ds.delete(f.quad(s, p, lit('1', 'integer')));
  assert.equal(ds.size, before);
  ds.delete(f.quad(s, p, lit('1', 'integer')), { match: 'value' });
  assert.equal(ds.size, before - 1); // "01"^^xsd:integer in the default graph only
  assert.equal(ds.has(f.quad(s, p, lit('1.0', 'decimal'), g)), true);
  ds.delete(f.quad(s, p, lit('1', 'integer'), g), { match: 'value' });
  assert.equal(ds.size, before - 2);
  ds.dispose();
});

test('Dataset value match: the index follows a change of the dataset', async () => {
  const ds = await parse(NQ, { format: 'nquads' });
  const q = f.quad(s, p, lit('7', 'integer'));
  assert.equal(ds.has(q, { match: 'value' }), false);
  ds.add(f.quad(s, p, lit('7.0', 'decimal')));
  assert.equal(ds.has(q, { match: 'value' }), true);
  ds.dispose();
});

test('Dataset match options: the engine refuses an unknown key or mode', async () => {
  const ds = await parse(NQ, { format: 'nquads' });
  const q = f.quad(s, p, lit('1', 'integer'));
  assert.throws(() => ds.has(q, { match: 'values' }),
    (e) => e instanceof FactoidalError && e.code === 'option.invalid-value');
  assert.throws(() => ds.match(null, null, null, null, { mode: 'value' }),
    (e) => e instanceof FactoidalError && e.code === 'option.unknown');
  ds.dispose();
});
