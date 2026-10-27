// Literal values: literalValue, isValidLiteral, canonicalLiteral,
// literalFromValue (https://github.com/danbri/factoidal/issues/1051 items 1-3).
// The engine decides every answer (formal/lean4/L4Factoidal/RDF/LiteralValue.lean);
// these are plain assertions against the wasm built from the same commit.

import test from 'node:test';
import assert from 'node:assert/strict';
import {
  ready, capabilities, dataFactory, FactoidalError,
  literalValue, isValidLiteral, canonicalLiteral, literalFromValue,
} from '../index.mjs';

const XSD = 'http://www.w3.org/2001/XMLSchema#';
const RDF = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#';
const lit = (v, dt) => dataFactory.literal(v, dataFactory.namedNode(XSD + dt));

await ready();

test('the engine has the literal-value ops', async () => {
  assert.equal((await capabilities()).literalValues, true);
});

test('literalValue: integers, bounds, canonical form, exact number', () => {
  assert.deepEqual(literalValue(lit('01', 'integer')), {
    datatype: XSD + 'integer', recognized: true, valid: true,
    value: { kind: 'decimal', decimal: '1', integer: true, number: 1 }, canonical: '1',
  });
  assert.equal(literalValue(lit('+99', 'int')).value.number, 99);
  assert.equal(isValidLiteral(lit('2147483648', 'int')), false);
  assert.equal(isValidLiteral(lit('2147483647', 'int')), true);
  assert.equal(isValidLiteral(lit('-129', 'byte')), false);
  assert.equal(isValidLiteral(lit(' 3 ', 'int')), false, 'RDF 1.1 Semantics 7: no whiteSpace processing');
  // A value a JavaScript number does not hold exactly is a decimal string only.
  const big = literalValue(lit('9007199254740993', 'integer')).value;
  assert.equal(big.decimal, '9007199254740993');
  assert.equal('number' in big, false);
});

test('literalValue: decimal, double, float', () => {
  assert.deepEqual(literalValue(lit('0.50', 'decimal')).value,
    { kind: 'decimal', decimal: '0.5', integer: false, number: 0.5 });
  assert.equal('number' in literalValue(lit('0.1', 'decimal')).value, false);
  const d = literalValue(lit('0.1', 'double'));
  assert.equal(d.value.number, 0.1);
  assert.equal(d.value.decimal, '0.1000000000000000055511151231257827021181583404541015625');
  assert.equal(d.canonical, '1.0E-1');
  const f = literalValue(lit('0.1', 'float'));
  assert.equal(f.value.number, Math.fround(0.1));
  assert.equal(f.canonical, '1.0E-1');
  assert.ok(Object.is(literalValue(lit('-0', 'double')).value.number, -0));
  assert.ok(Number.isNaN(literalValue(lit('NaN', 'double')).value.number));
  assert.equal(literalValue(lit('-INF', 'float')).value.number, -Infinity);
  assert.equal(isValidLiteral(lit('Infinity', 'double')), false);
  assert.equal(literalValue(lit('1e300', 'double')).value.number, 1e300);
});

test('literalValue: boolean, strings, date/time, duration, binary', () => {
  assert.deepEqual(literalValue(lit('1', 'boolean')).value, { kind: 'boolean', boolean: true });
  assert.equal(literalValue(lit('1', 'boolean')).canonical, 'true');
  assert.equal(isValidLiteral(lit('yes', 'boolean')), false);
  assert.equal(isValidLiteral(lit('a  b', 'token')), false);
  assert.deepEqual(literalValue(dataFactory.literal('x')).value, { kind: 'string', string: 'x' });
  assert.deepEqual(literalValue(lit('2026-10-27T10:30:15.250+01:00', 'dateTime')), {
    datatype: XSD + 'dateTime', recognized: true, valid: true,
    value: { kind: 'dateTime', year: 2026, month: 10, day: 27, hour: 10, minute: 30,
      second: '15.25', timezoneOffset: 60 },
    canonical: '2026-10-27T10:30:15.25+01:00',
  });
  assert.equal(isValidLiteral(lit('2026-02-30', 'date')), false);
  assert.deepEqual(literalValue(lit('P0Y14M', 'duration')).value,
    { kind: 'duration', months: 14, seconds: '0' });
  assert.equal(literalValue(lit('P0Y14M', 'duration')).canonical, 'P1Y2M');
  assert.equal(literalValue(lit('0fb7', 'hexBinary')).canonical, '0FB7');
});

test('literalValue: rdf:langString, XMLLiteral, JSON, unknown datatype', () => {
  assert.deepEqual(literalValue(dataFactory.literal('chat', 'fr')).value,
    { kind: 'langString', string: 'chat', language: 'fr' });
  assert.equal(isValidLiteral(dataFactory.literal('<a>b</a>', dataFactory.namedNode(RDF + 'XMLLiteral'))), true);
  assert.equal(isValidLiteral(dataFactory.literal('<a>b', dataFactory.namedNode(RDF + 'XMLLiteral'))), false);
  assert.equal(isValidLiteral(dataFactory.literal('{"a":1}', dataFactory.namedNode(RDF + 'JSON'))), true);
  const u = literalValue(dataFactory.literal('x', dataFactory.namedNode('http://example.org/dt')));
  assert.deepEqual(u, { datatype: 'http://example.org/dt', recognized: false, valid: null });
  assert.equal(isValidLiteral(dataFactory.literal('x', dataFactory.namedNode('http://example.org/dt'))), null);
  assert.throws(() => literalValue(dataFactory.namedNode('http://e/')), TypeError);
});

test('canonicalLiteral: the canonical form, same datatype; null when none', () => {
  const c = canonicalLiteral(lit('0010.50', 'decimal'));
  assert.equal(c.value, '10.5');
  assert.equal(c.datatype.value, XSD + 'decimal');
  assert.equal(canonicalLiteral(lit('100', 'double')).value, '1.0E2');
  assert.equal(canonicalLiteral(lit('x', 'integer')), null);
  assert.equal(canonicalLiteral(dataFactory.literal('x', dataFactory.namedNode('http://example.org/dt'))), null);
  const l = canonicalLiteral(dataFactory.literal('chat', 'fr'));
  assert.equal(l.value, 'chat');
  assert.equal(l.language, 'fr');
});

test('literalFromValue: the engine table with no datatype', () => {
  const t = (v) => { const l = literalFromValue(v); return [l.value, l.datatype.value.slice(XSD.length)]; };
  assert.deepEqual(t(99), ['99', 'integer']);
  assert.deepEqual(t(-0), ['-0.0E0', 'double']);
  assert.deepEqual(t(1.5), ['1.5E0', 'double']);
  assert.deepEqual(t(2 ** 53), ['9.007199254740992E15', 'double']);
  assert.deepEqual(t(NaN), ['NaN', 'double']);
  assert.deepEqual(t(12345678901234567890n), ['12345678901234567890', 'integer']);
  assert.deepEqual(t(true), ['true', 'boolean']);
  assert.deepEqual(t('x'), ['x', 'string']);
  assert.deepEqual(t(new Date(Date.UTC(2026, 9, 27, 12, 0, 0, 123))), ['2026-10-27T12:00:00.123Z', 'dateTime']);
  assert.deepEqual(t(new Date(0)), ['1970-01-01T00:00:00Z', 'dateTime']);
  assert.throws(() => literalFromValue(new Date(NaN)), FactoidalError);
  assert.throws(() => literalFromValue(Symbol('x')), TypeError);
  assert.throws(() => literalFromValue({}), TypeError);
});

test('literalFromValue: a named datatype', () => {
  const t = (v, dt) => { const l = literalFromValue(v, { datatype: dt }); return [l.value, l.datatype.value]; };
  assert.deepEqual(t(99, 'int'), ['99', XSD + 'int']);
  assert.deepEqual(t(99, XSD + 'long'), ['99', XSD + 'long']);
  assert.deepEqual(t(99, dataFactory.namedNode(XSD + 'short')), ['99', XSD + 'short']);
  assert.deepEqual(t(14, 'float'), ['1.4E1', XSD + 'float']);
  assert.deepEqual(t(14, 'double'), ['1.4E1', XSD + 'double']);
  assert.deepEqual(t(0.1, 'float'), ['1.0E-1', XSD + 'float']);
  assert.deepEqual(t(2 ** 60, 'integer'), ['1152921504606846976', XSD + 'integer']);
  assert.deepEqual(t(0.5, 'decimal'), ['0.5', XSD + 'decimal']);
  assert.deepEqual(t('0.1', 'decimal'), ['0.1', XSD + 'decimal']);
  assert.deepEqual(t('01', 'integer'), ['01', XSD + 'integer']);
  assert.deepEqual(t(9223372036854775807n, 'long'), ['9223372036854775807', XSD + 'long']);
  assert.deepEqual(t(new Date(0), 'dateTimeStamp'), ['1970-01-01T00:00:00Z', XSD + 'dateTimeStamp']);
  for (const [v, dt] of [[1.5, 'int'], [300, 'byte'], [-1, 'nonNegativeInteger'], [99, 'string'],
    ['x', 'integer'], [true, 'integer'], [9223372036854775808n, 'long'], [1e39, 'float'],
    [new Date(0), 'date'], [1, 'http://example.org/dt'], [1, 'anyAtomicType']]) {
    assert.throws(() => literalFromValue(v, { datatype: dt }),
      (err) => err instanceof FactoidalError && err.code === 'literal.value', `${String(v)} ${dt}`);
  }
});

test('literalFromValue and literalValue: the value maps back', () => {
  for (const [v, dt] of [[99, undefined], [0.1, undefined], [1e21, undefined], [true, undefined],
    [-7, 'byte'], [0.1, 'double'], [2 ** 60, 'unsignedLong'], [new Date(1793102400123), undefined]]) {
    const l = literalFromValue(v, dt ? { datatype: dt } : undefined);
    const r = literalValue(l);
    assert.equal(r.valid, true, l.value);
    assert.equal(r.canonical, canonicalLiteral(l).value);
    if (typeof v === 'number') assert.equal(r.value.number, v);
  }
});

test('an extension function may answer a Date (engine table, xsd:dateTime)', async () => {
  const { registerExtensionFunction, unregisterExtensionFunction, query } = await import('../index.mjs');
  const iri = 'http://example.org/fn/epoch';
  await registerExtensionFunction(iri, () => new Date(0));
  try {
    const rows = await query('<http://e/a> <http://e/p> "x" .',
      `SELECT ?d WHERE { BIND(<${iri}>() AS ?d) }`, { format: 'ntriples' });
    assert.equal(rows[0].get('d').value, '1970-01-01T00:00:00Z');
    assert.equal(rows[0].get('d').datatype.value, XSD + 'dateTime');
  } finally {
    await unregisterExtensionFunction(iri);
  }
});

test('before the engine is loaded the functions throw, naming ready()', async () => {
  const { createApi } = await import('../api.mjs');
  const api = createApi(() => { throw new Error('not loaded in this test'); });
  assert.throws(() => api.literalValue(lit('1', 'integer')),
    (err) => err instanceof FactoidalError && /ready\(\)/.test(err.message));
  assert.throws(() => api.literalFromValue(1),
    (err) => err instanceof FactoidalError && /ready\(\)/.test(err.message));
});
