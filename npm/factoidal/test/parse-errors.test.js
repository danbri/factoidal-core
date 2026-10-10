// Strict parsing (issue #344): every function that parses text input
// rejects with a positioned ParseError instead of silently dropping
// data. See README.md's "Parsing is strict by default" section and
// lib/api.mjs's entryResult()/ParseError.
//
// ParseError.offset is a UTF-16 code-unit index into the input string
// (index.d.ts), so text.slice(err.offset) starts at the error. The engine
// counts Unicode scalar values; lib/api.mjs converts. A character outside
// the Basic Multilingual Plane before the error is the case that tells
// the two units apart.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const { xfail, LENIENT_ISSUE } = require('./helpers.js');
const factoidal = require('../index.js');

function assertParseError(err, who) {
  assert.equal(err.name, 'ParseError', `${who}: err.name`);
  assert.ok(err instanceof Error, `${who}: ParseError extends Error`);
  assert.equal(err instanceof factoidal.ParseError, true,
    `${who}: err instanceof the exported ParseError class`);
  assert.equal(typeof err.line, 'number', `${who}: err.line is a number`);
  assert.equal(typeof err.column, 'number', `${who}: err.column is a number`);
  assert.equal(typeof err.offset, 'number', `${who}: err.offset is a number`);
}

test('parse("this is not turtle") rejects with a positioned ParseError', async () => {
  await assert.rejects(
    factoidal.parse('this is not turtle', { format: 'turtle' }),
    (err) => { assertParseError(err, 'parse'); return true; });
});

test('a Turtle document missing one "." rejects with a positioned ParseError', async () => {
  const text =
    '@prefix ex: <http://example.org/> .\n' +
    'ex:a ex:p ex:o\n' +        // missing '.' here
    'ex:b ex:p ex:o2 .\n';
  await assert.rejects(
    factoidal.parse(text, { format: 'turtle' }),
    (err) => {
      assertParseError(err, 'missing-dot');
      assert.equal(err.line, 3, 'the parser reports the failure on the FOLLOWING line');
      return true;
    });
});

test('a relative IRI with no baseIRI rejects with a message mentioning IRI', async () => {
  await assert.rejects(
    factoidal.parse('<a> <b> <c> .', { format: 'turtle' }),
    /IRI/i);
});

test('N-Triples syntax errors reject with a positioned ParseError', async () => {
  await assert.rejects(
    factoidal.parse('<http://x/s> <http://x/p> .', { format: 'ntriples' }),
    (err) => { assertParseError(err, 'ntriples'); return true; });
});

test('N-Quads syntax errors reject with a positioned ParseError', async () => {
  await assert.rejects(
    factoidal.parse('<http://x/s> <http://x/p> .', { format: 'nquads' }),
    (err) => { assertParseError(err, 'nquads'); return true; });
});

test('TriG syntax errors reject with a positioned ParseError', async () => {
  await assert.rejects(
    factoidal.parse('@prefix ex: <http://x/> . GRAPH ex:g { ex:s ex:p', { format: 'trig' }),
    (err) => { assertParseError(err, 'trig'); return true; });
});

test('RDF/XML syntax errors reject (a message only, no position -- issue #344)', async () => {
  // From the W3C rdfms-syntax-incomplete negative suite (error002.rdf):
  // an rdf:nodeID value must match the XML Name production.
  const bad =
    '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">' +
    '<rdf:Description rdf:nodeID="333-555-666" /></rdf:RDF>';
  await assert.rejects(
    factoidal.parse(bad, { format: 'rdfxml' }),
    (err) => {
      assert.notEqual(err.name, 'ParseError',
        'RDF/XML failures carry a message only, so they stay a plain Error');
      assert.match(err.message, /nodeID/);
      return true;
    });
});

xfail('{lenient:true} returns the recoverable statements and one diagnostic', LENIENT_ISSUE, async () => {
  const text =
    '@prefix ex: <http://example.org/> .\n' +
    'ex:a ex:p ex:o .\n' +
    'BOGUS\n' +
    'ex:b ex:p ex:o2 .\n';
  const ds = await factoidal.parse(text, { format: 'turtle', lenient: true });
  assert.equal(ds.size, 2, 'both statements around the bad line recover');
  assert.equal(ds.diagnostics.length, 1);
  assert.equal(typeof ds.diagnostics[0].message, 'string');
  assert.equal(typeof ds.diagnostics[0].line, 'number');
  assert.equal(typeof ds.diagnostics[0].column, 'number');
  assert.equal(typeof ds.diagnostics[0].offset, 'number');
  // Strict parsing of the SAME text rejects outright.
  await assert.rejects(factoidal.parse(text, { format: 'turtle' }));
});

test("query('bad text', sparql) rejects the same way", async () => {
  await assert.rejects(
    factoidal.query('this is not turtle', 'SELECT * WHERE { ?s ?p ?o }', { format: 'turtle' }),
    (err) => { assertParseError(err, 'query'); return true; });
});

// ---------------------------------------------------------------------
// The offset unit: UTF-16 code units of the input JavaScript string.
// ---------------------------------------------------------------------

const GRIN = '\u{1F600}'; // U+1F600: one Unicode scalar value, two UTF-16 code units

// The UTF-16 index of (line, column), with `column` counted in Unicode
// scalar values on that line: the position the engine reported, written in
// the unit ParseError.offset promises.
function utf16IndexOf(text, line, column) {
  let index = 0;
  for (let l = 1; l < line; l += 1) index = text.indexOf('\n', index) + 1;
  let scalars = 1;
  while (scalars < column) {
    const cp = text.codePointAt(index);
    index += cp > 0xffff ? 2 : 1;
    scalars += 1;
  }
  return index;
}

test('offset is a UTF-16 index: a non-BMP character before the error counts 2', async () => {
  // The error is on line 2; U+1F600 is inside the literal on line 1.
  const text = `<http://x/s> <http://x/p> "${GRIN}" .\nBOGUS .\n`;
  const plain = text.replace(GRIN, 'x');
  let grinErr;
  let plainErr;
  try { await factoidal.parse(text, { format: 'turtle' }); } catch (e) { grinErr = e; }
  try { await factoidal.parse(plain, { format: 'turtle' }); } catch (e) { plainErr = e; }
  assertParseError(grinErr, 'non-BMP');
  assertParseError(plainErr, 'plain');
  assert.equal(grinErr.line, 2);
  assert.equal(grinErr.column, plainErr.column, 'column counts Unicode scalar values on line 2');
  assert.equal(grinErr.offset, plainErr.offset + 1, 'U+1F600 is 2 UTF-16 code units where x is 1');
  assert.equal(grinErr.offset, utf16IndexOf(text, grinErr.line, grinErr.column),
    'text.slice(err.offset) starts where line and column point');
  assert.equal(text.slice(grinErr.offset), plain.slice(plainErr.offset),
    'the same text follows the error in both inputs');
});

test('offset is a UTF-16 index on N-Triples and through query() and openDataset()', async () => {
  const text = `<http://x/s> <http://x/p> "${GRIN}${GRIN}" .\n<http://x/s> <http://x/p> BOGUS .\n`;
  const check = (err) => {
    assertParseError(err, 'ntriples');
    assert.equal(err.line, 2);
    assert.equal(err.offset, utf16IndexOf(text, err.line, err.column),
      `offset ${err.offset} is not the UTF-16 index of line ${err.line}, column ${err.column}`);
    assert.ok(err.offset > text.indexOf('\n'), 'the offset is past line 1');
    return true;
  };
  await assert.rejects(factoidal.parse(text, { format: 'ntriples' }), check);
  await assert.rejects(
    factoidal.query(text, 'ASK { ?s ?p ?o }', { format: 'ntriples' }), check);
  await assert.rejects(factoidal.openDataset(text, { format: 'ntriples' }), check);
});
