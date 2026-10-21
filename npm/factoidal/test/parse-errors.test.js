// Strict parsing (issue #344): every function that parses text input
// rejects with a positioned FactoidalError instead of silently dropping
// data. See README.md's "Parsing is strict by default" section and
// lib/api.mjs's entryResult()/ParseError.
//
// ParseError.offset is a UTF-16 code-unit index into the input string
// (index.d.ts), so text.slice(err.position.offset) starts at the error. The engine
// counts Unicode scalar values; lib/api.mjs converts. A character outside
// the Basic Multilingual Plane before the error is the case that tells
// the two units apart.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');

const factoidal = require('../index.js');

function assertParseError(err, who) {
  assert.equal(err.name, 'FactoidalError', `${who}: err.name`);
  assert.ok(err instanceof Error, `${who}: FactoidalError extends Error`);
  assert.equal(err instanceof factoidal.FactoidalError, true,
    `${who}: err instanceof the exported FactoidalError class`);
  assert.ok(['parse.syntax', 'term.invalid-iri', 'term.invalid-langtag', 'parse.rdf12-required'].includes(err.code),
    `${who}: a parse code, got ${err.code}`);
  assert.equal(typeof err.spec, 'string', `${who}: err.spec`);
  assert.equal(typeof err.position.line, 'number', `${who}: err.position.line is a number`);
  assert.equal(typeof err.position.column, 'number', `${who}: err.position.column is a number`);
  assert.equal(typeof err.position.offset, 'number', `${who}: err.position.offset is a number`);
}

test('parse("this is not turtle") rejects with a positioned FactoidalError', async () => {
  await assert.rejects(
    factoidal.parse('this is not turtle', { format: 'turtle' }),
    (err) => { assertParseError(err, 'parse'); return true; });
});

test('a Turtle document missing one "." rejects with a positioned FactoidalError', async () => {
  const text =
    '@prefix ex: <http://example.org/> .\n' +
    'ex:a ex:p ex:o\n' +        // missing '.' here
    'ex:b ex:p ex:o2 .\n';
  await assert.rejects(
    factoidal.parse(text, { format: 'turtle' }),
    (err) => {
      assertParseError(err, 'missing-dot');
      assert.equal(err.position.line, 3, 'the parser reports the failure on the FOLLOWING line');
      return true;
    });
});

test('a relative IRI with no baseIRI rejects with a message mentioning IRI', async () => {
  await assert.rejects(
    factoidal.parse('<a> <b> <c> .', { format: 'turtle' }),
    /IRI/i);
});

test('N-Triples syntax errors reject with a positioned FactoidalError', async () => {
  await assert.rejects(
    factoidal.parse('<http://x/s> <http://x/p> .', { format: 'ntriples' }),
    (err) => { assertParseError(err, 'ntriples'); return true; });
});

test('N-Quads syntax errors reject with a positioned FactoidalError', async () => {
  await assert.rejects(
    factoidal.parse('<http://x/s> <http://x/p> .', { format: 'nquads' }),
    (err) => { assertParseError(err, 'nquads'); return true; });
});

test('TriG syntax errors reject with a positioned FactoidalError', async () => {
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
      assert.equal(err.code, 'parse.syntax');
      assert.equal(err.position, null, 'RDF/XML failures carry no position');
      assert.match(err.message, /nodeID/);
      return true;
    });
});

// Lenient parse (https://github.com/danbri/factoidal/issues/716). A Turtle
// statement is not delimited by a line end: recovery resumes at the next
// statement boundary as the Turtle statement scanner defines it (a `.` in
// normal mode followed by white space or `#`). So 'BOGUS' with no `.` runs
// on to the end of 'ex:b ex:p ex:o2 .' and that statement is skipped with
// it; 'BOGUS .' ends at its own `.` and the next statement recovers. (The
// F* engine resumed at the next line and kept ex:b in the first case.)
test('{lenient:true} returns the recoverable statements and one diagnostic', async () => {
  const text =
    '@prefix ex: <http://example.org/> .\n' +
    'ex:a ex:p ex:o .\n' +
    'BOGUS\n' +
    'ex:b ex:p ex:o2 .\n';
  const ds = await factoidal.parse(text, { format: 'turtle', lenient: true });
  assert.equal(ds.size, 1, 'the statement before the error recovers');
  assert.equal(ds.diagnostics.length, 1);
  const d = ds.diagnostics[0];
  assert.equal(typeof d.message, 'string');
  assert.deepEqual([d.line, d.column, d.class], [3, 6, 'bad-prefixed-name']);
  assert.equal(text.slice(d.offset), '\nex:b ex:p ex:o2 .\n');
  // Strict parsing of the SAME text rejects outright.
  await assert.rejects(factoidal.parse(text, { format: 'turtle' }));

  const ended = text.replace('BOGUS\n', 'BOGUS .\n');
  const ds2 = await factoidal.parse(ended, { format: 'turtle', lenient: true });
  assert.equal(ds2.size, 2, 'both statements around the bad statement recover');
  assert.equal(ds2.diagnostics.length, 1);
  assert.equal(ds2.diagnostics[0].line, 3);
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
  assert.equal(grinErr.position.line, 2);
  assert.equal(grinErr.position.column, plainErr.position.column, 'column counts Unicode scalar values on line 2');
  assert.equal(grinErr.position.offset, plainErr.position.offset + 1, 'U+1F600 is 2 UTF-16 code units where x is 1');
  assert.equal(grinErr.position.offset, utf16IndexOf(text, grinErr.position.line, grinErr.position.column),
    'text.slice(err.position.offset) starts where line and column point');
  assert.equal(text.slice(grinErr.position.offset), plain.slice(plainErr.position.offset),
    'the same text follows the error in both inputs');
});

test('offset is a UTF-16 index on N-Triples and through query() and openDataset()', async () => {
  const text = `<http://x/s> <http://x/p> "${GRIN}${GRIN}" .\n<http://x/s> <http://x/p> BOGUS .\n`;
  const check = (err) => {
    assertParseError(err, 'ntriples');
    assert.equal(err.position.line, 2);
    assert.equal(err.position.offset, utf16IndexOf(text, err.position.line, err.position.column),
      `offset ${err.position.offset} is not the UTF-16 index of line ${err.position.line}, column ${err.position.column}`);
    assert.ok(err.position.offset > text.indexOf('\n'), 'the offset is past line 1');
    return true;
  };
  await assert.rejects(factoidal.parse(text, { format: 'ntriples' }), check);
  await assert.rejects(
    factoidal.query(text, 'ASK { ?s ?p ?o }', { format: 'ntriples' }), check);
  await assert.rejects(factoidal.openDataset(text, { format: 'ntriples' }), check);
});
