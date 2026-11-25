import { test } from 'node:test';
import assert from 'node:assert/strict';
import { extractComments } from './comments.mjs';

test('hash inside IRI is not a comment', () => {
  assert.deepEqual(extractComments('PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>\nSELECT * {}'), []);
});

test('hash inside strings is not a comment', () => {
  assert.deepEqual(extractComments('SELECT * { ?x ?p "C#" . ?y ?q \'F#\' . ?z ?r """a\n#b""" }'), []);
});

test('less-than operator does not swallow a comment', () => {
  const cs = extractComments('FILTER(?a < 3) # small\n');
  assert.equal(cs.length, 1);
  assert.equal(cs[0].text, ' small');
  assert.equal(cs[0].standalone, false);
  assert.equal(cs[0].codeBefore, 'FILTER(?a < 3)');
});

test('directives, offsets and defaultView options', () => {
  const q = '#title:Things\n#defaultView:Map{"hide": ["?coord"]}\nSELECT ?x WHERE { ?x wdt:P31 wd:Q5 } # humans';
  const cs = extractComments(q);
  assert.equal(cs.length, 3);
  assert.equal(cs[0].kind, 'directive');
  assert.equal(cs[0].name, 'title');
  assert.equal(cs[0].value, 'Things');
  assert.deepEqual(cs[1].parsed, { view: 'Map', options: { hide: ['?coord'] } });
  assert.equal(cs[2].kind, 'comment');
  assert.equal(cs[2].line, 3);
  assert.equal(q.slice(cs[2].start, cs[2].end), '# humans');
});

test('escaped quote inside a string', () => {
  const cs = extractComments('?x ?p "say \\"hi\\" #not" # yes\n');
  assert.equal(cs.length, 1);
  assert.equal(cs[0].text, ' yes');
});

test('a directive name after code is an ordinary comment', () => {
  const cs = extractComments('?x ?p ?o #title:not a directive\n');
  assert.equal(cs[0].kind, 'comment');
});

test('commented-out code versus prose notes', () => {
  const kinds = (s) => extractComments(s).map(c => c.content);
  assert.deepEqual(kinds('#UNION{ ?item wdt:P1411 ?award }\n# ?work is a poem\n# wdt:P921 wdt:P189\n# human\n'),
    ['code', 'note', 'code', 'note']);
});
