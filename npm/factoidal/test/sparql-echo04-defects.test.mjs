// SPARQL defects found by the RDF4J-style echo (danbri/echochamber, working
// name echo04), fixed in the Lean engine. Each case is a plain assertion.
//
// https://github.com/danbri/factoidal/issues/1074 (Update blank-node labels)
// https://github.com/danbri/factoidal/issues/1049 (IN / NOT IN errors)
// https://github.com/danbri/factoidal/issues/1050 (ORDER BY an aggregate)
// https://github.com/danbri/factoidal/issues/1060 (SUBSTR derived integers)
// https://github.com/danbri/factoidal/issues/1062 (no cast from rdf:langString)
// https://github.com/danbri/factoidal/issues/1075 (lexer: `true.`)
// https://github.com/danbri/factoidal/issues/1069 (MINUS does not bind)

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const XSD = 'http://www.w3.org/2001/XMLSchema#';
const empty = await f.parse('', { format: 'nquads' });

async function valueOf(expr) {
  const rows = await empty.query(`PREFIX xsd: <${XSD}> SELECT ?v WHERE { BIND(${expr} AS ?v) }`);
  assert.equal(rows.length, 1);
  return rows[0].get('v');
}

test('#1074: a blank node written by SPARQL Update crosses CONSTRUCT and SHACL (Update §3.1.1)', async () => {
  const ds = await f.openDataset('', 'turtle');
  await ds.update('INSERT DATA { <http://e/a> <http://e/p> [] . <http://e/a> <http://e/q> ( 1 2 ) }');
  await ds.update('INSERT { <http://e/b> <http://e/p> [ <http://e/r> 1 ] } WHERE {}');
  const g = await ds.query('CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }');
  assert.equal([...g].length, 8);
  const nq = await ds.toNQuads();
  for (const m of nq.matchAll(/_:(\S+)/g)) assert.ok(!m[1].includes(':'), `label ${m[1]}`);
  const r = await f.shaclValidate(ds,
    '@prefix sh: <http://www.w3.org/ns/shacl#> . <http://e/S> a sh:NodeShape ; sh:targetNode <http://e/a> .',
    { format: 'turtle' });
  assert.equal(r.conforms, true);
});

test('#1049: IN / NOT IN raise an error unless another element decides (§17.4.1.9, §17.4.1.10)', async () => {
  assert.equal(await valueOf('2 IN (3, 1/0)'), undefined);
  assert.equal(await valueOf('2 NOT IN (3, 1/0)'), undefined);
  assert.equal(await valueOf('"70" IN (700)'), undefined);
  assert.equal((await valueOf('2 IN (1/0, 2)')).value, 'true');
  assert.equal((await valueOf('2 NOT IN (3, 4)')).value, 'true');
  assert.equal((await valueOf('2 IN ()')).value, 'false');
});

test('#1050: ORDER BY DESC(COUNT(?s)) orders the groups (§18.2.4.1)', async () => {
  const q = (order) => `PREFIX : <http://example.org/> SELECT ?type WHERE {
    VALUES (?s ?type) { (:b :D) (:a :L) (:c :D) (:d :N) (:e :N) (:f :N) } } GROUP BY ?type ORDER BY ${order}`;
  const names = async (order) => (await empty.query(q(order))).map((r) => r.get('type').value.slice(19));
  assert.deepEqual(await names('DESC(COUNT(?s))'), ['N', 'D', 'L']);
  assert.deepEqual(await names('(COUNT(?s))'), ['L', 'D', 'N']);
  const sub = await f.parse(`@prefix ex: <http://example.org/> .
    ex:george ex:knows ex:ringo, ex:john . ex:ringo ex:knows ex:george, ex:john . ex:paul ex:knows ex:george, ex:john .`,
  { format: 'turtle' });
  const rows = await sub.query(`PREFIX ex: <http://example.org/> SELECT ?friend WHERE { ?popular ex:knows ?friend .
    { SELECT ?popular WHERE { ?someone ex:knows ?popular } GROUP BY ?popular ORDER BY DESC(COUNT(?someone)) LIMIT 1 } }`);
  assert.equal(rows.length, 0);
});

test('#1060: SUBSTR takes start and length of types derived from xsd:integer (§17.4.3.3)', async () => {
  assert.equal((await valueOf('SUBSTR("foobar", "4"^^xsd:int)')).value, 'bar');
  assert.equal((await valueOf('SUBSTR("foobar", "4"^^xsd:long)')).value, 'bar');
  assert.equal((await valueOf('SUBSTR("foobar", "4"^^xsd:positiveInteger)')).value, 'bar');
  assert.equal((await valueOf('SUBSTR("foobar", 4, "2"^^xsd:int)')).value, 'ba');
  assert.equal(await valueOf('SUBSTR("foobar", "x"^^xsd:int)'), undefined);
});

test('#1062: xsd:string of a language-tagged literal is an error (§17.5)', async () => {
  assert.equal(await valueOf('xsd:string("foo"@en)'), undefined);
  assert.equal((await valueOf('xsd:string("foo")')).value, 'foo');
  assert.equal((await valueOf('STR("foo"@en)')).value, 'foo');
});

test('#1075: `true.` is the keyword true and the terminator (§19.8 [134])', async () => {
  const ds = await f.openDataset('', 'turtle');
  await ds.update('INSERT DATA { <http://e/a> <http://e/p> true. }');
  const rows = await ds.query('SELECT * { <http://e/a> <http://e/p> true. }');
  assert.equal(rows.length, 1);
});

test('#1069: a variable only inside MINUS is not in scope (§18.2.1)', async () => {
  const ds = await f.parse('<urn:a> <urn:p> 1 . <urn:b> <urn:q> 2 .', { format: 'turtle' });
  const rows = await ds.query('SELECT ?s (1 AS ?z) { ?s <urn:p> ?o MINUS { ?x <urn:q> ?z } }');
  assert.equal(rows.length, 1);
  assert.equal(rows[0].get('s').value, 'urn:a');
  assert.equal(rows[0].get('z').value, '1');
});
