// SPARQL 1.2 RL infer (https://github.com/danbri/factoidal/issues/1099):
// sparqlRlInfer(data, rules) answers the inference graph as a Dataset. The
// rule-set semantics is Lean (formal/lean4/L4Factoidal/SPARQLRL); these
// cases check the op and its envelope through the package.

import test from 'node:test';
import assert from 'node:assert/strict';
import * as f from '../index.mjs';

const P = 'PREFIX : <http://example/>\n';

test('sparqlRlInfer: recursion, negation in a higher stratum, data blocks', async () => {
  const data = `@prefix : <http://example/> .
    :a :link :b . :b :link :c . :c :type :Node . :a :type :Node .`;
  const rules = P + `
    DATA { :z :link :a }
    RULE { ?x :reach ?y } WHERE { ?x :link ?y }
    RULE { ?x :reach ?y } WHERE { ?x :reach ?z . ?z :reach ?y }
    RULE { ?x :isolated true } WHERE { ?x :type :Node NOT { ?x :reach ?y } }`;
  const inf = await f.sparqlRlInfer(data, rules, { format: 'turtle' });
  const nq = inf.toNQuads();
  // the DATA block triple is inferred; z reaches c through a and b
  assert.match(nq, /<http:\/\/example\/z> <http:\/\/example\/link> <http:\/\/example\/a>/);
  assert.match(nq, /<http:\/\/example\/z> <http:\/\/example\/reach> <http:\/\/example\/c>/);
  // c reaches nothing, a does
  assert.match(nq, /<http:\/\/example\/c> <http:\/\/example\/isolated>/);
  assert.doesNotMatch(nq, /<http:\/\/example\/a> <http:\/\/example\/isolated>/);
  // base triples are not in the inference graph
  assert.doesNotMatch(nq, /<http:\/\/example\/a> <http:\/\/example\/link> <http:\/\/example\/b>/);
  // reach: a-b, b-c, z-a, a-c, z-b, z-c; z link a; c isolated
  assert.equal(inf.size, 8);
  inf.dispose();
});

test('sparqlRlInfer: SET drops a solution whose expression is an error', async () => {
  const data = '<http://example/a> <http://example/v> 0 .\n<http://example/b> <http://example/v> 4 .\n';
  const inf = await f.sparqlRlInfer(data,
    P + 'RULE { ?x :inv ?z } WHERE { ?x :v ?o SET ( ?z := 1/?o ) }', { format: 'turtle' });
  assert.equal(inf.size, 1);
  assert.match(inf.toNQuads(), /<http:\/\/example\/b> <http:\/\/example\/inv> "0.25"/);
  inf.dispose();
});

test('sparqlRlInfer: a GROUP element counts', async () => {
  const data = '<http://example/a> <http://example/v> 1, 2, 3 .';
  const inf = await f.sparqlRlInfer(data,
    P + 'RULE { ?s :n ?N } WHERE { GROUP BY ?s { ?s :v ?x } [ ?N := COUNT(*) ] }', { format: 'turtle' });
  assert.match(inf.toNQuads(), /<http:\/\/example\/a> <http:\/\/example\/n> "3"/);
  inf.dispose();
});

test('sparqlRlInfer: refusals reject with a coded error', async () => {
  const data = '<http://example/a> <http://example/p> <http://example/b> .';
  // syntax error
  await assert.rejects(f.sparqlRlInfer(data, 'RULE { } WHERE', { format: 'ntriples' }),
    (e) => typeof e.code === 'string' && /sparqlRlInfer/.test(e.message));
  // not stratifiable: negation through itself
  await assert.rejects(f.sparqlRlInfer(data,
    P + 'RULE { ?s :p :c } WHERE { ?s :p ?o NOT { ?s :p :c } }', { format: 'ntriples' }),
    /stratification/);
  // not well-formed: a head variable the body does not bind
  await assert.rejects(f.sparqlRlInfer(data, P + 'RULE { ?s :p ?z } WHERE { ?s :p ?o }',
    { format: 'ntriples' }), /well-formed/);
  // IMPORTS: this op has no loader
  await assert.rejects(f.sparqlRlInfer(data, 'IMPORTS <http://example/lib.srl>',
    { format: 'ntriples' }), /IMPORTS/);
  await assert.rejects(f.sparqlRlInfer(data, 42), TypeError);
});

test('capabilities reports sparqlRl', async () => {
  assert.equal((await f.capabilities()).sparqlRl, true);
});
