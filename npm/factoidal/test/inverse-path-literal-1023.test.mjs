// Regression pin for https://github.com/danbri/factoidal/issues/1023: the
// inverse path `^p` dropped every pair whose object is a literal.
//
// SPARQL 1.1 §9.3 and §18.4: `?x ^p ?y` matches exactly what `?y p ?x`
// matches, so `?x` binds the OBJECT of the triple, and that can be a literal.
// Apache Jena ARQ 5.6.0 (`sparql --data d.nt --query q.rq`) answers the two
// queries below with the rows that the tests expect.
//
// Companion Lean pin: the `#guard`s beside `pathPairs (.inverse ...)` in
// formal/lean4/L4Factoidal/SPARQL/QueryTests.lean.
import './helpers.js';

import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
const { parse, query } = require('..');

const NT = `<http://e/s> <http://e/p> "v" .
<http://e/s> <http://e/p> <http://e/o> .
`;

const pairs = (rows) => {
  const out = [];
  for (const b of rows) {
    const x = b.get('x');
    const y = b.get('y');
    out.push(`${x.termType}:${x.value} ${y.termType}:${y.value}`);
  }
  return out.sort();
};

test('?x ^p ?y binds ?x to a literal object (issue 1023)', async () => {
  const ds = await parse(NT, { format: 'ntriples' });
  const rows = await query(ds, 'SELECT ?x ?y WHERE { ?x ^<http://e/p> ?y }');
  assert.deepEqual(pairs(rows), [
    'Literal:v NamedNode:http://e/s',
    'NamedNode:http://e/o NamedNode:http://e/s',
  ]);
});

test('^p/p joins through the subject from a literal and an IRI (issue 1023)', async () => {
  const ds = await parse(NT, { format: 'ntriples' });
  const rows = await query(ds, 'SELECT ?x ?y WHERE { ?x ^<http://e/p>/<http://e/p> ?y }');
  assert.deepEqual(pairs(rows), [
    'Literal:v Literal:v',
    'Literal:v NamedNode:http://e/o',
    'NamedNode:http://e/o Literal:v',
    'NamedNode:http://e/o NamedNode:http://e/o',
  ]);
});
