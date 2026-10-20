// A SELECT with 20,000 solutions, and canonicalize() of 24,000 blank-node
// quads, answer on Node's default stack, on both entries. Until 2026-10-10 the Lean evaluator numbered the rows of a SELECT
// with a projection by a recursion that took one stack frame per row
// (`SPARQL.numberRows`); the wasm module ran out of Node's stack at about
// 11,000 rows ("Maximum call stack size exceeded"), where the native build,
// with smaller frames and an 8 MB stack, did not. `numberRowsTR` and its
// `csimp` theorem (formal/lean4/L4Factoidal/SPARQL/Query.lean) repair it;
// the Results JSON writer (`SPARQL.rowsJoined`) and the duplicate removal of
// RDFC-1.0 (`RDF.Canonical.collapseKeyedQQuads`, `dedupAdj`) had the same
// shape and are repaired the same way.
// https://github.com/danbri/factoidal/issues/713 stage 5.

import test from 'node:test';
import assert from 'node:assert/strict';

import * as full from '../index.mjs';

const N = 20000;
const lines = [];
for (let i = 0; i < N; i += 1) lines.push(`<http://e/s${i}> <http://e/p> "${i}" .`);
const NT = lines.join('\n') + '\n';

for (const [name, api] of [['full', full]]) {
  test(`${name} entry: SELECT with ${N} solutions answers on the default stack`, async () => {
    const ds = await api.parse(NT, { format: 'ntriples' });
    assert.equal(ds.size, N);
    const rows = await api.query(ds, 'SELECT ?s ?o WHERE { ?s <http://e/p> ?o }');
    assert.equal(rows.length, N);
    const handle = await api.openDataset(NT, { format: 'ntriples' });
    try {
      const viaHandle = await handle.query('SELECT ?o WHERE { ?s <http://e/p> ?o } ORDER BY ?o');
      assert.equal(viaHandle.length, N);
    } finally {
      handle.dispose();
    }
  });
}

const B = 8000;
const bl = [];
for (let i = 0; i < B; i += 1) {
  bl.push(`_:p${i} <http://e/type> <http://e/Person> .`,
    `_:p${i} <http://e/name> "Person ${i}" .`,
    `_:p${i} <http://e/age> "${18 + (i % 60)}" .`);
}
const BNQ = bl.join('\n') + '\n';

for (const [name, api] of [['full', full]]) {
  test(`${name} entry: canonicalize of ${3 * B} blank-node quads answers on the default stack`, async () => {
    const out = await api.canonicalize(BNQ, { format: 'nquads' });
    const lines = out.split('\n').filter(Boolean);
    assert.equal(lines.length, 3 * B);
    assert.ok(lines.every((l) => l.startsWith('_:c14n')), 'every subject is a canonical label');
  });
}
