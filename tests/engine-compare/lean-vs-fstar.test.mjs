// Lean engine against F* engine, same inputs, same typed layer. Moved out
// of npm/factoidal/test/ when the package became Lean-only (issue 713 stage
// 3): l4-core.test.js (the join), l4-parity-2.test.js (matrix, sigmoid and
// the VCDM 2.0 verdicts) and describe.test.js (the F* DESCRIBE expected
// failure, issue 702). Run through ./run.sh.

import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { lean, fstar, fstarRawEngine, rowMultiset } from './engines.mjs';
// The npm package dropped matrix* and sigmoid* in 0.10.0 (owner, 2026-10-20);
// the Lean ops stay and are reached through the hub's marshalling helper.
import { demoMathsFor } from '../../docs/web/hub/assets/demo-maths.mjs';
const leanMaths = demoMathsFor(() => lean.loadEngine());
const fstarMaths = demoMathsFor(async () => fstarRawEngine());

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');

// ---------------------------------------------------------------- SPARQL

const X = 'http://x/';
const XSD_INT = 'http://www.w3.org/2001/XMLSchema#integer';
const JOIN_NT =
  `<${X}alice> <${X}name> "Alice" .\n` +
  `<${X}alice> <${X}age> "30"^^<${XSD_INT}> .\n` +
  `<${X}bob> <${X}name> "Bob" .\n` +
  `<${X}bob> <${X}age> "24"^^<${XSD_INT}> .\n`;
const JOIN_Q = `SELECT ?s ?n ?a WHERE { ?s <${X}name> ?n . ?s <${X}age> ?a }`;

test('same join, same row multiset', async () => {
  const leanRows = await lean.query(JOIN_NT, JOIN_Q, { format: 'ntriples' });
  const fstarRows = await fstar.query(JOIN_NT, JOIN_Q, { format: 'ntriples' });
  assert.equal(leanRows.length, 2);
  assert.deepEqual(rowMultiset(leanRows), rowMultiset(fstarRows));
});

test('same RDFC-1.0 canonical N-Quads for a graph with blank nodes', async () => {
  const ttl = '@prefix : <http://x/> . :a :p [ :q "v" ; :r [ :s 1 ] ] . _:z :p :a .';
  // Both engines canonicalize the same N-Quads text through their own
  // canonicalizeToNQuads op (the F* entry has no Dataset rdfc writer).
  const nq = (await lean.parse(ttl, { format: 'turtle' })).toString('nquads');
  const leanOut = (await lean.loadEngine()).call('canonicalizeToNQuads', [nq]);
  const fstarOut = fstarRawEngine().call('canonicalizeToNQuads', [nq]);
  assert.equal(leanOut.ok, true, JSON.stringify(leanOut));
  assert.equal(leanOut.nquads, fstarOut.nquads);
});

// DESCRIBE: the Lean engine answers the Concise Bounded Description; the F*
// engine answers the empty graph (https://github.com/danbri/factoidal/issues/702).
const DESCRIBE_NT = [
  `<${X}a> <${X}p> _:b1 .`,
  `_:b1 <${X}q> "v" .`,
  `<${X}a> <${X}r> <${X}c> .`,
  `<${X}c> <${X}p> "outside the description" .`,
].join('\n');
const FSTAR_DESCRIBE_ISSUE = 'https://github.com/danbri/factoidal/issues/702';

test('Lean DESCRIBE <iri> is the Concise Bounded Description (3 triples)', async () => {
  const out = await lean.query(DESCRIBE_NT, `DESCRIBE <${X}a>`, { format: 'ntriples' });
  assert.equal(out.size, 3);
});

test(`xfail: F* engine DESCRIBE <iri> returns the Concise Bounded Description (${FSTAR_DESCRIBE_ISSUE})`, async (t) => {
  let failed = false;
  try {
    const out = await fstar.query(DESCRIBE_NT, `DESCRIBE <${X}a>`, { format: 'ntriples' });
    assert.equal(out.size, 3);
  } catch (error) {
    failed = true;
    t.diagnostic(`expected failure: ${String(error.message).slice(0, 160)}`);
  }
  assert.ok(failed,
    `unexpected pass: F* DESCRIBE now works — flip this xfail to an assertion and close ${FSTAR_DESCRIBE_ISSUE}`);
});

// ----------------------------------------------------------------- maths

test('matrix functions: same results on the same inputs', async () => {
  const matrices = [[[1, 2], [3, 4]], [[1, 2, 3], [4, 5, 6]], [[[1, 2], 0], [0, [1, 2]]],
    [[2, 0, 1], [1, 3, 2], [1, 1, 1]], [[1, [1, 0]], [3, 4]], [[1, 2], [3]], []];
  for (const m of matrices) {
    assert.deepEqual(await leanMaths.matrixDeterminant(m), await fstarMaths.matrixDeterminant(m),
      `matrixDeterminant ${JSON.stringify(m)}`);
  }
  const pairs = [[[1, 2, 3], [4, 5, 6]], [[1, 0, 0], [0, 1, 0]], [[1, 2], [3, 4]], [[1, 2, 3], [4, 5]],
    [[[1, 2], 1], [2, [1, 3]]], [[1, [1, 0]], [2, 3]]];
  for (const [a, b] of pairs) {
    for (const fn of ['matrixScalarProduct', 'matrixVectorProduct', 'matrixOuterProduct']) {
      assert.deepEqual(await leanMaths[fn](a, b), await fstarMaths[fn](a, b), `${fn} ${JSON.stringify([a, b])}`);
    }
  }
});

test('sigmoidPoints and sigmoidFormulaMathml: identical digits and markup', async () => {
  for (const params of [
    { k: '1', x0: '0', l: '1', xmin: '-6', xmax: '6', n: 24 },
    { k: '2.5', x0: '-1.25', l: '3', xmin: '-4', xmax: '4', n: 16 },
    { k: '0.5', x0: '3', l: '1', xmin: '0', xmax: '10', n: 10 },
  ]) {
    assert.deepEqual(await leanMaths.sigmoidPoints(params), await fstarMaths.sigmoidPoints(params),
      JSON.stringify(params));
  }
  assert.equal(await leanMaths.sigmoidFormulaMathml(), await fstarMaths.sigmoidFormulaMathml());
});

// ------------------------------------------------------------ VCDM 2.0

const VC_FIXTURES = path.join(REPO, 'third_party', 'testing', 'vc');
const V2_CONTEXT_PATH = path.join(REPO, 'third_party', 'contexts', 'credentials-v2.jsonld');

function fixtureFiles(dir) {
  const out = [];
  for (const name of fs.readdirSync(dir).sort()) {
    const full = path.join(dir, name);
    if (fs.statSync(full).isDirectory()) out.push(...fixtureFiles(full));
    else if (name.endsWith('.json')) out.push(full);
  }
  return out;
}

test('vcCheckCredential: the same verdict on every VCDM 2.0 fixture', async () => {
  assert.ok(fs.existsSync(VC_FIXTURES) && fs.existsSync(V2_CONTEXT_PATH),
    'third_party/testing/vc and third_party/contexts must be present (tools/ensure-test-env.sh)');
  const v2ctx = fs.readFileSync(V2_CONTEXT_PATH, 'utf8');
  const disagreements = [];
  for (const file of fixtureFiles(VC_FIXTURES)) {
    const text = fs.readFileSync(file, 'utf8')
      .replace(/PAST DATE/g, '2020-01-01T00:00:00Z').replace(/FUTURE DATE/g, '2099-01-01T00:00:00Z');
    const a = await lean.vcCheckCredential(v2ctx, text);
    const b = await fstar.vcCheckCredential(v2ctx, text);
    if (a.valid !== b.valid) disagreements.push(`${path.basename(file)}: Lean ${a.valid}, F* ${b.valid}`);
  }
  assert.deepEqual(disagreements, []);
});
