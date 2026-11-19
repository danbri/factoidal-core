#!/usr/bin/env node
/**
 * EELS-generated state-test fixture inventory, NOT fixture execution.
 *
 * Real fixtures have pre-state accounts, an environment, transactions,
 * and one or more per-fork post-state-root/log-hash expectations.
 * This preflight validates required envelope shapes and reports the exact
 * denominator, but intentionally reports ZERO executed/conforming cases.
 *
 * Do not silently treat a partially supported fixture as passed.
 * Usage: node scripts/eels-state-preflight.mjs <JSON_FILE>
 */
import { readFileSync } from 'node:fs';

const die = (message) => {
  process.stderr.write(JSON.stringify({ status: 'invalid-fixture', message }) + '\n');
  process.exit(2);
};
const isObject = (x) => x !== null && typeof x === 'object' && !Array.isArray(x);
const hash32 = (x) => typeof x === 'string' && /^0x[0-9a-fA-F]{64}$/.test(x);

if (process.argv.length !== 3) {
  die('usage: node scripts/eels-state-preflight.mjs JSON_FILE');
}
let fixtures;
try {
  fixtures = JSON.parse(readFileSync(process.argv[2], 'utf8'));
} catch (e) {
  die('cannot read valid JSON fixture: ' + String(e));
}
if (!isObject(fixtures) || Object.keys(fixtures).length === 0) {
  die('nonempty fixture collection expected');
}

const counts = new Map();
let totalVectors = 0;
let totalAccounts = 0;
let firstTest = null;
for (const [name, fixture] of Object.entries(fixtures)) {
  if (firstTest === null) firstTest = name;
  if (!isObject(fixture)) die('fixture must be object: ' + name);
  if (!isObject(fixture.pre) || !isObject(fixture.env) ||
      !isObject(fixture.transaction) || !isObject(fixture.post)) {
    die('missing pre/env/transaction/post object: ' + name);
  }
  totalAccounts += Object.keys(fixture.pre).length;
  const forkEntries = Object.entries(fixture.post);
  if (forkEntries.length === 0) die('fixture has no fork-specific post: ' + name);
  for (const [fork, vectors] of forkEntries) {
    if (!Array.isArray(vectors) || vectors.length === 0) {
      die('missing post-state vectors: ' + name + '/' + fork);
    }
    counts.set(fork, (counts.get(fork) ?? 0) + vectors.length);
    for (const [i, vector] of vectors.entries()) {
      if (!isObject(vector) || !hash32(vector.hash) || !hash32(vector.logs)) {
        die('missing or invalid 32-byte post-state/logs hash: ' + name + '/' + fork + '/' + i);
      }
      if (vector.txbytes !== undefined &&
          !(typeof vector.txbytes === 'string' && /^0x([0-9a-fA-F]{2})*$/.test(vector.txbytes))) {
        die('invalid transaction bytes: ' + name + '/' + fork + '/' + i);
      }
      if (!isObject(vector.indexes)) {
        die('missing transaction selection indexes: ' + name + '/' + fork + '/' + i);
      }
      totalVectors += 1;
    }
  }
}
const forks = Object.fromEntries([...counts].sort(([a], [b]) => a.localeCompare(b)));
process.stdout.write(JSON.stringify({
  status: 'parsed-not-executed',
  fixtureFormat: 'EELS state_test JSON',
  fixtures: Object.keys(fixtures).length,
  vectors: totalVectors,
  accountPrestateEntries: totalAccounts,
  forks,
  exampleTestId: firstTest,
  executed: 0,
  conformancePasses: 0,
  unsupported: totalVectors,
  reason: 'The Lean EVM model lacks full transaction/world-state execution, receipts and state-root comparison.'
}) + '\n');
