#!/usr/bin/env node
// Replay the checked source inventory through the actual package and wasm.
// Each case runs in a child process; a synchronous wasm hang cannot mask a timeout.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync, existsSync, realpathSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const SELF = fileURLToPath(import.meta.url);
const PREFIX = 'OWL_ARTIFACT_CASE=';
const IDS = [
  'empty', 'annotation-domain', 'annotation-plus-real-clash', 'same-different',
  'same-chain', 'top-below-bottom', 'generated-looking-source-name', 'class-individual-punning',
  'unsupported-equivalence-contradiction', 'unsupported-import', 'unsupported-negative-property',
  'named-contradiction-is-outside-default', 'default-clash-with-named-data',
  'default-annotation-with-named-clash', 'named-declaration-does-not-classify-default',
  'zero-search-fuel', 'malformed-options', 'rdf12-refusal', 'named-rdf12-preflight', 'parse-error',
];
const FALSE_IDS = new Set(['annotation-plus-real-clash', 'same-different', 'same-chain',
  'top-below-bottom', 'default-clash-with-named-data', 'zero-search-fuel', 'malformed-options']);
const ERROR_IDS = new Set(['rdf12-refusal', 'named-rdf12-preflight', 'parse-error']);
const UNSUPPORTED_IDS = new Set(['unsupported-equivalence-contradiction', 'unsupported-import',
  'unsupported-negative-property', 'named-declaration-does-not-classify-default']);
const digest = data => createHash('sha256').update(data).digest('hex');

function inventory(path) {
  const report = JSON.parse(readFileSync(path, 'utf8'));
  assert.equal(report.format, 'owl-public-boundary-v1');
  assert.equal(report.status, 'pass', 'source boundary gate must pass first');
  assert.equal(report.cases.length, IDS.length);
  assert.deepEqual(report.cases.map(c => c.id).sort(), [...IDS].sort());
  for (const c of report.cases) {
    assert.equal(typeof c.input, 'string');
    assert.equal(typeof c.options, 'string');
    assert.equal(c.passed, true);
    assert.equal(c.expectedOk, !ERROR_IDS.has(c.id));
    assert.equal(c.expectedConsistent, FALSE_IDS.has(c.id) ? false : null);
    const reason = UNSUPPORTED_IDS.has(c.id) ? 'unsupported-syntax' :
      FALSE_IDS.has(c.id) || ERROR_IDS.has(c.id) ? '' : 'incomplete-search';
    assert.equal(c.expectedReasonPrefix, reason);
  }
  return report.cases;
}

async function child(pkg, casesPath, id) {
  const c = inventory(casesPath).find(c => c.id === id);
  assert(c);
  const observed = { id, status: 'error', lowLevel: null, publicApi: null };
  try {
    const api = await import(pathToFileURL(join(pkg, 'index.mjs')));
    assert.equal(typeof api.loadEngine, 'function');
    assert.equal(typeof api.owlIsConsistent, 'function');
    const engine = await api.loadEngine();
    let low;
    let dispatchFailure;
    try { low = engine.call('owlIsConsistent', [c.input, c.options]); }
    catch (error) {
      // The shipped loader throws on an error envelope, preserving it here.
      // A generic loader/runtime exception must never count as a refusal.
      assert.equal(c.expectedOk, false, 'successful case must not throw');
      assert(error instanceof Error);
      assert(error.envelope && typeof error.envelope === 'object', 'refusal must carry its ABI envelope');
      dispatchFailure = error;
      low = error.envelope;
    }
    observed.lowLevel = low;
    assert.equal(low.ok, c.expectedOk);
    if (c.expectedOk) {
      assert.deepEqual(Object.keys(low).sort(), ['consistent', 'ok', 'reason']);
      assert.equal(low.consistent, c.expectedConsistent);
      assert.equal(typeof low.reason, 'string');
      assert(low.reason.startsWith(c.expectedReasonPrefix));
    } else {
      assert(dispatchFailure, 'loader must throw for an error envelope');
      // main's ErrorModel adds dispatch metadata; the raw producer theorem
      // covers the smaller object. Pin the additional contract independently.
      const expected = { ok: false, error: JSON.parse(c.response).error,
        code: id === 'parse-error' ? 'reason.failed' : 'owl.unsupported-rdf12' };
      if (id !== 'parse-error') expected.spec =
        'https://www.w3.org/TR/owl2-mapping-to-rdf/#Mapping_from_RDF_Graphs_to_the_Structural_Specification';
      assert.deepEqual(low, expected, 'compiled dispatch must preserve the producer and its error metadata');
    }
    if (id === 'malformed-options') {
      observed.publicApi = { status: 'not-applicable', reason: 'malformed ABI options text has no public options-object equivalent' };
    } else {
      const opts = { format: 'nquads', ...(c.options ? JSON.parse(c.options) : {}) };
      if (c.expectedOk) {
        const answer = await api.owlIsConsistent(c.input, opts);
        observed.publicApi = answer;
        assert.deepEqual(answer, { consistent: low.consistent, reason: low.reason });
      } else {
        let failure;
        try { await api.owlIsConsistent(c.input, opts); } catch (error) { failure = error; }
        assert(failure instanceof Error, 'public facade must reject an error envelope');
        assert.equal(typeof api.FactoidalError, 'function');
        assert(failure instanceof api.FactoidalError, 'public errors must use the exported error class');
        observed.publicApi = { error: String(failure.message), name: failure.name,
          code: failure.code, position: failure.position, spec: failure.spec, format: failure.format };
        if (id === 'parse-error') {
          // nquadsOf parses before the OWL call. This is a distinct parser path.
          assert.equal(failure.name, 'FactoidalError');
          assert.equal(failure.code, 'parse.syntax');
          assert.equal(failure.spec, 'https://www.w3.org/TR/rdf12-n-quads/#sec-grammar');
          assert.equal(failure.format, 'nquads');
          assert.deepEqual(failure.position, { line: 1, column: 17, offset: 16, byteOffset: 16 });
          assert(failure.message.includes('expected object'));
        } else {
          assert(failure.message.includes(low.error), 'public refusal must preserve the engine error');
          assert.equal(failure.code, low.code);
          assert.equal(failure.spec, low.spec);
          assert.equal(failure.position, null);
        }
      }
    }
    observed.status = 'pass';
  } catch (error) {
    observed.error = String(error.stack || error);
  }
  console.log(PREFIX + JSON.stringify(observed));
  process.exitCode = observed.status === 'pass' ? 0 : 1;
}

async function main() {
  const args = process.argv.slice(2);
  if (args[0] === '--child') return child(args[1], args[2], args[3]);
  const flags = new Map();
  for (let i = 0; i < args.length; i += 2) {
    if (!['--package', '--cases', '--json'].includes(args[i]) || !args[i + 1])
      throw new Error('Usage: --package DIR --cases PASSING_SOURCE_REPORT --json NEW_REPORT');
    flags.set(args[i], args[i + 1]);
  }
  for (const name of ['--package', '--cases', '--json']) assert(flags.has(name), `missing ${name}`);
  const output = resolve(flags.get('--json'));
  assert(!existsSync(output), 'report exists; choose a new path');
  const report = { format: 'owl-public-artifact-v1', timeUtc: new Date().toISOString(),
    status: 'error', scope: 'restricted consistency API; no entailment or OWL completeness claim',
    artifact: {}, cases: [], runtime: process.version };
  try {
    const pkg = realpathSync(flags.get('--package'));
    const casesPath = realpathSync(flags.get('--cases'));
    const cases = inventory(casesPath);
    report.sourceReportSha256 = digest(readFileSync(casesPath));
    report.toolSha256 = digest(readFileSync(SELF));
    report.packagePath = pkg;
    for (const file of ['package.json', 'index.mjs', 'lib/api.mjs', 'lib/lean-entry.mjs',
      'l4-assets/l4factoidal.js', 'l4-assets/l4factoidal.mjs', 'l4-assets/l4factoidal.wasm']) {
      const bytes = readFileSync(join(pkg, file));
      assert(bytes.length > 0, `empty artifact: ${file}`);
      report.artifact[file] = { bytes: bytes.length, sha256: digest(bytes) };
    }
    const env = { ...process.env, FACTOIDAL_L4_ASSETS: join(pkg, 'l4-assets') };
    for (const c of cases) {
      const run = spawnSync(process.execPath, [SELF, '--child', pkg, casesPath, c.id],
        { env, encoding: 'utf8', timeout: 15000, killSignal: 'SIGKILL', maxBuffer: 2 * 1024 * 1024 });
      const lines = (run.stdout || '').split('\n').filter(line => line.startsWith(PREFIX));
      let observed;
      if (lines.length === 1) observed = JSON.parse(lines[0].slice(PREFIX.length));
      const passed = !run.error && run.status === 0 && observed?.id === c.id && observed?.status === 'pass';
      report.cases.push({ id: c.id, passed, observed, exitCode: run.status, signal: run.signal,
        error: run.error?.message, stdout: run.stdout, stderr: run.stderr });
    }
    report.status = report.cases.every(c => c.passed) ? 'pass' : 'fail';
  } catch (error) { report.error = String(error.stack || error); }
  writeFileSync(output, JSON.stringify(report, null, 2) + '\n', { flag: 'wx' });
  console.log(`OWL public artifact: ${report.status}; ${report.cases.filter(c => c.passed).length}/${report.cases.length} cases`);
  console.log(`Evidence: ${output}`);
  process.exitCode = report.status === 'pass' ? 0 : report.status === 'fail' ? 1 : 2;
}

await main();
