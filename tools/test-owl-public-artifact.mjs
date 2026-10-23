#!/usr/bin/env node
// Synthetic controls for the real artifact runner. These fixtures contain no
// engine: passing them tests the runner's contracts, not OWL or Wasm behavior.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { spawn } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const SELF = fileURLToPath(import.meta.url);
const RUNNER = join(dirname(SELF), 'check-owl-public-artifact.mjs');
const TIMEOUT_SENTINEL = 'SYNTHETIC_OWL_TIMEOUT_ENTERED';
const GENERIC_SENTINEL = 'SYNTHETIC_OWL_GENERIC_ERROR_ENTERED';
const digest = data => createHash('sha256').update(data).digest('hex');

function flagsOf(args) {
  const flags = new Map();
  for (let i = 0; i < args.length; i += 2) {
    assert(['--cases', '--json'].includes(args[i]) && args[i + 1] && !flags.has(args[i]),
      'Usage: --cases PASSING_SOURCE_REPORT --json NEW_REPORT');
    flags.set(args[i], args[i + 1]);
  }
  assert.equal(flags.size, 2, 'Supply --cases and --json');
  return flags;
}

function fakePackage(path, source, scenario) {
  mkdirSync(join(path, 'lib'), { recursive: true });
  mkdirSync(join(path, 'l4-assets'), { recursive: true });
  writeFileSync(join(path, 'package.json'), JSON.stringify({
    name: '@factoidal/synthetic-owl-artifact-control', version: '0.0.0-control',
    private: true, type: 'module', synthetic: true,
    description: 'Runner control only; no semantic engine; never publish',
  }));
  writeFileSync(join(path, 'cases.json'), JSON.stringify(source));
  for (const name of ['lib/api.mjs', 'lib/lean-entry.mjs', 'l4-assets/l4factoidal.js',
    'l4-assets/l4factoidal.mjs', 'l4-assets/l4factoidal.wasm']) {
    writeFileSync(join(path, name), 'SYNTHETIC runner control placeholder; no engine.\n');
  }
  writeFileSync(join(path, 'index.mjs'), `
// SYNTHETIC runner control. This is not a Lean, Wasm, or OWL implementation.
import { readFileSync } from 'node:fs';
const cases = JSON.parse(readFileSync(new URL('./cases.json', import.meta.url))).cases;
const scenario = ${JSON.stringify(scenario)};
const owlSpec = 'https://www.w3.org/TR/owl2-mapping-to-rdf/#Mapping_from_RDF_Graphs_to_the_Structural_Specification';
export class FactoidalError extends Error {
  constructor(message, info) {
    super(message); this.name = 'FactoidalError';
    Object.assign(this, { position: null, spec: null }, info);
  }
}
function dispatchEnvelope(c) {
  const raw = JSON.parse(c.response);
  if (c.expectedOk) return raw;
  return c.id === 'parse-error'
    ? { ...raw, code: 'reason.failed' }
    : { ...raw, code: 'owl.unsupported-rdf12', spec: owlSpec };
}
export async function loadEngine() {
  if (scenario === 'timeout' && process.argv.at(-1) === 'empty') {
    process.on('SIGTERM', () => console.log('SYNTHETIC_SIGTERM_IGNORED'));
    console.log(${JSON.stringify(TIMEOUT_SENTINEL)});
    await new Promise(() => setInterval(() => {}, 1000));
  }
  return { call(op, args) {
    if (op !== 'owlIsConsistent') throw new Error('unexpected synthetic op');
    const c = cases.find(c => c.input === args[0] && c.options === args[1]);
    if (!c) throw new Error('unexpected synthetic input/options');
    if (scenario === 'generic-error' && c.id === 'rdf12-refusal') {
      console.log(${JSON.stringify(GENERIC_SENTINEL)});
      throw new Error('synthetic generic runtime failure without envelope');
    }
    const envelope = dispatchEnvelope(c);
    if (!envelope.ok) throw Object.assign(new Error(envelope.error), { envelope });
    return envelope;
  }};
}
export async function owlIsConsistent(input, options) {
  const c = cases.find(c => c.input === input && (options.fuel === undefined
    ? c.options === '' : c.options === JSON.stringify({ fuel: String(options.fuel) })));
  if (!c) throw new Error('unexpected synthetic public input/options');
  const envelope = dispatchEnvelope(c);
  if (c.expectedOk) return { consistent: envelope.consistent, reason: envelope.reason };
  if (c.id === 'parse-error') throw new FactoidalError('expected object', {
    code: 'parse.syntax', spec: 'https://www.w3.org/TR/rdf12-n-quads/#sec-grammar',
    format: 'nquads', position: { line: 1, column: 17, offset: 16, byteOffset: 16 },
  });
  throw new FactoidalError(envelope.error, { code: envelope.code, spec: envelope.spec });
}
`);
}

// A process group lets the outer deadline clean up a runner and any child it
// failed to kill. Without that, an ignored SIGTERM could leak an orphan.
async function runRunner(pkg, cases, output) {
  const env = { ...process.env };
  delete env.NODE_OPTIONS;
  delete env.FACTOIDAL_L4_ASSETS;
  const started = Date.now();
  return new Promise((done, reject) => {
    const child = spawn(process.execPath, [RUNNER, '--package', pkg, '--cases', cases, '--json', output],
      { detached: true, env, stdio: ['ignore', 'pipe', 'pipe'] });
    let stdout = '', stderr = '', deadlineExceeded = false, outputExceeded = false;
    const killGroup = () => {
      try { process.kill(-child.pid, 'SIGKILL'); }
      catch (error) { if (error.code !== 'ESRCH') throw error; }
    };
    const timer = setTimeout(() => { deadlineExceeded = true; killGroup(); }, 35000);
    const append = (which, chunk) => {
      if (which === 'stdout') stdout += chunk;
      else stderr += chunk;
      if (stdout.length + stderr.length > 4 * 1024 * 1024) {
        outputExceeded = true; killGroup();
      }
    };
    child.stdout.setEncoding('utf8').on('data', data => append('stdout', data));
    child.stderr.setEncoding('utf8').on('data', data => append('stderr', data));
    child.once('error', error => { clearTimeout(timer); reject(error); });
    child.once('close', (exitCode, signal) => {
      clearTimeout(timer);
      killGroup();
      done({ exitCode, signal, deadlineExceeded, outputExceeded,
        elapsedMs: Date.now() - started, stdout, stderr });
    });
  });
}

function assertInventory(result, source) {
  assert.equal(result.format, 'owl-public-artifact-v1');
  assert.equal(result.error, undefined, 'setup/import/inventory errors are not control evidence');
  assert.deepEqual(result.cases.map(c => c.id).sort(), source.cases.map(c => c.id).sort());
  assert.equal(Object.keys(result.artifact).length, 7, 'all synthetic artifacts must be inventoried');
}

async function main() {
  const flags = flagsOf(process.argv.slice(2));
  const output = resolve(flags.get('--json'));
  assert(!existsSync(output), 'report exists; choose a new path');
  const report = { format: 'owl-public-artifact-controls-v1', timeUtc: new Date().toISOString(),
    status: 'error', synthetic: true, scope: 'Runner QA only; no OWL, Wasm, or package conformance claim',
    runtime: process.version, controls: [], expectedControls: 3, temporaryFilesCleaned: false };
  let temporary;
  try {
    assert.notEqual(process.platform, 'win32', 'SIGKILL process-group controls require a POSIX host');
    const casesPath = resolve(flags.get('--cases'));
    const sourceBytes = readFileSync(casesPath);
    const source = JSON.parse(sourceBytes);
    assert.equal(source.format, 'owl-public-boundary-v1');
    assert.equal(source.status, 'pass');
    assert.equal(source.cases.length, 20);
    assert(source.cases.every(c => c.passed && typeof c.dispatchResponse === 'string'));
    report.sourceReportSha256 = digest(sourceBytes);
    report.runnerSha256 = digest(readFileSync(RUNNER));
    report.controlToolSha256 = digest(readFileSync(SELF));
    temporary = mkdtempSync(join(tmpdir(), 'owl-artifact-controls-'));
    for (const scenario of ['baseline', 'generic-error', 'timeout']) {
      const pkg = join(temporary, scenario);
      fakePackage(pkg, source, scenario);
      const resultPath = join(temporary, scenario + '.json');
      const run = await runRunner(pkg, casesPath, resultPath);
      const control = { name: scenario, expectedStatus: scenario === 'baseline' ? 'pass' : 'fail',
        passed: false, run };
      report.controls.push(control);
      assert(!run.deadlineExceeded && !run.outputExceeded, 'outer deadline or output limit fired');
      assert.equal(run.signal, null, 'runner itself must exit normally');
      assert(existsSync(resultPath), 'runner must produce its own report');
      const result = JSON.parse(readFileSync(resultPath));
      control.runnerReport = result;
      assertInventory(result, source);
      assert.equal(result.status, control.expectedStatus);
      assert.equal(run.exitCode, scenario === 'baseline' ? 0 : 1);
      const failed = result.cases.filter(c => !c.passed);
      if (scenario === 'baseline') {
        assert.equal(failed.length, 0, 'synthetic baseline must pass every case');
      } else {
        assert.equal(failed.length, 1, 'only the injected failure may fail');
        const failure = failed[0];
        assert(result.cases.filter(c => c !== failure).every(c => c.observed?.status === 'pass'));
        if (scenario === 'generic-error') {
          assert.equal(failure.id, 'rdf12-refusal');
          assert.equal(failure.exitCode, 1);
          assert.equal(failure.signal, null);
          assert(failure.stdout.includes(GENERIC_SENTINEL));
          assert(failure.observed?.error.includes('refusal must carry its ABI envelope'));
          assert.equal(failure.observed.lowLevel, null);
        } else {
          assert.equal(failure.id, 'empty');
          assert.equal(failure.signal, 'SIGKILL');
          assert.equal(failure.exitCode, null);
          assert(failure.error.includes('ETIMEDOUT'));
          assert(failure.stdout.includes(TIMEOUT_SENTINEL));
          assert.equal(failure.observed, undefined);
          assert(run.elapsedMs >= 14000 && run.elapsedMs < 35000, 'child timeout must bound the run');
        }
      }
      control.passed = true;
    }
    report.status = 'pass';
  } catch (error) {
    report.status = report.controls.length ? 'fail' : 'error';
    report.error = String(error.stack || error);
  } finally {
    if (temporary) { rmSync(temporary, { recursive: true, force: true }); report.temporaryFilesCleaned = true; }
  }
  mkdirSync(dirname(output), { recursive: true });
  writeFileSync(output, JSON.stringify(report, null, 2) + '\n', { flag: 'wx' });
  console.log(`Synthetic OWL artifact controls: ${report.status}; ${report.controls.filter(c => c.passed).length}/3`);
  console.log(`Evidence: ${output}`);
  process.exitCode = report.status === 'pass' ? 0 : 1;
}

await main();
