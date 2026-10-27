// The load-time check of the engine against its release stamp
// (https://github.com/danbri/factoidal/issues/1106, layer 1; 0.20.0).
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { cpSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { checkEngineStamp, sha256Hex } from '../lib/engine-integrity.mjs';

const pkg = join(dirname(fileURLToPath(import.meta.url)), '..');
const bytes = new TextEncoder().encode('not really a wasm');
const hex = createHash('sha256').update(bytes).digest('hex');

test('sha256Hex is the SHA-256 of the bytes', async () => {
  assert.equal(await sha256Hex(bytes), hex);
});

test('checkEngineStamp: a match passes, a change refuses, no stamp is unchecked', async () => {
  assert.deepEqual(await checkEngineStamp(bytes, { stamped: true, wasmSha256: hex, wasmBytes: bytes.length }),
    { checked: true, sha256: hex });
  await assert.rejects(checkEngineStamp(bytes, { stamped: true, wasmSha256: '0'.repeat(64), wasmBytes: bytes.length }),
    (e) => e.code === 'engine.modified' && /not the engine of this release/.test(e.message));
  await assert.rejects(checkEngineStamp(bytes, { stamped: true, wasmSha256: hex, wasmBytes: bytes.length + 1 }),
    (e) => e.code === 'engine.modified');
  assert.deepEqual(await checkEngineStamp(bytes, null), { checked: false });
  assert.deepEqual(await checkEngineStamp(bytes, { stamped: false }), { checked: false });
  const warned = [];
  const r = await checkEngineStamp(bytes, { stamped: true, wasmSha256: '0'.repeat(64) },
    { allowModified: true, warn: (m) => warned.push(m) });
  assert.equal(r.checked, false);
  assert.equal(warned.length, 1);
  assert.match(warned[0], /FACTOIDAL_ALLOW_MODIFIED_ENGINE/);
});

// A copy of the package's engine loader, with its l4-assets and a version.json
// the test writes: loadEngine() of that copy.
function loadCopy(stamp, env = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'factoidal-integrity-'));
  try {
    for (const d of ['bin', 'lib', 'store-host', 'l4-assets']) cpSync(join(pkg, d), join(dir, d), { recursive: true });
    writeFileSync(join(dir, 'package.json'), readFileSync(join(pkg, 'package.json')));
    if (stamp !== undefined) writeFileSync(join(dir, 'l4-assets', 'version.json'), JSON.stringify(stamp));
    const code = "import('./bin/engine.mjs').then((m) => m.loadEngine()).then(" +
      "(e) => { console.log('LOADED', typeof e.call); }, (e) => { console.log('REFUSED', e.code); process.exit(3); })";
    return spawnSync(process.execPath, ['--input-type=module', '-e', code],
      { cwd: dir, encoding: 'utf8', env: { ...process.env, ...env } });
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

const wasm = readFileSync(join(pkg, 'l4-assets', 'l4factoidal.wasm'));
const wasmHex = createHash('sha256').update(wasm).digest('hex');

test('loadEngine refuses a stamped engine whose bytes differ, and names both digests', () => {
  const r = loadCopy({ stamped: true, wasmSha256: '0'.repeat(64), wasmBytes: wasm.length, gitSha: 'x' });
  assert.equal(r.status, 3, r.stdout + r.stderr);
  assert.match(r.stdout, /REFUSED engine\.modified/);
});

test('loadEngine loads an engine that matches its stamp, or has no stamp', () => {
  let r = loadCopy({ stamped: true, wasmSha256: wasmHex, wasmBytes: wasm.length });
  assert.equal(r.status, 0, r.stdout + r.stderr);
  assert.match(r.stdout, /LOADED function/);
  r = loadCopy({ stamped: false });
  assert.equal(r.status, 0, r.stdout + r.stderr);
});

test('FACTOIDAL_ALLOW_MODIFIED_ENGINE loads a changed engine, with a warning', () => {
  const r = loadCopy({ stamped: true, wasmSha256: '0'.repeat(64), wasmBytes: wasm.length },
    { FACTOIDAL_ALLOW_MODIFIED_ENGINE: '1' });
  assert.equal(r.status, 0, r.stdout + r.stderr);
  assert.match(r.stdout, /LOADED/);
  assert.match(r.stderr, /not the engine of this release/);
});
