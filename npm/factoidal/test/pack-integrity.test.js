// A consumer who `npm install`s @factoidal/core gets a working engine
// straight out of the packed tarball, not the source tree:
//
//   1. `npm pack` on npm/factoidal produces a tarball.
//   2. Its file list holds the Lean engine (l4-assets/l4factoidal.wasm,
//      .mjs, .js), and no F* bundle, no hacl-wasm, no core wasm and no
//      sample store (one engine since 0.9.0; one fat wasm and no demo
//      content since 0.10.0, owner 2026-10-20).
//   3. From the EXTRACTED tarball: require() and import() of the main
//      entry parse and query a graph.
//   4. From the EXTRACTED tarball: `factoidal pack` and `activate` build a
//      store from three triples, and openStore() answers COUNT 3.
//
// The extracted package resolves its engine from its own l4-assets/. The
// test sets FACTOIDAL_L4_ASSETS to an empty value for the child process so
// no override can point it back at the source tree.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const os = require('node:os');
const { execFileSync } = require('node:child_process');

const PKG_ROOT = path.resolve(__dirname, '..');

const PROBE = `
const assert = require('node:assert/strict');
(async () => {
  const f = require(process.argv[1]);
  const ds = await f.parse('@prefix ex: <http://example.org/> . ex:a ex:p "x" , "y" .');
  assert.equal(ds.size, 2);
  const rows = await f.query(ds, 'SELECT ?o WHERE { ?s ?p ?o } ORDER BY ?o');
  assert.deepEqual(rows.map((r) => r.get('o').value), ['x', 'y']);
  const esm = await import(require('node:url').pathToFileURL(require('node:path').join(process.argv[1], 'index.mjs')).href);
  assert.equal(esm.parse, f.parse, 'import() and require() give the same module');
  const fs = require('node:fs'), path = require('node:path'), cp = require('node:child_process');
  const dir = fs.mkdtempSync(path.join(require('node:os').tmpdir(), 'factoidal-pack-store-'));
  fs.writeFileSync(path.join(dir, 'd.ttl'), '<http://e/a> <http://e/p> 1, 2, 3 .\\n');
  fs.mkdirSync(path.join(dir, 'store', 'gen-1'), { recursive: true });
  const cli = path.join(process.argv[1], 'bin', 'factoidal.mjs');
  cp.execFileSync(process.execPath, [cli, 'pack', path.join(dir, 'd.ttl'), path.join(dir, 'store', 'gen-1'), '--quiet']);
  cp.execFileSync(process.execPath, [cli, 'activate', path.join(dir, 'store'), 'gen-1']);
  const store = await f.openStore(path.join(dir, 'store'));
  const n = await store.query('SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
  assert.equal(Number(n[0].get('n').value), 3);
  await store.close();
  fs.rmSync(dir, { recursive: true, force: true });
  const engineMod = await import(require('node:url').pathToFileURL(require('node:path').join(process.argv[1], 'bin', 'engine.mjs')).href);
  const loaded = engineMod.resolveEngine();
  process.stdout.write(JSON.stringify({ ok: true, loaded }));
})().catch((e) => { process.stderr.write(String(e && e.stack || e)); process.exit(1); });
`;

test('pack integrity: npm pack + extract + parse/query/openStore from the tarball', () => {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-pack-'));
  try {
    const packJson = execFileSync('npm', ['pack', '--json', '--pack-destination', tmp], {
      cwd: PKG_ROOT, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'],
    });
    const info = JSON.parse(packJson)[0];
    const files = info.files.map((f) => f.path);
    for (const required of ['l4-assets/l4factoidal.wasm', 'l4-assets/l4factoidal.mjs',
      'l4-assets/l4factoidal.js', 'index.js', 'index.mjs', 'browser.js', 'lib/api.mjs',
      'lib/lean-entry.mjs', 'rdfjs.mjs']) {
      assert.ok(files.includes(required), `tarball lacks ${required}`);
    }
    const forbidden = files.filter((p) => /^(factoidal[-.].*\.js|hacl-wasm\/|wasm\.js|lite\.|select\.|browser-wasm\.js|hacl-init\.js|factoidal\.wasm\.assets\/|factoidal-npm-entry)/.test(p));
    assert.deepEqual(forbidden, [], 'no F* bundle and no hacl-wasm in the tarball');
    const demo = files.filter((p) => /^(l4-assets\/l4factoidal-core\.|core\.|core-browser\.|sample-store\/|test\/)/.test(p));
    assert.deepEqual(demo, [], 'no core wasm, no sample store and no tests in the tarball');

    execFileSync('tar', ['xzf', path.join(tmp, info.filename), '-C', tmp]);
    const pkgDir = path.join(tmp, 'package');
    const out = execFileSync(process.execPath, ['-e', PROBE, pkgDir], {
      encoding: 'utf8', env: { ...process.env, FACTOIDAL_L4_ASSETS: '' },
    });
    const r = JSON.parse(out);
    assert.equal(r.ok, true);
    assert.ok(r.loaded.startsWith(pkgDir), `the engine came from the tarball (${r.loaded})`);
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
});
