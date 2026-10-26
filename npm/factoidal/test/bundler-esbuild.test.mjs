// Proves the bundler route of issue #682 end to end, on the Lean engine:
// esbuild --bundle over test/fixtures/bundler-app.mjs (which imports only
// '@factoidal/core/api' and the engine loader
// '@factoidal/core/l4-assets/l4factoidal.js', both statically) produces
// output that runs standalone, with the wasm handed in through the loader's
// instantiateWasm hook. The browser page under a Content-Security-Policy
// with no 'unsafe-eval' is proved separately by
// tests/web-demos/bundler_csp_smoke.sh, which bundles the same fixture and
// drives it through headless Chromium.
//
// Skips (does not fail) only when esbuild cannot be resolved -- `npm
// install` in npm/factoidal (esbuild is a devDependency) makes it
// resolvable; every other failure here is a regression.
//
// esbuild `external` list: the Emscripten glue (l4-assets/l4factoidal.mjs)
// has one dynamic `import("node:module")`, taken only when it runs under
// Node (it builds a `require` from it to read the wasm file). A browser
// bundle cannot resolve a `node:` specifier, so it must be external; in a
// browser that branch never runs. Every other Node access in the glue goes
// through that local `require`, which esbuild leaves alone. The list is
// derived from esbuild's own "Could not resolve" errors, not hard-coded,
// and the test asserts it is exactly ['node:module'].

import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';

const PKG_ROOT = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const FIXTURE = path.join(PKG_ROOT, 'test', 'fixtures', 'bundler-app.mjs');

// ESM test file: no CJS `require` in scope by default -- needed to
// load esbuild's own (CommonJS) package.
const require = createRequire(import.meta.url);

let esbuild = null;
let esbuildSkipReason = null;
try {
  esbuild = require('esbuild');
} catch (e) {
  esbuildSkipReason = `esbuild not resolvable in npm/factoidal (devDependency; ` +
    `run 'npm install' in npm/factoidal): ${e.message}`;
}

// esbuild resolves bare imports by walking up from the importing
// file's directory looking for node_modules/<name> at each ancestor
// (standard Node algorithm) -- a self-referencing symlink at
// npm/factoidal/node_modules/@factoidal/core, pointing at the package
// root itself, makes '@factoidal/core/...' resolve exactly as it
// would for a real consumer that ran `npm install @factoidal/core`,
// with no esbuild `alias` option needed.
function ensureSelfSymlink() {
  const nmDir = path.join(PKG_ROOT, 'node_modules');
  const scopeDir = path.join(nmDir, '@factoidal');
  const linkPath = path.join(scopeDir, 'core');
  fs.mkdirSync(scopeDir, { recursive: true });
  const already = fs.existsSync(linkPath) &&
    fs.lstatSync(linkPath).isSymbolicLink() &&
    fs.realpathSync(linkPath) === fs.realpathSync(PKG_ROOT);
  if (already) return;
  fs.rmSync(linkPath, { recursive: true, force: true });
  fs.symlinkSync(PKG_ROOT, linkPath, 'dir');
}

// Parse esbuild's "Could not resolve \"X\"" build-error text into the
// bare specifier X, deduplicated.
function unresolvedSpecifiers(esbuildError) {
  const specs = new Set();
  for (const err of (esbuildError && esbuildError.errors) || []) {
    const m = /Could not resolve "([^"]+)"/.exec(err.text || '');
    if (m) specs.add(m[1]);
  }
  return [...specs];
}

test('esbuild --bundle over the CSP fixture runs under Node (platform: browser, format: esm)',
  async (t) => {
    if (esbuildSkipReason) { t.skip(esbuildSkipReason); return; }

    ensureSelfSymlink();

    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-bundler-test-'));
    const outfile = path.join(outDir, 'bundle.mjs');

    const baseOptions = {
      entryPoints: [FIXTURE],
      outfile,
      bundle: true,
      platform: 'browser',
      format: 'esm',
      write: true,
      logLevel: 'silent',
    };

    const t0 = Date.now();
    let externalList = [];
    try {
      await esbuild.build(baseOptions);
    } catch (firstError) {
      externalList = unresolvedSpecifiers(firstError);
      assert.ok(externalList.length > 0,
        'esbuild build failed and reported no "Could not resolve" ' +
        `specifiers to mark external -- real failure:\n${firstError && firstError.message}`);
      await esbuild.build({ ...baseOptions, external: externalList });
    }
    const bundleMs = Date.now() - t0;
    console.log(`  esbuild bundle: ${bundleMs}ms, external=[${externalList.join(', ')}]`);

    // The empirically-derived external list must be exactly the glue's one
    // Node-only dynamic import (see the header): a stray extra name means
    // something in the fixture's import graph started importing a Node
    // built-in, which this test should catch rather than externalize.
    assert.deepEqual([...externalList].sort(), ['node:module'],
      'external list drifted from the documented Emscripten glue import');

    assert.ok(fs.existsSync(outfile), 'esbuild wrote the bundle output');
    const bundleSource = fs.readFileSync(outfile, 'utf8');
    assert.ok(!/new Function\(/.test(bundleSource), 'no new Function( in the bundle');

    // The page's part: hand the wasm bytes to the fixture's instantiateWasm.
    const wasmPath = path.join(PKG_ROOT, 'l4-assets', 'l4factoidal.wasm');
    const runSource =
      `import { readFileSync as __readWasm } from 'node:fs';\n` +
      `globalThis.__FACTOIDAL_WASM_BYTES__ = __readWasm(${JSON.stringify(wasmPath)});\n` +
      bundleSource;

    let stdout;
    try {
      stdout = execFileSync(process.execPath, ['--input-type=module'], {
        input: runSource,
        encoding: 'utf8',
        timeout: 30000,
      });
    } catch (runError) {
      assert.fail(
        'running the bundled output under Node failed ' +
        `(exit ${runError.status}):\nstdout: ${runError.stdout}\nstderr: ${runError.stderr}`);
    }

    const m = /ROW_COUNT:(\d+)/.exec(stdout);
    assert.ok(m, `bundle output did not print ROW_COUNT:N -- got:\n${stdout}`);
    assert.equal(Number(m[1]), 3, 'SELECT ?p WHERE { ?p a foaf:Person } returns 3 rows');

    fs.rmSync(outDir, { recursive: true, force: true });
  });
