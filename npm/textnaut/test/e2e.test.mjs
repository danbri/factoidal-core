// Packs the package, installs the tarball into a temporary directory outside the repository and
// runs it for real with the pinned Wasm engine. Downloads the engine (8.1 MB) once, into a
// temporary cache. Skipped, with the reason, when there is no Deno or TEXTNAUT_NO_NETWORK is set.
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, readdirSync, readFileSync, statSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const page = join(root, '..', '..', 'labs', 'demos', 'foafnaut', 'pages', 'showcase.html');
const hasDeno = spawnSync('deno', ['--version']).status === 0;
const skip = !hasDeno ? 'no deno' : process.env.TEXTNAUT_NO_NETWORK ? 'TEXTNAUT_NO_NETWORK is set' : false;

test('packed tarball, installed elsewhere, dumps a page on the fetched Wasm engine', { skip, timeout: 300000 }, () => {
  const work = mkdtempSync(join(tmpdir(), 'textnaut-e2e-'));
  const packed = JSON.parse(execFileSync('npm', ['pack', '--json', '--pack-destination', work], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }));
  const tarball = join(work, packed[0].filename);
  console.log(`tarball ${packed[0].filename}: ${statSync(tarball).size} bytes packed, ${packed[0].unpackedSize} unpacked, ${packed[0].files.length} files`);
  const prefix = join(work, 'install');
  execFileSync('npm', ['install', '--prefix', prefix, '--no-audit', '--no-fund', '--ignore-scripts', tarball], { stdio: 'ignore' });
  const bin = join(prefix, 'node_modules', '.bin', 'textnaut');
  const home = join(work, 'home');
  const env = { PATH: process.env.PATH, HOME: home, TEXTNAUT_CACHE: join(work, 'cache'), DENO_DIR: join(work, 'deno'), TERM: 'dumb' };

  const first = spawnSync(bin, ['--dump', '--width', '70', page], { encoding: 'utf8', env, cwd: work, timeout: 240000 });
  assert.equal(first.status, 0, first.stderr);
  assert(/fetching the Wasm engine, once: 8\.1 MB/.test(first.stderr), first.stderr);
  assert(/engine wasm/.test(first.stderr), first.stderr);
  assert(first.stdout.length > 200 && /\[\d+\]/.test(first.stdout), first.stdout.slice(0, 300));
  console.log(first.stderr.trim().split('\n').slice(-1)[0]);

  // The cache holds the two runtime files only.
  const cached = readdirSync(join(work, 'cache'))[0];
  assert.deepEqual(readdirSync(join(work, 'cache', cached)).sort(), ['PIN.json', 'web-render.mjs', 'web-render.wasm']);

  // The second run uses the cache and gives the same text.
  const second = spawnSync(bin, ['--dump', '--width', '70', page], { encoding: 'utf8', env, cwd: work, timeout: 120000 });
  assert.equal(second.status, 0, second.stderr);
  assert(!/fetching/.test(second.stderr));
  assert.equal(second.stdout, first.stdout);

  // A screensaver needs no engine: with an empty cache directory nothing is fetched.
  const saver = spawnSync(bin, ['--screensaver', 'life', '--frames', '2'], { encoding: 'utf8', env: { ...env, TEXTNAUT_CACHE: join(work, 'empty') }, cwd: work, timeout: 60000 });
  assert.equal(saver.status, 0, saver.stderr);
  assert(!/fetching/.test(saver.stderr) && saver.stdout.includes('\x1b['));
  assert.throws(() => readdirSync(join(work, 'empty')));

  // A corrupted cached file is not used: it is fetched again, or refused.
  const wasm = join(work, 'cache', cached, 'web-render.wasm');
  execFileSync('node', ['-e', `const fs=require('fs');const b=fs.readFileSync(${JSON.stringify(wasm)});b[1000]^=1;fs.writeFileSync(${JSON.stringify(wasm)},b)`]);
  const third = spawnSync(bin, ['--dump', '--width', '70', page], { encoding: 'utf8', env: { ...env, TEXTNAUT_CACHE: join(work, 'cache') }, cwd: work, timeout: 240000 });
  assert(/fetching/.test(third.stderr), 'a damaged cache is fetched again');
  assert.equal(third.stdout, first.stdout);
});
