import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join, relative } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { appFiles, sync } from '../scripts/sync.mjs';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const source = join(root, '..', '..', 'labs', 'demos', 'foafnaut');
const hasDeno = spawnSync('deno', ['--version']).status === 0;

test('the bin is textnaut and nothing in @factoidal/core uses that name', () => {
  const mine = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  const core = JSON.parse(readFileSync(join(root, '..', 'factoidal', 'package.json'), 'utf8'));
  assert.deepEqual(Object.keys(mine.bin), ['textnaut']);
  assert(!(mine.name in { [core.name]: 1 }));
  for (const name of Object.keys(mine.bin)) assert(!(name in core.bin), `${name} is also a bin of ${core.name}`);
  assert.deepEqual(mine.dependencies ?? {}, {}, 'no runtime dependencies');
  assert.equal(mine.license, 'Apache-2.0');
});

test('app/ holds exactly what textnaut.ts imports, plus the import map and its target', { skip: !hasDeno }, () => {
  sync();
  const info = JSON.parse(execFileSync('deno', ['info', '--json', `--import-map=${join(source, 'textnaut', 'import_map.json')}`, join(source, 'textnaut', 'textnaut.ts')], { encoding: 'utf8' }));
  const imported = info.modules.map((m) => m.specifier).filter((s) => s.startsWith('file://')).map((s) => relative(source, new URL(s).pathname)).sort();
  assert(imported.length >= 10, imported.join());
  const wanted = [...imported, 'textnaut/import_map.json'].sort();
  assert.deepEqual(appFiles(), wanted);
  for (const f of wanted) assert(existsSync(join(root, 'app', f)), f);
});

test('npm pack lists every file needed and only those', () => {
  const out = JSON.parse(execFileSync('npm', ['pack', '--dry-run', '--json'], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }));
  const files = out[0].files.map((f) => f.path).sort();
  const expected = ['LICENSE', 'NOTICE', 'README.md', 'package.json', 'engine-pin.json', 'bin/textnaut.mjs', 'lib/engine.mjs', ...appFiles().map((f) => `app/${f}`)].sort();
  assert.deepEqual(files, expected);
  assert(files.every((f) => !/\.test\.|\.py$|pty_check|\.wasm$|\.dylib$/.test(f)), 'no tests, scripts or binaries');
});

test('the launcher says so, with an install hint, when Deno is missing; and --help needs no Deno', () => {
  const bin = join(root, 'bin', 'textnaut.mjs');
  const run = spawnSync(process.execPath, [bin, '--screensaver'], { encoding: 'utf8', env: { ...process.env, DENO: '/nonexistent/deno' } });
  assert.equal(run.status, 127);
  assert(/Deno was not found/.test(run.stderr) && /install/.test(run.stderr) && /2\.0\.0/.test(run.stderr), run.stderr);
  const help = spawnSync(process.execPath, [bin, '--help'], { encoding: 'utf8', env: { ...process.env, DENO: '/nonexistent/deno' } });
  assert.equal(help.status, 0);
  assert(/Wasm engine/.test(help.stdout));
});

test('every file of the notice list is present in NOTICE', () => {
  const notice = readFileSync(join(root, 'NOTICE'), 'utf8');
  for (const name of ['Lean 4 runtime', 'mimalloc', 'Emscripten', 'musl', 'libc++', 'HACL', 'Unicode', 'WHATWG']) assert(notice.includes(name), name);
  assert(!/QuickJS/i.test(notice));
});
