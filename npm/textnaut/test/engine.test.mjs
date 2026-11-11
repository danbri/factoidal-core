import assert from 'node:assert/strict';
import { existsSync, mkdtempSync, readdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from 'node:test';
import { gunzipSync, gzipSync } from 'node:zlib';
import { cacheDir, checkTarball, chooseEngine, ensureEngine, pin, sha256, untar } from '../lib/engine.mjs';

function tar(files) {
  const blocks = [];
  for (const [name, data] of Object.entries(files)) {
    const header = Buffer.alloc(512);
    header.write(name.slice(-100), 0);
    header.write('0000644\0', 100); header.write('0000000\0', 108); header.write('0000000\0', 116);
    header.write(data.length.toString(8).padStart(11, '0') + '\0', 124);
    header.write('00000000000\0', 136); header.write('        ', 148); header.write('0', 156); header.write('ustar\0' + '00', 257);
    let sum = 0; for (const b of header) sum += b;
    header.write(sum.toString(8).padStart(6, '0') + '\0 ', 148);
    blocks.push(header, data, Buffer.alloc((512 - data.length % 512) % 512));
  }
  blocks.push(Buffer.alloc(1024));
  return Buffer.concat(blocks);
}
/** A pin and a download for two small made-up runtime files. */
function fixture() {
  const mjs = Buffer.from('export default async () => ({});\n'), wasm = Buffer.from([0, 97, 115, 109, 1, 0, 0, 0]);
  const gz = gzipSync(tar({ 'docs/other.txt': Buffer.from('x'), 'docs/rt/web-render.mjs': mjs, 'docs/rt/web-render.wasm': wasm }));
  const thePin = {
    tarball: { bytes: gz.length, sha256: sha256(gz) },
    files: { 'docs/rt/web-render.mjs': { name: 'web-render.mjs', bytes: mjs.length, sha256: sha256(mjs) }, 'docs/rt/web-render.wasm': { name: 'web-render.wasm', bytes: wasm.length, sha256: sha256(wasm) } },
  };
  return { gz, thePin, mjs, wasm };
}

test('the pin names a release, a commit and two runtime files with sha256', () => {
  assert.match(pin.release, /^build-386f8fb43f73-foafnaut-web$/);
  assert.match(pin.tarball.sha256, /^[0-9a-f]{64}$/);
  assert.deepEqual(Object.values(pin.files).map((f) => f.name).sort(), ['web-render.mjs', 'web-render.wasm']);
  assert(pin.url.startsWith('https://github.com/danbri/factoidal-builds/releases/download/'));
});

test('a good download gives exactly the two runtime files', () => {
  const { gz, thePin, mjs } = fixture();
  const files = checkTarball(gz, thePin);
  assert.deepEqual(files.map((f) => f.name), ['web-render.mjs', 'web-render.wasm']);
  assert.deepEqual(files[0].data, mjs);
  assert.equal(untar(gunzipSync(gz)).length, 3);
});

test('a corrupted download is refused: one flipped byte, a short file, a wrong inner file', () => {
  const { gz, thePin } = fixture();
  const flipped = Buffer.from(gz); flipped[20] ^= 1;
  assert.throws(() => checkTarball(flipped, thePin), /sha256/);
  assert.throws(() => checkTarball(gz.subarray(0, gz.length - 1), thePin), /bytes/);
  // The right download of the wrong content: the pin names a file hash the archive does not have.
  const bad = { ...thePin, files: { ...thePin.files, 'docs/rt/web-render.wasm': { ...thePin.files['docs/rt/web-render.wasm'], sha256: '0'.repeat(64) } } };
  assert.throws(() => checkTarball(gz, bad), /pinned sha256/);
});

test('ensureEngine keeps nothing from a corrupted download, and keeps the good one', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'textnaut-cache-'));
  const env = { TEXTNAUT_CACHE: dir };
  const real = pin.tarball;
  const { gz } = fixture();
  const corrupt = Buffer.from(gz); corrupt[30] ^= 255;
  const respond = (bytes) => async () => ({ ok: true, status: 200, arrayBuffer: async () => bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.length) });
  // The real pin does not match the fixture archive, so even an unmodified fixture is refused.
  await assert.rejects(ensureEngine({ env, fetchImpl: respond(corrupt), log: () => {} }), /refused/);
  assert(!existsSync(cacheDir(env)), 'nothing was kept');
  assert.deepEqual(readdirSync(dir).filter((n) => n.includes('tmp')), []);
  assert.equal(pin.tarball, real);
});

test('offline with no cache: a clear error that points to the screensavers', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'textnaut-cache-'));
  const logged = [];
  await assert.rejects(ensureEngine({ env: { TEXTNAUT_CACHE: dir }, fetchImpl: async () => { throw new TypeError('fetch failed', { cause: { code: 'ENOTFOUND' } }); }, log: (s) => logged.push(s) }),
    (error) => /offline/.test(error.message) && /textnaut --screensaver/.test(error.message) && /ENOTFOUND/.test(error.message));
  assert(/8\.1 MB/.test(logged.join('')), 'it said what it was fetching and its size');
});

test('the engine is chosen in the stated order', () => {
  const home = mkdtempSync(join(tmpdir(), 'textnaut-home-'));
  assert.equal(chooseEngine(['--engine', 'x.dylib', 'p.html'], {}, home).how, '--engine');
  assert.equal(chooseEngine(['p.html'], { TEXTNAUT_NATIVE: '/a', TEXTNAUT_WASM_DIR: '/b' }, home).how, 'TEXTNAUT_NATIVE');
  assert.equal(chooseEngine(['p.html'], { TEXTNAUT_WASM_DIR: '/b' }, home).how, 'TEXTNAUT_WASM_DIR');
  assert.equal(chooseEngine(['--wasm', 'p.html'], { TEXTNAUT_NATIVE: '/a' }, home).how, 'pinned Wasm engine');
});

test('the installed foafnaut library comes before the fetch, and FOAFNAUT_HOME moves it', async () => {
  const { mkdirSync, writeFileSync } = await import('node:fs');
  const home = mkdtempSync(join(tmpdir(), 'textnaut-home-'));
  const lib = join(home, 'fh', 'current', 'foafnaut');
  mkdirSync(lib, { recursive: true });
  writeFileSync(join(lib, 'libweb-render.dylib'), ''); writeFileSync(join(lib, 'libweb-render.so'), '');
  const choice = chooseEngine(['p.html'], { FOAFNAUT_HOME: join(home, 'fh') }, home, 'darwin');
  assert.equal(choice.how, 'installed foafnaut');
  assert.equal(choice.env.TEXTNAUT_NATIVE, join(lib, 'libweb-render.dylib'));
  assert.equal(chooseEngine(['p.html'], { FOAFNAUT_HOME: join(home, 'none') }, home, 'darwin').fetch, true);
});

test('the cache directory is keyed by the engine commit', () => {
  assert(cacheDir({ TEXTNAUT_CACHE: '/c' }, '/h').endsWith('engine-386f8fb43f73'));
  assert.equal(cacheDir({ XDG_CACHE_HOME: '/x' }, '/h'), '/x/textnaut/engine-386f8fb43f73');
  assert.equal(cacheDir({}, '/h'), '/h/.cache/textnaut/engine-386f8fb43f73');
});
