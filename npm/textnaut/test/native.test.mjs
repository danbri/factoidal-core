import assert from 'node:assert/strict';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from 'node:test';
import { gzipSync } from 'node:zlib';
import { chooseEngine, sha256 } from '../lib/engine.mjs';
import { checkNativeTarball, installNative, nativeChoice, nativePlatform } from '../lib/native.mjs';

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

const LIB = Buffer.from('\x7fELF made-up library');
const GZ = gzipSync(tar({ 'foafnaut/libweb-render.so': LIB, 'foafnaut/README-linux.txt': Buffer.from('readme'), 'foafnaut/ldd.txt': Buffer.from('x') }));
const TAG = 'build-0123456789ab-foafnaut-linux-x86_64';
const OLD = 'build-aaaaaaaaaaaa-foafnaut-linux-x86_64';
const BRANCH = 'build-bbbbbbbbbbbb-foafnaut-linux-x86_64';
const dl = (tag, name) => `https://github.com/r/b/releases/download/${tag}/${name}`;
const URL_ = dl(TAG, 'foafnaut-linux-x86_64.tar.gz');
const info = (selfContained, sha = '0123456789ab') => ({ source_commit: sha.padEnd(40, 'c'), library: selfContained ? { self_contained: true } : undefined,
  artifacts: { 'foafnaut-linux-x86_64.tar.gz': { sha256: sha256(GZ), size: GZ.length, files: { 'foafnaut/libweb-render.so': { sha256: sha256(LIB), size: LIB.length } } } } });

/**
 * A fetch that serves a release list with one old (toolchain-needing) build of main, one self-contained
 * build of main, and a self-contained branch build published last; and the source repository's compare API.
 */
function fakeFetch(seen = []) {
  const headers = { get: () => null };
  return async (url) => {
    seen.push(url);
    const reply = (body, ok = true) => ({ ok, status: ok ? 200 : 404, headers, json: async () => body, arrayBuffer: async () => body });
    if (url.startsWith('https://api.github.com/repos/r/b/releases?')) {
      return reply([
        { tag_name: OLD, published_at: '2026-11-15T10:00:00Z' },
        { tag_name: TAG, published_at: '2026-11-15T09:00:00Z' },
        { tag_name: 'build-bbbbbbbbbbbb-foafnaut-web', published_at: '2026-11-15T11:00:00Z' },
        { tag_name: BRANCH, published_at: '2026-11-15T12:00:00Z' },
      ]);
    }
    const compare = /\/repos\/danbri\/factoidal-core\/compare\/([0-9a-f]{12})\.\.\.main$/.exec(url);
    if (compare) {
      const ahead = { aaaaaaaaaaaa: 3, '0123456789ab': 5 }[compare[1]];
      return reply(ahead === undefined ? { status: 'diverged', ahead_by: 2, behind_by: 4, base_commit: { sha: compare[1] } }
        : { status: 'ahead', ahead_by: ahead, behind_by: 0, base_commit: { sha: compare[1].padEnd(40, 'c'), commit: { committer: { date: '2026-11-15T08:00:00Z' } } } });
    }
    if (url === dl(OLD, 'build-info.json')) return reply(info(false, 'aaaaaaaaaaaa'));
    if (url === dl(TAG, 'build-info.json')) return reply(info(true));
    if (url === dl(BRANCH, 'build-info.json')) return reply(info(true, 'bbbbbbbbbbbb'));
    if (url === URL_) return reply(GZ.buffer.slice(GZ.byteOffset, GZ.byteOffset + GZ.length));
    return reply(null, false);
  };
}

test('native platforms: Linux x86_64 and arm64 only', () => {
  assert.equal(nativePlatform('linux', 'x64'), 'linux-x86_64');
  assert.equal(nativePlatform('linux', 'arm64'), 'linux-arm64');
  assert.equal(nativePlatform('darwin', 'arm64'), undefined);
  assert.equal(nativePlatform('linux', 'ia32'), undefined);
});

test('latest skips releases that are not self-contained', async () => {
  const choice = await nativeChoice('linux-x86_64', { channel: 'latest', fetchImpl: fakeFetch(), thePin: { repository: 'r/b' }, env: {} });
  assert.equal(choice.release, TAG);
  assert.equal(choice.pinned, false);
  assert.equal(choice.tarball.sha256, sha256(GZ));
});

test('latest never takes a branch build, even one published later', async () => {
  const seen = [];
  const choice = await nativeChoice('linux-x86_64', { channel: 'latest', fetchImpl: fakeFetch(seen), thePin: { repository: 'r/b' }, env: {} });
  assert.equal(choice.release, TAG);
  assert(!seen.includes(dl(BRANCH, 'build-info.json')));
});

test('a named release is used only if it is self-contained', async () => {
  const thePin = { repository: 'r/b' };
  assert.equal((await nativeChoice('linux-x86_64', { channel: TAG, fetchImpl: fakeFetch(), thePin })).release, TAG);
  await assert.rejects(nativeChoice('linux-x86_64', { channel: OLD, fetchImpl: fakeFetch(), thePin }), /not a self-contained/);
  await assert.rejects(nativeChoice('linux-x86_64', { channel: 'build-0123456789ab-foafnaut-web', fetchImpl: fakeFetch(), thePin }), /not a release of/);
});

test('a pinned entry is used as it is, with no release list', async () => {
  const seen = [];
  const entry = { release: TAG, url: URL_, commit: 'c'.repeat(40), tarball: { bytes: GZ.length, sha256: sha256(GZ) }, file: { bytes: LIB.length, sha256: sha256(LIB) } };
  const choice = await nativeChoice('linux-x86_64', { fetchImpl: fakeFetch(seen), thePin: { repository: 'r/b', native: { 'linux-x86_64': entry } } });
  assert.equal(choice.pinned, true);
  assert.deepEqual(seen, []);
});

test('a corrupted or wrong download is refused', () => {
  const choice = { tarball: { bytes: GZ.length, sha256: sha256(GZ) }, file: { sha256: sha256(LIB) } };
  const flipped = Buffer.from(GZ); flipped[30] ^= 1;
  assert.throws(() => checkNativeTarball(flipped, choice), /sha256|bytes/);
  assert.throws(() => checkNativeTarball(GZ, { ...choice, file: { sha256: '0'.repeat(64) } }), /does not match/);
  assert.deepEqual(checkNativeTarball(GZ, choice).map((e) => e.name).sort(), ['foafnaut/README-linux.txt', 'foafnaut/libweb-render.so']);
});

test('install puts the library where chooseEngine finds it, and replaces current', async () => {
  const home = mkdtempSync(join(tmpdir(), 'textnaut-native-'));
  const env = { FOAFNAUT_HOME: join(home, 'fh') };
  const path = await installNative({ channel: 'latest', env, home, os: 'linux', cpu: 'x64', fetchImpl: fakeFetch(), log: () => {}, thePin: { repository: 'r/b' } });
  assert.deepEqual(readFileSync(path), LIB);
  assert.equal(readlinkSync(join(env.FOAFNAUT_HOME, 'current')), join('versions', '0123456789ab'));
  const choice = chooseEngine(['p.html'], env, home, 'linux');
  assert.equal(choice.how, 'installed foafnaut');
  assert.equal(choice.env.TEXTNAUT_NATIVE, path);
  assert.equal(chooseEngine(['--wasm', 'p.html'], env, home, 'linux').fetch, true);
  // Installing again replaces the link and the version directory.
  await installNative({ channel: 'latest', env, home, os: 'linux', cpu: 'x64', fetchImpl: fakeFetch(), log: () => {}, thePin: { repository: 'r/b' } });
  assert(existsSync(path));
});

test('install refuses to replace a current that is a real directory, and on macOS', async () => {
  const home = mkdtempSync(join(tmpdir(), 'textnaut-native-'));
  const env = { FOAFNAUT_HOME: join(home, 'fh') };
  mkdirSync(join(env.FOAFNAUT_HOME, 'current'), { recursive: true });
  writeFileSync(join(env.FOAFNAUT_HOME, 'current', 'mine'), 'x');
  await assert.rejects(installNative({ channel: 'latest', env, home, os: 'linux', cpu: 'x64', fetchImpl: fakeFetch(), log: () => {}, thePin: { repository: 'r/b' } }), /not a symbolic link/);
  assert(existsSync(join(env.FOAFNAUT_HOME, 'current', 'mine')));
  await assert.rejects(installNative({ env, home, os: 'darwin', cpu: 'arm64', fetchImpl: fakeFetch(), log: () => {} }), /foafnaut app/);
});
