// The foafnaut launcher's choice of release (bin/foafnaut-releases.mjs) and its --update, --which and
// --list, against mocked GitHub replies: many pages of releases in no order, a branch build published
// last, the macOS lane's pointer present, stale or absent, the API limit, no network, a bad digest.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readlinkSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';
import { linkPages, mainReleases } from '../bin/foafnaut-releases.mjs';
import { list, parseArgs, update, which } from '../bin/foafnaut.mjs';

const here = fileURLToPath(new URL('.', import.meta.url));
const API = 'https://api.github.com/repos/danbri/factoidal-builds/releases?per_page=100&page=';
const POINTER = 'https://raw.githubusercontent.com/danbri/factoidal-builds/HEAD/latest/darwin-status.json';
const mac = (sha) => `build-${sha}-foafnaut-darwin-arm64`;
const dl = (tag, name) => `https://github.com/danbri/factoidal-builds/releases/download/${tag}/${name}`;
const sha = (c) => c.repeat(12);

// Main's history, newest first: commits 'e' (no macOS build), 'd', 'c', 'b', 'a'. 'f' is a branch build.
const AHEAD = { e: 0, d: 1, c: 2, b: 3, a: 4 };

/** A tarball holding foafnaut/foafnaut.app, as the release archive does. */
function archive() {
  const dir = mkdtempSync(join(tmpdir(), 'foafnaut-archive-'));
  mkdirSync(join(dir, 'foafnaut', 'foafnaut.app', 'Contents'), { recursive: true });
  writeFileSync(join(dir, 'foafnaut', 'foafnaut.app', 'Contents', 'Info.plist'), 'plist');
  spawnSync('tar', ['-czf', 'a.tar.gz', 'foafnaut'], { cwd: dir });
  const bytes = readFileSync(join(dir, 'a.tar.gz'));
  rmSync(dir, { recursive: true, force: true });
  return bytes;
}
const ARCHIVE = archive();
const digest = (b) => createHash('sha256').update(b).digest('hex');

/**
 * A fetch over 250 releases on 3 pages. The macOS builds of 'a' to 'd' are scattered, 'd' (the newest on
 * main) on the last page; the branch build 'f' is published last. Options change one thing each.
 */
function github({ pointer = mac(sha('b')), pointerSchema = 'mac_release', limited = false, offline = false, badDigest = false, compareLimited = false, seen = [] } = {}) {
  const releases = [];
  for (let i = 0; i < 246; i++) releases.push({ tag_name: `build-${i.toString(16).padStart(12, '0')}-web`, published_at: '2026-11-16T10:00:00Z' });
  const builds = { a: '2026-11-16T09:00:00Z', b: '2026-11-16T17:11:41Z', c: '2026-11-16T15:11:35Z', d: '2026-11-16T23:19:28Z', f: '2026-11-16T23:50:00Z' };
  releases.splice(3, 0, { tag_name: mac(sha('c')), published_at: builds.c });
  releases.splice(70, 0, { tag_name: mac(sha('f')), published_at: builds.f });
  releases.splice(120, 0, { tag_name: mac(sha('b')), published_at: builds.b }, { tag_name: mac(sha('a')), published_at: builds.a });
  releases.splice(230, 0, { tag_name: mac(sha('d')), published_at: builds.d });
  releases.push({ tag_name: mac('0123456789ab'), published_at: null, draft: true });
  const headers = (h = {}) => ({ get: (k) => h[k.toLowerCase()] ?? null });
  const reply = (body, status = 200, h) => ({ ok: status < 300, status, headers: headers(h), json: async () => body,
    arrayBuffer: async () => (body instanceof ArrayBuffer ? body : new TextEncoder().encode(JSON.stringify(body)).buffer) });
  return async (url) => {
    seen.push(url);
    if (offline) throw new TypeError('fetch failed', { cause: { code: 'ENOTFOUND' } });
    if (url === POINTER) {
      if (!pointer) return reply(null, 404);
      return reply({ schema: 'darwin-status/1', [pointerSchema]: { tag: pointer, sha: pointer.slice(6, 18).padEnd(40, '0'), published_at: builds[pointer[6]] } });
    }
    if (url.startsWith(API)) {
      if (limited) return reply({ message: 'API rate limit exceeded' }, 403, { 'x-ratelimit-remaining': '0' });
      const page = Number(url.slice(API.length));
      const last = '<https://api.github.com/repositories/1/releases?per_page=100&page=3>; rel="last"';
      const next = page < 3 ? `<https://api.github.com/repositories/1/releases?per_page=100&page=${page + 1}>; rel="next", ` : '';
      return reply(releases.slice((page - 1) * 100, page * 100), 200, { link: next + last });
    }
    const compare = /\/repos\/danbri\/factoidal-core\/compare\/([0-9a-f]{12})\.\.\.main$/.exec(url);
    if (compare) {
      if (compareLimited) return reply({ message: 'API rate limit exceeded' }, 403, { 'x-ratelimit-remaining': '0' });
      const c = compare[1][0];
      if (AHEAD[c] === undefined) return reply({ status: 'diverged', ahead_by: 9, behind_by: 2, base_commit: { sha: compare[1].padEnd(40, '9') } });
      return reply({ status: AHEAD[c] ? 'ahead' : 'identical', ahead_by: AHEAD[c], behind_by: 0,
        base_commit: { sha: compare[1].padEnd(40, '9'), commit: { committer: { date: `2026-11-16T0${4 - AHEAD[c]}:00:00Z` } } } });
    }
    const asset = /releases\/download\/(build-([0-9a-f]{12})-foafnaut-darwin-arm64)\/(.*)$/.exec(url);
    if (asset && asset[3] === 'build-info.json') {
      return reply({ source_commit: asset[2].padEnd(40, '9'), built_at: builds[asset[2][0]],
        artifacts: { 'foafnaut-darwin-arm64.tar.gz': { sha256: badDigest ? '0'.repeat(64) : digest(ARCHIVE), size: ARCHIVE.length } } });
    }
    if (asset && asset[3] === 'foafnaut-darwin-arm64.tar.gz') return reply(ARCHIVE.buffer.slice(ARCHIVE.byteOffset, ARCHIVE.byteOffset + ARCHIVE.length));
    return reply(null, 404);
  };
}

/** A FOAFNAUT_HOME with the given versions installed and `current` naming the first. */
function home(names = []) {
  const dir = mkdtempSync(join(tmpdir(), 'foafnaut-home-'));
  for (const n of names) {
    mkdirSync(join(dir, 'versions', n, 'foafnaut', 'foafnaut.app'), { recursive: true });
    writeFileSync(join(dir, 'versions', n, 'build-info.json'), JSON.stringify({ source_commit: n.padEnd(40, '9'), built_at: '2026-11-16T09:00:00Z' }));
  }
  if (names.length) symlinkSync(join('versions', names[0]), join(dir, 'current'));
  writeFileSync(join(dir, 'config.json'), JSON.stringify({ bleedingEdge: join(dir, 'no-local-build', 'foafnaut.app') }));
  return { FOAFNAUT_HOME: dir };
}
const lines = () => { const out = []; return { out, log: (s) => out.push(...s.split('\n')) }; };

test('Link headers name the next and last pages', () => {
  assert.deepEqual(linkPages('<https://x/r?per_page=100&page=2>; rel="next", <https://x/r?per_page=100&page=10>; rel="last"'), { next: 2, last: 10 });
  assert.deepEqual(linkPages(null), {});
});

test('the newest build of main is found on the last of 3 pages, and the later branch build is not taken', async () => {
  const seen = [];
  const { releases, notes } = await mainReleases({ fetchImpl: github({ seen }), env: {} });
  assert.equal(releases[0].tag, mac(sha('d')));
  assert.deepEqual(releases.map((r) => r.sha12[0]), ['d', 'c', 'b', 'a']);
  assert.equal(releases[0].aheadBy, 1);
  assert.equal(releases[0].committedAt, '2026-11-16T03:00:00Z');
  assert(notes.some((n) => n.startsWith(`${mac(sha('f'))}: not on main`)));
  for (const p of [1, 2, 3]) assert(seen.includes(API + p), `page ${p} read`);
  assert(!seen.some((u) => u.includes('0123456789ab')), 'drafts are not candidates');
});

test('a page GitHub refuses (HTTP 422 past 1000 results) is left out with a note; at most 10 pages are asked for', async () => {
  const base = github();
  const seen = [];
  const fetchImpl = async (url, o) => {
    seen.push(url);
    if (url === API + 1) {
      const r = await base(url, o);
      return { ...r, headers: { get: (k) => (k.toLowerCase() === 'link' ? '<https://x/r?per_page=100&page=2>; rel="next", <https://x/r?per_page=100&page=11>; rel="last"' : null) } };
    }
    if (url === API + 11) return { ok: false, status: 422, headers: { get: () => null }, json: async () => ({}) };
    return base(url, o);
  };
  const { releases, notes } = await mainReleases({ fetchImpl, env: {} });
  assert.equal(releases[0].tag, mac(sha('d')));
  assert(!seen.includes(API + 11), 'page 11 is not asked for');
  const refused = async (url, o) => (url === API + 3 ? { ok: false, status: 422, headers: { get: () => null }, json: async () => ({}) } : base(url, o));
  const partial = await mainReleases({ fetchImpl: refused, env: {} });
  assert(partial.notes.some((n) => /release list page 3: .*HTTP 422/.test(n)), partial.notes.join('\n'));
  assert.equal(partial.releases[0].tag, mac(sha('c')), 'the newest of the pages read and the pointer');
});

test('a first page of 100 alone (the old lookup) would have missed it', async () => {
  const fetchImpl = github();
  const first = await (await fetchImpl(API + 1)).json();
  assert(!first.some((r) => r.tag_name === mac(sha('d'))));
});

test('the pointer may be stale or absent, and either schema name is read', async () => {
  for (const options of [{ pointer: mac(sha('a')) }, { pointer: null }, { pointer: mac(sha('d')), pointerSchema: 'newest_release' }]) {
    const { releases } = await mainReleases({ fetchImpl: github(options), env: {} });
    assert.equal(releases[0].tag, mac(sha('d')), JSON.stringify(options));
  }
});

test('when the release list is refused, the pointer is used; with no pointer the limit is explained', async () => {
  const { releases, notes } = await mainReleases({ fetchImpl: github({ limited: true }), env: {} });
  assert.equal(releases[0].tag, mac(sha('b')));
  assert.match(notes[0], /API limit .* using the macOS lane's pointer alone/);
  await assert.rejects(mainReleases({ fetchImpl: github({ limited: true, pointer: null }), env: {} }), /API limit for this address is used up .* GITHUB_TOKEN/);
  const unchecked = await mainReleases({ fetchImpl: github({ compareLimited: true }), env: {} });
  assert.equal(unchecked.releases[0].tag, mac(sha('b')));
  assert.match(unchecked.notes[0], /pointer unchecked/);
});

test('a token is sent to the API only, when one is set', async () => {
  const sent = [];
  const base = github();
  await mainReleases({ fetchImpl: (url, o) => { sent.push([url, o?.headers?.authorization]); return base(url, o); }, env: { GITHUB_TOKEN: 't0k' } });
  for (const [url, auth] of sent) assert.equal(auth, url.startsWith('https://api.github.com/') ? 'Bearer t0k' : undefined, url);
});

test('--update installs the newest build of main, checks its digest and says what it replaced', async () => {
  const env = home([sha('c')]);
  const { out, log } = lines();
  const app = await update({ env, fetchImpl: github(), log });
  assert.equal(readlinkSync(join(env.FOAFNAUT_HOME, 'current')), join('versions', sha('d')));
  assert(app.endsWith(join('versions', sha('d'), 'foafnaut', 'foafnaut.app')));
  assert(out.some((l) => l.startsWith(`foafnaut: was ${sha('c')} (committed 2026-11-16 02:00Z`)), out.join('\n'));
  assert(out.some((l) => l.startsWith(`foafnaut: now ${sha('d')} (committed 2026-11-16 03:00Z, built 2026-11-16 23:19Z), from ${mac(sha('d'))}; main has 1 newer commits`)), out.join('\n'));
  const installed = JSON.parse(readFileSync(join(env.FOAFNAUT_HOME, 'versions', sha('d'), 'installed.json'), 'utf8'));
  assert.equal(installed.committedAt, '2026-11-16T03:00:00Z');
  // Again: nothing to do.
  const again = lines();
  await update({ env, fetchImpl: github(), log: again.log });
  assert(again.out.some((l) => l.startsWith(`foafnaut: already up to date: ${sha('d')}`)), again.out.join('\n'));
});

test('--update keeps an installed build that is newer on main than every release', async () => {
  const env = home([sha('e')]);
  const { out, log } = lines();
  await update({ env, fetchImpl: github(), log });
  assert.equal(readlinkSync(join(env.FOAFNAUT_HOME, 'current')), join('versions', sha('e')));
  assert(out.some((l) => /as new as or newer than the newest release .*kept it/.test(l)), out.join('\n'));
});

test('a digest mismatch, no network or no build changes nothing and says why', async () => {
  const env = home([sha('c')]);
  await assert.rejects(update({ env, fetchImpl: github({ badDigest: true }), log: () => {} }), /does not match its published digest .* nothing was changed/);
  assert.equal(readlinkSync(join(env.FOAFNAUT_HOME, 'current')), join('versions', sha('c')));
  assert(!existsSync(join(env.FOAFNAUT_HOME, 'versions', sha('d'))));
  await assert.rejects(update({ env, fetchImpl: github({ offline: true }), log: () => {} }), /can not reach .*ENOTFOUND.*network connection\. Nothing was changed/);
  const empty = async (url) => ({ ok: true, status: 200, headers: { get: () => null }, json: async () => (url.startsWith(API) ? [] : null) });
  await assert.rejects(update({ env, fetchImpl: empty, log: () => {} }), /no macOS build of main has been published yet/);
});

test('--which shows what runs, how far behind it is, and the local build; --list the installed builds', async () => {
  const env = home([sha('b'), sha('a')]);
  const which_ = lines();
  await which({ env, fetchImpl: github(), out: which_.log });
  const text = which_.out.join('\n');
  assert.match(text, new RegExp(`^runs: +.*versions/${sha('b')}/foafnaut/foafnaut.app$`, 'm'));
  assert.match(text, new RegExp(`^installed: +${sha('b')} \\(committed 2026-11-16 01:00Z, built 2026-11-16 09:00Z\\)$`, 'm'));
  assert.match(text, new RegExp(`^newest on main: ${sha('d')} .*published 2026-11-16 23:19Z\\n {4}2 commits newer than the installed build; foafnaut --update installs it`, 'm'));
  assert.match(text, /^bleeding edge: +.*no-local-build\/foafnaut.app \(not found\)$/m);
  const offline = lines();
  await which({ env, fetchImpl: github({ offline: true }), out: offline.log });
  assert.match(offline.out.join('\n'), /^newest on main: could not check: can not reach/m);
  const list_ = lines();
  list({ env, out: list_.log });
  assert.deepEqual(list_.out.slice(0, 2).map((l) => l.slice(0, 14)).sort(), [`  ${sha('a')}`, `* ${sha('b')}`]);
});

test('options: --install-latest is --update with a note; picks that conflict are refused', () => {
  assert.equal(parseArgs(['--update']).action, 'update');
  const old = parseArgs(['--install-latest']);
  assert.equal(old.action, 'update');
  assert.match(old.notes[0], /now called --update/);
  assert.equal(parseArgs(['--latest', 'https://example.org/']).channel, 'latest');
  assert.equal(parseArgs(['https://example.org/']).channel, 'current');
  assert.throws(() => parseArgs(['--update', '--bleeding-edge']), /can not be used together/);
  assert.throws(() => parseArgs(['--latest', '--install-latest']), /can not be used together/);
  assert.throws(() => parseArgs(['--nope']), /unknown option --nope/);
});

test('Textnaut carries the same release lookup', () => {
  const textnaut = join(here, '..', '..', 'textnaut', 'lib', 'releases.mjs');
  if (!existsSync(textnaut)) return; // the installed package has no sibling
  assert.equal(readFileSync(textnaut, 'utf8'), readFileSync(join(here, '..', 'bin', 'foafnaut-releases.mjs'), 'utf8'));
});
