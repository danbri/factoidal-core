// Re-runs the commands that docs/web/hub/servers.md and
// docs/web/hub/shardborough.md show, through the npm package's CLI, and
// checks the outputs the pages quote. Those pages have no live cells (a
// server cannot run in a browser), so this file is what keeps their
// transcripts true.

import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { xfail } from './_helpers.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const CLI = path.join(ROOT, 'npm', 'factoidal', 'bin', 'factoidal.mjs');
const DATA = `@prefix ex: <http://example.org/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:knows ex:bob .
ex:bob a foaf:Person ; foaf:name "Bob" .
`;
const NAMES = 'SELECT ?name WHERE { ?p <http://xmlns.com/foaf/0.1/name> ?name } ORDER BY ?name';

const work = fs.mkdtempSync(path.join(os.tmpdir(), 'hub-servers-'));
fs.writeFileSync(path.join(work, 'data.ttl'), DATA);
test.after(() => fs.rmSync(work, { recursive: true, force: true }));

const cli = (...args) => spawnSync(process.execPath, [CLI, ...args], { cwd: work, encoding: 'utf8', timeout: 300000 });

/** Start `factoidal serve`, resolve with the origin it prints and the child. */
function serve(args) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [CLI, 'serve', ...args, '--port', '0', '--quiet'], { cwd: work });
    let out = '';
    let err = '';
    const timer = setTimeout(() => { child.kill(); reject(new Error(`serve did not start: ${err}`)); }, 120000);
    child.stdout.on('data', (b) => {
      out += b;
      const m = /http:\/\/127\.0\.0\.1:\d+/.exec(out);
      if (m) { clearTimeout(timer); resolve({ origin: m[0], child }); }
    });
    child.stderr.on('data', (b) => { err += b; });
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`serve exited ${code}: ${err}`)); });
  });
}
/** Start a CLI server command; resolve with the first origin it prints and the child. */
function startServer(args) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [CLI, ...args], { cwd: work });
    let out = '';
    let err = '';
    const timer = setTimeout(() => { child.kill(); reject(new Error(`${args[0]} did not start: ${err}`)); }, 120000);
    const look = () => {
      const m = /http:\/\/127\.0\.0\.1:\d+/.exec(out);
      if (m) { clearTimeout(timer); resolve({ origin: m[0], child }); }
    };
    child.stdout.on('data', (b) => { out += b; look(); });
    child.stderr.on('data', (b) => { err += b; });
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`${args[0]} exited ${code}: ${err}`)); });
  });
}
const stop = (child) => new Promise((resolve) => { child.once('exit', resolve); child.kill(); });

const lines = (text) => text.split(/\r?\n/).filter((l) => l !== '');

test('servers: serve --file, Fuseki paths, query, update, read-only /get', async () => {
  const { origin, child } = await serve(['--file', 'data.ttl', '/ds']);
  try {
    const q = await fetch(`${origin}/ds/sparql`, { method: 'POST', headers: { accept: 'text/csv', 'content-type': 'application/x-www-form-urlencoded' }, body: new URLSearchParams({ query: NAMES }) });
    assert.deepEqual(lines(await q.text()), ['name', 'Alice', 'Bob']);
    const u = await fetch(`${origin}/ds/update`, { method: 'POST', headers: { 'content-type': 'application/x-www-form-urlencoded' }, body: new URLSearchParams({ update: 'INSERT DATA { <http://example.org/carol> <http://xmlns.com/foaf/0.1/name> "Carol" }' }) });
    assert.equal(u.status, 204);
    const g = await fetch(`${origin}/ds/data?default`, { headers: { accept: 'application/n-triples' } });
    assert.equal(lines(await g.text()).length, 6);
    const put = await fetch(`${origin}/ds/get?default`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '<http://e/x> <http://e/p> 1 .' });
    assert.equal(put.status, 405);
    const sd = await fetch(`${origin}/ds/sparql`, { headers: { accept: 'text/turtle' } });
    assert.match(await sd.text(), /SPARQL11Query/);
    const ping = await fetch(`${origin}/$/ping`);
    assert.equal(ping.status, 200);
    const admin = await fetch(`${origin}/$/datasets?dbName=other`, { method: 'POST' });
    assert.equal(admin.status, 405);
  } finally {
    child.kill();
  }
});

test('shardborough: npm pack, activate, query', () => {
  let r = cli('pack', 'data.ttl', 'store/gen-1', '--layout', 'ibk5');
  assert.equal(r.status, 0, r.stderr);
  assert.match(r.stdout, /5 rows/);
  r = cli('activate', 'store', 'gen-1');
  assert.equal(r.status, 0, r.stderr);
  r = cli('query', 'store', NAMES);
  assert.equal(r.status, 0, r.stderr);
  assert.match(r.stdout + r.stderr, /"Alice"\r?\n"Bob"/);
});

test('shardborough: npm pack --layout sbm11, activate, query, inspect (0.17.0)', () => {
  let r = cli('pack', 'data.ttl', 'sbm/gen-1', '--layout', 'sbm11');
  assert.equal(r.status, 0, r.stderr);
  assert.match(r.stdout, /21 files, \d+ bytes, layout sbm11/);
  r = cli('activate', 'sbm', 'gen-1');
  assert.equal(r.status, 0, r.stderr);
  assert.match(r.stdout, /layout sbm11/);
  r = cli('query', 'sbm', NAMES);
  assert.equal(r.status, 0, r.stderr);
  assert.match(r.stdout + r.stderr, /"Alice"\r?\n"Bob"/);
  assert.match(r.stdout + r.stderr, /path=ids, \d+ reads/);
  r = cli('inspect', 'sbm');
  assert.equal(r.status, 0, r.stderr);
  assert.match(r.stdout, /manifest manifest\.sbm11/);
  assert.match(r.stdout, /8 terms/);
});

xfail('shardborough: npm update through the delta log', 'https://github.com/danbri/factoidal/issues/641', () => {
  if (!fs.existsSync(path.join(work, 'store', 'CURRENT'))) {
    cli('pack', 'data.ttl', 'store/gen-1', '--layout', 'ibk5');
    cli('activate', 'store', 'gen-1');
  }
  const r = cli('update', 'store', 'INSERT DATA { <http://example.org/carol> <http://xmlns.com/foaf/0.1/name> "Carol" }');
  assert.equal(r.status, 0, r.stderr);
});

test('servers: lws-serve --authz, 401 with resource metadata, RFC 8414 metadata (0.17.0)', async () => {
  const { origin, child } = await startServer(['lws-serve', 'lws-store', '--authz', 'lws-authz', '--port', '0']);
  try {
    const r = await fetch(`${origin}/notes/a.ttl`);
    assert.equal(r.status, 401);
    assert.equal(r.headers.get('www-authenticate'), `Bearer resource_metadata="${origin}/.well-known/oauth-protected-resource/notes/a.ttl"`);
    const meta = await (await fetch(`${origin}/.well-known/lws-configuration`)).json();
    assert.equal(meta.issuer, origin);
    assert.equal(meta.token_endpoint, `${origin}/.well-known/lws-token`);
    assert.equal(meta.jwks_uri, `${origin}/.well-known/lws-jwks`);
  } finally {
    await stop(child);
  }
});

test('servers: webdav-serve over a local LWS storage (0.18.0)', async () => {
  const lws = await startServer(['lws-serve', 'alice-storage', '--insecure-no-auth', '--port', '0']);
  try {
    const put = await fetch(`${lws.origin}/notes/a.ttl`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '<#it> <http://purl.org/dc/terms/title> "A" .' });
    assert.equal(put.status, 201);
  } finally {
    await stop(lws.child);
  }
  fs.mkdirSync(path.join(work, 'dav'), { recursive: true });
  fs.writeFileSync(path.join(work, 'dav', 'alice.md'), '# Alice\n- kind: local\n- path: ../alice-storage\n');
  const { origin, child } = await startServer(['webdav-serve', 'dav', '--port', '0']);
  try {
    const opt = await fetch(`${origin}/`, { method: 'OPTIONS' });
    assert.equal(opt.headers.get('dav'), '1, 2');
    assert.match(opt.headers.get('allow'), /PROPFIND, PROPPATCH, LOCK, UNLOCK/);
    const pf = await fetch(`${origin}/alice/notes/`, { method: 'PROPFIND', headers: { depth: '1' } });
    assert.equal(pf.status, 207);
    const xml = await pf.text();
    assert.match(xml, /<D:href>\/alice\/notes\/a\.ttl<\/D:href>/);
    assert.match(xml, /<D:getcontenttype>text\/turtle<\/D:getcontenttype><D:getcontentlength>44<\/D:getcontentlength>/);
    const w = await fetch(`${origin}/alice/notes/hello.txt`, { method: 'PUT', body: 'hello' });
    assert.equal(w.status, 201);
    assert.equal(await (await fetch(`${origin}/alice/notes/hello.txt`)).text(), 'hello');
  } finally {
    await stop(child);
  }
});
