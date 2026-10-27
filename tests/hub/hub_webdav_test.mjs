// Re-runs the commands that docs/web/hub/webdav.md shows, through the npm
// package's CLI, and checks what the page says they do. The page has no live
// cells (a server cannot run in a browser page), so this file keeps its
// transcripts and claims true.
//
// The expected failures name the gaps the page states:
// https://github.com/danbri/factoidal/issues/1108 (no login, no TLS on the
// WebDAV listener) and https://github.com/danbri/factoidal/issues/1107 (no
// HTTP over XMPP).

import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import fs from 'node:fs';
import http from 'node:http';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { xfail } from './_helpers.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const CLI = path.join(ROOT, 'npm', 'factoidal', 'bin', 'factoidal.mjs');
const LOGIN_ISSUE = 'https://github.com/danbri/factoidal/issues/1108';
const XMPP_ISSUE = 'https://github.com/danbri/factoidal/issues/1107';

const work = fs.mkdtempSync(path.join(os.tmpdir(), 'hub-webdav-'));
const children = [];
test.after(async () => {
  for (const c of children) {
    if (c.exitCode === null) { c.kill('SIGTERM'); await new Promise((r) => c.on('close', r)); }
  }
  fs.rmSync(work, { recursive: true, force: true });
});

/** Start a CLI command; resolve with its full stdout once the origin line is printed. */
function start(args, cwd) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [CLI, ...args], { cwd, stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, FACTOIDAL_LWS_KEY: '' } });
    children.push(child);
    let out = '';
    let err = '';
    const timer = setTimeout(() => { child.kill(); reject(new Error(`no start: ${out} ${err}`)); }, 120000);
    const look = () => {
      const m = /^(https?:\/\/127\.0\.0\.1:\d+)$/m.exec(out);
      if (m) { clearTimeout(timer); resolve({ child, origin: m[1], out: () => out + err }); }
    };
    child.stdout.on('data', (b) => { out += b; look(); });
    child.stderr.on('data', (b) => { err += b; });
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`exited ${code}: ${err.trim().split('\n').slice(1, 8).join(' / ')}`)); });
  });
}

/** One request with full control of the headers (fetch cannot set Host). */
function req(origin, method, p, headers = {}, body = undefined) {
  const u = new URL(p, origin);
  return new Promise((resolve, reject) => {
    const r = http.request({ host: u.hostname, port: u.port, method, path: u.pathname, headers }, (res) => {
      let text = '';
      res.setEncoding('utf8');
      res.on('data', (c) => { text += c; });
      res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, text }));
    });
    r.on('error', reject);
    if (body !== undefined) r.write(body);
    r.end();
  });
}

test('webdav: quick start, one local mount', async () => {
  const dir = path.join(work, 'quick');
  fs.mkdirSync(path.join(dir, 'dav', 'notes'), { recursive: true });
  fs.writeFileSync(path.join(dir, 'dav', 'notes.md'), '# My notes\n- kind: local\n- path: ./notes\n');
  const s = await start(['webdav-serve', 'dav', '--port', '0'], dir);
  assert.match(s.out(), /\/notes\/ - My notes \(local\)/);

  const o = await req(s.origin, 'OPTIONS', '/');
  assert.equal(o.status, 200);
  assert.equal(o.headers.dav, '1, 2');
  assert.equal(o.headers['ms-author-via'], 'DAV');

  assert.equal((await req(s.origin, 'PUT', '/notes/hello.txt', { 'content-type': 'text/plain' }, 'hello')).status, 201);
  assert.equal((await req(s.origin, 'MKCOL', '/notes/docs/')).status, 201);
  assert.equal((await req(s.origin, 'GET', '/notes/hello.txt')).text, 'hello');
  const pf = await req(s.origin, 'PROPFIND', '/notes/', { depth: '1' });
  assert.equal(pf.status, 207);
  const hrefs = [...pf.text.matchAll(/<D:href>([^<]*)<\/D:href>/g)].map((m) => m[1]).sort();
  assert.deepEqual(hrefs, ['/notes/', '/notes/docs/', '/notes/hello.txt']);

  // The page: a proxy must pass the Host header unchanged, or MOVE and COPY
  // read the Destination as another server (RFC 4918 §9.9.4).
  const host = new URL(s.origin).host;
  const ok = await req(s.origin, 'MOVE', '/notes/hello.txt', { host, destination: `https://${host}/notes/docs/hello.txt` });
  assert.equal(ok.status, 201);
  const bad = await req(s.origin, 'MOVE', '/notes/docs/hello.txt', { host: '127.0.0.1:1', destination: `https://${host}/notes/hello.txt` });
  assert.equal(bad.status, 502);

  // The directory is the storage's own layout, not a copy of the folder tree.
  assert.ok(!fs.existsSync(path.join(dir, 'dav', 'notes', 'hello.txt')));
  assert.ok(!fs.existsSync(path.join(dir, 'dav', 'notes', 'docs', 'hello.txt')));
});

test('webdav: an lws mount signs in to lws-serve --authz with did:key', async () => {
  const dir = path.join(work, 'remote');
  fs.mkdirSync(path.join(dir, 'dav'), { recursive: true });
  // The mount file names the storage URL, so the port is chosen first.
  const port = await new Promise((resolve) => {
    const srv = http.createServer().listen(0, '127.0.0.1', () => { const p = srv.address().port; srv.close(() => resolve(p)); });
  });
  fs.writeFileSync(path.join(dir, 'dav', 'alice.md'),
    `# Alice on the LWS server\n- kind: lws\n- url: http://127.0.0.1:${port}/\n- auth: did-key\n- key-file: alice.jwk\n- writable: true\n`);
  fs.writeFileSync(path.join(dir, 'dav', 'alice-ro.md'),
    `# Alice, read only\n- kind: lws\n- url: http://127.0.0.1:${port}/\n- auth: did-key\n- key-file: alice.jwk\n`);
  const first = await start(['webdav-serve', 'dav', '--port', '0'], dir);
  const did = /\(lws, as (did:key:z[1-9A-HJ-NP-Za-km-z]+)\)/.exec(first.out());
  assert.ok(did, first.out());
  assert.equal(fs.statSync(path.join(dir, 'dav', 'alice.jwk')).mode & 0o777, 0o600);

  await start(['lws-serve', 'alice-storage', '--port', String(port), '--authz', 'alice-as', '--owner', did[1], '--quiet'], dir);
  const origin = `http://127.0.0.1:${port}`;
  assert.equal((await req(origin, 'GET', '/')).status, 401);

  assert.equal((await req(first.origin, 'PUT', '/alice/note.txt', { 'content-type': 'text/plain' }, 'from Finder')).status, 201);
  assert.equal((await req(first.origin, 'GET', '/alice/note.txt')).text, 'from Finder');
  assert.equal((await req(first.origin, 'GET', '/alice-ro/note.txt')).text, 'from Finder');
  assert.equal((await req(first.origin, 'PUT', '/alice-ro/other.txt', { 'content-type': 'text/plain' }, 'x')).status, 403);
});

function emptyConfig(name) {
  const dir = path.join(work, name);
  fs.mkdirSync(path.join(dir, 'dav', 'notes'), { recursive: true });
  fs.writeFileSync(path.join(dir, 'dav', 'notes.md'), '# Notes\n- kind: local\n- path: ./notes\n');
  return dir;
}

xfail('webdav: --users gives HTTP Basic login on the listener', LOGIN_ISSUE, async () => {
  const dir = emptyConfig('users');
  fs.writeFileSync(path.join(dir, 'users.txt'), 'alice:placeholder\n');
  const s = await start(['webdav-serve', 'dav', '--port', '0', '--users', 'users.txt'], dir);
  assert.equal((await req(s.origin, 'PROPFIND', '/', { depth: '1' })).status, 401);
});

xfail('webdav: --cert and --key serve HTTPS', LOGIN_ISSUE, async () => {
  const dir = emptyConfig('tls');
  await start(['webdav-serve', 'dav', '--port', '0', '--cert', 'cert.pem', '--key', 'key.pem'], dir);
});

xfail('webdav: reach the server through XMPP', XMPP_ISSUE, async () => {
  const dir = emptyConfig('xmpp');
  await start(['webdav-serve', 'dav', '--port', '0', '--xmpp', 'alice@example.org'], dir);
});
