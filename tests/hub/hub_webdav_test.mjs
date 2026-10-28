// Re-runs the commands that docs/web/hub/webdav.md shows, through the npm
// package's CLI, and checks what the page says they do. The page has no live
// cells (a server cannot run in a browser page), so this file keeps its
// transcripts and claims true.
//
// The login and HTTPS of the listener (https://github.com/danbri/factoidal/issues/1108)
// are checked as the page shows them. HTTP over XMPP
// (https://github.com/danbri/factoidal/issues/1107) is checked through the
// local proxy `xmpp-http-proxy`, as the page shows it.

import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import http from 'node:http';
import https from 'node:https';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { TestClient, request as xreq } from '../webdav/xmpp-client.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const CLI = path.join(ROOT, 'npm', 'factoidal', 'bin', 'factoidal.mjs');

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

/** One request with full control of the headers (fetch cannot set Host).
 *  `ca`: the certificate an https origin is checked against. */
function req(origin, method, p, headers = {}, body = undefined, ca = undefined) {
  const u = new URL(p, origin);
  return new Promise((resolve, reject) => {
    const lib = u.protocol === 'https:' ? https : http;
    const r = lib.request({ host: u.hostname, port: u.port, method, path: u.pathname, headers, ca }, (res) => {
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

/** `factoidal webdav-user FILE NAME` with the password on standard input. */
function addUser(cwd, file, name, password) {
  const r = spawnSync(process.execPath, [CLI, 'webdav-user', file, name, '--iterations', '100000'], { cwd, input: password + '\n', encoding: 'utf8' });
  assert.equal(r.status, 0, r.stderr);
  return r.stderr;
}

const basic = (user, password) => 'Basic ' + Buffer.from(`${user}:${password}`).toString('base64');

test('webdav: --users gives HTTP Basic login on the listener', async () => {
  const dir = emptyConfig('users');
  assert.match(addUser(dir, 'users.txt', 'alice', 'correct horse'), /added alice in users\.txt/);
  assert.match(fs.readFileSync(path.join(dir, 'users.txt'), 'utf8'), /^alice:pbkdf2-sha256:100000:[^:]+:[^:]+\n$/);
  assert.equal(fs.statSync(path.join(dir, 'users.txt')).mode & 0o777, 0o600);
  const s = await start(['webdav-serve', 'dav', '--port', '0', '--users', 'users.txt'], dir);
  const no = await req(s.origin, 'PROPFIND', '/', { depth: '1' });
  assert.equal(no.status, 401);
  assert.equal(no.headers['www-authenticate'], 'Basic realm="factoidal webdav", charset="UTF-8"');
  assert.equal((await req(s.origin, 'PROPFIND', '/', { depth: '1', authorization: basic('alice', 'wrong') })).status, 401);
  assert.equal((await req(s.origin, 'PROPFIND', '/', { depth: '1', authorization: basic('alice', 'correct horse') })).status, 207);
  // The page: without TLS, --users is refused on an address that is not loopback.
  const r = spawnSync(process.execPath, [CLI, 'webdav-serve', 'dav', '--port', '0', '--host', '0.0.0.0', '--users', 'users.txt'], { cwd: dir, encoding: 'utf8' });
  assert.equal(r.status, 1);
  assert.match(r.stderr, /0\.0\.0\.0 is not a loopback address/);
});

test('webdav: failed logins are limited (--login-limit, --login-window); --dangerously-disable-ratelimits warns', async () => {
  // https://github.com/danbri/factoidal/issues/1119; the page's command.
  const dir = emptyConfig('limit');
  addUser(dir, 'users.txt', 'alice', 'correct horse');
  const s = await start(['webdav-serve', 'dav', '--port', '0', '--users', 'users.txt', '--login-limit', '10', '--login-window', '300'], dir);
  const statuses = [];
  for (let i = 0; i < 11; i++) {
    statuses.push((await req(s.origin, 'PROPFIND', '/', { depth: '0', authorization: basic('alice', `wrong-${i}`) })).status);
  }
  assert.deepEqual(statuses, [...Array(10).fill(401), 429]);
  const right = await req(s.origin, 'PROPFIND', '/', { depth: '0', authorization: basic('alice', 'correct horse') });
  assert.equal(right.status, 429);
  assert.match(right.headers['retry-after'], /^[0-9]+$/);
  assert.ok(Number(right.headers['retry-after']) <= 300);
  assert.equal((await req(s.origin, 'PROPFIND', '/', { depth: '0' })).status, 401);
  const off = await start(['webdav-serve', 'dav', '--port', '0', '--users', 'users.txt', '--dangerously-disable-ratelimits'], dir);
  // Standard error and standard output are two pipes: wait for the warning.
  for (let i = 0; i < 50 && !off.out().includes('WARNING: --dangerously'); i++) await new Promise((r) => setTimeout(r, 100));
  assert.match(off.out(), /WARNING: --dangerously-disable-ratelimits: failed logins are NOT limited/);
});

const OPENSSL = spawnSync('openssl', ['version'], { encoding: 'utf8' }).status === 0;

test('webdav: --cert and --key serve HTTPS', { skip: OPENSSL ? false : 'openssl is not installed: no certificate can be made for the test' }, async () => {
  const dir = emptyConfig('tls');
  const made = spawnSync('openssl', ['req', '-x509', '-newkey', 'ec', '-pkeyopt', 'ec_paramgen_curve:P-256', '-nodes',
    '-keyout', 'key.pem', '-out', 'cert.pem', '-days', '1', '-subj', '/CN=localhost', '-addext', 'subjectAltName=IP:127.0.0.1'],
  { cwd: dir, encoding: 'utf8' });
  assert.equal(made.status, 0, made.stderr);
  addUser(dir, 'users.txt', 'alice', 'correct horse');
  const s = await start(['webdav-serve', 'dav', '--port', '0', '--cert', 'cert.pem', '--key', 'key.pem', '--users', 'users.txt'], dir);
  assert.match(s.origin, /^https:/);
  const ca = fs.readFileSync(path.join(dir, 'cert.pem'));
  assert.equal((await req(s.origin, 'OPTIONS', '/', {}, undefined, ca)).status, 401);
  const o = await req(s.origin, 'OPTIONS', '/', { authorization: basic('alice', 'correct horse') }, undefined, ca);
  assert.equal(o.status, 200);
  assert.equal(o.headers.dav, '1, 2');
});

/** Start a CLI command; resolve once a stdout line matches `pattern`. */
function startUntil(args, cwd, pattern) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [CLI, ...args], { cwd, stdio: ['ignore', 'pipe', 'pipe'] });
    children.push(child);
    let out = '';
    let err = '';
    const timer = setTimeout(() => { child.kill(); reject(new Error(`no start: ${out} ${err}`)); }, 120000);
    child.stdout.on('data', (b) => {
      out += b;
      const m = pattern.exec(out);
      if (m) { clearTimeout(timer); resolve(m); }
    });
    child.stderr.on('data', (b) => { err += b; });
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`exited ${code}: ${err.trim()}`)); });
  });
}

// The page's XMPP commands: xmpp-serve with three accounts, then
// webdav-serve --xmpp as bob with alice allowed. The reader is a minimal
// XEP-0332 test client (tests/webdav/xmpp-client.mjs); the full test is
// tests/webdav/xmpp.mjs.
test('webdav: reach the server through XMPP (XEP-0332)', async () => {
  const dir = emptyConfig('xmpp');
  fs.mkdirSync(path.join(dir, 'xmpp-state'));
  fs.writeFileSync(path.join(dir, 'accounts'), 'alice:alice-password\nbob:bob-password\ncarol:carol-password\n');
  fs.writeFileSync(path.join(dir, 'bob.password'), 'bob-password\n');
  const xs = await startUntil(['xmpp-serve', 'xmpp-state', '--port', '0', '--domain', 'example.org', '--accounts', 'accounts'],
    dir, /^xmpp:\/\/127\.0\.0\.1:(\d+)$/m);
  const port = xs[1];
  const bound = await startUntil(['webdav-serve', 'dav', '--xmpp', 'bob@example.org', '--xmpp-password-file', 'bob.password',
    '--xmpp-allow', 'alice@example.org', '--xmpp-host', '127.0.0.1', '--xmpp-port', port,
    '--dangerously-allow-writable-without-login'], dir, /^xmpp:(\S+)$/m);
  assert.equal(bound[1], 'bob@example.org/dav');

  const alice = new TestClient(Number(port), 'example.org');
  try {
    await alice.login('alice', 'alice-password');
    const pf = await xreq(alice, bound[1], 'PROPFIND', '/', { headers: [['Depth', '1']] });
    assert.equal(pf.status, 207);
    assert.match(pf.iq, /\/notes\//);
    assert.equal((await xreq(alice, bound[1], 'PUT', '/notes/a.txt', { headers: [['Content-Type', 'text/plain']], data: '<data><text>hi</text></data>' })).status, 201);
    assert.match((await xreq(alice, bound[1], 'GET', '/notes/a.txt')).iq, /<text>hi<\/text>/);
  } finally {
    alice.close();
  }
  const carol = new TestClient(Number(port), 'example.org');
  try {
    await carol.login('carol', 'carol-password');
    assert.match((await xreq(carol, bound[1], 'GET', '/notes/a.txt')).iq, /forbidden/);
  } finally {
    carol.close();
  }
});

// The page: a file browser reaches the server through the local proxy of
// step 2 (`xmpp-http-proxy`, https://github.com/danbri/factoidal/issues/1107).
// The full test, with litmus, rclone and cadaver, is tests/webdav/xmpp-proxy.mjs.
test('webdav: a file browser reaches the server through XMPP (local proxy)', async () => {
  const dir = emptyConfig('xmpp-proxy');
  fs.mkdirSync(path.join(dir, 'xmpp-state'));
  fs.writeFileSync(path.join(dir, 'accounts'), 'alice:alice-password\nbob:bob-password\ncarol:carol-password\n');
  fs.writeFileSync(path.join(dir, 'bob.password'), 'bob-password\n');
  fs.writeFileSync(path.join(dir, 'alice.password'), 'alice-password\n');
  const xs = await startUntil(['xmpp-serve', 'xmpp-state', '--port', '0', '--domain', 'example.org', '--accounts', 'accounts'],
    dir, /^xmpp:\/\/127\.0\.0\.1:(\d+)$/m);
  const port = xs[1];
  await startUntil(['webdav-serve', 'dav', '--xmpp', 'bob@example.org', '--xmpp-password-file', 'bob.password',
    '--xmpp-allow', 'alice@example.org', '--xmpp-host', '127.0.0.1', '--xmpp-port', port,
    '--dangerously-allow-writable-without-login'], dir, /^xmpp:(\S+)$/m);
  const proxy = await startUntil(['xmpp-http-proxy', '--xmpp', 'alice@example.org', '--xmpp-password-file', 'alice.password',
    '--target', 'bob@example.org/dav', '--xmpp-host', '127.0.0.1', '--xmpp-port', port, '--port', '0'],
  dir, /^(http:\/\/127\.0\.0\.1:\d+)\/$/m);
  const origin = proxy[1];
  const pf = await req(origin, 'PROPFIND', '/', { depth: '1' });
  assert.equal(pf.status, 207);
  assert.match(pf.text, /\/notes\//);
  assert.equal((await req(origin, 'PUT', '/notes/b.txt', { 'content-type': 'text/plain' }, 'via the proxy')).status, 201);
  assert.equal((await req(origin, 'GET', '/notes/b.txt')).text, 'via the proxy');
  // The page: --host other than 127.0.0.1 is refused.
  const refused = spawnSync(process.execPath, [CLI, 'xmpp-http-proxy', '--xmpp', 'alice@example.org',
    '--xmpp-password-file', 'alice.password', '--target', 'bob@example.org/dav', '--xmpp-host', '127.0.0.1',
    '--xmpp-port', port, '--host', '0.0.0.0'], { cwd: dir, encoding: 'utf8' });
  assert.equal(refused.status, 1);
  assert.match(refused.stderr, /127\.0\.0\.1 only/);
});
