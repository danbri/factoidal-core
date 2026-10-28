// Re-runs the commands that docs/web/hub/webdav.md shows, through the npm
// package's CLI, and checks what the page says they do. The page has no live
// cells (a server cannot run in a browser page), so this file keeps its
// transcripts and claims true.
//
// The login and HTTPS of the listener (https://github.com/danbri/factoidal/issues/1108)
// are checked as the page shows them. The rules of issue 1147 (read only,
// a request acts as one named user, `users:` per mount, `--guest`, local
// mounts refused, `allow-external-token`) are checked as the page states
// them. HTTP over XMPP
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

/** A free port on 127.0.0.1. */
function freePort() {
  return new Promise((resolve) => {
    const srv = http.createServer().listen(0, '127.0.0.1', () => { const p = srv.address().port; srv.close(() => resolve(p)); });
  });
}

/** The LWS server of the quick start, shared by the later tests: its URL,
 *  the owner's did:key and the key file's text. */
let lwsServer = null;

const READ_ALLOW = 'OPTIONS, GET, HEAD, PROPFIND';

test('webdav: quick start, an lws mount, read only, the guest', async () => {
  const dir = path.join(work, 'quick');
  fs.mkdirSync(path.join(dir, 'dav'), { recursive: true });
  // The mount file names the storage URL, so the port is chosen first.
  const port = await freePort();
  fs.writeFileSync(path.join(dir, 'dav', 'alice.md'),
    `# Alice on the LWS server\n- kind: lws\n- url: http://127.0.0.1:${port}/\n- auth: did-key\n- key-file: alice.jwk\n- users: guest\n`);
  const first = await start(['webdav-serve', 'dav', '--port', '0', '--guest', 'guest'], dir);
  for (let i = 0; i < 50 && !/users: guest\)/.test(first.out()); i++) await new Promise((r) => setTimeout(r, 100));
  assert.match(first.out(), /WARNING: read only \(emergency mode, issue 1147\)/);
  assert.match(first.out(), /acts as the guest user "guest" \(--guest\)/);
  assert.match(first.out(), /no --users: credentials get 401, guest guest/);
  const did = /\(lws, read-only, as (did:key:z[1-9A-HJ-NP-Za-km-z]+), users: guest\)/.exec(first.out());
  assert.ok(did, first.out());
  assert.equal(fs.statSync(path.join(dir, 'dav', 'alice.jwk')).mode & 0o777, 0o600);

  await start(['lws-serve', 'alice-storage', '--port', String(port), '--authz', 'alice-as', '--owner', did[1], '--quiet'], dir);
  const origin = `http://127.0.0.1:${port}`;
  assert.equal((await req(origin, 'GET', '/')).status, 401);
  // The page: files are written with an LWS client that holds the key.
  const jwkText = fs.readFileSync(path.join(dir, 'dav', 'alice.jwk'), 'utf8');
  const { createLwsClient } = await import('../../npm/factoidal/lws/client.mjs');
  const owner = await createLwsClient({ selfIssued: { subject: did[1], keyId: `${did[1]}#${did[1].slice(8)}`, jwk: JSON.parse(jwkText) } });
  const w = await owner.update(`${origin}/note.txt`, { body: 'from an LWS client', mediaType: 'text/plain', precondition: 'none' });
  assert.ok(w.status === 201 || w.status === 204, `seed ${w.status}`);
  lwsServer = { origin, did: did[1], jwkText, owner };

  const o = await req(first.origin, 'OPTIONS', '/');
  assert.equal(o.status, 200);
  assert.equal(o.headers.dav, '1');
  assert.equal(o.headers['ms-author-via'], 'DAV');
  assert.equal(o.headers.allow, READ_ALLOW);
  assert.equal((await req(first.origin, 'GET', '/alice/note.txt')).text, 'from an LWS client');
  const pf = await req(first.origin, 'PROPFIND', '/alice/', { depth: '1' });
  assert.equal(pf.status, 207);
  const hrefs = [...pf.text.matchAll(/<D:href>([^<]*)<\/D:href>/g)].map((m) => m[1]).sort();
  assert.deepEqual(hrefs, ['/alice/', '/alice/note.txt']);
  const put = await req(first.origin, 'PUT', '/alice/note.txt', {}, 'x');
  assert.equal(put.status, 403);
  assert.equal(put.text, 'this server is read only (emergency mode, https://github.com/danbri/factoidal/issues/1147)\n');
  // The page: every write method is 403 on every mount.
  for (const m of ['DELETE', 'MKCOL', 'COPY', 'MOVE', 'PROPPATCH', 'LOCK', 'UNLOCK']) {
    const r = await req(first.origin, m, '/alice/note.txt', { destination: `${first.origin}/alice/other.txt` });
    assert.equal(r.status, 403, m);
    assert.equal(r.headers.allow, READ_ALLOW, m);
  }
  const still = await owner.read(`${origin}/note.txt`);
  assert.equal(still.body, 'from an LWS client');
});

/** A configuration directory with one lws mount of the quick start's storage. */
function lwsConfig(name, users) {
  const dir = path.join(work, name);
  fs.mkdirSync(path.join(dir, 'dav'), { recursive: true });
  fs.writeFileSync(path.join(dir, 'dav', 'alice.jwk'), lwsServer.jwkText, { mode: 0o600 });
  fs.writeFileSync(path.join(dir, 'dav', 'notes.md'),
    `# Notes\n- kind: lws\n- url: ${lwsServer.origin}/\n- auth: did-key\n- key-file: alice.jwk\n- users: ${users}\n`);
  return dir;
}

/** `factoidal webdav-user FILE NAME` with the password on standard input. */
function addUser(cwd, file, name, password) {
  const r = spawnSync(process.execPath, [CLI, 'webdav-user', file, name, '--iterations', '100000'], { cwd, input: password + '\n', encoding: 'utf8' });
  assert.equal(r.status, 0, r.stderr);
  return r.stderr;
}

const basic = (user, password) => 'Basic ' + Buffer.from(`${user}:${password}`).toString('base64');

test('webdav: mount files: users: is required, local mounts are refused, bearer needs allow-external-token', () => {
  assert.ok(lwsServer, 'the quick start ran');
  const dir = path.join(work, 'refused');
  fs.mkdirSync(path.join(dir, 'dav', 'store'), { recursive: true });
  fs.writeFileSync(path.join(dir, 'dav', 'l.md'), '# L\n- kind: local\n- path: ./store\n- users: guest\n');
  let r = spawnSync(process.execPath, [CLI, 'webdav-serve', 'dav', '--port', '0', '--guest', 'guest'], { cwd: dir, encoding: 'utf8' });
  assert.equal(r.status, 1);
  assert.match(r.stderr, /l\.md:2: a `kind: local` mount opens its storage with no authorization and is refused \(emergency mode, https:\/\/github\.com\/danbri\/factoidal\/issues\/1147\); use kind: lws with an agent key/);
  fs.writeFileSync(path.join(dir, 'dav', 'l.md'), `# L\n- kind: lws\n- url: ${lwsServer.origin}/\n`);
  r = spawnSync(process.execPath, [CLI, 'webdav-serve', 'dav', '--port', '0', '--guest', 'guest'], { cwd: dir, encoding: 'utf8' });
  assert.equal(r.status, 1);
  assert.match(r.stderr, /l\.md:2: the settings list has no `users`/);
  fs.writeFileSync(path.join(dir, 'dav', 't.token'), 'abc\n');
  fs.writeFileSync(path.join(dir, 'dav', 'l.md'), `- kind: lws\n- url: ${lwsServer.origin}/\n- auth: bearer\n- token-file: t.token\n- users: guest\n`);
  r = spawnSync(process.execPath, [CLI, 'webdav-serve', 'dav', '--port', '0', '--guest', 'guest'], { cwd: dir, encoding: 'utf8' });
  assert.equal(r.status, 1);
  assert.match(r.stderr, /l\.md:3: auth `bearer` uses the token file, a credential from outside this installation; refused unless the mount file says `allow-external-token: true`/);
});

test('webdav: each mount names its users; another user gets 404 and does not see it', async () => {
  const dir = lwsConfig('users-per-mount', 'alice, guest');
  fs.writeFileSync(path.join(dir, 'dav', 'bob.md'),
    `# Bob only\n- kind: lws\n- url: ${lwsServer.origin}/\n- auth: did-key\n- key-file: alice.jwk\n- users: bob\n`);
  addUser(dir, 'users.txt', 'alice', 'correct horse');
  addUser(dir, 'users.txt', 'bob', 'battery staple');
  const s = await start(['webdav-serve', 'dav', '--port', '0', '--users', 'users.txt', '--guest', 'guest'], dir);
  const alice = { authorization: basic('alice', 'correct horse') };
  const bob = { authorization: basic('bob', 'battery staple') };
  let pf = await req(s.origin, 'PROPFIND', '/', { depth: '1', ...alice });
  assert.match(pf.text, /\/notes\//);
  assert.doesNotMatch(pf.text, /\/bob\//);
  pf = await req(s.origin, 'PROPFIND', '/', { depth: '1', ...bob });
  assert.match(pf.text, /\/bob\//);
  assert.doesNotMatch(pf.text, /\/notes\//);
  const absent = await req(s.origin, 'GET', '/nothing/note.txt', alice);
  const hidden = await req(s.origin, 'GET', '/bob/note.txt', alice);
  assert.equal(hidden.status, 404);
  assert.equal(hidden.text, absent.text);
  assert.equal((await req(s.origin, 'GET', '/bob/note.txt')).status, 404);
  assert.equal((await req(s.origin, 'GET', '/bob/note.txt', bob)).text, 'from an LWS client');
  assert.equal((await req(s.origin, 'GET', '/notes/note.txt')).text, 'from an LWS client');
  // A request with credentials never falls back to the guest.
  for (const a of [basic('alice', 'wrong'), 'Bearer x', 'garbage']) {
    assert.equal((await req(s.origin, 'GET', '/notes/note.txt', { authorization: a })).status, 401, a);
  }
  // The guest may not be a user of the users file.
  const r = spawnSync(process.execPath, [CLI, 'webdav-serve', 'dav', '--port', '0', '--users', 'users.txt', '--guest', 'alice'], { cwd: dir, encoding: 'utf8' });
  assert.equal(r.status, 1);
  assert.match(r.stderr, /"alice" is a user of the users file/);
});

test('webdav: --users gives HTTP Basic login on the listener', async () => {
  const dir = lwsConfig('users', 'alice');
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
  const dir = lwsConfig('limit', 'alice');
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
  s.child.kill('SIGTERM');
  await new Promise((r) => (s.child.exitCode !== null ? r() : s.child.on('close', r)));
  const off = await start(['webdav-serve', 'dav', '--port', '0', '--users', 'users.txt', '--dangerously-disable-ratelimits'], dir);
  // Standard error and standard output are two pipes: wait for the warning.
  for (let i = 0; i < 50 && !off.out().includes('WARNING: --dangerously'); i++) await new Promise((r) => setTimeout(r, 100));
  assert.match(off.out(), /WARNING: --dangerously-disable-ratelimits: failed logins are NOT limited/);
});

const OPENSSL = spawnSync('openssl', ['version'], { encoding: 'utf8' }).status === 0;

test('webdav: --cert and --key serve HTTPS', { skip: OPENSSL ? false : 'openssl is not installed: no certificate can be made for the test' }, async () => {
  const dir = lwsConfig('tls', 'alice');
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
  assert.equal(o.headers.dav, '1');
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
  const dir = lwsConfig('xmpp', 'guest');
  fs.mkdirSync(path.join(dir, 'xmpp-state'));
  fs.writeFileSync(path.join(dir, 'accounts'), 'alice:alice-password\nbob:bob-password\ncarol:carol-password\n');
  fs.writeFileSync(path.join(dir, 'bob.password'), 'bob-password\n');
  const xs = await startUntil(['xmpp-serve', 'xmpp-state', '--port', '0', '--domain', 'example.org', '--accounts', 'accounts'],
    dir, /^xmpp:\/\/127\.0\.0\.1:(\d+)$/m);
  const port = xs[1];
  const bound = await startUntil(['webdav-serve', 'dav', '--xmpp', 'bob@example.org', '--xmpp-password-file', 'bob.password',
    '--xmpp-allow', 'alice@example.org', '--xmpp-host', '127.0.0.1', '--xmpp-port', port,
    '--guest', 'guest'], dir, /^xmpp:(\S+)$/m);
  assert.equal(bound[1], 'bob@example.org/dav');

  const alice = new TestClient(Number(port), 'example.org');
  try {
    await alice.login('alice', 'alice-password');
    const pf = await xreq(alice, bound[1], 'PROPFIND', '/', { headers: [['Depth', '1']] });
    assert.equal(pf.status, 207);
    assert.match(pf.iq, /\/notes\//);
    assert.equal((await xreq(alice, bound[1], 'PUT', '/notes/a.txt', { headers: [['Content-Type', 'text/plain']], data: '<data><text>hi</text></data>' })).status, 403);
    assert.match((await xreq(alice, bound[1], 'GET', '/notes/note.txt')).iq, /from an LWS client/);
  } finally {
    alice.close();
  }
  const carol = new TestClient(Number(port), 'example.org');
  try {
    await carol.login('carol', 'carol-password');
    assert.match((await xreq(carol, bound[1], 'GET', '/notes/note.txt')).iq, /forbidden/);
  } finally {
    carol.close();
  }
});

// The page: a file browser reaches the server through the local proxy of
// step 2 (`xmpp-http-proxy`, https://github.com/danbri/factoidal/issues/1107).
// The full test, with litmus, rclone and cadaver, is tests/webdav/xmpp-proxy.mjs.
test('webdav: a file browser reaches the server through XMPP (local proxy)', async () => {
  const dir = lwsConfig('xmpp-proxy', 'guest');
  fs.mkdirSync(path.join(dir, 'xmpp-state'));
  fs.writeFileSync(path.join(dir, 'accounts'), 'alice:alice-password\nbob:bob-password\ncarol:carol-password\n');
  fs.writeFileSync(path.join(dir, 'bob.password'), 'bob-password\n');
  fs.writeFileSync(path.join(dir, 'alice.password'), 'alice-password\n');
  const xs = await startUntil(['xmpp-serve', 'xmpp-state', '--port', '0', '--domain', 'example.org', '--accounts', 'accounts'],
    dir, /^xmpp:\/\/127\.0\.0\.1:(\d+)$/m);
  const port = xs[1];
  await startUntil(['webdav-serve', 'dav', '--xmpp', 'bob@example.org', '--xmpp-password-file', 'bob.password',
    '--xmpp-allow', 'alice@example.org', '--xmpp-host', '127.0.0.1', '--xmpp-port', port,
    '--guest', 'guest'], dir, /^xmpp:(\S+)$/m);
  const proxy = await startUntil(['xmpp-http-proxy', '--xmpp', 'alice@example.org', '--xmpp-password-file', 'alice.password',
    '--target', 'bob@example.org/dav', '--xmpp-host', '127.0.0.1', '--xmpp-port', port, '--port', '0'],
  dir, /^(http:\/\/127\.0\.0\.1:\d+)\/$/m);
  const origin = proxy[1];
  const pf = await req(origin, 'PROPFIND', '/', { depth: '1' });
  assert.equal(pf.status, 207);
  assert.match(pf.text, /\/notes\//);
  assert.equal((await req(origin, 'PUT', '/notes/b.txt', { 'content-type': 'text/plain' }, 'via the proxy')).status, 403);
  assert.equal((await req(origin, 'GET', '/notes/note.txt')).text, 'from an LWS client');
  // The page: --host other than 127.0.0.1 is refused.
  const refused = spawnSync(process.execPath, [CLI, 'xmpp-http-proxy', '--xmpp', 'alice@example.org',
    '--xmpp-password-file', 'alice.password', '--target', 'bob@example.org/dav', '--xmpp-host', '127.0.0.1',
    '--xmpp-port', port, '--host', '0.0.0.0'], { cwd: dir, encoding: 'utf8' });
  assert.equal(refused.status, 1);
  assert.match(refused.stderr, /127\.0\.0\.1 only/);
});
