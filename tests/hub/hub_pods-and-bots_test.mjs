// Re-runs the setup that docs/web/hub/pods-and-bots.md shows — three did:key
// agents, a pod with a Web Access Control root ACL, a read-only webdav-serve
// front end with one mount per agent, each listing one WebDAV login of the
// same name (0.21.0, issue 1147) — through the npm package's CLI, and checks
// the rights and answers the page states. The macOS mount_webdav transcript
// is not re-run.

import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import http from 'node:http';
import net from 'node:net';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const CLI = path.join(ROOT, 'npm', 'factoidal', 'bin', 'factoidal.mjs');
const AGENTS = ['danbri1', 'danbri1_bot1', 'danbri1_bot2'];
const READ_ALLOW = 'OPTIONS, GET, HEAD, PROPFIND';
const READ_ONLY = 'this server is read only (emergency mode, https://github.com/danbri/factoidal/issues/1147)\n';

const work = fs.mkdtempSync(path.join(os.tmpdir(), 'hub-pods-'));
const children = [];
test.after(async () => {
  for (const c of children) {
    if (c.exitCode === null) { c.kill('SIGTERM'); await new Promise((r) => c.on('close', r)); }
  }
  fs.rmSync(work, { recursive: true, force: true });
});

/** Start a CLI command in `cwd`; resolve once it prints its origin line. */
function start(args, cwd = work) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [CLI, ...args], { cwd, stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, FACTOIDAL_LWS_KEY: '' } });
    children.push(child);
    let out = '';
    let err = '';
    const timer = setTimeout(() => { child.kill(); reject(new Error(`no start: ${out} ${err}`)); }, 120000);
    child.stdout.on('data', (b) => {
      out += b;
      const m = /^(https?:\/\/127\.0\.0\.1:\d+)$/m.exec(out);
      // The mount lines (with each did:key) go to standard error, the origin to standard output.
      if (m) { clearTimeout(timer); setTimeout(() => resolve({ child, origin: m[1], out: () => out + err }), 200); }
    });
    child.stderr.on('data', (b) => { err += b; });
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`exited ${code}: ${err}`)); });
  });
}

async function stop(child) {
  if (child.exitCode !== null) return;
  child.kill('SIGTERM');
  await new Promise((r) => child.on('close', r));
}

function freePort() {
  return new Promise((resolve) => {
    const s = net.createServer();
    s.listen(0, '127.0.0.1', () => { const { port } = s.address(); s.close(() => resolve(port)); });
  });
}

/** One request with full control of the headers. */
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

const basic = (user, password) => ({ authorization: 'Basic ' + Buffer.from(`${user}:${password}`).toString('base64') });
const login = (a) => basic(a, `pw-${a}`);
const hrefs = (text) => [...text.matchAll(/<D:href>([^<]*)<\/D:href>/g)].map((m) => m[1]).sort();

let dav;
let pod;
const did = {};
const client = {};

/** Write the three mount files into `dir`; `extra` adds users to one agent's mount. */
function mountFiles(dir, extra = {}) {
  fs.mkdirSync(dir, { recursive: true });
  for (const a of AGENTS) {
    const users = [a, ...(extra[a] ?? [])].join(', ');
    fs.writeFileSync(path.join(dir, `${a}.md`),
      `# ${a} on the danbri1 pod\n- kind: lws\n- url: ${pod}/\n- auth: did-key\n- key-file: ../keys/${a}.jwk\n- users: ${users}\n`);
  }
}

test('setup: three did:key agents, three WebDAV logins, a pod with the root ACL, the WebDAV front end', async () => {
  const podPort = await freePort();
  pod = `http://127.0.0.1:${podPort}`;
  fs.mkdirSync(path.join(work, 'keys'));
  mountFiles(path.join(work, 'dav'));
  assert.equal(fs.readFileSync(path.join(work, 'dav', 'danbri1_bot1.md'), 'utf8'),
    `# danbri1_bot1 on the danbri1 pod\n- kind: lws\n- url: ${pod}/\n- auth: did-key\n- key-file: ../keys/danbri1_bot1.jwk\n- users: danbri1_bot1\n`);
  for (const a of AGENTS) {
    const r = spawnSync(process.execPath, [CLI, 'webdav-user', 'users.txt', a, '--iterations', '100000'], { cwd: work, input: `pw-${a}\n`, encoding: 'utf8' });
    assert.equal(r.status, 0, r.stderr);
    assert.match(r.stderr, new RegExp(`webdav-user: added ${a} in users\\.txt`));
  }
  assert.equal(fs.statSync(path.join(work, 'users.txt')).mode & 0o777, 0o600);

  // The first start makes the keys and prints each agent's did:key.
  const first = await start(['webdav-serve', 'dav', '--port', '0', '--users', 'users.txt', '--guest', 'guest']);
  for (const a of AGENTS) {
    const m = new RegExp(`/${a}/ - ${a} on the danbri1 pod \\(lws, read-only, as (did:key:z[1-9A-HJ-NP-Za-km-z]+), users: ${a}\\)`).exec(first.out());
    assert.ok(m, `no did:key for ${a} in: ${first.out()}`);
    did[a] = m[1];
    const mode = fs.statSync(path.join(work, 'keys', `${a}.jwk`)).mode & 0o777;
    assert.equal(mode, 0o600, `${a}.jwk is owner-only`);
  }
  await stop(first.child);
  assert.equal(new Set(Object.values(did)).size, 3);

  const R = `${pod}/`;
  const auth = (frag, agent, modes) => `<${R}.acl#${frag}> a acl:Authorization ;\n  acl:agent <${did[agent]}> ;\n` +
    `  acl:accessTo <${R}> ; acl:default <${R}> ;\n  acl:mode ${modes} .\n`;
  fs.writeFileSync(path.join(work, 'root.acl'), '@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n\n' +
    auth('owner', 'danbri1', 'acl:Read, acl:Write, acl:Control') +
    auth('bot1', 'danbri1_bot1', 'acl:Read, acl:Write') +
    auth('bot2', 'danbri1_bot2', 'acl:Read'));

  const p = await start(['lws-serve', 'danbri1-pod', '--port', String(podPort), '--authz', 'danbri1-as',
    '--storage', 'files', '--root-acl', 'root.acl']);
  assert.equal(p.origin, pod);
  assert.match(p.out(), /lws-serve: encryption at rest is OFF/);
  assert.equal((await fetch(`${pod}/`)).status, 401, 'the pod refuses an anonymous request');

  const s = await start(['webdav-serve', 'dav', '--port', '0', '--users', 'users.txt', '--guest', 'guest']);
  assert.match(s.out(), /WARNING: read only \(emergency mode, issue 1147\)/);
  assert.match(s.out(), /a request with no credentials acts as the guest user "guest" \(--guest\)/);
  assert.match(s.out(), /listening on http:\/\/127\.0\.0\.1:\d+ for dav, login from users\.txt, guest guest/);
  dav = s.origin;
});

test('the rights of each agent over LWS, as the page states them', async () => {
  assert.ok(dav, 'setup ran');
  const { createLwsClient } = await import('../../npm/factoidal/lws/client.mjs');
  for (const a of AGENTS) {
    const jwk = JSON.parse(fs.readFileSync(path.join(work, 'keys', `${a}.jwk`), 'utf8'));
    client[a] = await createLwsClient({ selfIssued: { subject: did[a], keyId: `${did[a]}#${did[a].slice(8)}`, jwk } });
  }
  // A refusal is thrown; its status is what the page shows.
  const st = (p) => p.then((r) => r.status, (e) => e.detail?.status ?? e.message);
  const put = (a, name, body, mediaType = 'text/plain') => st(client[a].update(`${pod}/${name}`, { body, mediaType, precondition: 'none' }));
  assert.equal(await put('danbri1', 'hello.txt', 'hello from danbri1'), 201);
  assert.equal(await st(client.danbri1.read(`${pod}/hello.txt`)), 200);
  assert.equal(await st(client.danbri1_bot1.read(`${pod}/hello.txt`)), 200);
  assert.equal(await put('danbri1_bot1', 'bot1.txt', 'written by bot1'), 201);
  assert.equal(await st(client.danbri1_bot2.read(`${pod}/hello.txt`)), 200);
  assert.equal((await client.danbri1_bot2.read(`${pod}/bot1.txt`)).body, 'written by bot1');
  assert.equal(await put('danbri1_bot2', 'bot2.txt', 'bot2 tries'), 403, 'bot2 has Read only');
  assert.equal(await st(client.danbri1_bot2.delete(`${pod}/hello.txt`, { precondition: 'none' })), 403);
  assert.equal(await put('danbri1_bot1', '.acl', '', 'text/turtle'), 403, 'bot1 has no Control');
  assert.equal((await fetch(`${pod}/hello.txt`)).status, 401, 'no token, no access');
  assert.equal((await client.danbri1.read(`${pod}/hello.txt`)).body, 'hello from danbri1', 'the file is still there');
});

test('over WebDAV each login reads its own folder only, and nothing writes', async () => {
  assert.ok(client.danbri1, 'the LWS rights ran');
  for (const a of AGENTS) {
    const g = await req(dav, 'GET', `/${a}/hello.txt`, login(a));
    assert.equal(g.status, 200, a);
    assert.equal(g.text, 'hello from danbri1');
    const root = await req(dav, 'PROPFIND', '/', { depth: '1', ...login(a) });
    assert.equal(root.status, 207);
    assert.deepEqual(hrefs(root.text), ['/', `/${a}/`], `the root lists only ${a}'s folder`);
    const put = await req(dav, 'PUT', `/${a}/new.txt`, login(a), 'x');
    assert.equal(put.status, 403, `${a}: read only, whatever the pod allows`);
    assert.equal(put.text, READ_ONLY);
    for (const m of ['DELETE', 'MKCOL', 'COPY', 'MOVE', 'PROPPATCH', 'LOCK', 'UNLOCK']) {
      const r = await req(dav, m, `/${a}/hello.txt`, { destination: `${dav}/${a}/other.txt`, ...login(a) });
      assert.equal(r.status, 403, `${a} ${m}`);
    }
    for (const b of AGENTS.filter((x) => x !== a)) {
      const r = await req(dav, 'GET', `/${b}/hello.txt`, login(a));
      assert.equal(r.status, 404, `${a} in ${b}'s folder`);
      assert.equal(r.text, 'no mount of this name\n');
    }
  }
  // bot1 may write over LWS, but not over WebDAV: the pod holds no new.txt.
  await assert.rejects(client.danbri1.read(`${pod}/new.txt`));
  assert.equal((await req(dav, 'GET', '/danbri1_bot1/hello.txt', basic('danbri1_bot1', 'wrong'))).status, 401);
  assert.equal((await req(dav, 'GET', '/danbri1/.acl', login('danbri1'))).status, 200, 'the owner reads the ACL');
  assert.equal((await req(dav, 'PUT', '/danbri1/.acl', { 'content-type': 'text/turtle', ...login('danbri1') }, '')).status, 403);
});

test('WebDAV does not show the rights: the same read methods everywhere, no privilege set', async () => {
  assert.ok(dav, 'setup ran');
  for (const a of AGENTS) {
    const o = await req(dav, 'OPTIONS', `/${a}/`, login(a));
    assert.equal(o.headers.dav, '1');
    assert.equal(o.headers.allow, READ_ALLOW);
  }
  const r = await req(dav, 'PROPFIND', '/danbri1_bot2/hello.txt', { depth: '0', 'content-type': 'application/xml', ...login('danbri1_bot2') },
    '<?xml version="1.0"?><D:propfind xmlns:D="DAV:"><D:prop><D:current-user-privilege-set/></D:prop></D:propfind>');
  assert.equal(r.status, 207);
  assert.match(r.text, /current-user-privilege-set[\s\S]*404 Not Found/);
});

test('Guest gets only what --guest maps to', async () => {
  assert.ok(dav, 'setup ran');
  // --guest guest, and no mount lists guest: nothing.
  const root = await req(dav, 'PROPFIND', '/', { depth: '1' });
  assert.equal(root.status, 207);
  assert.deepEqual(hrefs(root.text), ['/']);
  for (const a of AGENTS) assert.equal((await req(dav, 'GET', `/${a}/hello.txt`)).status, 404, a);

  // A mount lists guest: Guest reads that mount as its agent, read only, and no other.
  mountFiles(path.join(work, 'dav-guest'), { danbri1_bot2: ['guest'] });
  const g = await start(['webdav-serve', 'dav-guest', '--port', '0', '--users', 'users.txt', '--guest', 'guest']);
  assert.match(g.out(), /\/danbri1_bot2\/ - .*users: danbri1_bot2, guest\)/);
  assert.deepEqual(hrefs((await req(g.origin, 'PROPFIND', '/', { depth: '1' })).text), ['/', '/danbri1_bot2/']);
  assert.equal((await req(g.origin, 'GET', '/danbri1_bot2/hello.txt')).text, 'hello from danbri1');
  assert.equal((await req(g.origin, 'PUT', '/danbri1_bot2/g.txt', {}, 'x')).status, 403);
  const other = await req(g.origin, 'GET', '/danbri1_bot1/hello.txt');
  assert.equal(other.status, 404);
  assert.equal(other.text, 'no mount of this name\n');
  // Credentials never fall back to Guest.
  assert.equal((await req(g.origin, 'GET', '/danbri1_bot2/hello.txt', basic('danbri1_bot2', 'wrong'))).status, 401);
  await stop(g.child);

  // No --guest: a request with no credentials gets 401.
  const n = await start(['webdav-serve', 'dav-guest', '--port', '0', '--users', 'users.txt']);
  assert.equal((await req(n.origin, 'GET', '/danbri1_bot2/hello.txt')).status, 401);
  await stop(n.child);

  // The guest may not be a user of the users file.
  const r = spawnSync(process.execPath, [CLI, 'webdav-serve', 'dav', '--port', '0', '--users', 'users.txt', '--guest', 'danbri1'], { cwd: work, encoding: 'utf8' });
  assert.equal(r.status, 1);
  assert.match(r.stderr, /"danbri1" is a user of the users file/);
});

test('the 0.20.0 routes around the ACL are closed: local mounts and solid-serve are refused', () => {
  assert.ok(dav, 'setup ran');
  const raw = path.join(work, 'raw');
  fs.mkdirSync(path.join(raw, 'dav'), { recursive: true });
  fs.writeFileSync(path.join(raw, 'dav', 'raw.md'), '# the pod storage, local mount\n- kind: local\n- path: ../../danbri1-pod\n- storage: files\n- users: guest\n');
  let r = spawnSync(process.execPath, [CLI, 'webdav-serve', 'dav', '--port', '0', '--guest', 'guest'], { cwd: raw, encoding: 'utf8', timeout: 60000 });
  assert.equal(r.status, 1);
  assert.match(r.stderr, /raw\.md:2: a `kind: local` mount opens its storage with no authorization and is refused \(emergency mode, https:\/\/github\.com\/danbri\/factoidal\/issues\/1147\); use kind: lws with an agent key \(`auth: did-key`, `key-file`\) and the storage's own access control/);
  // A copy without lws.lock: the pod's storage as it is when lws-serve is not running.
  fs.cpSync(path.join(work, 'danbri1-pod'), path.join(work, 'pod-copy'), { recursive: true,
    filter: (src) => path.basename(src) !== 'lws.lock' });
  r = spawnSync(process.execPath, [CLI, 'solid-serve', 'pod-copy', '--port', '0', '--issuer', 'https://issuer.example'], { cwd: work, encoding: 'utf8', timeout: 60000 });
  assert.equal(r.status, 1);
  assert.match(r.stderr, /solid-serve: config: this directory holds a Linked Web Storage storage \(written by lws-serve\); only lws-serve serves it, through LWS authorization/);
});
