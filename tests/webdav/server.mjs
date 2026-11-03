// Host tests of `factoidal webdav-serve` (https://github.com/danbri/factoidal/issues/1066).
//
//   node tests/webdav/server.mjs
//
// Emergency mode (https://github.com/danbri/factoidal/issues/1147): the
// server is read only, every request acts as one named user (the --guest
// user with no credentials, a user of --users with credentials), a mount
// names its users (`users:`), and local mounts are refused at start.
//
// One `lws-serve --authz` storage started here, owned by the did:key of
// remote.jwk, filled through the LWS client as the owner. One configuration
// directory, three lws mounts of that storage:
//   remote.md  auth did-key remote.jwk (the owner), users: alice, guest
//   other.md   auth did-key other.jwk (made by the engine; not the owner, so
//              the storage refuses it), users: alice
//   hidden.md  auth did-key remote.jwk, users: bob
// plus README.md, which is not a mount. Then the refusals at start, and the
// login of the listener (https://github.com/danbri/factoidal/issues/1108).
// Every decision is formal/lean4/L4Factoidal/WebDAV/; this file plays the
// file browser.
//
// Score line: "N pass, M fail, X xfail, S skipped (out of T)".

import { spawn } from 'node:child_process'
import { mkdtempSync, mkdirSync, rmSync, writeFileSync, readFileSync, existsSync, statSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { keyPair, didKeyOf } from '../authz/fixtures.mjs'

let passed = 0
let failed = 0
let skipped = 0
const failures = []

async function check (name, body) {
  try {
    await body()
    passed += 1
    console.log(`  ok    ${name}`)
  } catch (error) {
    failed += 1
    failures.push(`${name}: ${error && error.message ? error.message : String(error)}`)
    console.log(`  FAIL  ${name}`)
  }
}

let xfailed = 0

/** An expected failure: a stated shortfall with its open issue. It counts as
 *  xfail while it fails; when it passes the run turns red, so the issue is
 *  closed and the check made a plain one. */
async function xfail (name, issue, body) {
  try {
    await body()
    failed += 1
    failures.push(`${name}: passes, but is an expected failure of ${issue}: make it a check and close the issue`)
    console.log(`  XPASS ${name}`)
  } catch (error) {
    xfailed += 1
    console.log(`  xfail ${name} - ${issue}: ${error && error.message ? error.message : String(error)}`)
  }
}

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

const CLI = fileURLToPath(new URL('../../npm/factoidal/bin/factoidal.mjs', import.meta.url))

function start (args) {
  const child = spawn(process.execPath, [CLI, ...args], { stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, FACTOIDAL_LWS_KEY: '' } })
  return new Promise((resolve, reject) => {
    let out = ''
    let errText = ''
    const timer = setTimeout(() => reject(new Error(`no origin printed: ${out} ${errText}`)), 60000)
    child.stdout.on('data', (c) => {
      out += c
      const m = /(http:\/\/[^\s]+)/.exec(out)
      if (m) { clearTimeout(timer); resolve({ child, origin: m[1], errText: () => errText }) }
    })
    child.stderr.on('data', (c) => { errText += c })
    child.on('exit', (code) => { clearTimeout(timer); reject(Object.assign(new Error(`exited ${code}: ${out} ${errText}`), { code, out, errText })) })
  })
}

function run (args) {
  const child = spawn(process.execPath, [CLI, ...args], { stdio: ['ignore', 'pipe', 'pipe'] })
  return new Promise((resolve) => {
    let out = ''
    let errText = ''
    child.stdout.on('data', (c) => { out += c })
    child.stderr.on('data', (c) => { errText += c })
    child.on('exit', (code) => resolve({ code, out, errText }))
  })
}

/** Run the CLI with `input` on standard input (not a terminal). */
function runWithInput (args, input) {
  const child = spawn(process.execPath, [CLI, ...args], { stdio: ['pipe', 'pipe', 'pipe'] })
  child.stdin.end(input)
  return new Promise((resolve) => {
    let out = ''
    let errText = ''
    child.stdout.on('data', (c) => { out += c })
    child.stderr.on('data', (c) => { errText += c })
    child.on('exit', (code) => resolve({ code, out, errText }))
  })
}

function basic (user, password) {
  return 'Basic ' + Buffer.from(`${user}:${password}`, 'utf8').toString('base64')
}

/** The login of the listener (issue 1108). */
async function login (dir, lwsOrigin, ownerJwk) {
  const conf = join(dir, 'login')
  mkdirSync(conf, { recursive: true })
  writeFileSync(join(conf, 'owner.jwk'), ownerJwk, { mode: 0o600 })
  writeFileSync(join(conf, 'notes.md'), `# Notes\n- kind: lws\n- url: ${lwsOrigin}/\n- auth: did-key\n- key-file: owner.jwk\n- users: alice, bob\n`)
  const users = join(dir, 'users.txt')
  await check('webdav-user: writes NAME:pbkdf2-sha256:ITERATIONS:SALT:HASH with mode 0600; a second name is added', async () => {
    let r = await runWithInput(['webdav-user', users, 'alice', '--iterations', '100000'], 'open sesame\n')
    assert(r.code === 0, `exit ${r.code} ${r.errText}`)
    r = await runWithInput(['webdav-user', users, 'bob'], 'hunter2')
    assert(r.code === 0, `exit ${r.code} ${r.errText}`)
    const lines = readFileSync(users, 'utf8').split('\n').filter((l) => l !== '')
    assert(lines.length === 2, `lines ${lines.length}`)
    assert(/^alice:pbkdf2-sha256:100000:[A-Za-z0-9+/]{22}==:[A-Za-z0-9+/]{43}=$/.test(lines[0]), lines[0])
    assert(/^bob:pbkdf2-sha256:600000:/.test(lines[1]), lines[1])
    assert((statSync(users).mode & 0o777) === 0o600, `mode ${(statSync(users).mode & 0o777).toString(8)}`)
  })
  await check('webdav-user: replaces a line in place; refuses an empty password, a name with ":" and 99999 iterations (exit 1)', async () => {
    const before = readFileSync(users, 'utf8').split('\n')
    let r = await runWithInput(['webdav-user', users, 'alice', '--iterations', '100000'], 'open sesame\n')
    assert(r.code === 0 && r.errText.includes('replaced alice'), `exit ${r.code} ${r.errText}`)
    const after = readFileSync(users, 'utf8').split('\n')
    assert(after.length === before.length && after[1] === before[1] && after[0] !== before[0], 'not replaced in place')
    r = await runWithInput(['webdav-user', users, 'carol'], '\n')
    assert(r.code === 1 && r.errText.includes('the password is empty'), `empty ${r.code} ${r.errText}`)
    r = await runWithInput(['webdav-user', users, 'a:b'], 'x\n')
    assert(r.code === 1 && r.errText.includes('holds ":"'), `colon ${r.code} ${r.errText}`)
    r = await runWithInput(['webdav-user', users, 'carol', '--iterations', '99999'], 'x\n')
    assert(r.code === 1 && r.errText.includes('outside 100000'), `iterations ${r.code} ${r.errText}`)
  })
  let web = null
  try {
    web = await start(['webdav-serve', conf, '--port', '0', '--users', users])
    const origin = web.origin
    await check('login: no credentials is 401 with WWW-Authenticate: Basic realm, charset UTF-8', async () => {
      const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '1' } })
      assert(r.status === 401, `status ${r.status}`)
      assert(r.headers.get('www-authenticate') === 'Basic realm="factoidal webdav", charset="UTF-8"', `${r.headers.get('www-authenticate')}`)
      const o = await dav(origin, 'OPTIONS', '/')
      assert(o.status === 401, `OPTIONS ${o.status}`)
    })
    await check('login: a wrong password, an unknown user and a Bearer token are 401', async () => {
      for (const a of [basic('alice', 'wrong'), basic('mallory', 'open sesame'), 'Bearer x']) {
        const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '1', authorization: a } })
        assert(r.status === 401, `${a}: ${r.status}`)
      }
    })
    await check('login: the right password is 207; GET works for both users; PUT is 403 (read only, issue 1147)', async () => {
      let r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '1', authorization: basic('alice', 'open sesame') } })
      assert(r.status === 207 && r.text.includes('<D:href>/notes/</D:href>'), `PROPFIND ${r.status} ${r.text}`)
      r = await dav(origin, 'PUT', '/notes/a.txt', { headers: { authorization: basic('bob', 'hunter2') }, body: 'from bob' })
      assert(r.status === 403, `PUT ${r.status} ${r.text}`)
      for (const a of [basic('alice', 'open sesame'), basic('bob', 'hunter2')]) {
        r = await dav(origin, 'GET', '/notes/greeting.txt', { headers: { authorization: a } })
        assert(r.status === 200 && r.text === 'hello', `GET ${r.status} ${r.text}`)
      }
      r = await dav(origin, 'GET', '/notes/greeting.txt')
      assert(r.status === 401, `GET without credentials and no --guest ${r.status}`)
    })
    // The failed-login limit (https://github.com/danbri/factoidal/issues/1119):
    // 5 failures per 60 s per name and per address. The checks above made 2
    // failures from this address (alice, mallory); the Bearer 401 is not one.
    await check('login: repeated wrong passwords get 429 (limit 5 per 60 s, per name and per address)', async () => {
      const statuses = []
      for (let i = 0; i < 8; i++) {
        const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '0', authorization: basic('alice', `wrong-${i}`) } })
        statuses.push(r.status)
      }
      assert(statuses.join(' ') === '401 401 401 429 429 429 429 429', `statuses ${statuses.join(' ')}`)
    })
    await check('login: a 429 carries Retry-After (1 to 60 s); the right password and another name from this address get 429 too', async () => {
      for (const a of [basic('alice', 'open sesame'), basic('bob', 'hunter2'), basic('mallory', 'x')]) {
        const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '0', authorization: a } })
        const ra = r.headers.get('retry-after')
        assert(r.status === 429, `${a}: ${r.status}`)
        assert(/^[0-9]+$/.test(ra || '') && Number(ra) >= 1 && Number(ra) <= 60, `Retry-After ${ra}`)
      }
      const n = await dav(origin, 'PROPFIND', '/', { headers: { depth: '0' } })
      assert(n.status === 401, `no credentials while blocked: ${n.status}`)
    })
  } finally {
    await stop(web)
  }
  web = null
  try {
    web = await start(['webdav-serve', conf, '--port', '0', '--users', users, '--login-limit', '2', '--login-window', '2'])
    const origin = web.origin
    await check('login: --login-limit 2 --login-window 2: the right password gets 429 until the window ends, then 207', async () => {
      const statuses = []
      for (const pw of ['w1', 'w2', 'open sesame']) {
        const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '0', authorization: basic('alice', pw) } })
        statuses.push(r.status)
      }
      assert(statuses.join(' ') === '401 401 429', `statuses ${statuses.join(' ')}`)
      await new Promise((resolve) => setTimeout(resolve, 3200))
      const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '0', authorization: basic('alice', 'open sesame') } })
      assert(r.status === 207, `after the window ${r.status}`)
    })
  } finally {
    await stop(web)
  }
  web = null
  try {
    web = await start(['webdav-serve', conf, '--port', '0', '--users', users, '--dangerously-disable-ratelimits'])
    const origin = web.origin
    await check('login: --dangerously-disable-ratelimits prints a warning at start and gives 401, not 429, after 8 failures', async () => {
      // Standard error and standard output are two pipes: wait for the warning.
      for (let i = 0; i < 50 && !web.errText().includes('WARNING: --dangerously'); i++) await new Promise((resolve) => setTimeout(resolve, 100))
      assert(web.errText().includes('WARNING: --dangerously-disable-ratelimits: failed logins are NOT limited'), web.errText())
      assert(web.errText().includes('EXPERIMENTAL UNREVIEWED CODE'), web.errText())
      const statuses = []
      for (let i = 0; i < 9; i++) {
        const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '0', authorization: basic('alice', `wrong-${i}`) } })
        statuses.push(r.status)
      }
      assert(statuses.every((x) => x === 401), `statuses ${statuses.join(' ')}`)
      const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '0', authorization: basic('alice', 'open sesame') } })
      assert(r.status === 207, `right password ${r.status}`)
    })
  } finally {
    await stop(web)
  }
  await check('start: bad limit options stop the start (exit 1): --login-limit 0, --login-window x, the dangerous option with --login-limit or without --users', async () => {
    let r = await run(['webdav-serve', conf, '--port', '0', '--users', users, '--login-limit', '0'])
    assert(r.code === 1 && r.errText.includes('--login-limit 0: give a whole number from 1 to 1000'), `limit ${r.code} ${r.errText}`)
    r = await run(['webdav-serve', conf, '--port', '0', '--users', users, '--login-window', 'x'])
    assert(r.code === 1 && r.errText.includes('--login-window x: give a whole number of seconds'), `window ${r.code} ${r.errText}`)
    r = await run(['webdav-serve', conf, '--port', '0', '--users', users, '--login-limit', '3', '--dangerously-disable-ratelimits'])
    assert(r.code === 1 && r.errText.includes('cannot go with it'), `both ${r.code} ${r.errText}`)
    r = await run(['webdav-serve', conf, '--port', '0', '--dangerously-disable-ratelimits'])
    assert(r.code === 1 && r.errText.includes('need --users'), `no users ${r.code} ${r.errText}`)
  })
  await check('login cache: one PBKDF2 derivation for the first request, none for the next, one for a wrong password', async () => {
    const { openWebdav } = await import('../../npm/factoidal/webdav/server.mjs')
    const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
    const engine = await loadEngine()
    let derivations = 0
    const counting = {
      call: (op, args) => engine.call(op, args),
      callBlobIO: (op, args, bytes) => {
        const got = engine.callBlobIO(op, args, bytes)
        if (got.envelope && got.envelope.need !== undefined) derivations += 1
        return got
      }
    }
    const h = await openWebdav({ configDir: conf, users: users, engine: counting })
    try {
      const ask = (a) => h.step({ method: 'PROPFIND', target: '/', headers: [['Depth', '0'], ['Authorization', a]], body: new Uint8Array(0) })
      let r = await ask(basic('alice', 'open sesame'))
      assert(r.status === 207 && derivations === 1, `first ${r.status}, ${derivations} derivations`)
      r = await ask(basic('alice', 'open sesame'))
      assert(r.status === 207 && derivations === 1, `second ${r.status}, ${derivations} derivations`)
      r = await ask(basic('alice', 'wrong'))
      assert(r.status === 401 && derivations === 2, `wrong ${r.status}, ${derivations} derivations`)
      r = await ask(basic('alice', 'open sesame'))
      assert(r.status === 207 && derivations === 2, `after a wrong one ${r.status}, ${derivations} derivations`)
    } finally {
      h.close()
    }
  })
  await check('start: --users on a non-loopback address without TLS stops the start (exit 1)', async () => {
    const r = await run(['webdav-serve', conf, '--port', '0', '--host', '0.0.0.0', '--users', users])
    assert(r.code === 1 && r.errText.includes('0.0.0.0 is not a loopback address'), `exit ${r.code} ${r.errText}`)
  })
  await check('start: a malformed users file stops the start with its name and line (exit 1); so does a missing one', async () => {
    const bad = join(dir, 'bad-users.txt')
    writeFileSync(bad, '# users\nalice:placeholder\n')
    let r = await run(['webdav-serve', conf, '--port', '0', '--users', bad])
    assert(r.code === 1 && r.errText.includes('bad-users.txt:2: a line has 5 fields'), `exit ${r.code} ${r.errText}`)
    r = await run(['webdav-serve', conf, '--port', '0', '--users', join(dir, 'absent.txt')])
    assert(r.code === 1 && r.errText.includes('absent.txt: the users file could not be read'), `exit ${r.code} ${r.errText}`)
  })
}

async function stop (proc) {
  if (proc === null) return
  proc.child.kill('SIGTERM')
  await new Promise((resolve) => proc.child.on('close', resolve))
}

const LOCK = '<?xml version="1.0" encoding="utf-8"?><D:lockinfo xmlns:D="DAV:"><D:lockscope><D:exclusive/></D:lockscope><D:locktype><D:write/></D:locktype><D:owner>tests/webdav</D:owner></D:lockinfo>'
const PROPSET = '<D:propertyupdate xmlns:D="DAV:" xmlns:Z="http://example.org/z/"><D:set><D:prop><Z:colour>green</Z:colour></D:prop></D:set></D:propertyupdate>'
const READ_ALLOW = 'OPTIONS, GET, HEAD, PROPFIND'

async function dav (origin, method, path, { headers = {}, body } = {}) {
  const r = await fetch(origin + path, { method, headers, body })
  return { status: r.status, headers: r.headers, text: await r.text() }
}

/** Every write method on `path`, with these headers: each must be 403. */
async function writesRefused (origin, path, headers = {}) {
  const writes = [
    ['PUT', { body: 'changed' }],
    ['DELETE', {}],
    ['MKCOL', {}],
    ['COPY', { headers: { destination: origin + path + '.copy' } }],
    ['MOVE', { headers: { destination: origin + path + '.moved' } }],
    ['PROPPATCH', { body: PROPSET }],
    ['LOCK', { headers: { timeout: 'Second-60' }, body: LOCK }],
    ['UNLOCK', { headers: { 'lock-token': '<urn:uuid:00000000-0000-4000-8000-000000000000>' } }]
  ]
  for (const [method, opts] of writes) {
    const r = await dav(origin, method, path, { headers: { ...headers, ...(opts.headers || {}) }, body: opts.body })
    assert(r.status === 403, `${method} ${path}: ${r.status} ${r.text}`)
    assert(r.headers.get('allow') === READ_ALLOW, `${method} Allow ${r.headers.get('allow')}`)
    assert(r.text.includes('read only (emergency mode'), `${method} body ${r.text}`)
  }
}

async function main () {
  const dir = mkdtempSync(join(process.env.WEBDAV_TEST_TMP || tmpdir(), 'factoidal-webdav-'))
  const conf = join(dir, 'conf')
  mkdirSync(conf)
  const owner = keyPair('ES256')
  const did = didKeyOf(owner)
  const ownerJwk = JSON.stringify(owner.privateKey.export({ format: 'jwk' }))
  writeFileSync(join(conf, 'remote.jwk'), ownerJwk, { mode: 0o600 })
  writeFileSync(join(conf, 'README.md'), '# Not a mount\n- colour: red\n')
  const users = join(dir, 'users-main.txt')
  let lws = null
  let web = null
  try {
    try {
      lws = await start(['lws-serve', join(dir, 'lws'), '--port', '0', '--authz', join(dir, 'lws-as'), '--owner', did, '--quiet'])
    } catch (error) {
      console.log(`  skip  every check - lws-serve did not start: ${error.message}`)
      skipped += 1
      return
    }
    // The storage, filled as its owner through the LWS client.
    const { createLwsClient } = await import('../../npm/factoidal/lws/client.mjs')
    const ownerClient = await createLwsClient({
      selfIssued: { subject: did, keyId: `${did}#${did.slice(8)}`, jwk: owner.privateKey.export({ format: 'jwk' }) }
    })
    const seeded = await ownerClient.update(`${lws.origin}/greeting.txt`, { body: 'hello', mediaType: 'text/plain', precondition: 'none' })
    assert(seeded.status === 201 || seeded.status === 204, `seed ${seeded.status}`)
    const bin = new Uint8Array([0, 0xff, 0x80, 0x89, 0x50, 0x4e, 0x47, 0xfe])
    await ownerClient.update(`${lws.origin}/bin.dat`, { body: bin, mediaType: 'application/octet-stream', precondition: 'none' })
    writeFileSync(join(conf, 'remote.md'), `# Remote storage\n- kind: lws\n- url: ${lws.origin}/\n- auth: did-key\n- key-file: remote.jwk\n- writable: true\n- users: alice, guest\n`)
    writeFileSync(join(conf, 'other.md'), `# Someone else\n- kind: lws\n- url: ${lws.origin}/\n- auth: did-key\n- key-file: other.jwk\n- users: alice\n`)
    writeFileSync(join(conf, 'hidden.md'), `# Bob only\n- kind: lws\n- url: ${lws.origin}/\n- auth: did-key\n- key-file: remote.jwk\n- users: bob\n`)
    let r0 = await runWithInput(['webdav-user', users, 'alice', '--iterations', '100000'], 'open sesame\n')
    assert(r0.code === 0, `webdav-user alice ${r0.code} ${r0.errText}`)
    r0 = await runWithInput(['webdav-user', users, 'bob', '--iterations', '100000'], 'hunter2\n')
    assert(r0.code === 0, `webdav-user bob ${r0.code} ${r0.errText}`)
    const alice = { authorization: basic('alice', 'open sesame') }
    const bob = { authorization: basic('bob', 'hunter2') }
    try {
      web = await start(['webdav-serve', conf, '--port', '0', '--users', users, '--guest', 'guest'])
    } catch (error) {
      if (/exited 3|not yet wired|does not carry webdav/.test(String(error.message))) {
        skipped += 1
        console.log(`  skip  every check - the wasm module carries no WebDAV ops: ${error.message}`)
        return
      }
      throw error
    }
    const origin = web.origin
    await check('start: the output says read only (emergency mode, issue 1147) and names the guest', async () => {
      for (let i = 0; i < 50 && !web.errText().includes('listening on'); i++) await new Promise((resolve) => setTimeout(resolve, 100))
      assert(web.errText().includes('read only (emergency mode, issue 1147)'), web.errText())
      assert(web.errText().includes('acts as the guest user "guest"'), web.errText())
      assert(web.errText().includes('users: alice, guest'), web.errText())
    })
    await check('start: the remote mount acts as the did:key of its key file; the key file the engine made exists, mode 0600', async () => {
      assert(web.errText().includes(did), `the start lines do not name ${did}: ${web.errText()}`)
      const p = join(conf, 'other.jwk')
      assert(existsSync(p), 'no other.jwk')
      assert((statSync(p).mode & 0o777) === 0o600, `mode ${(statSync(p).mode & 0o777).toString(8)}`)
    })
    await check('OPTIONS: DAV 1, MS-Author-Via, Allow lists only the read methods', async () => {
      const r = await dav(origin, 'OPTIONS', '/remote/')
      assert(r.status === 200, `status ${r.status}`)
      assert(r.headers.get('dav') === '1', `dav ${r.headers.get('dav')}`)
      assert(r.headers.get('ms-author-via') === 'DAV', 'no MS-Author-Via')
      assert(r.headers.get('allow') === READ_ALLOW, `allow ${r.headers.get('allow')}`)
    })
    await check('guest (no credentials): the root lists only the mounts that name guest, not README.md', async () => {
      const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '1' } })
      assert(r.status === 207, `status ${r.status}`)
      assert(r.text.includes('<D:href>/remote/</D:href>'), 'no remote')
      assert(!r.text.includes('/other/') && !r.text.includes('/hidden/'), `lists another user's mount: ${r.text}`)
      assert(!r.text.includes('README'), 'README.md is a mount')
      assert(r.text.includes('<D:displayname>Remote storage</D:displayname>'), 'no display name')
      const g = await dav(origin, 'GET', '/')
      assert(g.status === 200 && g.text.includes('/remote/') && !g.text.includes('/hidden/'), `GET / ${g.text}`)
    })
    await check('guest: GET, HEAD and PROPFIND read the storage as the mount agent', async () => {
      let r = await dav(origin, 'GET', '/remote/greeting.txt')
      assert(r.status === 200 && r.text === 'hello', `GET ${r.status} ${r.text}`)
      r = await dav(origin, 'HEAD', '/remote/greeting.txt')
      assert(r.status === 200, `HEAD ${r.status}`)
      r = await dav(origin, 'PROPFIND', '/remote/greeting.txt', { headers: { depth: '0' } })
      assert(r.status === 207 && r.text.includes('<D:getcontentlength>5</D:getcontentlength>'), `PROPFIND ${r.status} ${r.text}`)
      assert(r.text.includes('<D:supportedlock/>'), 'a lock is offered')
      r = await dav(origin, 'PROPFIND', '/remote/', { headers: { depth: '1' } })
      assert(r.status === 207 && r.text.split('<D:href>/remote/greeting.txt</D:href>').length === 2, `Depth 1 ${r.text}`)
      const b = await fetch(origin + '/remote/bin.dat')
      const got = new Uint8Array(await b.arrayBuffer())
      assert(got.length === bin.length && got.every((x, i) => x === bin[i]), 'bytes differ')
      r = await dav(origin, 'PROPFIND', '/remote/', { headers: { depth: 'infinity' } })
      assert(r.status === 403 && r.text.includes('propfind-finite-depth'), `infinity ${r.status}`)
    })
    await check('read only: every write method is 403 with Allow of the read methods, for the guest and for a logged-in user, on every mount (writable: true is ignored)', async () => {
      await writesRefused(origin, '/remote/greeting.txt')
      await writesRefused(origin, '/remote/greeting.txt', alice)
      await writesRefused(origin, '/remote/new.txt', alice)
      await writesRefused(origin, '/hidden/greeting.txt', bob)
      await writesRefused(origin, '/', alice)
    })
    await check('read only: the LWS storage is unchanged after the writes (read by the LWS client as the owner)', async () => {
      const got = await ownerClient.read(`${lws.origin}/greeting.txt`)
      assert(got.status === 200 && got.body === 'hello', `LWS client read ${got.status} ${got.body}`)
      for (const name of ['new.txt', 'greeting.txt.copy', 'greeting.txt.moved']) {
        const h = await fetch(`${lws.origin}/${name}`)
        assert(h.status === 401 || h.status === 404, `${name}: ${h.status}`)
        let gone = false
        try {
          const x = await ownerClient.read(`${lws.origin}/${name}`)
          gone = x.status === 404
        } catch (error) {
          gone = error && error.detail && error.detail.status === 404
        }
        assert(gone, `${name} exists in the storage`)
      }
    })
    await check('users: alice sees remote and other, not hidden; bob sees hidden only', async () => {
      let r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '1', ...alice } })
      assert(r.status === 207 && r.text.includes('/remote/') && r.text.includes('/other/') && !r.text.includes('/hidden/'), `alice ${r.text}`)
      r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '1', ...bob } })
      assert(r.status === 207 && r.text.includes('/hidden/') && !r.text.includes('/remote/') && !r.text.includes('/other/'), `bob ${r.text}`)
      r = await dav(origin, 'GET', '/hidden/greeting.txt', { headers: bob })
      assert(r.status === 200 && r.text === 'hello', `bob GET ${r.status}`)
    })
    await check('users: a mount the user may not use is 404, as a mount that does not exist (same body), on every read method', async () => {
      const absent = await dav(origin, 'GET', '/nomount/greeting.txt', { headers: alice })
      assert(absent.status === 404, `absent ${absent.status}`)
      for (const [method, path, headers] of [['GET', '/hidden/greeting.txt', alice], ['HEAD', '/hidden/greeting.txt', alice],
        ['PROPFIND', '/hidden/', { depth: '0', ...alice }], ['OPTIONS', '/hidden/', alice],
        ['GET', '/remote/greeting.txt', bob], ['GET', '/other/greeting.txt', {}], ['GET', '/hidden/', {}]]) {
        const r = await dav(origin, method, path, { headers })
        assert(r.status === 404, `${method} ${path}: ${r.status}`)
        if (method !== 'HEAD') assert(r.text === absent.text, `${method} ${path} body ${r.text}`)
      }
    })
    await check('the storage decides: a mount agent that is not the owner gets the storage refusal (403)', async () => {
      const r = await dav(origin, 'PROPFIND', '/other/', { headers: { depth: '1', ...alice } })
      assert(r.status === 403, `PROPFIND ${r.status} ${r.text}`)
    })
    await check('credentials: a wrong password, an unknown user, a Bearer token and a malformed value are 401, never the guest', async () => {
      for (const a of [basic('alice', 'wrong'), basic('mallory', 'x'), 'Bearer x', 'garbage']) {
        const r = await dav(origin, 'GET', '/remote/greeting.txt', { headers: { authorization: a } })
        assert(r.status === 401, `${a}: ${r.status}`)
        assert((r.headers.get('www-authenticate') || '').startsWith('Basic'), `${a}: no challenge`)
      }
    })
    await stop(web)
    web = null
    web = await start(['webdav-serve', conf, '--port', '0', '--users', users])
    await check('no --guest: a request with no credentials is 401 with WWW-Authenticate: Basic; a user is served', async () => {
      let r = await dav(web.origin, 'PROPFIND', '/', { headers: { depth: '1' } })
      assert(r.status === 401 && (r.headers.get('www-authenticate') || '').startsWith('Basic'), `status ${r.status}`)
      r = await dav(web.origin, 'GET', '/remote/greeting.txt')
      assert(r.status === 401, `GET ${r.status}`)
      r = await dav(web.origin, 'GET', '/remote/greeting.txt', { headers: alice })
      assert(r.status === 200 && r.text === 'hello', `alice ${r.status}`)
    })
    await stop(web)
    web = null
    web = await start(['webdav-serve', conf, '--port', '0', '--guest', 'guest'])
    await check('no --users: the guest is served; any request with credentials is 401 (no one to log in as)', async () => {
      let r = await dav(web.origin, 'GET', '/remote/greeting.txt')
      assert(r.status === 200 && r.text === 'hello', `guest ${r.status}`)
      r = await dav(web.origin, 'GET', '/remote/greeting.txt', { headers: alice })
      assert(r.status === 401, `credentials ${r.status}`)
    })
    await stop(web)
    web = null
    web = await start(['webdav-serve', conf, '--port', '0'])
    await check('neither --users nor --guest: every request is 401', async () => {
      for (const h of [{}, alice]) {
        const r = await dav(web.origin, 'PROPFIND', '/', { headers: { depth: '0', ...h } })
        assert(r.status === 401, `status ${r.status}`)
      }
      for (let i = 0; i < 50 && !web.errText().includes('no --guest'); i++) await new Promise((resolve) => setTimeout(resolve, 100))
      assert(web.errText().includes('no --guest: a request with no credentials gets 401'), web.errText())
    })
    await stop(web)
    web = null
    await check('start: --guest naming a user of --users stops the start (exit 1)', async () => {
      const r = await run(['webdav-serve', conf, '--port', '0', '--users', users, '--guest', 'alice'])
      assert(r.code === 1 && r.errText.includes('"alice" is a user of the users file'), `exit ${r.code} ${r.errText}`)
    })
    await check('start: a kind: local mount is refused with FILE:LINE, naming kind: lws with an agent key (exit 1)', async () => {
      const bad = join(dir, 'local')
      mkdirSync(join(bad, 'store'), { recursive: true })
      writeFileSync(join(bad, 'l.md'), '# L\n- kind: local\n- path: ./store\n- users: guest\n')
      const r = await run(['webdav-serve', bad, '--port', '0', '--guest', 'guest'])
      assert(r.code === 1 && r.errText.includes('l.md:2: a `kind: local` mount opens its storage with no authorization'), `exit ${r.code} ${r.errText}`)
      assert(r.errText.includes('use kind: lws with an agent key') && r.errText.includes('issues/1147'), r.errText)
    })
    await check('start: a mount with no users: is refused with FILE:LINE (exit 1)', async () => {
      const bad = join(dir, 'nousers')
      mkdirSync(bad)
      writeFileSync(join(bad, 'n.md'), `# N\n- kind: lws\n- url: ${lws.origin}/\n`)
      const r = await run(['webdav-serve', bad, '--port', '0', '--guest', 'guest'])
      assert(r.code === 1 && r.errText.includes('n.md:2: the settings list has no `users`'), `exit ${r.code} ${r.errText}`)
    })
    await check('start: auth bearer with a token file is refused without allow-external-token: true (exit 1); with it, a warning', async () => {
      const bad = join(dir, 'bearer')
      mkdirSync(bad)
      writeFileSync(join(bad, 't.token'), 'abc\n')
      writeFileSync(join(bad, 't.md'), `- kind: lws\n- url: ${lws.origin}/\n- auth: bearer\n- token-file: t.token\n- users: guest\n`)
      const r = await run(['webdav-serve', bad, '--port', '0', '--guest', 'guest'])
      assert(r.code === 1 && r.errText.includes('t.md:3: auth `bearer` uses the token file, a credential from outside this installation'), `exit ${r.code} ${r.errText}`)
      writeFileSync(join(bad, 't.md'), `- kind: lws\n- url: ${lws.origin}/\n- auth: bearer\n- token-file: t.token\n- users: guest\n- allow-external-token: true\n`)
      const w = await start(['webdav-serve', bad, '--port', '0', '--guest', 'guest'])
      try {
        for (let i = 0; i < 50 && !w.errText().includes('allow-external-token'); i++) await new Promise((resolve) => setTimeout(resolve, 100))
        assert(w.errText().includes('WARNING: t.md: allow-external-token: true: the mount uses the token file t.token'), w.errText())
      } finally {
        await stop(w)
      }
    })
    await check('start: a malformed state file stops the start with its name (exit 1)', async () => {
      const bad = join(dir, 'badstate')
      mkdirSync(bad)
      writeFileSync(join(bad, 's.md'), `- kind: lws\n- url: ${lws.origin}/\n- users: guest\n`)
      writeFileSync(join(bad, '.webdav-state.json'), '{"format":"factoidal-webdav-state","version":1,')
      let r = await run(['webdav-serve', bad, '--port', '0'])
      assert(r.code === 1 && r.errText.includes('.webdav-state.json: not JSON'), `exit ${r.code} ${r.errText}`)
      writeFileSync(join(bad, '.webdav-state.json'), '{"format":"factoidal-webdav-state","version":9,"serial":0,"props":[],"locks":[]}')
      r = await run(['webdav-serve', bad, '--port', '0'])
      assert(r.code === 1 && r.errText.includes('.webdav-state.json: format version 9 is not known'), `exit ${r.code} ${r.errText}`)
    })
    await check('start: a malformed mount file stops the start with its name and line (exit 1)', async () => {
      const bad = join(dir, 'bad')
      mkdirSync(bad)
      writeFileSync(join(bad, 'x.md'), '# X\n- kind: lws\n- colour: red\n')
      const r = await run(['webdav-serve', bad, '--port', '0'])
      assert(r.code === 1, `exit ${r.code}`)
      assert(r.errText.includes('x.md:3: unknown key "colour"'), r.errText)
    })
    await login(dir, lws.origin, ownerJwk)
  } finally {
    await stop(web)
    await stop(lws)
    rmSync(dir, { recursive: true, force: true })
  }
}

await main()
console.log(`webdav server: ${passed} pass, ${failed} fail, ${xfailed} xfail, ${skipped} skipped (out of ${passed + failed + xfailed + skipped})`)
for (const f of failures) console.log(`  ${f}`)
process.exit(failed === 0 ? 0 : 1)
