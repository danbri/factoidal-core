// Host tests of `factoidal webdav-serve` (https://github.com/danbri/factoidal/issues/1066).
//
//   node tests/webdav/server.mjs
//
// One configuration directory, three mounts:
//   local.md   kind local, an lws-serve storage directory (snapshot), writable
//   remote.md  kind lws, `lws-serve --authz` started here with --owner the
//              did:key of remote.jwk, auth did-key, writable
//   other.md   kind lws, the same storage, auth did-key with a key file that
//              does not exist (the engine makes it), read-only; that agent is
//              not the owner, so the storage refuses it
// plus README.md, which is not a mount. Then the login of the listener
// (https://github.com/danbri/factoidal/issues/1108): `webdav-user` writes a
// users file, `webdav-serve --users` needs HTTP Basic, the login cache, and
// the refusals at start. Every WebDAV method runs through the
// local and the remote mount, through the CLI and the socket. Every decision
// is formal/lean4/L4Factoidal/WebDAV/; this file plays the file browser.
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
async function login (dir) {
  const conf = join(dir, 'login')
  mkdirSync(join(conf, 'store'), { recursive: true })
  writeFileSync(join(conf, 'notes.md'), '# Notes\n- kind: local\n- path: ./store\n')
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
    await check('login: the right password is 207; PUT and GET work for both users', async () => {
      let r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '1', authorization: basic('alice', 'open sesame') } })
      assert(r.status === 207 && r.text.includes('<D:href>/notes/</D:href>'), `PROPFIND ${r.status} ${r.text}`)
      r = await dav(origin, 'PUT', '/notes/a.txt', { headers: { authorization: basic('bob', 'hunter2') }, body: 'from bob' })
      assert(r.status === 201, `PUT ${r.status} ${r.text}`)
      r = await dav(origin, 'GET', '/notes/a.txt', { headers: { authorization: basic('alice', 'open sesame') } })
      assert(r.status === 200 && r.text === 'from bob', `GET ${r.status} ${r.text}`)
      r = await dav(origin, 'GET', '/notes/a.txt')
      assert(r.status === 401, `GET without credentials ${r.status}`)
    })
    await xfail('login: repeated wrong passwords get 429', 'https://github.com/danbri/factoidal/issues/1119', async () => {
      const statuses = []
      for (let i = 0; i < 8; i++) {
        const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '0', authorization: basic('alice', `wrong-${i}`) } })
        statuses.push(r.status)
      }
      assert(statuses.includes(429), `no 429 after 8 wrong passwords: ${statuses.join(' ')}`)
    })
  } finally {
    await stop(web)
  }
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
const PROPGET = '<D:propfind xmlns:D="DAV:"><D:prop><Z:colour xmlns:Z="http://example.org/z/"/><D:getcontentlength/></D:prop></D:propfind>'

async function dav (origin, method, path, { headers = {}, body } = {}) {
  const r = await fetch(origin + path, { method, headers, body })
  return { status: r.status, headers: r.headers, text: await r.text() }
}

/** Every method through one mount. */
async function methods (origin, m) {
  const base = `/${m}/`
  await check(`${m}: OPTIONS advertises DAV 1, 2 and MS-Author-Via`, async () => {
    const r = await dav(origin, 'OPTIONS', base)
    assert(r.status === 200, `status ${r.status}`)
    assert(r.headers.get('dav') === '1, 2', `dav ${r.headers.get('dav')}`)
    assert(r.headers.get('ms-author-via') === 'DAV', 'no MS-Author-Via')
  })
  await check(`${m}: PUT creates (201), GET reads it back, PUT again replaces (204)`, async () => {
    let r = await dav(origin, 'PUT', base + 'hello.txt', { headers: { 'content-type': 'text/plain' }, body: 'hello' })
    assert(r.status === 201, `PUT ${r.status} ${r.text}`)
    r = await dav(origin, 'GET', base + 'hello.txt')
    assert(r.status === 200 && r.text === 'hello', `GET ${r.status} ${r.text}`)
    r = await dav(origin, 'PUT', base + 'hello.txt', { headers: { 'content-type': 'text/plain' }, body: 'hello, world' })
    assert(r.status === 204, `PUT again ${r.status}`)
  })
  await check(`${m}: PUT of bytes that are not UTF-8 reads back byte for byte`, async () => {
    const bytes = new Uint8Array([0, 0xff, 0x80, 0x89, 0x50, 0x4e, 0x47, 0xfe])
    let r = await fetch(origin + base + 'bin.dat', { method: 'PUT', body: bytes })
    assert(r.status === 201, `PUT ${r.status}`)
    r = await fetch(origin + base + 'bin.dat')
    const got = new Uint8Array(await r.arrayBuffer())
    assert(got.length === bytes.length && got.every((b, i) => b === bytes[i]), 'bytes differ')
  })
  await check(`${m}: MKCOL creates a collection (201); again 405; no parent 409`, async () => {
    let r = await dav(origin, 'MKCOL', base + 'docs')
    assert(r.status === 201, `MKCOL ${r.status} ${r.text}`)
    r = await dav(origin, 'MKCOL', base + 'docs')
    assert(r.status === 405, `MKCOL again ${r.status}`)
    r = await dav(origin, 'MKCOL', base + 'no/such')
    assert(r.status === 409, `MKCOL no parent ${r.status}`)
  })
  await check(`${m}: PROPFIND Depth 0 of a file gives its length, type and date`, async () => {
    const r = await dav(origin, 'PROPFIND', base + 'hello.txt', { headers: { depth: '0' } })
    assert(r.status === 207, `status ${r.status}`)
    assert(r.text.includes('<D:getcontentlength>12</D:getcontentlength>'), r.text)
    assert(r.text.includes('<D:getlastmodified>'), 'no getlastmodified')
    assert(r.text.includes('<D:getcontenttype>text/plain</D:getcontenttype>'), 'no getcontenttype')
  })
  await check(`${m}: PROPFIND Depth 1 lists each member once`, async () => {
    const r = await dav(origin, 'PROPFIND', base, { headers: { depth: '1' } })
    assert(r.status === 207, `status ${r.status}`)
    for (const href of [`${base}hello.txt`, `${base}docs/`, `${base}bin.dat`]) {
      const n = r.text.split(`<D:href>${href}</D:href>`).length - 1
      assert(n === 1, `${href} listed ${n} times`)
    }
  })
  await check(`${m}: PROPFIND Depth infinity is refused (403, propfind-finite-depth)`, async () => {
    const r = await dav(origin, 'PROPFIND', base, { headers: { depth: 'infinity' } })
    assert(r.status === 403 && r.text.includes('propfind-finite-depth'), `status ${r.status}`)
  })
  await check(`${m}: PROPPATCH sets a dead property; PROPFIND reads it`, async () => {
    let r = await dav(origin, 'PROPPATCH', base + 'hello.txt', { headers: { 'content-type': 'application/xml' }, body: PROPSET })
    assert(r.status === 207 && r.text.includes('200 OK'), `PROPPATCH ${r.status} ${r.text}`)
    r = await dav(origin, 'PROPFIND', base + 'hello.txt', { headers: { depth: '0' }, body: PROPGET })
    assert(r.status === 207 && r.text.includes('>green</Z:colour>'), r.text)
  })
  await check(`${m}: COPY (201), COPY over it (204), Overwrite F (412)`, async () => {
    let r = await dav(origin, 'COPY', base + 'hello.txt', { headers: { destination: origin + base + 'docs/copy.txt' } })
    assert(r.status === 201, `COPY ${r.status} ${r.text}`)
    r = await dav(origin, 'COPY', base + 'hello.txt', { headers: { destination: origin + base + 'docs/copy.txt' } })
    assert(r.status === 204, `COPY over ${r.status}`)
    r = await dav(origin, 'COPY', base + 'hello.txt', { headers: { destination: origin + base + 'docs/copy.txt', overwrite: 'F' } })
    assert(r.status === 412, `Overwrite F ${r.status}`)
    r = await dav(origin, 'GET', base + 'docs/copy.txt')
    assert(r.text === 'hello, world', `copy reads ${r.text}`)
  })
  await check(`${m}: MOVE renames a collection with its members and dead properties`, async () => {
    let r = await dav(origin, 'MOVE', base + 'docs/', { headers: { destination: origin + base + 'papers/' } })
    assert(r.status === 201, `MOVE ${r.status} ${r.text}`)
    r = await dav(origin, 'GET', base + 'papers/copy.txt')
    assert(r.status === 200 && r.text === 'hello, world', `moved member ${r.status}`)
    r = await dav(origin, 'GET', base + 'docs/copy.txt')
    assert(r.status === 404, `old member ${r.status}`)
    r = await dav(origin, 'MOVE', base + 'hello.txt', { headers: { destination: origin + base + 'greeting.txt' } })
    assert(r.status === 201, `MOVE file ${r.status}`)
    r = await dav(origin, 'PROPFIND', base + 'greeting.txt', { headers: { depth: '0' }, body: PROPGET })
    assert(r.text.includes('>green</Z:colour>'), 'the dead property did not move')
  })
  await check(`${m}: LOCK (Lock-Token); PUT without the token 423, with it 204; UNLOCK 204`, async () => {
    let r = await dav(origin, 'LOCK', base + 'greeting.txt', { headers: { timeout: 'Second-600', 'content-type': 'application/xml' }, body: LOCK })
    assert(r.status === 200, `LOCK ${r.status} ${r.text}`)
    const token = (r.headers.get('lock-token') || '').replace(/^<|>$/g, '')
    assert(token.startsWith('urn:uuid:'), `token ${token}`)
    assert(r.text.includes('<D:lockdiscovery>'), 'no lockdiscovery')
    r = await dav(origin, 'PUT', base + 'greeting.txt', { body: 'x' })
    assert(r.status === 423 && r.text.includes('lock-token-submitted'), `PUT without token ${r.status}`)
    r = await dav(origin, 'PUT', base + 'greeting.txt', { headers: { if: `(<${token}>)` }, body: 'locked write' })
    assert(r.status === 204, `PUT with token ${r.status}`)
    r = await dav(origin, 'UNLOCK', base + 'greeting.txt', { headers: { 'lock-token': `<${token}>` } })
    assert(r.status === 204, `UNLOCK ${r.status}`)
    r = await dav(origin, 'PUT', base + 'greeting.txt', { body: 'free' })
    assert(r.status === 204, `PUT after UNLOCK ${r.status}`)
  })
  await check(`${m}: DELETE of a collection (204) removes its members; DELETE again 404`, async () => {
    let r = await dav(origin, 'DELETE', base + 'papers/')
    assert(r.status === 204, `DELETE ${r.status} ${r.text}`)
    r = await dav(origin, 'GET', base + 'papers/copy.txt')
    assert(r.status === 404, `member ${r.status}`)
    r = await dav(origin, 'DELETE', base + 'papers/')
    assert(r.status === 404, `again ${r.status}`)
  })
}

async function main () {
  const dir = mkdtempSync(join(process.env.WEBDAV_TEST_TMP || tmpdir(), 'factoidal-webdav-'))
  const conf = join(dir, 'conf')
  mkdirSync(conf)
  mkdirSync(join(conf, 'store'))
  const owner = keyPair('ES256')
  const did = didKeyOf(owner)
  writeFileSync(join(conf, 'remote.jwk'), JSON.stringify(owner.privateKey.export({ format: 'jwk' })), { mode: 0o600 })
  writeFileSync(join(conf, 'local.md'), '# Local storage\n- kind: local\n- path: ./store\n\nA storage directory of lws-serve.\n')
  writeFileSync(join(conf, 'README.md'), '# Not a mount\n- colour: red\n')
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
    writeFileSync(join(conf, 'remote.md'), `# Remote storage\n- kind: lws\n- url: ${lws.origin}/\n- auth: did-key\n- key-file: remote.jwk\n- writable: true\n`)
    writeFileSync(join(conf, 'other.md'), `# Someone else\n- kind: lws\n- url: ${lws.origin}/\n- auth: did-key\n- key-file: other.jwk\n`)
    try {
      web = await start(['webdav-serve', conf, '--port', '0'])
    } catch (error) {
      if (/exited 3|not yet wired|does not carry webdav/.test(String(error.message))) {
        skipped += 1
        console.log(`  skip  every check - the wasm module carries no WebDAV ops: ${error.message}`)
        return
      }
      throw error
    }
    const origin = web.origin
    await check('root: PROPFIND Depth 1 lists the three mounts and not README.md', async () => {
      const r = await dav(origin, 'PROPFIND', '/', { headers: { depth: '1' } })
      assert(r.status === 207, `status ${r.status}`)
      for (const m of ['local', 'remote', 'other']) assert(r.text.includes(`<D:href>/${m}/</D:href>`), `no ${m}`)
      assert(!r.text.includes('README'), 'README.md is a mount')
      assert(r.text.includes('<D:displayname>Local storage</D:displayname>'), 'no display name')
    })
    await check('start: the key file the engine made exists, mode 0600, with a P-256 private key', async () => {
      const p = join(conf, 'other.jwk')
      assert(existsSync(p), 'no other.jwk')
      assert((statSync(p).mode & 0o777) === 0o600, `mode ${(statSync(p).mode & 0o777).toString(8)}`)
      const jwk = JSON.parse(readFileSync(p, 'utf8'))
      assert(jwk.kty === 'EC' && jwk.crv === 'P-256' && typeof jwk.d === 'string', 'not a P-256 private JWK')
    })
    await check('start: the remote mount acts as the did:key of its key file', async () => {
      assert(web.errText().includes(did), `the start lines do not name ${did}: ${web.errText()}`)
    })
    await methods(origin, 'local')
    await methods(origin, 'remote')
    await check('remote: the storage refuses an agent that is not its owner (403), read-only mount refuses PUT (403)', async () => {
      let r = await dav(origin, 'PROPFIND', '/other/', { headers: { depth: '1' } })
      assert(r.status === 403, `PROPFIND ${r.status} ${r.text}`)
      r = await dav(origin, 'PUT', '/other/x.txt', { body: 'x' })
      assert(r.status === 403, `PUT ${r.status}`)
    })
    await check('remote: a file written through WebDAV is in the LWS storage (read by the LWS client as the owner)', async () => {
      const r = await fetch(`${lws.origin}/greeting.txt`)
      assert(r.status === 401, `unauthenticated read ${r.status}`)
      const { createLwsClient } = await import('../../npm/factoidal/lws/client.mjs')
      const client = await createLwsClient({
        selfIssued: { subject: did, keyId: `${did}#${did.slice(8)}`, jwk: owner.privateKey.export({ format: 'jwk' }) }
      })
      const got = await client.read(`${lws.origin}/greeting.txt`)
      assert(got.status === 200 && got.body === 'free', `LWS client read ${got.status} ${got.body}`)
    })
    await check('cross-mount MOVE is 502 (RFC 4918 §9.9.4)', async () => {
      const r = await dav(origin, 'MOVE', '/local/bin.dat', { headers: { destination: origin + '/remote/bin.dat' } })
      assert(r.status === 502, `status ${r.status}`)
    })
    await check('local: the storage directory is written (lws-state.json) and read again after a restart', async () => {
      assert(existsSync(join(conf, 'store', 'lws-state.json')), 'no lws-state.json')
      const set = await dav(origin, 'PROPPATCH', '/local/greeting.txt', { body: PROPSET })
      assert(set.status === 207, `PROPPATCH before the restart ${set.status}`)
      await stop(web)
      web = await start(['webdav-serve', conf, '--port', '0'])
      const r = await dav(web.origin, 'GET', '/local/greeting.txt')
      assert(r.status === 200 && r.text === 'free', `after restart ${r.status} ${r.text}`)
    })
    // https://github.com/danbri/factoidal/issues/1078: dead properties and
    // locks are kept in CONFIGDIR/.webdav-state.json.
    await check('local: a dead property survives a restart', async () => {
      const r = await dav(web.origin, 'PROPFIND', '/local/greeting.txt', { headers: { depth: '0' }, body: PROPGET })
      assert(r.status === 207 && r.text.includes('>green</Z:colour>'), `the dead property set before the restart is gone: ${r.status} ${r.text}`)
    })
    await check('local: a lock survives a restart; its token still unlocks; the state file has mode 0600', async () => {
      const lockBody = '<?xml version="1.0"?><D:lockinfo xmlns:D="DAV:"><D:lockscope><D:exclusive/></D:lockscope>' +
        '<D:locktype><D:write/></D:locktype><D:owner>tester</D:owner></D:lockinfo>'
      const l = await dav(web.origin, 'LOCK', '/local/greeting.txt', { headers: { timeout: 'Second-600' }, body: lockBody })
      assert(l.status === 200, `LOCK ${l.status} ${l.text}`)
      const token = l.headers.get('lock-token')
      assert(token && token.startsWith('<urn:uuid:'), `Lock-Token ${token}`)
      const file = join(conf, '.webdav-state.json')
      assert(existsSync(file), 'no .webdav-state.json')
      assert((statSync(file).mode & 0o777) === 0o600, `mode ${(statSync(file).mode & 0o777).toString(8)}`)
      await stop(web)
      web = await start(['webdav-serve', conf, '--port', '0'])
      let r = await dav(web.origin, 'PUT', '/local/greeting.txt', { body: 'changed' })
      assert(r.status === 423, `PUT without the token after the restart ${r.status}`)
      r = await dav(web.origin, 'PROPFIND', '/local/greeting.txt', { headers: { depth: '0' } , body: '<D:propfind xmlns:D="DAV:"><D:prop><D:lockdiscovery/></D:prop></D:propfind>' })
      assert(r.status === 207 && r.text.includes(token.slice(1, -1)), `lockdiscovery after the restart ${r.status} ${r.text}`)
      r = await dav(web.origin, 'UNLOCK', '/local/greeting.txt', { headers: { 'lock-token': token } })
      assert(r.status === 204, `UNLOCK after the restart ${r.status} ${r.text}`)
      r = await dav(web.origin, 'GET', '/local/greeting.txt')
      assert(r.status === 200 && r.text === 'free', `GET ${r.status} ${r.text}`)
    })
    await check('start: a malformed state file stops the start with its name (exit 1)', async () => {
      const bad = join(dir, 'badstate')
      mkdirSync(bad)
      mkdirSync(join(bad, 'store'))
      writeFileSync(join(bad, 's.md'), '- kind: local\n- path: ./store\n')
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
      writeFileSync(join(bad, 'x.md'), '# X\n- kind: local\n- colour: red\n')
      const r = await run(['webdav-serve', bad, '--port', '0'])
      assert(r.code === 1, `exit ${r.code}`)
      assert(r.errText.includes('x.md:3: unknown key "colour"'), r.errText)
    })
    await check('start: a local mount whose directory does not exist stops the start', async () => {
      const bad = join(dir, 'bad2')
      mkdirSync(bad)
      writeFileSync(join(bad, 'y.md'), '- kind: local\n- path: ./absent\n')
      const r = await run(['webdav-serve', bad, '--port', '0'])
      assert(r.code === 1 && r.errText.includes('does not exist'), `exit ${r.code} ${r.errText}`)
    })
    await login(dir)
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
