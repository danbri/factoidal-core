// End-to-end test of `factoidal webdav-serve --xmpp`: WebDAV reached through
// HTTP over XMPP (XEP-0332), https://github.com/danbri/factoidal/issues/1107.
//
//   node tests/webdav/xmpp.mjs
//
// Three processes and one test client, all on 127.0.0.1:
//   factoidal xmpp-serve        accounts alice, bob, carol (direct TLS, a
//                               self-signed certificate for example.org)
//   factoidal webdav-serve --xmpp bob@example.org --xmpp-allow alice@example.org
//                               connects OUT as bob (SCRAM-SHA-256), binds
//                               resource "dav", opens no port
//   the test client (below)     logs in as alice, then as carol, and sends
//                               XEP-0332 `req` stanzas to bob@example.org/dav
// The test client is test code: it writes the stanza text by hand (SASL
// PLAIN over TLS, then `req` iqs) and reads the
// `resp` iqs with regular expressions. Every decision on the server side is
// formal/lean4/L4Factoidal/XMPP/ (ClientStream, HttpOverXmpp) and
// formal/lean4/L4Factoidal/WebDAV/.
//
// Emergency mode (https://github.com/danbri/factoidal/issues/1147): the
// mount is an lws mount of an `lws-serve --authz` storage started here and
// filled through the LWS client as its owner; webdav-serve is read only and
// every request over XMPP acts as the --guest user.
//
// Score line: "N pass, M fail, X xfail (out of T)".

import { spawn, execFileSync } from 'node:child_process'
import { mkdtempSync, mkdirSync, rmSync, writeFileSync, readFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { TestClient, request as xreq } from './xmpp-client.mjs'
import { keyPair, didKeyOf } from '../authz/fixtures.mjs'

const CLI = fileURLToPath(new URL('../../npm/factoidal/bin/factoidal.mjs', import.meta.url))
const DOMAIN = 'example.org'
const TARGET = `bob@${DOMAIN}/dav`

let passed = 0
let failed = 0
let xfailed = 0
const failures = []

/** An expected failure: a stated shortfall with its open issue. When it
 *  passes, the run turns red so the issue is closed and the check made
 *  plain. */
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

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

const children = []

/** Start a CLI command; resolve once a stdout line matches `pattern`. */
function start (args, pattern, cwd) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [CLI, ...args], { cwd, stdio: ['ignore', 'pipe', 'pipe'] })
    children.push(child)
    let out = ''
    let errText = ''
    const timer = setTimeout(() => { child.kill(); reject(new Error(`no start: ${out} ${errText}`)) }, 120000)
    child.stdout.on('data', (b) => {
      out += b
      const m = pattern.exec(out)
      if (m) { clearTimeout(timer); resolve({ child, match: m, errText: () => errText }) }
    })
    child.stderr.on('data', (b) => { errText += b })
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`exited ${code}: ${errText.trim()}`)) })
  })
}

/** Run a CLI command to its end. */
function run (args, cwd) {
  return new Promise((resolve) => {
    const child = spawn(process.execPath, [CLI, ...args], { cwd, stdio: ['ignore', 'pipe', 'pipe'] })
    let out = ''
    let errText = ''
    const timer = setTimeout(() => child.kill(), 120000)
    child.stdout.on('data', (b) => { out += b })
    child.stderr.on('data', (b) => { errText += b })
    child.on('close', (code) => { clearTimeout(timer); resolve({ code, out, errText }) })
  })
}

/** Run a CLI command with `input` on standard input. */
function runWithInput (args, input, cwd) {
  return new Promise((resolve) => {
    const child = spawn(process.execPath, [CLI, ...args], { cwd, stdio: ['pipe', 'pipe', 'pipe'] })
    let out = ''
    let errText = ''
    const timer = setTimeout(() => child.kill(), 120000)
    child.stdout.on('data', (b) => { out += b })
    child.stderr.on('data', (b) => { errText += b })
    child.on('close', (code) => { clearTimeout(timer); resolve({ code, out, errText }) })
    child.stdin.end(input)
  })
}

/** SASL PLAIN attempts on one stream: the outcome of each ('success' or the
 *  failure condition). Test code: the stanza text is written by hand. */
async function saslAttempts (c, user, passwords) {
  c.header()
  await c.wait(/<\/stream:features>/)
  const got = []
  for (const pw of passwords) {
    c.send(`<auth xmlns='urn:ietf:params:xml:ns:xmpp-sasl' mechanism='PLAIN'>${Buffer.from(`\u0000${user}\u0000${pw}`).toString('base64')}</auth>`)
    const m = await c.wait(/<success[^>]*\/>|<success[\s\S]*?<\/success>|<failure[\s\S]*?<\/failure>/)
    if (m[0].startsWith('<success')) { got.push('success'); break }
    got.push((/<failure[^>]*><([a-z-]+)/.exec(m[0]) || [null, '?'])[1])
  }
  return got
}

async function main () {
  const dir = mkdtempSync(join(tmpdir(), 'webdav-xmpp-'))
  try {
    mkdirSync(join(dir, 'dav'), { recursive: true })
    mkdirSync(join(dir, 'xmpp'))
    mkdirSync(join(dir, 'xmpp2'))
    mkdirSync(join(dir, 'xmpp3'))
    mkdirSync(join(dir, 'xmpp4'))
    // The storage: lws-serve --authz, owned by the did:key of owner.jwk,
    // filled through the LWS client (webdav-serve is read only, issue 1147).
    const owner = keyPair('ES256')
    const did = didKeyOf(owner)
    const ownerJwk = owner.privateKey.export({ format: 'jwk' })
    writeFileSync(join(dir, 'dav', 'owner.jwk'), JSON.stringify(ownerJwk), { mode: 0o600 })
    const lws = await start(['lws-serve', 'lws', '--port', '0', '--authz', 'lws-as', '--owner', did, '--quiet'],
      /^(http:\/\/127\.0\.0\.1:\d+)$/m, dir)
    const lwsOrigin = lws.match[1]
    const { createLwsClient } = await import('../../npm/factoidal/lws/client.mjs')
    const ownerClient = await createLwsClient({ selfIssued: { subject: did, keyId: `${did}#${did.slice(8)}`, jwk: ownerJwk } })
    await ownerClient.update(`${lwsOrigin}/hello.txt`, { body: 'hello over xmpp', mediaType: 'text/plain', precondition: 'none' })
    writeFileSync(join(dir, 'dav', 'notes.md'),
      `# Notes\n- kind: lws\n- url: ${lwsOrigin}/\n- auth: did-key\n- key-file: owner.jwk\n- users: guest\n`)
    writeFileSync(join(dir, 'accounts'), 'alice:alice-pw\nbob:bob-pw\ncarol:carol-pw\ndave:dave-pw\n')
    writeFileSync(join(dir, 'bob.password'), 'bob-pw\n')
    writeFileSync(join(dir, 'wrong.password'), 'not-bob-pw\n')

    // A certificate for example.org, so both sides use direct TLS (XEP-0368).
    execFileSync('openssl', ['req', '-x509', '-newkey', 'ec', '-pkeyopt', 'ec_paramgen_curve:P-256', '-nodes',
      '-keyout', join(dir, 'key.pem'), '-out', join(dir, 'cert.pem'), '-days', '1', '-subj', `/CN=${DOMAIN}`,
      '-addext', `subjectAltName=DNS:${DOMAIN}`], { stdio: 'ignore' })
    const ca = readFileSync(join(dir, 'cert.pem'))
    const xs = await start(['xmpp-serve', 'xmpp', '--port', '0', '--domain', DOMAIN, '--accounts', 'accounts',
      '--cert', 'cert.pem', '--key', 'key.pem'], /^xmpps:\/\/127\.0\.0\.1:(\d+)$/m, dir)
    const xport = xs.match[1]
    const tlsArgs = ['--xmpp-host', '127.0.0.1', '--xmpp-port', xport, '--xmpp-tls', '--xmpp-ca', 'cert.pem']
    const OPT_IN = '--guest'
    const GUEST = 'guest'

    // Constraints of https://github.com/danbri/factoidal/issues/1120 and
    // https://github.com/danbri/factoidal/issues/1125, decided in Lean
    // (`xcStartRefusal`, `ClientStream.secureTransport`).
    await check('start refused: plain TCP to a host that is not loopback (exit 1, no connection)', async () => {
      const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}`, '--xmpp-host', '192.0.2.1', '--xmpp-port', '5222', OPT_IN, GUEST], dir)
      assert(r.code === 1 && r.errText.includes('plain TCP to 192.0.2.1 is refused'), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: an allow-list entry with a resource (exit 1)', async () => {
      const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}/phone`, ...tlsArgs, OPT_IN, GUEST], dir)
      assert(r.code === 1 && r.errText.includes('only bare JIDs'), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: no --xmpp-allow (exit 2, usage)', async () => {
      const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password', ...tlsArgs, OPT_IN, GUEST], dir)
      assert(r.code !== 0 && r.errText.includes('--xmpp-allow'), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: a local mount (exit 1, issue 1147)', async () => {
      mkdirSync(join(dir, 'davlocal', 'store'), { recursive: true })
      writeFileSync(join(dir, 'davlocal', 'l.md'), '# L\n- kind: local\n- path: ./store\n- users: guest\n')
      const r = await run(['webdav-serve', 'davlocal', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}`, ...tlsArgs, OPT_IN, GUEST], dir)
      assert(r.code === 1 && r.errText.includes('l.md:2: a `kind: local` mount opens its storage with no authorization'), `exit ${r.code}: ${r.errText}`)
    })

    await check('webdav-serve --xmpp: a wrong password stops the start with the SASL condition (exit 1)', async () => {
      const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'wrong.password',
        '--xmpp-allow', `alice@${DOMAIN}`, ...tlsArgs, OPT_IN, GUEST], dir)
      assert(r.code === 1, `exit ${r.code}: ${r.errText}`)
      assert(r.errText.includes('SASL failure: not-authorized'), r.errText)
    })

    let web = null
    await check('webdav-serve --xmpp: connects out as bob (direct TLS, SCRAM-SHA-256) and binds bob@example.org/dav', async () => {
      web = await start(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}`, ...tlsArgs, OPT_IN, GUEST],
      /^xmpp:(\S+)$/m, dir)
      assert(web.match[1] === TARGET, web.match[1])
      for (let i = 0; i < 50 && !web.errText().includes('read only'); i++) await new Promise((resolve) => setTimeout(resolve, 100))
      assert(web.errText().includes('read only (emergency mode, issue 1147)'), web.errText())
    })
    if (web === null) return

    const alice = new TestClient(Number(xport), DOMAIN, ca)
    await alice.login('alice', 'alice-pw')

    await check('alice: PROPFIND / gives 207 with the multistatus as xml', async () => {
      const r = await request(alice, 'PROPFIND', '/', { headers: [['Depth', '1']] })
      assert(r.status === 207, `status ${r.status}: ${r.iq.slice(0, 300)}`)
      assert(/<xml>[\s\S]*multistatus[\s\S]*\/notes\/[\s\S]*<\/xml>/.test(r.iq), r.iq.slice(0, 500))
    })

    await check('alice: PUT /notes/hello.txt gives 403 (read only, issue 1147)', async () => {
      const r = await request(alice, 'PUT', '/notes/hello.txt', {
        headers: [['Content-Type', 'text/plain']], data: '<data><text>overwritten</text></data>'
      })
      assert(r.status === 403, `status ${r.status}: ${r.iq.slice(0, 300)}`)
    })

    await check('alice: GET /notes/hello.txt gives 200 and the text', async () => {
      const r = await request(alice, 'GET', '/notes/hello.txt')
      assert(r.status === 200, `status ${r.status}`)
      assert(r.iq.includes('<text>hello over xmpp</text>'), r.iq.slice(0, 400))
    })

    await check('alice: MKCOL is 403; PROPFIND Depth 1 lists the storage', async () => {
      const m = await request(alice, 'MKCOL', '/notes/docs/')
      assert(m.status === 403, `MKCOL status ${m.status}`)
      const p = await request(alice, 'PROPFIND', '/notes/', { headers: [['Depth', '1']] })
      assert(p.status === 207 && !p.iq.includes('/notes/docs/') && p.iq.includes('/notes/hello.txt'), p.iq.slice(0, 600))
    })

    // 100,000 bytes: above the 65,536-byte inline limit, so the response
    // comes back as chunkedBase64 (two chunks of at most 65,536 bytes).
    const big = Buffer.alloc(100000)
    for (let i = 0; i < big.length; i += 1) big[i] = (i * 7) % 251
    await check('alice: a 100,000-byte binary file (written over LWS), GET in chunkedBase64 chunks', async () => {
      const put = await ownerClient.update(`${lwsOrigin}/big.bin`, { body: new Uint8Array(big), mediaType: 'application/octet-stream', precondition: 'none' })
      assert(put.status === 201 || put.status === 204, `LWS update status ${put.status}`)
      const r = await request(alice, 'GET', '/notes/big.bin', { chunks: 2 })
      assert(r.status === 200, `GET status ${r.status}`)
      assert(/<chunkedBase64 streamId="[^"]+"/.test(r.iq), r.iq.slice(0, 400))
      const parts = r.chunks.map((t) => {
        const nr = Number(/nr="(\d+)"/.exec(t)[1])
        const b64 = /<chunk[^>]*>([^<]*)<\/chunk>/.exec(t)[1]
        return [nr, Buffer.from(b64, 'base64')]
      }).sort((a, b) => a[0] - b[0])
      assert(r.chunks.some((t) => /last="true"/.test(t)), 'no chunk marked last')
      assert(Buffer.concat(parts.map((p) => p[1])).equals(big), 'the chunks do not reassemble to the stored bytes')
    })

    await check('alice: CONNECT is refused with not-allowed', async () => {
      const r = await request(alice, 'CONNECT', '/notes/')
      assert(/type="error"/.test(r.iq) && r.iq.includes('not-allowed'), r.iq.slice(0, 300))
    })

    await check('alice: an iq that is not HTTP gets service-unavailable', async () => {
      alice.send(`<iq type='get' id='v1' to='${TARGET}'><query xmlns='jabber:iq:version'/></iq>`)
      const m = await alice.wait(/<iq[^>]*id="v1"[\s\S]*?<\/iq>/)
      assert(m[0].includes('service-unavailable'), m[0])
    })
    alice.close()

    await check('carol (not in --xmpp-allow): PUT gets forbidden and the storage does not change', async () => {
      const carol = new TestClient(Number(xport), DOMAIN, ca)
      await carol.login('carol', 'carol-pw')
      try {
        const r = await request(carol, 'PUT', '/notes/hello.txt', {
          headers: [['Content-Type', 'text/plain']], data: '<data><text>overwritten</text></data>'
        })
        assert(/type="error"/.test(r.iq) && r.iq.includes('forbidden'), r.iq.slice(0, 300))
      } finally {
        carol.close()
      }
      const again = new TestClient(Number(xport), DOMAIN, ca)
      await again.login('alice', 'alice-pw')
      try {
        const g = await request(again, 'GET', '/notes/hello.txt')
        assert(g.iq.includes('<text>hello over xmpp</text>'), g.iq.slice(0, 300))
      } finally {
        again.close()
      }
    })

    // RFC 6120 section 10.5.4: an IQ to a full JID of a local account goes to
    // that resource, also when the sender is another resource of the same
    // account (https://github.com/danbri/factoidal/issues/1139, fixed
    // 2026-11-03 by `Out.routeFull`; Server.lean `handleIq_no_route`).
    await check('xmpp-serve routes an IQ from alice/u to alice/t (two resources of one account)',
      async () => {
        const t = new TestClient(Number(xport), DOMAIN, ca)
        const u = new TestClient(Number(xport), DOMAIN, ca)
        try {
          await t.login('alice', 'alice-pw', 't')
          await u.login('alice', 'alice-pw', 'u')
          u.send(`<iq type='get' id='same1' to='alice@${DOMAIN}/t'><query xmlns='jabber:iq:version'/></iq>`)
          const m = await t.wait(/<iq[^>]*id="same1"[\s\S]*?(?:\/>|<\/iq>)/, 5000)
          assert(/from="alice@example\.org\/u"/.test(m[0]), m[0])
        } finally {
          t.close()
          u.close()
        }
      })

    // https://github.com/danbri/factoidal/issues/1125 and
    // https://github.com/danbri/factoidal/issues/1128: --users over XMPP.
    // A second webdav-serve (resource dav2) with a users file, no --guest, and
    // three allowed JIDs. Every decision is Lean: the allow list
    // (HttpOverXmpp.plan), then Login.admit with the sender's bare JID as the
    // requester (Wasm/Ops/WebDAV.lean, davRequesterOf).
    mkdirSync(join(dir, 'davlogin'))
    writeFileSync(join(dir, 'davlogin', 'owner.jwk'), JSON.stringify(ownerJwk), { mode: 0o600 })
    writeFileSync(join(dir, 'davlogin', 'notes.md'),
      `# Notes\n- kind: lws\n- url: ${lwsOrigin}/\n- auth: did-key\n- key-file: owner.jwk\n- users: anna, ben\n`)
    const users = join(dir, 'users.txt')
    for (const [name, pw] of [['anna', 'anna-dav-pw'], ['ben', 'ben-dav-pw']]) {
      const r = await runWithInput(['webdav-user', users, name, '--iterations', '100000'], `${pw}\n`, dir)
      assert(r.code === 0, `webdav-user ${name}: exit ${r.code}: ${r.errText}`)
    }
    const TARGET2 = `bob@${DOMAIN}/dav2`
    const basic = (u, p) => ['Authorization', 'Basic ' + Buffer.from(`${u}:${p}`).toString('base64')]
    const request2 = (c, ...rest) => xreq(c, TARGET2, ...rest)

    await check('start refused: --users over XMPP on plain TCP to a host that is not loopback (exit 1)', async () => {
      const r = await run(['webdav-serve', 'davlogin', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}`, '--xmpp-host', '192.0.2.1', '--xmpp-port', '5222', '--users', 'users.txt'], dir)
      assert(r.code === 1 && /plain TCP to 192\.0\.2\.1 is refused|over XMPP sends each password/.test(r.errText), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: --cert with --xmpp (no port is open; usage)', async () => {
      const r = await run(['webdav-serve', 'davlogin', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}`, ...tlsArgs, '--users', 'users.txt', '--cert', 'cert.pem', '--key', 'key.pem'], dir)
      assert(r.code !== 0 && r.errText.includes('--cert and --key do not apply with --xmpp'), `exit ${r.code}: ${r.errText}`)
    })

    let web2 = null
    await check('webdav-serve --xmpp --users: starts, and says the login is limited per bare JID', async () => {
      web2 = await start(['webdav-serve', 'davlogin', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN},carol@${DOMAIN},dave@${DOMAIN}`, '--xmpp-resource', 'dav2', ...tlsArgs,
        '--users', 'users.txt'], /^xmpp:(\S+)$/m, dir)
      assert(web2.match[1] === TARGET2, web2.match[1])
      for (let i = 0; i < 50 && !web2.errText().includes('per bare JID'); i++) await new Promise((resolve) => setTimeout(resolve, 100))
      assert(web2.errText().includes('login from users.txt (failed logins limited per user name and per bare JID)'), web2.errText())
    })
    if (web2 !== null) {
      const a = new TestClient(Number(xport), DOMAIN, ca)
      const cl = new TestClient(Number(xport), DOMAIN, ca)
      const d = new TestClient(Number(xport), DOMAIN, ca)
      try {
        await a.login('alice', 'alice-pw', 'l1')
        await cl.login('carol', 'carol-pw', 'l2')
        await d.login('dave', 'dave-pw', 'l3')

        await check('--users over XMPP: an allowed JID with no credentials gets 401 (no --guest)', async () => {
          const r = await request2(a, 'GET', '/notes/hello.txt')
          assert(r.status === 401 && /www-authenticate/i.test(r.iq), `status ${r.status}: ${r.iq.slice(0, 300)}`)
        })
        await check('--users over XMPP: Basic credentials in the request headers log in (GET 200)', async () => {
          const r = await request2(a, 'GET', '/notes/hello.txt', { headers: [basic('anna', 'anna-dav-pw')] })
          assert(r.status === 200 && r.iq.includes('<text>hello over xmpp</text>'), `status ${r.status}: ${r.iq.slice(0, 300)}`)
        })
        await check('--users over XMPP: a wrong password gets 401', async () => {
          const r = await request2(a, 'GET', '/notes/hello.txt', { headers: [basic('anna', 'wrong')] })
          assert(r.status === 401, `status ${r.status}`)
        })
        await check('JID A: 6 wrong passwords (for another name); then JID B logs in with the right password (not blocked)', async () => {
          const got = []
          for (let i = 0; i < 6; i += 1) got.push((await request2(cl, 'GET', '/notes/hello.txt', { headers: [basic('mallory', `x${i}`)] })).status)
          assert(got.slice(0, 5).every((x) => x === 401) && got[5] === 429, `statuses ${got.join(',')}`)
          const r = await request2(a, 'GET', '/notes/hello.txt', { headers: [basic('ben', 'ben-dav-pw')] })
          assert(r.status === 200, `JID B: status ${r.status}`)
        })
        await check('JID A is blocked for every name (the jid: key), also with the right password: 429 with Retry-After', async () => {
          const r = await request2(cl, 'GET', '/notes/hello.txt', { headers: [basic('ben', 'ben-dav-pw')] })
          assert(r.status === 429 && /retry-after/i.test(r.iq), `status ${r.status}: ${r.iq.slice(0, 300)}`)
        })
        await check('one JID that tries many names is refused at the sixth (one failure per name)', async () => {
          const got = []
          for (let i = 0; i < 6; i += 1) got.push((await request2(d, 'GET', '/notes/hello.txt', { headers: [basic(`u${i}`, 'x')] })).status)
          assert(got.slice(0, 5).every((x) => x === 401) && got[5] === 429, `statuses ${got.join(',')}`)
        })
        await check("JID A's 16 open chunked requests: 4 wait, 12 get resource-constraint; JID B's chunked request is served", async () => {
          let refused = 0
          for (let i = 0; i < 16; i += 1) {
            a.send(`<iq type='set' id='ck${i}' to='${TARGET2}'><req xmlns='urn:xmpp:http' method='PROPFIND' resource='/notes/' version='1.1'>` +
              `<headers xmlns='http://jabber.org/protocol/shim'><header name='Depth'>0</header></headers>` +
              `<data><chunkedBase64 streamId='a${i}'/></data></req></iq>`)
          }
          for (let i = 4; i < 16; i += 1) {
            const m = await a.wait(new RegExp(`<iq[^>]*id="ck${i}"[\\s\\S]*?</iq>`))
            if (m[0].includes('resource-constraint')) refused += 1
          }
          assert(refused === 12, `refused ${refused}`)
          const [hn, hv] = basic('ben', 'ben-dav-pw')
          d.send(`<iq type='set' id='bk1' to='${TARGET2}'><req xmlns='urn:xmpp:http' method='PROPFIND' resource='/notes/' version='1.1'>` +
            `<headers xmlns='http://jabber.org/protocol/shim'><header name='Depth'>0</header><header name='${hn}'>${hv}</header></headers>` +
            `<data><chunkedBase64 streamId='b1'/></data></req></iq>`)
          d.send(`<message to='${TARGET2}'><chunk xmlns='urn:xmpp:http' streamId='b1' nr='0' last='true'></chunk></message>`)
          const m = await d.wait(/<iq[^>]*id="bk1"[\s\S]*?<\/iq>/)
          assert(!m[0].includes('resource-constraint') && /statusCode="(207|429)"/.test(m[0]), m[0].slice(0, 300))
        })
      } finally {
        a.close()
        cl.close()
        d.close()
      }
    }

    await check('webdav-serve --help: the login limit over XMPP is keyed per bare JID', async () => {
      const r = await run(['webdav-serve', '--help'], dir)
      assert(/login limit[^\n]*bare JID/i.test(r.out + r.errText), 'no login limit keyed by JID in --help')
    })

    // xmpp-serve: the failed SASL login limit (issue 1128), on its own server so
    // that its address counter (127.0.0.1) does not block the logins above.
    const xs2 = await start(['xmpp-serve', 'xmpp2', '--port', '0', '--domain', DOMAIN, '--accounts', 'accounts',
      '--cert', 'cert.pem', '--key', 'key.pem'], /^xmpps:\/\/127\.0\.0\.1:(\d+)$/m, dir)
    const port2 = Number(xs2.match[1])
    await check('xmpp-serve: 5 failed SASL logins on one stream are not-authorized; the 6th (right password) is temporary-auth-failure', async () => {
      const c = new TestClient(port2, DOMAIN, ca)
      try {
        const got = await saslAttempts(c, 'alice', ['w1', 'w2', 'w3', 'w4', 'w5', 'alice-pw'])
        assert(got.slice(0, 5).every((x) => x === 'not-authorized') && got[5] === 'temporary-auth-failure', got.join(','))
      } finally { c.close() }
    })
    await check('xmpp-serve: a new stream from the same address is refused too, for another account', async () => {
      const c = new TestClient(port2, DOMAIN, ca)
      try {
        const got = await saslAttempts(c, 'carol', ['carol-pw'])
        assert(got[0] === 'temporary-auth-failure', got.join(','))
      } finally { c.close() }
    })
    await check('xmpp-serve --dangerously-disable-ratelimits: a start warning; 8 failures, then the right password logs in', async () => {
      const xs3 = await start(['xmpp-serve', 'xmpp3', '--port', '0', '--domain', DOMAIN, '--accounts', 'accounts',
        '--cert', 'cert.pem', '--key', 'key.pem', '--dangerously-disable-ratelimits'], /^xmpps:\/\/127\.0\.0\.1:(\d+)$/m, dir)
      assert(xs3.errText().includes('WARNING: --dangerously-disable-ratelimits: failed SASL logins are NOT limited'), xs3.errText())
      const c = new TestClient(Number(xs3.match[1]), DOMAIN, ca)
      try {
        const got = await saslAttempts(c, 'alice', ['w1', 'w2', 'w3', 'w4', 'w5', 'w6', 'w7', 'w8', 'alice-pw'])
        assert(got.slice(0, 8).every((x) => x === 'not-authorized') && got[8] === 'success', got.join(','))
      } finally { c.close() }
    })

    // Row C4 of docs/designissues/2026-10-28-feature-combination-safety.md:
    // a server offers PLAIN (the password in clear text) only on TLS or on a
    // loopback listener. Not met yet; it stays under issue 1125.
    await xfail('xmpp-serve on a non-loopback address without --cert does not offer SASL PLAIN',
      'https://github.com/danbri/factoidal/issues/1125', async () => {
        const xs4 = await start(['xmpp-serve', 'xmpp4', '--port', '0', '--host', '0.0.0.0', '--domain', DOMAIN,
          '--accounts', 'accounts'], /^xmpps?:\/\/0\.0\.0\.0:(\d+)$/m, dir)
        const c = new TestClient(Number(xs4.match[1]), DOMAIN)
        try {
          c.header()
          const m = await c.wait(/<stream:features>[\s\S]*?<\/stream:features>/)
          assert(!m[0].includes('>PLAIN<'), 'PLAIN is offered on a plain-TCP listener bound to 0.0.0.0')
        } finally { c.close() }
      })
  } finally {
    for (const c of children) {
      if (c.exitCode === null) { c.kill('SIGTERM'); await new Promise((resolve) => c.on('close', resolve)) }
    }
    rmSync(dir, { recursive: true, force: true })
  }
}

const request = (c, ...rest) => xreq(c, TARGET, ...rest)

await main()
console.log(`webdav over xmpp: ${passed} pass, ${failed} fail, ${xfailed} xfail (out of ${passed + failed + xfailed})`)
for (const f of failures) console.log(`  ${f}`)
process.exit(failed === 0 && passed > 0 ? 0 : 1)
