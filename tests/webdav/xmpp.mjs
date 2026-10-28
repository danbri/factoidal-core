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
// Score line: "N pass, M fail, X xfail (out of T)".

import { spawn, execFileSync } from 'node:child_process'
import { mkdtempSync, mkdirSync, rmSync, writeFileSync, readFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { TestClient, request as xreq } from './xmpp-client.mjs'

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

async function main () {
  const dir = mkdtempSync(join(tmpdir(), 'webdav-xmpp-'))
  try {
    mkdirSync(join(dir, 'dav', 'notes'), { recursive: true })
    mkdirSync(join(dir, 'xmpp'))
    writeFileSync(join(dir, 'dav', 'notes.md'), '# Notes\n- kind: local\n- path: ./notes\n')
    writeFileSync(join(dir, 'accounts'), 'alice:alice-pw\nbob:bob-pw\ncarol:carol-pw\n')
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
    const OPT_IN = '--dangerously-allow-writable-without-login'

    // Constraints of https://github.com/danbri/factoidal/issues/1120 and
    // https://github.com/danbri/factoidal/issues/1125, decided in Lean
    // (`xcStartRefusal`, `ClientStream.secureTransport`).
    await check('start refused: plain TCP to a host that is not loopback (exit 1, no connection)', async () => {
      const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}`, '--xmpp-host', '192.0.2.1', '--xmpp-port', '5222', OPT_IN], dir)
      assert(r.code === 1 && r.errText.includes('plain TCP to 192.0.2.1 is refused'), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: an allow-list entry with a resource (exit 1)', async () => {
      const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}/phone`, ...tlsArgs, OPT_IN], dir)
      assert(r.code === 1 && r.errText.includes('only bare JIDs'), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: no --xmpp-allow (exit 2, usage)', async () => {
      const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password', ...tlsArgs, OPT_IN], dir)
      assert(r.code !== 0 && r.errText.includes('--xmpp-allow'), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: a writable local mount without the opt-in (exit 1)', async () => {
      const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}`, ...tlsArgs], dir)
      assert(r.code === 1 && r.errText.includes('--dangerously-allow-writable-without-login'), `exit ${r.code}: ${r.errText}`)
    })

    await check('webdav-serve --xmpp: a wrong password stops the start with the SASL condition (exit 1)', async () => {
      const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'wrong.password',
        '--xmpp-allow', `alice@${DOMAIN}`, ...tlsArgs, OPT_IN], dir)
      assert(r.code === 1, `exit ${r.code}: ${r.errText}`)
      assert(r.errText.includes('SASL failure: not-authorized'), r.errText)
    })

    let web = null
    await check('webdav-serve --xmpp: connects out as bob (direct TLS, SCRAM-SHA-256) and binds bob@example.org/dav', async () => {
      web = await start(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
        '--xmpp-allow', `alice@${DOMAIN}`, ...tlsArgs, OPT_IN],
      /^xmpp:(\S+)$/m, dir)
      assert(web.match[1] === TARGET, web.match[1])
      assert(web.errText().includes('WARNING: --dangerously-allow-writable-without-login'), web.errText())
    })
    if (web === null) return

    const alice = new TestClient(Number(xport), DOMAIN, ca)
    await alice.login('alice', 'alice-pw')

    await check('alice: PROPFIND / gives 207 with the multistatus as xml', async () => {
      const r = await request(alice, 'PROPFIND', '/', { headers: [['Depth', '1']] })
      assert(r.status === 207, `status ${r.status}: ${r.iq.slice(0, 300)}`)
      assert(/<xml>[\s\S]*multistatus[\s\S]*\/notes\/[\s\S]*<\/xml>/.test(r.iq), r.iq.slice(0, 500))
    })

    await check('alice: PUT /notes/hello.txt as text gives 201', async () => {
      const r = await request(alice, 'PUT', '/notes/hello.txt', {
        headers: [['Content-Type', 'text/plain']], data: '<data><text>hello over xmpp</text></data>'
      })
      assert(r.status === 201, `status ${r.status}: ${r.iq.slice(0, 300)}`)
    })

    await check('alice: GET /notes/hello.txt gives 200 and the text', async () => {
      const r = await request(alice, 'GET', '/notes/hello.txt')
      assert(r.status === 200, `status ${r.status}`)
      assert(r.iq.includes('<text>hello over xmpp</text>'), r.iq.slice(0, 400))
    })

    await check('alice: MKCOL then PROPFIND Depth 1 lists the new collection', async () => {
      const m = await request(alice, 'MKCOL', '/notes/docs/')
      assert(m.status === 201, `MKCOL status ${m.status}`)
      const p = await request(alice, 'PROPFIND', '/notes/', { headers: [['Depth', '1']] })
      assert(p.status === 207 && p.iq.includes('/notes/docs/') && p.iq.includes('/notes/hello.txt'), p.iq.slice(0, 600))
    })

    // 100,000 bytes: above the 65,536-byte inline limit, so the response
    // comes back as chunkedBase64 (two chunks of at most 65,536 bytes).
    const big = Buffer.alloc(100000)
    for (let i = 0; i < big.length; i += 1) big[i] = (i * 7) % 251
    await check('alice: a 100,000-byte binary PUT as base64, then GET in chunkedBase64 chunks', async () => {
      const put = await request(alice, 'PUT', '/notes/big.bin', {
        headers: [['Content-Type', 'application/octet-stream']], data: `<data><base64>${big.toString('base64')}</base64></data>`
      })
      assert(put.status === 201, `PUT status ${put.status}`)
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

    // Not met by step 1; each names its issue and turns the run red when it
    // starts to pass.
    await xfail('webdav-serve --xmpp --users: allowed JIDs must still log in (login gate on the XMPP path)',
      'https://github.com/danbri/factoidal/issues/1125', async () => {
        writeFileSync(join(dir, 'users.txt'), 'alice:placeholder\n')
        const r = await run(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
          '--xmpp-allow', `alice@${DOMAIN}`, ...tlsArgs, '--users', 'users.txt', '--port', '0'], dir)
        assert(r.code === 0, `exit ${r.code}: ${r.errText.trim().split('\n').slice(-1)[0]}`)
      })
    await xfail('the login-limit key on the XMPP path is the bare JID of the sender, never empty',
      'https://github.com/danbri/factoidal/issues/1128', async () => {
        const r = await run(['webdav-serve', '--help'], dir)
        assert(/login limit[^\n]*bare JID/i.test(r.out + r.errText), 'no login limit keyed by JID on the XMPP path')
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
