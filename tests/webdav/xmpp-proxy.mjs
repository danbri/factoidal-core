// End-to-end test of `factoidal xmpp-http-proxy`: a WebDAV server behind
// NAT (`webdav-serve --xmpp`), reached by plain HTTP clients through a local
// proxy that sends each request over XMPP (XEP-0332).
// https://github.com/danbri/factoidal/issues/1107, step 2. Design record:
// docs/designissues/2026-10-28-http-over-xmpp.md, section "Step 2".
//
//   node tests/webdav/xmpp-proxy.mjs
//
// Processes, all on 127.0.0.1:
//   factoidal xmpp-serve          accounts alice, bob, carol (direct TLS,
//                                 a self-signed certificate for example.org)
//   factoidal webdav-serve --xmpp bob@example.org --xmpp-allow alice@example.org
//   factoidal xmpp-http-proxy --xmpp alice@example.org --target bob@example.org/dav
//   factoidal xmpp-http-proxy --xmpp carol@example.org --target bob@example.org/dav
//   factoidal xmpp-http-proxy --xmpp alice@example.org --target carol@example.org/t
//                                 (a test client that never answers: the
//                                 headers it receives, the timeout, a forged
//                                 answer from bob@example.org/t)
// Then fetch, litmus, rclone and cadaver use the proxies'
// http://127.0.0.1:PORT/. Every decision is in
// formal/lean4/L4Factoidal/XMPP/ (ClientStream, HttpOverXmpp, HttpRequester).
//
// A client program that is not installed is reported "skip", never a pass.
// Score line: "N pass, M fail, X xfail, S skip (out of T)".

import { spawn, spawnSync, execFileSync } from 'node:child_process'
import { mkdtempSync, mkdirSync, rmSync, writeFileSync, readFileSync } from 'node:fs'
import net from 'node:net'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { TestClient } from './xmpp-client.mjs'

const CLI = fileURLToPath(new URL('../../npm/factoidal/bin/factoidal.mjs', import.meta.url))
const DOMAIN = 'example.org'
const TARGET = `bob@${DOMAIN}/dav`
const HOST_ISSUE = 'https://github.com/danbri/factoidal/issues/1124'

let passed = 0
let failed = 0
let xfailed = 0
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

/** An expected failure: a stated shortfall with its open issue. When it
 *  passes, the run turns red. */
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

function skip (name, why) {
  skipped += 1
  console.log(`  skip  ${name} - ${why}`)
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

/** One raw HTTP/1.1 request on a socket (for request targets fetch will not send). */
function rawRequest (port, text) {
  return new Promise((resolve, reject) => {
    const s = net.connect({ host: '127.0.0.1', port }, () => s.write(text))
    let got = ''
    s.setEncoding('latin1')
    s.on('data', (d) => { got += d; if (/\r\n\r\n/.test(got)) { s.destroy(); resolve(got) } })
    s.on('error', reject)
    setTimeout(() => { s.destroy(); reject(new Error(`no answer: ${got}`)) }, 30000)
  })
}

function has (program) {
  return !spawnSync(program, ['--version'], { encoding: 'utf8' }).error
}

async function main () {
  const dir = mkdtempSync(join(process.env.WEBDAV_TEST_TMP || tmpdir(), 'webdav-xmpp-proxy-'))
  try {
    mkdirSync(join(dir, 'dav', 'notes'), { recursive: true })
    mkdirSync(join(dir, 'xmpp'))
    writeFileSync(join(dir, 'dav', 'notes.md'), '# Notes\n- kind: local\n- path: ./notes\n')
    writeFileSync(join(dir, 'accounts'), 'alice:alice-pw\nbob:bob-pw\ncarol:carol-pw\n')
    writeFileSync(join(dir, 'alice.password'), 'alice-pw\n')
    writeFileSync(join(dir, 'bob.password'), 'bob-pw\n')
    writeFileSync(join(dir, 'carol.password'), 'carol-pw\n')
    execFileSync('openssl', ['req', '-x509', '-newkey', 'ec', '-pkeyopt', 'ec_paramgen_curve:P-256', '-nodes',
      '-keyout', join(dir, 'key.pem'), '-out', join(dir, 'cert.pem'), '-days', '1', '-subj', `/CN=${DOMAIN}`,
      '-addext', `subjectAltName=DNS:${DOMAIN}`], { stdio: 'ignore' })
    const ca = readFileSync(join(dir, 'cert.pem'))
    const xs = await start(['xmpp-serve', 'xmpp', '--port', '0', '--domain', DOMAIN, '--accounts', 'accounts',
      '--cert', 'cert.pem', '--key', 'key.pem'], /^xmpps:\/\/127\.0\.0\.1:(\d+)$/m, dir)
    const xport = xs.match[1]
    const tlsArgs = ['--xmpp-host', '127.0.0.1', '--xmpp-port', xport, '--xmpp-tls', '--xmpp-ca', 'cert.pem']
    const proxyArgs = (user, target, ...more) => ['xmpp-http-proxy', '--xmpp', `${user}@${DOMAIN}`,
      '--xmpp-password-file', `${user}.password`, '--target', target, '--port', '0', ...tlsArgs, ...more]

    // Start refusals, decided in Lean (`xcProxyRefusal`).
    await check('start refused: --host other than 127.0.0.1 (exit 1)', async () => {
      const r = await run([...proxyArgs('alice', TARGET), '--host', '0.0.0.0'], dir)
      assert(r.code === 1 && r.errText.includes('127.0.0.1 only'), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: --target is a bare JID (exit 1)', async () => {
      const r = await run(proxyArgs('alice', `bob@${DOMAIN}`), dir)
      assert(r.code === 1 && r.errText.includes('full JID'), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: plain TCP to a host that is not loopback (exit 1, no connection)', async () => {
      const r = await run(['xmpp-http-proxy', '--xmpp', `alice@${DOMAIN}`, '--xmpp-password-file', 'alice.password',
        '--target', TARGET, '--port', '0', '--xmpp-host', '192.0.2.1', '--xmpp-port', '5222'], dir)
      assert(r.code === 1 && r.errText.includes('plain TCP to 192.0.2.1 is refused'), `exit ${r.code}: ${r.errText}`)
    })
    await check('start refused: a timeout outside 1 to 3600 seconds (exit 1)', async () => {
      const r = await run([...proxyArgs('alice', TARGET), '--timeout', '0'], dir)
      assert(r.code === 1 && r.errText.includes('1 to 3600'), `exit ${r.code}: ${r.errText}`)
    })

    await start(['webdav-serve', 'dav', '--xmpp', `bob@${DOMAIN}`, '--xmpp-password-file', 'bob.password',
      '--xmpp-allow', `alice@${DOMAIN}`, ...tlsArgs, '--dangerously-allow-writable-without-login'], /^xmpp:(\S+)$/m, dir)

    let proxy = null
    await check('xmpp-http-proxy as alice: binds, listens on 127.0.0.1, prints its origin', async () => {
      proxy = await start(proxyArgs('alice', TARGET), /^(http:\/\/127\.0\.0\.1:(\d+)\/)$/m, dir)
      assert(proxy.errText().includes('EXPERIMENTAL UNREVIEWED CODE'), 'no review notice on standard error')
      assert(proxy.errText().includes(`go to ${TARGET} only`), proxy.errText())
    })
    if (proxy === null) return
    const base = proxy.match[1]
    const pport = Number(proxy.match[2])

    await check('PROPFIND / through the proxy gives 207 with the notes mount', async () => {
      const r = await fetch(base, { method: 'PROPFIND', headers: { Depth: '1' } })
      const t = await r.text()
      assert(r.status === 207 && t.includes('/notes/'), `status ${r.status}: ${t.slice(0, 300)}`)
    })
    await check('PUT then GET a text file through the proxy (201, 200, same bytes)', async () => {
      const p = await fetch(`${base}notes/hello.txt`, { method: 'PUT', headers: { 'Content-Type': 'text/plain' }, body: 'hello\r\nthrough the proxy\n' })
      assert(p.status === 201, `PUT ${p.status}`)
      const g = await fetch(`${base}notes/hello.txt`)
      const t = await g.text()
      assert(g.status === 200 && t === 'hello\r\nthrough the proxy\n', `GET ${g.status}: ${JSON.stringify(t)}`)
    })
    await check('MKCOL then PROPFIND Depth 1 lists the new collection', async () => {
      const m = await fetch(`${base}notes/docs/`, { method: 'MKCOL' })
      assert(m.status === 201, `MKCOL ${m.status}`)
      const p = await fetch(`${base}notes/`, { method: 'PROPFIND', headers: { Depth: '1' } })
      const t = await p.text()
      assert(p.status === 207 && t.includes('/notes/docs/') && t.includes('/notes/hello.txt'), t.slice(0, 500))
    })
    const big = Buffer.alloc(100000)
    for (let i = 0; i < big.length; i += 1) big[i] = (i * 7) % 251
    await check('a 100,000-byte body: PUT (chunked request) and GET (chunked response) give the same bytes', async () => {
      const p = await fetch(`${base}notes/big.bin`, { method: 'PUT', headers: { 'Content-Type': 'application/octet-stream' }, body: big })
      assert(p.status === 201, `PUT ${p.status}`)
      const g = await fetch(`${base}notes/big.bin`)
      const b = Buffer.from(await g.arrayBuffer())
      assert(g.status === 200 && b.equals(big), `GET ${g.status}, ${b.length} bytes`)
    })
    await check('an absolute-form request target gets 400 (not a forward proxy)', async () => {
      const t = await rawRequest(pport, 'GET http://other.example/ HTTP/1.1\r\nHost: other.example\r\nConnection: close\r\n\r\n')
      assert(/^HTTP\/1\.1 400/.test(t), t.slice(0, 200))
    })
    await check('CONNECT gets 405', async () => {
      const t = await rawRequest(pport, 'CONNECT other.example:443 HTTP/1.1\r\nHost: other.example:443\r\n\r\n')
      assert(/^HTTP\/1\.1 405/.test(t), t.slice(0, 200))
    })
    await xfail('a request with a foreign Host header is refused (DNS rebinding guard)', HOST_ISSUE, async () => {
      const t = await rawRequest(pport, 'PROPFIND / HTTP/1.1\r\nHost: attacker.example\r\nDepth: 0\r\nConnection: close\r\n\r\n')
      assert(/^HTTP\/1\.1 (403|421)/.test(t), `answered ${t.split('\r\n')[0]}`)
    })

    // carol is not in --xmpp-allow: the server refuses with `forbidden`,
    // which the proxy gives as 403; the storage does not change.
    await check('carol\'s proxy (carol not in --xmpp-allow): GET and PUT get 403, the file does not change', async () => {
      const cp = await start(proxyArgs('carol', TARGET), /^(http:\/\/127\.0\.0\.1:\d+\/)$/m, dir)
      const g = await fetch(`${cp.match[1]}notes/hello.txt`)
      assert(g.status === 403, `GET ${g.status}`)
      const p = await fetch(`${cp.match[1]}notes/hello.txt`, { method: 'PUT', body: 'overwritten' })
      assert(p.status === 403, `PUT ${p.status}`)
      const again = await fetch(`${base}notes/hello.txt`)
      assert((await again.text()) === 'hello\r\nthrough the proxy\n', 'the file changed')
    })

    // A target that never answers: a test client logged in as carol/t. It
    // reads the request the proxy sends, bob/t forges an answer (dropped,
    // because it is not from the target), and the proxy gives 504.
    await check('headers: Authorization unchanged, no Proxy-Authorization or Connection; a forged answer from another JID is dropped; 504 after --timeout', async () => {
      const echo = new TestClient(Number(xport), DOMAIN, ca)
      const forger = new TestClient(Number(xport), DOMAIN, ca)
      try {
        await echo.login('carol', 'carol-pw')
        await forger.login('bob', 'bob-pw')
        const ep = await start([...proxyArgs('alice', `carol@${DOMAIN}/t`, '--timeout', '3'), '--xmpp-resource', 'p3'],
          /^(http:\/\/127\.0\.0\.1:\d+\/)$/m, dir)
        const t0 = Date.now()
        const pending = fetch(`${ep.match[1]}x`, { headers: { Authorization: 'Bearer abc.def', 'Proxy-Authorization': 'Basic cDpx' } })
        const m = await echo.wait(/<iq[^>]*type="set"[\s\S]*?<\/iq>/)
        const iq = m[0]
        assert(iq.includes('<header name="authorization">Bearer abc.def</header>') ||
          iq.includes('<header name="Authorization">Bearer abc.def</header>'), `no Authorization: ${iq}`)
        assert(!/proxy-authorization/i.test(iq), `Proxy-Authorization forwarded: ${iq}`)
        assert(!/name="connection"/i.test(iq), `Connection forwarded: ${iq}`)
        const id = /id="([^"]+)"/.exec(iq)[1]
        forger.send(`<iq type='result' id='${id}' to='alice@${DOMAIN}/p3'><resp xmlns='urn:xmpp:http' version='1.1' statusCode='200'>` +
          `<data><text>forged</text></data></resp></iq>`)
        const r = await pending
        const elapsed = Date.now() - t0
        assert(r.status === 504, `status ${r.status}: ${await r.text()}`)
        assert(elapsed >= 2500, `answered after ${elapsed} ms, before the timeout`)
      } finally {
        echo.close()
        forger.close()
      }
    })

    // litmus, the WebDAV conformance suite, through the proxy.
    if (!has('litmus')) {
      skip('litmus through the proxy', 'litmus is not installed (apt-get install litmus)')
    } else {
      await check('litmus (basic, copymove, props, locks, http) through the proxy: every test passes', async () => {
        const work = join(dir, 'litmus-work')
        mkdirSync(work)
        const r = spawnSync('litmus', [`${base}notes/`], { cwd: work, encoding: 'utf8', timeout: 600000 })
        const text = (r.stdout || '') + (r.stderr || '')
        const sums = text.split('\n').filter((l) => l.startsWith('<- summary'))
        for (const s of sums) console.log(`        ${s}`)
        const bad = text.split('\n').filter((l) => /\.\s+(FAIL|WARNING)/.test(l))
        assert(sums.length === 5, `litmus ran ${sums.length} of 5 suites: ${text.slice(-600)}`)
        assert(bad.length === 0, bad.join('\n'))
      })
    }

    if (!has('rclone')) {
      skip('rclone through the proxy', 'rclone is not installed')
    } else {
      mkdirSync(join(dir, 'src', 'sub'), { recursive: true })
      writeFileSync(join(dir, 'src', 'a.txt'), 'hello\n')
      writeFileSync(join(dir, 'src', 'sub', 'b.txt'), 'world\n')
      writeFileSync(join(dir, 'rclone.conf'), '')
      const env = { ...process.env, RCLONE_CONFIG: join(dir, 'rclone.conf'),
        RCLONE_CONFIG_F_TYPE: 'webdav', RCLONE_CONFIG_F_URL: base, RCLONE_CONFIG_F_VENDOR: 'other' }
      const rc = (...args) => {
        const r = spawnSync('rclone', args, { env, cwd: dir, encoding: 'utf8', timeout: 120000 })
        if (r.status !== 0) throw new Error(`rclone ${args.join(' ')}: exit ${r.status}: ${r.stderr}`)
        return r.stdout
      }
      await check('rclone through the proxy: copy a tree, list it, check the bytes, move, purge', async () => {
        rc('copy', 'src', 'f:notes/proj')
        const ls = rc('lsf', '-R', 'f:notes/proj').split('\n').filter(Boolean).sort()
        assert(JSON.stringify(ls) === JSON.stringify(['a.txt', 'sub/', 'sub/b.txt']), `listing ${JSON.stringify(ls)}`)
        rc('check', 'src', 'f:notes/proj')
        rc('moveto', 'f:notes/proj/a.txt', 'f:notes/proj/renamed.txt')
        assert(rc('cat', 'f:notes/proj/renamed.txt') === 'hello\n', 'content after move')
        rc('purge', 'f:notes/proj')
      })
    }

    if (!has('cadaver')) {
      skip('cadaver through the proxy', 'cadaver is not installed')
    } else {
      writeFileSync(join(dir, 'up.txt'), 'hi\n')
      await check('cadaver through the proxy: MKCOL, PUT, PROPPATCH, LOCK, COPY, MOVE, DELETE', async () => {
        const script = ['cd notes', 'mkcol d1', 'put up.txt d1/up.txt', 'propset d1/up.txt color blue',
          'propget d1/up.txt color', 'lock d1/up.txt', 'unlock d1/up.txt', 'copy d1/up.txt d1/copy.txt',
          'move d1/copy.txt d1/moved.txt', 'cat d1/moved.txt', 'rm d1/moved.txt', 'rm d1/up.txt', 'rmcol d1', 'quit', ''].join('\n')
        const r = spawnSync('cadaver', [base], { input: script, encoding: 'utf8', cwd: dir, timeout: 120000 })
        const out = `${r.stdout}${r.stderr}`
        assert(/Value of color is: blue/.test(out) && /cat d1\/moved\.txt\nhi\n/.test(out), out)
        assert(!/failed/i.test(out), `a command failed:\n${out}`)
      })
    }
  } finally {
    for (const c of children) {
      if (c.exitCode === null) { c.kill('SIGTERM'); await new Promise((resolve) => c.on('close', resolve)) }
    }
    rmSync(dir, { recursive: true, force: true })
  }
}

await main()
console.log(`webdav through xmpp-http-proxy: ${passed} pass, ${failed} fail, ${xfailed} xfail, ${skipped} skip (out of ${passed + failed + xfailed + skipped})`)
for (const f of failures) console.log(`  ${f}`)
process.exit(failed === 0 && passed > 0 ? 0 : 1)
