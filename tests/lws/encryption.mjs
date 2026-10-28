// Host tests for encryption at rest of the LWS and Solid storage snapshot.
// https://github.com/danbri/factoidal/issues/921
//
//   node tests/lws/encryption.mjs
//
// Owner decision, 2026-10-21: "Yes env var please. Again off by default but
// good to show we can." With FACTOIDAL_LWS_KEY (or the `storageKey` option)
// the snapshot DIR/lws-state.json is sealed with ChaCha20-Poly1305 (HACL*)
// under a fresh random nonce for every write, and authenticated when the
// storage is opened. Every decision is made in Lean
// (formal/lean4/L4Factoidal/LWS/SnapshotSeal.lean): the key text, the key id,
// the header, the refusals. The host reads the variable and draws the nonce.
//
// Checked for `lws-serve` and `solid-serve`: the round trip through a
// restart; the file is sealed and names the key id (first 8 bytes of
// SHA-256 of the key, computed here with node:crypto); a new nonce per write;
// the hex and base64url forms of one key; a wrong key, an altered byte (every
// byte of the file, through the engine's open op), a truncated file, a
// clear-text file with a key and a sealed file without one each refuse to
// open with their own message; with no key a clear-text storage behaves as
// before. Then the CLI with the environment variable.
//
// Score line: "N pass, M fail, X xfail, S skipped (out of T)". An xfail is a
// case that fails today and names its open issue; if it passes, it counts as
// a failure (stale expectation), so the issue closure is not forgotten.

import { mkdtempSync, rmSync, readFileSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { createHash, randomBytes } from 'node:crypto'
import { spawn } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import http from 'node:http'

// This suite tests the sealed SNAPSHOT file; a storage kept in files with a
// key is tested by tests/lws/storage-files.mjs (issue 918). The variable
// that selects the files mode is therefore not passed to the servers and the
// command lines started here.
delete process.env.FACTOIDAL_LWS_STORAGE

const ROOT = fileURLToPath(new URL('../../', import.meta.url))
const CLI = join(ROOT, 'npm/factoidal/bin/factoidal.mjs')

let passed = 0
let failed = 0
let skipped = 0
let xfailed = 0
const failures = []

async function xfail (name, issue, body) {
  try {
    await body()
  } catch (error) {
    xfailed += 1
    console.log(`  xfail ${name} (${issue}): ${error && error.message ? error.message : error}`)
    return
  }
  failed += 1
  failures.push(`${name}: passes, but is marked as an expected failure of ${issue}; make it a check and close the issue`)
  console.log(`  FAIL  ${name} (unexpected pass)`)
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

function skip (name, reason) {
  skipped += 1
  console.log(`  skip  ${name} - ${reason}`)
}

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

function request (origin, method, target, headers = {}, body = undefined) {
  const url = new URL(origin)
  return new Promise((resolve, reject) => {
    const req = http.request({ host: url.hostname, port: url.port, method, path: target, headers },
      (res) => {
        const chunks = []
        res.on('data', (c) => chunks.push(c))
        res.on('end', () => resolve({
          status: res.statusCode, headers: res.headers, body: Buffer.concat(chunks).toString('utf8')
        }))
      })
    req.on('error', reject)
    if (body !== undefined) req.end(Buffer.from(body)); else req.end()
  })
}

/** Run `body`; it must throw, and the message must contain `needle`. */
async function refuses (body, needle) {
  let message = null
  try {
    const r = await body()
    if (r && typeof r.close === 'function') await r.close()
  } catch (error) {
    message = error && error.message ? error.message : String(error)
  }
  assert(message !== null, `opened, expected a refusal containing "${needle}"`)
  assert(message.indexOf(needle) >= 0, `refused with "${message}", expected "${needle}"`)
}

const KEY = randomBytes(32)
const KEY_HEX = KEY.toString('hex')
const KEY_B64URL = KEY.toString('base64url')
const KEY_ID = createHash('sha256').update(KEY).digest('hex').slice(0, 16)
const OTHER_HEX = randomBytes(32).toString('hex')
const SECRET_TEXT = 'a-secret-line-that-must-not-reach-the-disk-in-clear'
const BODY = `<http://example.org/s> <http://example.org/p> "${SECRET_TEXT}" .\n`

const SERVERS = [
  { label: 'lws-serve', module: '../../npm/factoidal/lws/server.mjs', options: { insecureNoAuth: true },
    openOp: 'lwsOpen', closeOp: 'lwsClose', openConfig: { insecureNoAuth: true } },
  { label: 'solid-serve', module: '../../npm/factoidal/solid/server/index.mjs', options: {},
    openOp: 'solidOpen', closeOp: 'solidClose', openConfig: {} }
]

const CHECK_NAMES = [
  'with a key, the snapshot is sealed, names the key id and holds no clear text',
  'with a key, a restart reads the resource back',
  'every write uses a new nonce',
  'the base64url form of the key opens the storage sealed under its hex form',
  'a wrong key is refused at open',
  'every one-byte change of the sealed file is refused at open',
  'a truncated file is refused at open',
  'a ciphertext shortened by one base64 group is refused (authentication)',
  'a clear-text file with a key set is refused',
  'a sealed file with no key is refused',
  'a key that is not 32 bytes is refused',
  'with no key, a clear-text storage behaves as before'
]

// ANTICIPATORY AND UNSTABLE (https://github.com/danbri/factoidal/issues/922):
// the search results records ride in the snapshot, so they are sealed too.
const RESULTS_CHECK = 'lws-serve: with a key, search results records (unstable, issue 922) are sealed and survive a restart'

const CLI_CHECKS = [
  'CLI lws-serve with FACTOIDAL_LWS_KEY writes a sealed snapshot and reopens it',
  'CLI lws-serve with a wrong FACTOIDAL_LWS_KEY exits 1 with the message',
  'CLI solid-serve with FACTOIDAL_LWS_KEY writes a sealed snapshot and reopens it'
]

async function runServer (server, engine) {
  const mod = await import(server.module)
  const names = CHECK_NAMES.map((n) => `${server.label}: ${n}`)
  const open = (extra) => mod.listen({ engine, port: 0, now: 1000, ...server.options, ...extra })
  const dir = mkdtempSync(join(tmpdir(), `lws921-${server.label}-`))
  const file = join(dir, 'lws-state.json')
  try {
    let firstNonce = null
    await check(names[0], async () => {
      const s = await open({ dir, storageKey: KEY_HEX })
      try {
        const put = await request(s.origin, 'PUT', '/notes/a.nt', { 'content-type': 'application/n-triples' }, BODY)
        assert(put.status === 201, `PUT answered ${put.status}`)
      } finally { await s.close() }
      const text = readFileSync(file, 'utf8')
      const doc = JSON.parse(text)
      assert(doc.format === 'lws-snapshot-sealed-1', `format ${doc.format}`)
      assert(doc.cipher === 'chacha20-poly1305', `cipher ${doc.cipher}`)
      assert(doc.keyId === KEY_ID, `keyId ${doc.keyId}, expected ${KEY_ID}`)
      assert(Buffer.from(doc.nonce, 'base64').length === 12, 'nonce is not 12 bytes')
      assert(text.indexOf(SECRET_TEXT) < 0, 'the resource text is in the file')
      assert(text.indexOf(Buffer.from(BODY).toString('base64').slice(0, 24)) < 0, 'the base64 body is in the file')
      assert(text.indexOf('/notes/a.nt') < 0, 'a resource path is in the file')
      firstNonce = doc.nonce
    })

    await check(names[1], async () => {
      const s = await open({ dir, storageKey: KEY_HEX })
      try {
        const get = await request(s.origin, 'GET', '/notes/a.nt')
        assert(get.status === 200, `GET after restart answered ${get.status}`)
        assert(get.body === BODY, `GET after restart gave ${JSON.stringify(get.body)}`)
      } finally { await s.close() }
    })

    await check(names[2], async () => {
      const s = await open({ dir, storageKey: KEY_HEX })
      const nonces = new Set([firstNonce])
      try {
        for (let i = 0; i < 4; i++) {
          const put = await request(s.origin, 'PUT', `/notes/n${i}.txt`, { 'content-type': 'text/plain' }, `note ${i}`)
          assert(put.status === 201, `PUT answered ${put.status}`)
          nonces.add(JSON.parse(readFileSync(file, 'utf8')).nonce)
        }
      } finally { await s.close() }
      assert(nonces.size === 5, `5 writes gave ${nonces.size} distinct nonces`)
    })

    await check(names[3], async () => {
      const s = await open({ dir, storageKey: KEY_B64URL })
      try {
        const get = await request(s.origin, 'GET', '/notes/n3.txt')
        assert(get.status === 200 && get.body === 'note 3', `GET answered ${get.status} ${get.body}`)
      } finally { await s.close() }
    })

    const sealedText = readFileSync(file, 'utf8')

    await check(names[4], async () => {
      await refuses(() => open({ dir, storageKey: OTHER_HEX }), 'wrong key')
      assert(readFileSync(file, 'utf8') === sealedText, 'the refused open changed the file')
    })

    await check(names[5], async () => {
      // Every byte of the file, changed by flipping its low bit, through the
      // same two steps the host takes: JSON.parse (a failure there is the
      // host's refusal), then the engine's open op with the snapshot.
      const bytes = Buffer.from(sealedText, 'utf8')
      let accepted = []
      for (let i = 0; i < bytes.length; i++) {
        const changed = Buffer.from(bytes)
        changed[i] ^= 1
        let snapshot
        try { snapshot = JSON.parse(changed.toString('utf8')) } catch (_error) { continue }
        let handle = null
        try {
          const answer = engine.call(server.openOp, [JSON.stringify({
            ...server.openConfig, storageKey: KEY_HEX, snapshot
          })])
          handle = answer.handle
        } catch (_error) { continue }
        accepted.push(i)
        try { engine.call(server.closeOp, [handle]) } catch (_error) { /* refused already */ }
      }
      assert(accepted.length === 0, `${accepted.length} of ${bytes.length} one-byte changes opened, first at ${accepted[0]}`)
      // And one through the host itself: a changed ciphertext character.
      const doc = JSON.parse(sealedText)
      const ct = doc.ciphertext
      const mid = Math.floor(ct.length / 2)
      doc.ciphertext = ct.slice(0, mid) + (ct[mid] === 'A' ? 'B' : 'A') + ct.slice(mid + 1)
      writeFileSync(file, JSON.stringify(doc))
      await refuses(() => open({ dir, storageKey: KEY_HEX }), 'snapshot:')
      writeFileSync(file, sealedText)
    })

    await check(names[6], async () => {
      writeFileSync(file, sealedText.slice(0, Math.floor(sealedText.length / 2)))
      await refuses(() => open({ dir, storageKey: KEY_HEX }), 'is not JSON')
      writeFileSync(file, sealedText)
    })

    await check(names[7], async () => {
      const doc = JSON.parse(sealedText)
      doc.ciphertext = doc.ciphertext.slice(0, -4)
      writeFileSync(file, JSON.stringify(doc))
      await refuses(() => open({ dir, storageKey: KEY_HEX }), 'authentication failed')
      writeFileSync(file, sealedText)
    })

    await check(names[8], async () => {
      const clearDir = mkdtempSync(join(tmpdir(), `lws921-${server.label}-clear-`))
      try {
        const s = await open({ dir: clearDir, storageKey: null })
        try {
          await request(s.origin, 'PUT', '/c.txt', { 'content-type': 'text/plain' }, 'clear')
        } finally { await s.close() }
        await refuses(() => open({ dir: clearDir, storageKey: KEY_HEX }), 'clear text')
      } finally { rmSync(clearDir, { recursive: true, force: true }) }
    })

    await check(names[9], async () => {
      await refuses(() => open({ dir, storageKey: null }), KEY_ID)
    })

    await check(names[10], async () => {
      await refuses(() => open({ dir, storageKey: KEY_HEX.slice(2) }), '32 bytes')
      await refuses(() => open({ dir, storageKey: randomBytes(31).toString('base64url') }), '32 bytes')
    })

    await check(names[11], async () => {
      const clearDir = mkdtempSync(join(tmpdir(), `lws921-${server.label}-plain-`))
      try {
        const s = await open({ dir: clearDir, storageKey: null })
        try {
          const put = await request(s.origin, 'PUT', '/c.txt', { 'content-type': 'text/plain' }, 'clear')
          assert(put.status === 201, `PUT answered ${put.status}`)
        } finally { await s.close() }
        const doc = JSON.parse(readFileSync(join(clearDir, 'lws-state.json'), 'utf8'))
        assert(doc.format === 'lws-snapshot-2', `format ${doc.format}`)
        const t = await open({ dir: clearDir, storageKey: null })
        try {
          const get = await request(t.origin, 'GET', '/c.txt')
          assert(get.status === 200 && get.body === 'clear', `GET answered ${get.status}`)
        } finally { await t.close() }
      } finally { rmSync(clearDir, { recursive: true, force: true }) }
    })
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

/** Start the CLI; resolve with its origin, or with its exit code and stderr. */
function startCli (command, dir, key) {
  return new Promise((resolve) => {
    const child = spawn(process.execPath, [CLI, command, dir, '--insecure-no-auth', '--port', '0', '--quiet'],
      { env: { ...process.env, FACTOIDAL_LWS_KEY: key }, stdio: ['ignore', 'pipe', 'pipe'] })
    let out = ''
    let errText = ''
    let done = false
    child.stdout.on('data', (d) => {
      out += d.toString()
      const line = out.split('\n')[0]
      if (!done && out.indexOf('\n') >= 0 && line.startsWith('http')) {
        done = true
        resolve({ child, origin: line.trim() })
      }
    })
    child.stderr.on('data', (d) => { errText += d.toString() })
    child.on('exit', (code) => {
      if (!done) { done = true; resolve({ code, stderr: errText }) }
    })
  })
}

function stopCli (child) {
  return new Promise((resolve) => {
    child.on('exit', () => resolve())
    child.kill('SIGINT')
  })
}

async function runCli () {
  for (const [index, command] of [[0, 'lws-serve'], [2, 'solid-serve']]) {
    await check(CLI_CHECKS[index], async () => {
      const dir = mkdtempSync(join(tmpdir(), `lws921-cli-${command}-`))
      try {
        const first = await startCli(command, dir, KEY_HEX)
        assert(first.origin !== undefined, `did not start: exit ${first.code} ${first.stderr}`)
        try {
          const put = await request(first.origin, 'PUT', '/x.txt', { 'content-type': 'text/plain' }, SECRET_TEXT)
          assert(put.status === 201, `PUT answered ${put.status}`)
        } finally { await stopCli(first.child) }
        const text = readFileSync(join(dir, 'lws-state.json'), 'utf8')
        assert(JSON.parse(text).keyId === KEY_ID, 'the file is not sealed under the key')
        assert(text.indexOf(SECRET_TEXT) < 0, 'the resource text is in the file')
        const second = await startCli(command, dir, KEY_B64URL)
        assert(second.origin !== undefined, `did not restart: exit ${second.code} ${second.stderr}`)
        try {
          const get = await request(second.origin, 'GET', '/x.txt')
          assert(get.status === 200 && get.body === SECRET_TEXT, `GET answered ${get.status}`)
        } finally { await stopCli(second.child) }
      } finally { rmSync(dir, { recursive: true, force: true }) }
    })
  }
  await check(CLI_CHECKS[1], async () => {
    const dir = mkdtempSync(join(tmpdir(), 'lws921-cli-wrong-'))
    try {
      const { listen } = await import('../../npm/factoidal/lws/server.mjs')
      const s = await listen({ port: 0, insecureNoAuth: true, dir, storageKey: KEY_HEX })
      try {
        await request(s.origin, 'PUT', '/x.txt', { 'content-type': 'text/plain' }, 'x')
      } finally { await s.close() }
      const third = await startCli('lws-serve', dir, OTHER_HEX)
      if (third.origin !== undefined) await stopCli(third.child)
      assert(third.origin === undefined, 'started with the wrong key')
      assert(third.code === 1, `exit code ${third.code}`)
      assert(third.stderr.indexOf('wrong key') >= 0, `stderr: ${third.stderr}`)
      assert(third.stderr.indexOf('    at ') < 0, `stderr carries a stack: ${third.stderr}`)
    } finally { rmSync(dir, { recursive: true, force: true }) }
  })
}

async function runResults (engine) {
  const { listen } = await import('../../npm/factoidal/lws/server.mjs')
  const dir = mkdtempSync(join(tmpdir(), 'lws922-sealed-'))
  const AGENT = 'https://alice.example/sealed-agent#me'
  const TYPE = `https://ex.org/${SECRET_TEXT}#T`
  const options = { engine, port: 0, now: 1000, insecureNoAuth: true, agent: AGENT, searchResults: true, dir, storageKey: KEY_HEX }
  try {
    await check(RESULTS_CHECK, async () => {
      let path = null
      let origin = null
      const s = await listen(options)
      try {
        origin = s.origin
        const w = await request(s.origin, 'PUT', '/r/a', { 'content-type': 'text/plain', prefer: 'set-linkset', link: `<${TYPE}>; rel="type"` }, 'x')
        assert(w.status === 201, `PUT answered ${w.status}`)
        const q = await fetch(`${s.origin}/.well-known/lws-type-search`, { method: 'QUERY', headers: { 'content-type': 'application/lws-query+json' }, body: JSON.stringify({ type: [TYPE] }) })
        await q.text()
        const loc = q.headers.get('content-location')
        assert(q.status === 200 && loc !== null, `QUERY answered ${q.status}, Content-Location ${loc}`)
        path = new URL(loc).pathname
      } finally {
        await s.close()
      }
      const text = readFileSync(join(dir, 'lws-state.json'), 'utf8')
      assert(text.indexOf('searchResults') < 0 && text.indexOf(AGENT) < 0 && text.indexOf(path.split('/').pop()) < 0,
        'the sealed file shows the results record in clear text')
      const t = await listen({ ...options, baseIri: `${origin}/` })
      try {
        const g = await fetch(`${t.origin}${path}`)
        const j = await g.json()
        assert(g.status === 200 && j.items.length === 1 && j.items[0].id === `${origin}/r/a`, `after the restart GET answered ${g.status} ${JSON.stringify(j)}`)
      } finally {
        await t.close()
      }
    })
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

async function main () {
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const s of SERVERS) for (const n of CHECK_NAMES) skip(`${s.label}: ${n}`, `the Lean engine did not load: ${error.message}`)
    for (const n of CLI_CHECKS) skip(n, 'the Lean engine did not load')
    return
  }
  // A module built before issue 921 ignores `storageKey`; probe once.
  let sealing = false
  try {
    engine.call('lwsOpen', [JSON.stringify({ insecureNoAuth: true, storageKey: 'too-short' })])
  } catch (error) {
    sealing = String(error.message).indexOf('32 bytes') >= 0
  }
  if (!sealing) {
    for (const s of SERVERS) for (const n of CHECK_NAMES) skip(`${s.label}: ${n}`, 'the module does not read storageKey (rebuild the wasm)')
    for (const n of CLI_CHECKS) skip(n, 'the module does not read storageKey (rebuild the wasm)')
    skip(RESULTS_CHECK, 'the module does not read storageKey (rebuild the wasm)')
    return
  }
  for (const s of SERVERS) await runServer(s, engine)
  await runResults(engine)
  await runCli()
  await runRekey()
}

// A key change of a sealed storage is not possible yet
// (https://github.com/danbri/factoidal/issues/1136): the case states what
// it should do (`factoidal lws-rekey DIR` with the old key in
// FACTOIDAL_LWS_KEY_OLD and the new key in FACTOIDAL_LWS_KEY), and fails
// today because there is no such command.
async function runRekey () {
  await xfail('re-key: a storage sealed under one key opens under a new key after a re-key',
    'https://github.com/danbri/factoidal/issues/1136', async () => {
      const dir = mkdtempSync(join(tmpdir(), 'lws1136-rekey-'))
      try {
        const { listen } = await import('../../npm/factoidal/lws/server.mjs')
        const s = await listen({ port: 0, insecureNoAuth: true, dir, storageKey: KEY_HEX })
        try {
          await request(s.origin, 'PUT', '/x.txt', { 'content-type': 'text/plain' }, SECRET_TEXT)
        } finally { await s.close() }
        const { spawnSync } = await import('node:child_process')
        const r = spawnSync(process.execPath, [CLI, 'lws-rekey', dir], {
          env: { ...process.env, FACTOIDAL_LWS_KEY_OLD: KEY_HEX, FACTOIDAL_LWS_KEY: OTHER_HEX }, encoding: 'utf8'
        })
        assert(r.status === 0, `lws-rekey exit ${r.status}: ${(r.stderr || '').split('\n').find((l) => l.includes('unknown command')) || r.stderr}`)
        const t = await listen({ port: 0, insecureNoAuth: true, dir, storageKey: OTHER_HEX })
        try {
          const get = await request(t.origin, 'GET', '/x.txt')
          assert(get.status === 200 && get.body === SECRET_TEXT, `GET answered ${get.status}`)
        } finally { await t.close() }
      } finally { rmSync(dir, { recursive: true, force: true }) }
    })
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + xfailed + skipped
console.log(`lws-encryption node: ${passed} pass, ${failed} fail, ${xfailed} xfail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
