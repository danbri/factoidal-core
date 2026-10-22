// Host tests for an LWS storage kept in files (`storage: "files"`,
// `lws-serve --storage files`). https://github.com/danbri/factoidal/issues/918
// Design record: docs/designissues/2026-10-22-lws-storage-on-disk.md
//
//   node tests/lws/storage-files.mjs
//
// The engine decides every file name and every byte
// (formal/lean4/L4Factoidal/LWS/FileLayout.lean); the host
// (npm/factoidal/lws/persist.mjs) reads what it names and performs its plans.
// Checked here, through `listen` and the CLI:
//
//   * a round trip across a restart: bytes, entity tags and the container
//     listing are the same, also for a body with NUL and 0xFF bytes;
//   * one body file per body version, removed after it is replaced or the
//     resource is deleted; no lws-state.json is written;
//   * a crash in the last journal record: the journal is cut at EVERY byte of
//     its last record, and each start gives the state before that record;
//     the complete record gives the state after it; a write after a torn
//     start survives the next restart;
//   * encryption at rest (FACTOIDAL_LWS_KEY, the `storageKey` option): body
//     files, journal and metadata hold no clear text; a restart with the key
//     works; a wrong key, no key, and a changed body byte refuse to start;
//   * migration from an existing lws-state.json (clear and sealed): the
//     snapshot is renamed to lws-state.json.migrated and every resource reads
//     back with its entity tag;
//   * the CLI: `--storage files` round trip, and `--storage bogus` refused.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import { mkdtempSync, rmSync, readFileSync, writeFileSync, existsSync, readdirSync, statSync, cpSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { randomBytes } from 'node:crypto'
import { spawn } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import http from 'node:http'

const ROOT = fileURLToPath(new URL('../../', import.meta.url))
const CLI = join(ROOT, 'npm/factoidal/bin/factoidal.mjs')

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
        res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, bytes: Buffer.concat(chunks) }))
      })
    req.on('error', reject)
    if (body !== undefined) req.end(Buffer.from(body)); else req.end()
  })
}

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

/** Every file under DIR, relative names. */
function filesUnder (dir, prefix = '') {
  const out = []
  for (const name of readdirSync(join(dir, prefix))) {
    const rel = prefix === '' ? name : `${prefix}/${name}`
    if (statSync(join(dir, rel)).isDirectory()) out.push(...filesUnder(dir, rel))
    else out.push(rel)
  }
  return out.sort()
}

const bodyFiles = (dir) => existsSync(join(dir, 'bodies')) ? filesUnder(dir).filter((f) => f.startsWith('bodies/')) : []

const SECRET = 'a-line-that-must-not-reach-the-disk-in-clear'
const BINARY = Buffer.from([0, 255, 1, 254, 0, 0, 10, 13, 128, 200, 0])
const KEY_HEX = randomBytes(32).toString('hex')
const OTHER_HEX = randomBytes(32).toString('hex')

/** What a client sees of a storage: bodies, entity tags, the listings. */
async function observe (origin, paths) {
  const seen = {}
  for (const p of paths) {
    const r = await request(origin, 'GET', p, p.endsWith('/') ? { accept: 'application/lws+json' } : {})
    seen[p] = { status: r.status, etag: r.headers.etag ?? null, body: r.bytes.toString('base64') }
  }
  return seen
}

const PATHS = ['/', '/notes/', '/notes/a.txt', '/notes/b.bin', '/notes/c.ttl', '/gone.txt']

/** A few changes of every kind: create, update, binary, container, delete. */
async function populate (origin) {
  const steps = [
    ['PUT', '/notes/a.txt', { 'content-type': 'text/plain' }, `first ${SECRET}`],
    ['PUT', '/notes/b.bin', { 'content-type': 'application/octet-stream' }, BINARY],
    ['PUT', '/notes/c.ttl', { 'content-type': 'text/turtle' }, `<#x> a <http://example.org/T> ; <http://example.org/p> "${SECRET}" .\n`],
    ['PUT', '/gone.txt', { 'content-type': 'text/plain' }, 'to be deleted'],
    ['PUT', '/notes/a.txt', { 'content-type': 'text/plain' }, `second ${SECRET}`],
    ['DELETE', '/gone.txt', {}, undefined]
  ]
  for (const [m, p, h, b] of steps) {
    const r = await request(origin, m, p, h, b)
    assert(r.status < 300, `${m} ${p} answered ${r.status}`)
  }
}

async function runFiles (engine, listen) {
  const open = (dir, extra = {}) => listen({ engine, port: 0, now: 1000, insecureNoAuth: true, onError: () => {}, dir, storage: 'files', ...extra })

  // ---------------------------------------------------------------- round trip
  {
    const dir = mkdtempSync(join(tmpdir(), 'lws918-files-'))
    try {
      let before = null
      await check('round trip across a restart: bodies, entity tags and listings are the same', async () => {
        const s = await open(dir)
        try {
          await populate(s.origin)
          before = await observe(s.origin, PATHS)
        } finally { await s.close() }
        assert(before['/notes/b.bin'].body === BINARY.toString('base64'), 'the binary body did not round trip in memory')
        assert(before['/gone.txt'].status === 404, 'the deleted resource answered')
        const t = await open(dir)
        try {
          const after = await observe(t.origin, PATHS)
          for (const p of PATHS) {
            assert(JSON.stringify(after[p]) === JSON.stringify(before[p]), `${p} differs after the restart`)
          }
        } finally { await t.close() }
      })
      await check('the directory holds lws-files.json, lws-journal and one file per body; no lws-state.json', async () => {
        assert(existsSync(join(dir, 'lws-files.json')), 'no lws-files.json')
        assert(existsSync(join(dir, 'lws-journal')), 'no lws-journal')
        assert(!existsSync(join(dir, 'lws-state.json')), 'lws-state.json was written in files mode')
        // Live bodies: a.txt (second), b.bin, c.ttl. The first a.txt and
        // gone.txt were removed after their records.
        const bodies = bodyFiles(dir)
        assert(bodies.length === 3, `${bodies.length} body files: ${bodies.join(', ')}`)
        const contents = bodies.map((f) => readFileSync(join(dir, f)))
        assert(contents.some((c) => c.equals(BINARY)), 'no body file holds the binary bytes (clear text mode)')
        assert(contents.some((c) => c.toString() === `second ${SECRET}`), 'no body file holds the second a.txt')
        assert(!contents.some((c) => c.toString() === 'to be deleted'), 'the deleted body is still on disk')
        // A restart compacts: the journal is empty after it.
        assert(readFileSync(join(dir, 'lws-journal')).length === 0, 'the journal is not empty after a restart')
      })
    } finally { rmSync(dir, { recursive: true, force: true }) }
  }

  // ------------------------------------------------------------- torn journal
  {
    const dir = mkdtempSync(join(tmpdir(), 'lws918-torn-'))
    try {
      await check('a journal cut at every byte of its last record starts with the state before it', async () => {
        // The crash: the plan of the last write is "write the new body file,
        // append the record, remove the old body file". A crash during the
        // append leaves the directory as it was before the write, plus the
        // new body file, plus a prefix of the record.
        const saved = mkdtempSync(join(tmpdir(), 'lws918-torn-saved-'))
        const s = await open(dir)
        let metaText, journalBefore, journalAfter, stateBefore, stateAfter, newBodies
        try {
          await populate(s.origin)
          stateBefore = await observe(s.origin, PATHS)
          metaText = readFileSync(join(dir, 'lws-files.json'))
          journalBefore = readFileSync(join(dir, 'lws-journal'))
          cpSync(dir, saved, { recursive: true })
          const bodiesBefore = new Set(bodyFiles(dir))
          const r = await request(s.origin, 'PUT', '/notes/a.txt', { 'content-type': 'text/plain' }, 'third version')
          assert(r.status === 204, `PUT answered ${r.status}`)
          stateAfter = await observe(s.origin, PATHS)
          journalAfter = readFileSync(join(dir, 'lws-journal'))
          newBodies = bodyFiles(dir).filter((f) => !bodiesBefore.has(f)).map((f) => [f, readFileSync(join(dir, f))])
          assert(readFileSync(join(dir, 'lws-files.json')).equals(metaText), 'the last write compacted; the test needs an appended record')
        } finally { await s.close() }
        assert(newBodies.length === 1, `the last write made ${newBodies.length} body files`)
        assert(journalAfter.length > journalBefore.length, 'the last write appended nothing')
        assert(journalAfter.subarray(0, journalBefore.length).equals(journalBefore), 'the journal was not appended to')
        try {
          const last = journalAfter.length - journalBefore.length
          let wrong = []
          for (let k = 0; k <= last; k++) {
            rmSync(dir, { recursive: true, force: true })
            cpSync(saved, dir, { recursive: true })
            for (const [f, b] of newBodies) writeFileSync(join(dir, f), b)
            writeFileSync(join(dir, 'lws-journal'), journalAfter.subarray(0, journalBefore.length + k))
            const t = await open(dir)
            try {
              const seen = await observe(t.origin, PATHS)
              const want = k === last ? stateAfter : stateBefore
              if (JSON.stringify(seen) !== JSON.stringify(want)) wrong.push(k)
            } finally { await t.close() }
          }
          assert(wrong.length === 0, `cut at ${wrong.length} of ${last + 1} byte counts gave another state (first ${wrong[0]})`)
        } finally { rmSync(saved, { recursive: true, force: true }) }
      })
      await check('after a torn start, a new write survives the next restart', async () => {
        const s = await open(dir)
        try {
          const r = await request(s.origin, 'PUT', '/notes/after.txt', { 'content-type': 'text/plain' }, 'after the crash')
          assert(r.status === 201, `PUT answered ${r.status}`)
        } finally { await s.close() }
        const t = await open(dir)
        try {
          const r = await request(t.origin, 'GET', '/notes/after.txt')
          assert(r.status === 200 && r.bytes.toString() === 'after the crash', `GET answered ${r.status}`)
        } finally { await t.close() }
      })
    } finally { rmSync(dir, { recursive: true, force: true }) }
  }

  // --------------------------------------------------------------- encryption
  {
    const dir = mkdtempSync(join(tmpdir(), 'lws918-sealed-'))
    try {
      let before = null
      await check('with a key, body files, journal and metadata hold no clear text', async () => {
        const s = await open(dir, { storageKey: KEY_HEX })
        try {
          await populate(s.origin)
          before = await observe(s.origin, PATHS)
        } finally { await s.close() }
        const all = filesUnder(dir)
        assert(bodyFiles(dir).length === 3, `${bodyFiles(dir).length} body files`)
        for (const f of all) {
          const b = readFileSync(join(dir, f))
          assert(b.indexOf(SECRET) < 0, `${f} holds the secret text`)
          assert(b.indexOf('/notes/') < 0, `${f} holds a resource path`)
          assert(b.indexOf(BINARY) < 0, `${f} holds the binary body`)
        }
        const meta = JSON.parse(readFileSync(join(dir, 'lws-files.json'), 'utf8'))
        assert(meta.format === 'lws-snapshot-sealed-1', `lws-files.json has format ${meta.format}`)
      })
      await check('with a key, a restart reads every resource back', async () => {
        const t = await open(dir, { storageKey: KEY_HEX })
        try {
          const after = await observe(t.origin, PATHS)
          for (const p of PATHS) assert(JSON.stringify(after[p]) === JSON.stringify(before[p]), `${p} differs`)
          // One more write, appended sealed, read back after one more restart.
          const r = await request(t.origin, 'PUT', '/notes/d.txt', { 'content-type': 'text/plain' }, SECRET)
          assert(r.status === 201, `PUT answered ${r.status}`)
          assert(readFileSync(join(dir, 'lws-journal')).indexOf('/notes/d.txt') < 0, 'the journal record is clear text')
        } finally { await t.close() }
        const u = await open(dir, { storageKey: KEY_HEX })
        try {
          const r = await request(u.origin, 'GET', '/notes/d.txt')
          assert(r.status === 200 && r.bytes.toString() === SECRET, `GET answered ${r.status}`)
        } finally { await u.close() }
      })
      await check('a wrong key, no key, and a changed body byte each refuse to start', async () => {
        await refuses(() => open(dir, { storageKey: OTHER_HEX }), 'wrong key')
        await refuses(() => open(dir, { storageKey: null }), 'encrypted')
        const f = bodyFiles(dir)[0]
        const b = readFileSync(join(dir, f))
        const changed = Buffer.from(b)
        changed[changed.length - 1] ^= 1
        writeFileSync(join(dir, f), changed)
        try {
          await refuses(() => open(dir, { storageKey: KEY_HEX }), 'authentication failed')
        } finally { writeFileSync(join(dir, f), b) }
        const ok = await open(dir, { storageKey: KEY_HEX })
        await ok.close()
      })
    } finally { rmSync(dir, { recursive: true, force: true }) }
  }

  // ---------------------------------------------------------------- migration
  for (const sealed of [false, true]) {
    const dir = mkdtempSync(join(tmpdir(), 'lws918-migrate-'))
    const key = sealed ? { storageKey: KEY_HEX } : { storageKey: null }
    try {
      await check(`migration from lws-state.json (${sealed ? 'sealed' : 'clear'}): renamed, every resource with its entity tag`, async () => {
        const s = await listen({ engine, port: 0, now: 1000, insecureNoAuth: true, onError: () => {}, dir, ...key })
        let before
        try {
          await populate(s.origin)
          before = await observe(s.origin, PATHS)
        } finally { await s.close() }
        assert(existsSync(join(dir, 'lws-state.json')), 'the snapshot mode wrote no lws-state.json')
        const t = await open(dir, key)
        try {
          const after = await observe(t.origin, PATHS)
          for (const p of PATHS) assert(JSON.stringify(after[p]) === JSON.stringify(before[p]), `${p} differs after migration`)
        } finally { await t.close() }
        assert(!existsSync(join(dir, 'lws-state.json')), 'lws-state.json is still there')
        assert(existsSync(join(dir, 'lws-state.json.migrated')), 'no lws-state.json.migrated')
        assert(bodyFiles(dir).length === 3, `${bodyFiles(dir).length} body files after migration`)
        const u = await open(dir, key)
        try {
          const again = await observe(u.origin, PATHS)
          for (const p of PATHS) assert(JSON.stringify(again[p]) === JSON.stringify(before[p]), `${p} differs on the second start`)
        } finally { await u.close() }
      })
    } finally { rmSync(dir, { recursive: true, force: true }) }
  }
}

/** Start the CLI, read the origin it prints, run `body`, stop it. */
async function withCli (args, env, body) {
  const child = spawn(process.execPath, [CLI, 'lws-serve', ...args], { env: { ...process.env, ...env }, stdio: ['ignore', 'pipe', 'pipe'] })
  let out = ''
  let errText = ''
  child.stderr.on('data', (d) => { errText += d })
  const origin = await new Promise((resolve, reject) => {
    child.stdout.on('data', (d) => {
      out += d
      const line = out.split('\n').find((l) => l.startsWith('http://'))
      if (line) resolve(line.trim())
    })
    child.on('exit', (code) => reject(Object.assign(new Error(`exited ${code}: ${errText.trim()}`), { code, errText })))
  })
  try {
    return await body(origin)
  } finally {
    child.kill('SIGTERM')
    await new Promise((resolve) => child.on('exit', resolve))
  }
}

async function runCli () {
  const dir = mkdtempSync(join(tmpdir(), 'lws918-cli-'))
  try {
    await check('CLI lws-serve --storage files keeps a resource across a restart', async () => {
      const args = [dir, '--storage', 'files', '--insecure-no-auth', '--port', '0', '--quiet']
      await withCli(args, {}, async (origin) => {
        const r = await request(origin, 'PUT', '/cli.txt', { 'content-type': 'text/plain' }, 'from the command line')
        assert(r.status === 201, `PUT answered ${r.status}`)
      })
      assert(existsSync(join(dir, 'lws-files.json')) && !existsSync(join(dir, 'lws-state.json')), 'not a files storage')
      await withCli(args, {}, async (origin) => {
        const r = await request(origin, 'GET', '/cli.txt')
        assert(r.status === 200 && r.bytes.toString() === 'from the command line', `GET answered ${r.status}`)
      })
    })
    await check('CLI lws-serve --storage bogus is refused with the engine message', async () => {
      let refused = null
      try {
        await withCli([dir, '--storage', 'bogus', '--insecure-no-auth', '--port', '0'], {}, async () => {})
      } catch (error) { refused = error }
      assert(refused !== null && refused.code === 1, `exit ${refused && refused.code}`)
      assert(refused.errText.indexOf('"storage" is "snapshot" or "files"') >= 0, `stderr: ${refused.errText}`)
    })
  } finally { rmSync(dir, { recursive: true, force: true }) }
}

const ALL = 11

async function main () {
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  const { listen } = await import('../../npm/factoidal/lws/server.mjs')
  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (let i = 0; i < ALL; i++) skip(`storage files check ${i + 1}`, `the Lean engine did not load: ${error.message}`)
    return
  }
  // A module built before issue 918 does not know `storage`; probe once.
  let files = false
  try {
    const opened = engine.call('lwsOpen', [JSON.stringify({ insecureNoAuth: true, storage: 'files' })])
    files = opened !== null && typeof opened === 'object' && opened.load !== undefined
  } catch (_error) { files = false }
  if (!files) {
    for (let i = 0; i < ALL; i++) skip(`storage files check ${i + 1}`, 'the module does not know "storage": "files" (rebuild the wasm)')
    return
  }
  await runFiles(engine, listen)
  await runCli()
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`lws-storage-files node: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
