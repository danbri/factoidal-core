// SPARQL over an SBM11 generation held in an LWS storage, read through the
// LWS medium (lib/sbm11-lws.mjs; https://github.com/danbri/factoidal/issues/1010
// KR3, read part).
//
// The test starts `factoidal lws-serve` in a child process on a temporary
// directory (the reader blocks this thread while it waits for an answer, so
// the server must not run here), PUTs every file of the fixture collection
// root test/fixtures/sbm11-tiny/root as one LWS resource, and checks:
//
//   * every file read through the LWS reader has the bytes the local
//     directory reader gives, and the server answered 206 to range reads;
//   * a server that ignores Range (simulated by a transport that drops the
//     header) is read by whole GETs, one request per file;
//   * a changed entity tag between two reads of one file refuses the read;
//   * the 13 fixture queries answer the same bytes and path through LWS as
//     through the local directory, and the store's evidence lists each
//     resource read with its ETag (needs a wasm with the sbm11 ops).
//
// A wasm without the lws or sbm11 ops fails the cases, never skips them
// (https://github.com/danbri/factoidal/issues/1038, P2). No RDF logic here.

import test from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, readFileSync, readdirSync, rmSync, statSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { spawn } from 'node:child_process'
import { openSbm11, lwsSbm11Reader, loadEngine } from '../index.mjs'
import { nodeDirectoryReader } from '../lib/sbm11-node.mjs'
import { nodeSyncTransport } from '../lib/sync-http-node.mjs'

const HERE = dirname(fileURLToPath(import.meta.url))
const CLI = join(HERE, '..', 'bin', 'factoidal.mjs')
const FIX = join(HERE, 'fixtures', 'sbm11-tiny')
const ROOT = join(FIX, 'root')
const QUERIES = JSON.parse(readFileSync(join(FIX, 'queries.json'), 'utf8'))

const eng = await loadEngine()
const opsText = (() => { const r = eng.call('ops', []); return typeof r === 'string' ? r : JSON.stringify(r) })()
const hasLws = opsText.includes('"lwsStep"')
const hasSbm11 = opsText.includes('"sbm11Query"')

test('the package wasm serves the lws and sbm11 ops', () => {
  assert.ok(hasLws, 'ops reflection names lwsStep')
  assert.ok(hasSbm11, 'ops reflection names sbm11Query')
})

/** Every file under the collection root, as relative names. */
function filesUnder (dir, prefix = '') {
  const out = []
  for (const name of readdirSync(dir).sort()) {
    const p = join(dir, name)
    if (statSync(p).isDirectory()) out.push(...filesUnder(p, prefix + name + '/'))
    else out.push(prefix + name)
  }
  return out
}
const FILES = filesUnder(ROOT)

let server = null
let origin = null
let storeUrl = null
let dataDir = null

async function startServer () {
  dataDir = mkdtempSync(join(tmpdir(), 'sbm11-lws-'))
  server = spawn(process.execPath, [CLI, 'lws-serve', dataDir, '--insecure-no-auth', '--port', '0', '--storage', 'files'],
    { stdio: ['ignore', 'pipe', 'pipe'] })
  origin = await new Promise((resolve, reject) => {
    let text = ''
    const timer = setTimeout(() => reject(new Error(`lws-serve did not start: ${text}`)), 60000)
    server.stdout.on('data', (chunk) => {
      text += chunk
      const m = /(http:\/\/127\.0\.0\.1:\d+)/.exec(text)
      if (m) { clearTimeout(timer); resolve(m[1]) }
    })
    server.stderr.on('data', (chunk) => { text += chunk })
    server.on('exit', (code) => { clearTimeout(timer); reject(new Error(`lws-serve exited ${code}: ${text}`)) })
  })
  storeUrl = `${origin}/stores/tiny/`
  for (const f of FILES) {
    const r = await fetch(storeUrl + f, {
      method: 'PUT', headers: { 'content-type': 'application/octet-stream' }, body: readFileSync(join(ROOT, f))
    })
    assert.ok(r.status === 201 || r.status === 204, `PUT ${f}: ${r.status}`)
  }
}

test('start lws-serve and upload the fixture generation', async () => {
  await startServer()
  assert.ok(FILES.includes('CURRENT') && FILES.includes('gen/manifest.sbm11'))
})

test('the LWS reader gives the bytes of the directory reader; the server answers 206', () => {
  const local = nodeDirectoryReader(ROOT)
  const lws = lwsSbm11Reader(storeUrl)
  try {
    assert.equal(lws.size('no-such-file'), null)
    for (const f of FILES) {
      const n = local.size(f)
      assert.equal(lws.size(f), n, `size ${f}`)
      assert.deepEqual(lws.readAt(f, 0, n), local.readAt(f, 0, n), `whole ${f}`)
      if (n > 3) assert.deepEqual(lws.readAt(f, 1, n - 2), local.readAt(f, 1, n - 2), `inner ${f}`)
      assert.equal(lws.readAt(f, n, 1), null, `past the end ${f}`)
    }
    const ev = lws.evidence()
    assert.equal(ev.length, FILES.length)
    for (const e of ev) {
      assert.match(e.etag, /^(W\/)?"/)
      assert.ok(e.resource.startsWith(storeUrl))
    }
    assert.ok(ev.some((e) => e.partial > 0), 'no read was answered with 206')
  } finally {
    lws.close()
    local.close()
  }
})

test('a server that ignores Range: whole GETs, one request per file', () => {
  const inner = nodeSyncTransport()
  const noRange = (url, headers) => {
    const h = { ...headers }
    delete h.range
    return inner(url, h)
  }
  const local = nodeDirectoryReader(ROOT)
  const lws = lwsSbm11Reader(storeUrl, { transport: noRange })
  try {
    for (const f of FILES) {
      const n = local.size(f)
      assert.equal(lws.size(f), n)
      assert.deepEqual(lws.readAt(f, 0, n), local.readAt(f, 0, n))
      if (n > 3) assert.deepEqual(lws.readAt(f, 2, n - 3), local.readAt(f, 2, n - 3))
    }
    for (const e of lws.evidence()) {
      assert.equal(e.partial, 0)
      assert.equal(e.requests, 1, e.resource)
    }
  } finally {
    lws.close()
    local.close()
    inner.close()
  }
})

test('a changed entity tag between two reads of one file refuses the read', async () => {
  const url = `${origin}/stores/changing/`
  await fetch(url + 'CURRENT', { method: 'PUT', headers: { 'content-type': 'application/octet-stream' }, body: 'gen' })
  const lws = lwsSbm11Reader(url)
  try {
    assert.equal(lws.size('CURRENT'), 3)
    await fetch(url + 'CURRENT', { method: 'PUT', headers: { 'content-type': 'application/octet-stream' }, body: 'g2x' })
    assert.equal(lws.readAt('CURRENT', 0, 3), null)
    assert.match(lws.errors().join('\n'), /entity tag changed/)
  } finally {
    lws.close()
  }
})

let local = null
let remote = null
let reader = null
test('open the generation through LWS and through the directory', async () => {
  local = await openSbm11(ROOT)
  reader = lwsSbm11Reader(storeUrl)
  remote = await openSbm11(storeUrl, { reader })
  assert.equal(remote.generation, 'gen')
  assert.equal(remote.terms, local.terms)
})

for (const [name, sparql] of QUERIES) {
  test(`sbm11 over LWS ${name}: the bytes and path of the directory`, () => {
    const want = local.query(sparql)
    const got = remote.query(sparql)
    assert.equal(got.result, want.result)
    assert.equal(got.path, want.path)
  })
}

test('the store evidence names each resource read with its ETag', () => {
  const ev = remote.evidence
  assert.ok(Array.isArray(ev) && ev.length > 0)
  assert.ok(ev.some((e) => e.resource === storeUrl + 'gen/manifest.sbm11'))
  assert.ok(ev.some((e) => e.resource === storeUrl + 'CURRENT'))
  for (const e of ev) assert.match(e.etag, /^(W\/)?"/)
  assert.ok(ev.some((e) => e.partial > 0), 'no read was answered with 206')
  assert.equal(local.evidence, undefined)
})

test('close and stop the server', () => {
  if (remote) remote.close()
  if (local) local.close()
  if (reader) reader.close()
  if (server) server.kill()
  if (dataDir) rmSync(dataDir, { recursive: true, force: true })
})
