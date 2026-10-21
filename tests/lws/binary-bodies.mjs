// Host tests for resource bodies as BYTES in `lws-serve` and `solid-serve`.
// https://github.com/danbri/factoidal/issues/889
//
//   node tests/lws/binary-bodies.mjs
//
// Every decision checked here is made in Lean: the resource model stores a
// `ByteArray` (L4Factoidal/LWS/Model.lean), ranges are byte ranges
// (RFC 9110 §14, `rangeBytes` in L4Factoidal/LWS/Binding.lean), RDF content
// that is not UTF-8 is refused (`rdfContentRefused`), and the snapshot keeps
// bodies as base64 (L4Factoidal/LWS/Snapshot.lean, format lws-snapshot-2).
// The hosts move the bytes through the engine's byte-region entry.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import { mkdtempSync, rmSync, writeFileSync, readFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import http from 'node:http'

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

/** One request with raw bytes in and out (no fetch body decoding). */
function request (origin, method, target, headers = {}, body = undefined) {
  const url = new URL(origin)
  return new Promise((resolve, reject) => {
    const req = http.request({ host: url.hostname, port: url.port, method, path: target, headers },
      (res) => {
        const chunks = []
        res.on('data', (c) => chunks.push(c))
        res.on('end', () => resolve({
          status: res.statusCode, headers: res.headers, body: new Uint8Array(Buffer.concat(chunks))
        }))
      })
    req.on('error', reject)
    if (body !== undefined) req.end(Buffer.from(body)); else req.end()
  })
}

function same (a, b) {
  return a.length === b.length && a.every((x, i) => x === b[i])
}

function show (u) {
  return '[' + Array.from(u).join(',') + ']'
}

// A PNG signature and IHDR start, with NUL and 0xFF bytes and a byte (0x80)
// that is never the start of a UTF-8 sequence.
const PNG_LIKE = new Uint8Array([
  0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a, 0x00, 0x00, 0x00, 0x0d,
  0x49, 0x48, 0x44, 0x52, 0xff, 0x00, 0x80, 0xfe, 0xff, 0xff, 0x00, 0x01])

// UTF-8 text with two-, three- and four-byte sequences, so a range can
// start or end inside each of them.
const MULTIBYTE = new TextEncoder().encode('aé€\u{1F600}z')

const SERVERS = [
  { label: 'lws-serve', module: '../../npm/factoidal/lws/server.mjs', options: { insecureNoAuth: true } },
  { label: 'solid-serve', module: '../../npm/factoidal/solid/server/index.mjs', options: {} }
]

const CHECK_NAMES = [
  'PUT then GET of a PNG-like body is byte-identical',
  'HEAD answers 200 with no content',
  'every byte range of a small binary body answers 206 with exactly that slice',
  'every byte range of UTF-8 text, also inside a multibyte sequence, answers 206',
  'a suffix range answers the last bytes; a range past the end answers 416',
  'POST of a binary body to a container stores it byte for byte',
  'the ETag changes when the bytes change',
  'invalid UTF-8 sent as text/turtle answers 400 and stores nothing',
  'a restarted server reads the binary body back from DIR',
  'a format-1 snapshot (lws-snapshot-1) is still read'
]

async function runServer (server, engine) {
  const mod = await import(server.module)
  const names = CHECK_NAMES.map((n) => `${server.label}: ${n}`)
  const open = (extra) => mod.listen({ engine, port: 0, now: 1000, ...server.options, ...extra })
  const running = await open({})
  const o = running.origin
  try {
    await check(names[0], async () => {
      const put = await request(o, 'PUT', '/img/a.png', { 'content-type': 'image/png' }, PNG_LIKE)
      assert(put.status === 201, `PUT answered ${put.status}`)
      const get = await request(o, 'GET', '/img/a.png')
      assert(get.status === 200, `GET answered ${get.status}`)
      assert(get.headers['content-type'] === 'image/png', `content-type ${get.headers['content-type']}`)
      assert(same(get.body, PNG_LIKE), `got ${show(get.body)}`)
      // Overwrite with other bytes and read again.
      const other = PNG_LIKE.slice().reverse()
      const put2 = await request(o, 'PUT', '/img/a.png', { 'content-type': 'image/png' }, other)
      assert(put2.status === 204, `second PUT answered ${put2.status}`)
      const get2 = await request(o, 'GET', '/img/a.png')
      assert(same(get2.body, other), `after overwrite got ${show(get2.body)}`)
      await request(o, 'PUT', '/img/a.png', { 'content-type': 'image/png' }, PNG_LIKE)
    })

    await check(names[1], async () => {
      const head = await request(o, 'HEAD', '/img/a.png')
      assert(head.status === 200 && head.body.length === 0, `HEAD answered ${head.status} with ${head.body.length} bytes`)
      assert(typeof head.headers.etag === 'string', 'HEAD has no ETag')
    })

    await check(names[2], async () => {
      const n = PNG_LIKE.length
      for (let a = 0; a < n; a++) {
        for (let b = a; b < n; b++) {
          const r = await request(o, 'GET', '/img/a.png', { range: `bytes=${a}-${b}` })
          assert(r.status === 206, `bytes=${a}-${b} answered ${r.status}`)
          assert(same(r.body, PNG_LIKE.slice(a, b + 1)), `bytes=${a}-${b} gave ${show(r.body)}`)
          assert(r.headers['content-range'] === `bytes ${a}-${b}/${n}`,
            `bytes=${a}-${b} Content-Range ${r.headers['content-range']}`)
        }
      }
    })

    await check(names[3], async () => {
      const put = await request(o, 'PUT', '/t.txt', { 'content-type': 'text/plain; charset=utf-8' }, MULTIBYTE)
      assert(put.status === 201, `PUT answered ${put.status}`)
      const n = MULTIBYTE.length
      for (let a = 0; a < n; a++) {
        for (let b = a; b < n; b++) {
          const r = await request(o, 'GET', '/t.txt', { range: `bytes=${a}-${b}` })
          assert(r.status === 206, `bytes=${a}-${b} answered ${r.status}`)
          assert(same(r.body, MULTIBYTE.slice(a, b + 1)), `bytes=${a}-${b} gave ${show(r.body)}`)
        }
      }
      const whole = await request(o, 'GET', '/t.txt')
      assert(same(whole.body, MULTIBYTE), `whole body ${show(whole.body)}`)
    })

    await check(names[4], async () => {
      const n = PNG_LIKE.length
      const s = await request(o, 'GET', '/img/a.png', { range: 'bytes=-5' })
      assert(s.status === 206 && same(s.body, PNG_LIKE.slice(n - 5)), `suffix ${s.status} ${show(s.body)}`)
      assert(s.headers['content-range'] === `bytes ${n - 5}-${n - 1}/${n}`, `Content-Range ${s.headers['content-range']}`)
      const open = await request(o, 'GET', '/img/a.png', { range: `bytes=${n - 3}-` })
      assert(open.status === 206 && same(open.body, PNG_LIKE.slice(n - 3)), `open range ${open.status}`)
      const past = await request(o, 'GET', '/img/a.png', { range: `bytes=${n}-${n + 4}` })
      assert(past.status === 416, `past the end answered ${past.status}`)
      assert(past.headers['content-range'] === `bytes */${n}`, `416 Content-Range ${past.headers['content-range']}`)
    })

    await check(names[5], async () => {
      const post = await request(o, 'POST', '/img/', { 'content-type': 'application/octet-stream', slug: 'blob' }, PNG_LIKE)
      assert(post.status === 201, `POST answered ${post.status}`)
      const loc = post.headers.location
      assert(typeof loc === 'string', 'no Location')
      const path = loc.startsWith('http') ? new URL(loc).pathname : loc
      const get = await request(o, 'GET', path)
      assert(same(get.body, PNG_LIKE), `got ${show(get.body)}`)
    })

    await check(names[6], async () => {
      await request(o, 'PUT', '/e.bin', { 'content-type': 'application/octet-stream' }, new Uint8Array([0, 1, 2]))
      const t1 = (await request(o, 'HEAD', '/e.bin')).headers.etag
      await request(o, 'PUT', '/e.bin', { 'content-type': 'application/octet-stream' }, new Uint8Array([0, 1, 3]))
      const t2 = (await request(o, 'HEAD', '/e.bin')).headers.etag
      assert(typeof t1 === 'string' && typeof t2 === 'string' && t1 !== t2, `tags ${t1} ${t2}`)
    })

    await check(names[7], async () => {
      const bad = new Uint8Array([0x3c, 0x61, 0x3e, 0x20, 0xff, 0xfe, 0x20, 0x2e])
      const put = await request(o, 'PUT', '/bad.ttl', { 'content-type': 'text/turtle' }, bad)
      assert(put.status === 400, `PUT answered ${put.status}`)
      const get = await request(o, 'GET', '/bad.ttl')
      assert(get.status === 404, `the resource was stored (${get.status})`)
      const post = await request(o, 'POST', '/', { 'content-type': 'text/turtle' }, bad)
      assert(post.status === 400, `POST answered ${post.status}`)
      // Positive: valid UTF-8 Turtle is stored.
      const ok = await request(o, 'PUT', '/good.ttl', { 'content-type': 'text/turtle' },
        new TextEncoder().encode('<#a> <#b> "é" .'))
      assert(ok.status === 201, `valid Turtle answered ${ok.status}`)
    })
  } finally {
    await running.close()
  }

  const dir = mkdtempSync(join(tmpdir(), `lb-889-${server.label}-`))
  try {
    await check(names[8], async () => {
      const first = await open({ dir })
      try {
        const r = await request(first.origin, 'PUT', '/kept.png', { 'content-type': 'image/png' }, PNG_LIKE)
        assert(r.status === 201, `PUT answered ${r.status}`)
      } finally {
        await first.close()
      }
      const state = JSON.parse(readFileSync(join(dir, 'lws-state.json'), 'utf8'))
      assert(state.format === 'lws-snapshot-2', `format ${state.format}`)
      const second = await open({ dir })
      try {
        const g = await request(second.origin, 'GET', '/kept.png')
        assert(g.status === 200 && same(g.body, PNG_LIKE), `after restart ${g.status} ${show(g.body)}`)
        const part = await request(second.origin, 'GET', '/kept.png', { range: 'bytes=16-19' })
        assert(part.status === 206 && same(part.body, PNG_LIKE.slice(16, 20)), `range after restart ${show(part.body)}`)
      } finally {
        await second.close()
      }
    })
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }

  const old = mkdtempSync(join(tmpdir(), `lb-889-${server.label}-v1-`))
  try {
    await check(names[9], async () => {
      writeFileSync(join(old, 'lws-state.json'), JSON.stringify({
        format: 'lws-snapshot-1',
        clock: 10,
        entries: [
          { path: '/', kind: 'storageRoot', contentType: 'text/turtle', body: '', mtime: 1 },
          { path: '/note.txt', kind: 'dataResource', contentType: 'text/plain', body: 'café', mtime: 2 }
        ]
      }))
      const s = await open({ dir: old })
      try {
        const g = await request(s.origin, 'GET', '/note.txt')
        assert(g.status === 200 && same(g.body, new TextEncoder().encode('café')), `${g.status} ${show(g.body)}`)
      } finally {
        await s.close()
      }
    })
  } finally {
    rmSync(old, { recursive: true, force: true })
  }
}

async function main () {
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const s of SERVERS) for (const n of CHECK_NAMES) skip(`${s.label}: ${n}`, `the Lean engine did not load: ${error.message}`)
    return
  }
  const ops = engine.call('ops', [])
  const blobIo = Array.isArray(ops.blobIoOps) ? ops.blobIoOps : []
  for (const s of SERVERS) {
    const op = s.label === 'lws-serve' ? 'lwsStep' : 'solidStep'
    if (!blobIo.includes(op)) {
      for (const n of CHECK_NAMES) skip(`${s.label}: ${n}`, `the module does not serve ${op} with byte regions (rebuild the wasm)`)
      continue
    }
    await runServer(s, engine)
  }
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`lws-binary-bodies node: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
