// Measure the LWS engine with large bodies: files mode, sealed under a storage key.
// node tests/lws/large-bodies.mjs   (a measurement, not a pass/fail suite; issue https://github.com/danbri/factoidal/issues/1240)
import { mkdtempSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { randomBytes } from 'node:crypto'

const pkg = process.argv[2] || join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'npm', 'factoidal')
const { openLwsStorage } = await import(join(pkg, 'lws/server.mjs'))
const dir = mkdtempSync(join(tmpdir(), 'lws-bulk-'))
const MiB = 1024 * 1024
const rss = () => (process.memoryUsage().rss / MiB).toFixed(0)
const storage = await openLwsStorage({
  baseIri: 'https://pod.example/', dir, storage: 'files', insecureNoAuth: true, realClock: true,
  storageKey: randomBytes(32).toString('hex')
})
const step = (method, target, body, headers = []) =>
  storage.step({ method, target, headers, body: body ?? new Uint8Array(0) })
console.log(`start rss ${rss()} MiB`)
await step('PUT', '/small.txt', new TextEncoder().encode('hi'), [['Content-Type', 'text/plain']])
for (const mb of [1, 10, 50, 100, 200]) {
  const body = new Uint8Array(randomBytes(mb * MiB))
  let t = performance.now()
  let r
  try { r = await step('PUT', `/b${mb}.bin`, body, [['Content-Type', 'application/octet-stream']]) } catch (e) {
    console.log(`${mb} MiB PUT threw: ${e.message.slice(0, 200)}`); break
  }
  const put = performance.now() - t
  const rssPut = rss()
  t = performance.now()
  const g = await step('GET', `/b${mb}.bin`)
  const get = performance.now() - t
  const same = g.body && g.body.length === body.length
  // A small request right after: how long the engine is busy is how long others wait.
  t = performance.now()
  await step('GET', '/small.txt')
  const small = performance.now() - t
  console.log(`${String(mb).padStart(4)} MiB  PUT ${r.status} ${put.toFixed(0).padStart(6)} ms  GET ${g.status} ${get.toFixed(0).padStart(6)} ms  ok=${same}  small GET after ${small.toFixed(1)} ms  rss ${rssPut} → ${rss()} MiB`)
}
// Many medium items: 100 × 1 MiB, then one small GET.
let t = performance.now()
for (let i = 0; i < 100; i++) await step('PUT', `/m/${i}.bin`, new Uint8Array(randomBytes(MiB)), [['Content-Type', 'application/octet-stream']])
console.log(`100 × 1 MiB PUT: ${((performance.now() - t) / 100).toFixed(1)} ms each; rss ${rss()} MiB`)
t = performance.now()
const ls = await step('GET', '/', undefined, [['Accept', 'application/lws+json']])
console.log(`root listing ${ls.status} ${(performance.now() - t).toFixed(1)} ms`)
storage.close()
rmSync(dir, { recursive: true, force: true })
