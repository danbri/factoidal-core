// Latency and resident memory of a live `factoidal serve`
// (https://github.com/danbri/factoidal/issues/669 step 1).
//
//   node tests/store-serve/measure.mjs COLLECTION SUBJECT-IRI [REQUESTS]
//
// Starts the server over COLLECTION, then measures:
//   * the time to the first answer (open: read, verify, decode, index);
//   * per-request latency of a bound-subject SELECT over SUBJECT-IRI, REQUESTS
//     times (default 1000), sequentially on one keep-alive connection;
//   * per-request latency of a full scan, `SELECT (COUNT(*) AS ?n)`, 20 times,
//     and of a scan that evaluates a FILTER on every row, 5 times;
//   * the server process's resident set (VmRSS) after the first 100 bound
//     requests and after all of them. The gate is growth of at most 10%.
//
// Prints one JSON object. Linux only (reads /proc).

import { spawn } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { Agent, request } from 'node:http'

const here = dirname(fileURLToPath(import.meta.url))
const cli = join(resolve(here, '../..'), 'npm/factoidal/bin/factoidal.mjs')
const [collection, subject, countText] = process.argv.slice(2)
if (collection === undefined || subject === undefined) {
  console.error('usage: node tests/store-serve/measure.mjs COLLECTION SUBJECT-IRI [REQUESTS]')
  process.exit(2)
}
const requests = Number(countText ?? '1000')

function rssOf (pid) {
  const status = readFileSync(`/proc/${pid}/status`, 'utf8')
  const match = /VmRSS:\s+(\d+) kB/.exec(status)
  return match === null ? null : Number(match[1]) * 1024
}

const started = process.hrtime.bigint()
const child = spawn(process.execPath, [cli, 'serve', collection, '--port', '0', '--quiet'],
  { stdio: ['ignore', 'pipe', 'inherit'] })
const origin = await new Promise((resolveOrigin, reject) => {
  let out = ''
  child.stdout.on('data', (chunk) => {
    out += chunk
    if (out.indexOf('\n') >= 0) resolveOrigin(out.split('\n')[0].trim())
  })
  child.once('exit', (code) => reject(new Error(`serve exited ${code}`)))
})
const openMs = Number(process.hrtime.bigint() - started) / 1e6

const agent = new Agent({ keepAlive: true, maxSockets: 1 })
const url = new URL(origin)

function query (sparql) {
  return new Promise((resolveQuery, reject) => {
    const body = Buffer.from(sparql)
    const t0 = process.hrtime.bigint()
    const req = request({
      host: url.hostname, port: url.port, path: '/sparql', method: 'POST', agent,
      headers: { 'content-type': 'application/sparql-query', accept: 'application/sparql-results+json', 'content-length': body.length }
    }, (res) => {
      const chunks = []
      res.on('data', (c) => chunks.push(c))
      res.on('end', () => resolveQuery({
        status: res.statusCode, ms: Number(process.hrtime.bigint() - t0) / 1e6,
        text: Buffer.concat(chunks).toString('utf8')
      }))
    })
    req.on('error', reject)
    req.end(body)
  })
}

function summary (values) {
  const sorted = [...values].sort((a, b) => a - b)
  const at = (q) => sorted[Math.min(sorted.length - 1, Math.floor(q * sorted.length))]
  return {
    n: sorted.length,
    medianMs: Number(at(0.5).toFixed(2)),
    p95Ms: Number(at(0.95).toFixed(2)),
    maxMs: Number(sorted[sorted.length - 1].toFixed(2)),
    meanMs: Number((sorted.reduce((a, b) => a + b, 0) / sorted.length).toFixed(2))
  }
}

const bound = `SELECT ?p ?o WHERE { <${subject}> ?p ?o }`
const first = await query(bound)
const firstAnswerMs = Number(process.hrtime.bigint() - started) / 1e6
const rows = JSON.parse(first.text).results.bindings.length
const boundTimes = []
let rss100 = null
const rssSeries = []
for (let i = 0; i < requests; i += 1) {
  const r = await query(bound)
  if (r.status !== 200) throw new Error(`bound query answered ${r.status}: ${r.text}`)
  boundTimes.push(r.ms)
  if (i === 99) rss100 = rssOf(child.pid)
  if ((i + 1) % 250 === 0) rssSeries.push([i + 1, rssOf(child.pid)])
}
const rssAfter = rssOf(child.pid)
const scanTimes = []
let scanCount = null
for (let i = 0; i < 20; i += 1) {
  const r = await query('SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }')
  if (r.status !== 200) throw new Error(`scan answered ${r.status}: ${r.text}`)
  scanTimes.push(r.ms)
  scanCount = JSON.parse(r.text).results.bindings[0].n.value
}
// A scan that must evaluate an expression on every row: no count shortcut.
const filterScan = 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o FILTER(isIRI(?o)) }'
const filterTimes = []
let filterCount = null
for (let i = 0; i < 5; i += 1) {
  const r = await query(filterScan)
  if (r.status !== 200) throw new Error(`filtered scan answered ${r.status}: ${r.text}`)
  filterTimes.push(r.ms)
  filterCount = JSON.parse(r.text).results.bindings[0].n.value
}
const rssEnd = rssOf(child.pid)
child.kill('SIGTERM')
agent.destroy()

const growth = rss100 === null ? null : (rssAfter - rss100) / rss100
console.log(JSON.stringify({
  collection,
  serverStartToOriginMs: Number(openMs.toFixed(0)),
  serverStartToFirstAnswerMs: Number(firstAnswerMs.toFixed(0)),
  boundSubject: { query: bound, rows, ...summary(boundTimes) },
  fullScan: { query: 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }', count: scanCount, ...summary(scanTimes) },
  filteredScan: { query: filterScan, count: filterCount, ...summary(filterTimes) },
  rssAfter100Bytes: rss100,
  rssAfterAllBoundBytes: rssAfter,
  rssAfterScansBytes: rssEnd,
  rssGrowthAfter100: growth === null ? null : Number(growth.toFixed(4)),
  rssSeries,
  gateGrowthAtMost10Percent: growth !== null && growth <= 0.10
}, null, 2))
process.exitCode = growth !== null && growth <= 0.10 ? 0 : 1
