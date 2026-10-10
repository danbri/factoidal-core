// Gates for `factoidal serve` (https://github.com/danbri/factoidal/issues/669
// step 1): the live server against `factoidal query`, against the in-memory
// Lean engine over the source file, and against the native delta-log tools.
//
//   node tests/store-serve/serve.mjs
//
// Prints "N pass, M fail, X expected failures (out of T)". An expected
// failure names its issue; one that starts to pass is STALE and fails the
// run (CLAUDE.md, "A stated shortfall is a failing test plus an open issue").
//
// WHAT IT GATES
//  1. Queries only the reference semantics decide — FILTER NOT EXISTS,
//     FILTER EXISTS, MINUS, OPTIONAL with FILTER, a sub-SELECT — answered by
//     the live server, by `factoidal query` over the same collection, and by
//     the in-memory Lean engine (`l4factoidal query`) over the source file;
//     the three row sets must be equal and non-empty (CLAUDE.md
//     anti-pattern 34).
//  2. An update through the server, then a query showing it, through the
//     server and through the native `l4block-id-v3-query` (which replays the
//     same delta log); then `l4block-shard-compact` and activation of the new
//     generation, a restarted server, and the same query again.
//  3. The write scope: an IBK3 generation refuses a named-graph change (501)
//     and stores nothing; a quad generation stores it and serves it.
//  4. HTTP framing decided by the engine: two pipelined requests on one
//     connection get two responses; a chunked body is read; a malformed
//     request line is refused.
//
// Requires the native binaries (`lake build` in formal/lean4) and a wasm
// module with the storeServe ops (Wasm/build-wasm.sh). Without the ops the
// suite reports every check as skipped, never as passed.

import { spawn, spawnSync } from 'node:child_process'
import { mkdtempSync, rmSync, writeFileSync, existsSync } from 'node:fs'
import { connect } from 'node:net'
import { tmpdir } from 'node:os'
import { join, dirname, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const here = dirname(fileURLToPath(import.meta.url))
const repo = resolve(here, '../..')
const cli = join(repo, 'npm/factoidal/bin/factoidal.mjs')
const bin = process.env.L4_BIN ?? join(repo, 'formal/lean4/.lake/build/bin')
const work = mkdtempSync(join(tmpdir(), 'store-serve-'))

const EXPECTED_FAILURES = {
  'native quad query sees a server update':
    'https://github.com/danbri/factoidal/issues/770'
}

let pass = 0
let fail = 0
let xfail = 0
let skipped = 0
const failures = []

function record (name, ok, detail = '') {
  const issue = EXPECTED_FAILURES[name]
  if (issue !== undefined) {
    if (ok) {
      fail += 1
      failures.push(name)
      console.log(`STALE ${name}: passes, but is listed as an expected failure (${issue})`)
    } else {
      xfail += 1
      console.log(`XFAIL ${name} (${issue}) ${detail}`)
    }
    return
  }
  if (ok) {
    pass += 1
    console.log(`PASS ${name}`)
  } else {
    fail += 1
    failures.push(name)
    console.log(`FAIL ${name} ${detail}`)
  }
}

function run (command, args, options = {}) {
  const out = spawnSync(command, args, { encoding: 'utf8', timeout: 600000, ...options })
  if (out.status !== 0) {
    throw new Error(`${command} ${args.join(' ')} exited ${out.status}: ${out.stderr}${out.stdout}`)
  }
  return out.stdout
}

function pack (input, collection, generation, layout) {
  run(join(bin, 'l4block-shard-pack'), [input, join(collection, generation), layout])
  run(join(bin, 'l4block-shard-activate'), [collection, generation])
}

/** Start `factoidal serve`; resolves with { origin, stop }. */
function startServer (collection) {
  return new Promise((resolveStart, reject) => {
    const child = spawn(process.execPath, [cli, 'serve', collection, '--port', '0', '--quiet'],
      { stdio: ['ignore', 'pipe', 'pipe'] })
    let stdout = ''
    let stderr = ''
    child.stderr.on('data', (chunk) => { stderr += chunk })
    child.stdout.on('data', (chunk) => {
      stdout += chunk
      const line = stdout.split('\n')[0]
      if (stdout.indexOf('\n') >= 0) {
        if (line.startsWith('http://')) {
          resolveStart({
            origin: line.trim(),
            stop: () => new Promise((done) => { child.once('exit', done); child.kill('SIGTERM') })
          })
        } else reject(new Error(`serve printed ${line}: ${stderr}`))
      }
    })
    child.once('exit', (code) => reject(new Error(`serve exited ${code}: ${stderr}`)))
  })
}

async function sparql (origin, query, extra = {}) {
  const response = await fetch(`${origin}/sparql`, {
    method: 'POST',
    headers: { 'content-type': 'application/sparql-query', accept: 'application/sparql-results+json', ...extra },
    body: query
  })
  return { status: response.status, text: await response.text(), type: response.headers.get('content-type') }
}

async function update (origin, text) {
  const response = await fetch(`${origin}/sparql`, {
    method: 'POST', headers: { 'content-type': 'application/sparql-update' }, body: text
  })
  return { status: response.status, text: await response.text() }
}

/** A SPARQL Results JSON document as a sorted list of row strings. */
function rowsOf (srjText) {
  const srj = JSON.parse(srjText)
  const vars = srj.head.vars
  return srj.results.bindings
    .map((b) => vars.map((v) => (b[v] === undefined ? '' : `${b[v].type}:${b[v].value}:${b[v]['xml:lang'] ?? ''}:${b[v].datatype ?? ''}`)).join('|'))
    .sort()
}

function same (a, b) { return JSON.stringify(a) === JSON.stringify(b) }

const EX = 'http://example.org/'
const DATA = `@prefix ex: <${EX}> .
ex:a ex:knows ex:b . ex:b ex:knows ex:c . ex:c ex:knows ex:a . ex:d ex:knows ex:a .
ex:a ex:age 30 . ex:b ex:age 17 . ex:c ex:age 45 .
ex:a ex:name "Alice" . ex:b ex:name "Bob" . ex:d ex:name "Dan" .
ex:b ex:blocked ex:c .
`
const REFERENCE_QUERIES = {
  'FILTER NOT EXISTS': `PREFIX ex: <${EX}> SELECT ?s ?o WHERE { ?s ex:knows ?o FILTER NOT EXISTS { ?s ex:blocked ?o } }`,
  'FILTER EXISTS': `PREFIX ex: <${EX}> SELECT ?s WHERE { ?s ex:knows ?o FILTER EXISTS { ?o ex:age ?x } }`,
  MINUS: `PREFIX ex: <${EX}> SELECT ?s WHERE { ?s ex:knows ?o MINUS { ?s ex:age ?a } }`,
  'OPTIONAL with FILTER': `PREFIX ex: <${EX}> SELECT ?s ?a WHERE { ?s ex:name ?n OPTIONAL { ?s ex:age ?a FILTER(?a > 20) } }`,
  'sub-SELECT': `PREFIX ex: <${EX}> SELECT ?s ?c WHERE { ?s ex:name ?n { SELECT ?s (COUNT(?o) AS ?c) WHERE { ?s ex:knows ?o } GROUP BY ?s } }`
}

function opsPresent () {
  const probe = spawnSync(process.execPath, ['-e', `
    import('${join(repo, 'npm/factoidal/bin/engine.mjs')}').then(async (m) => {
      const e = await m.loadEngine()
      try { e.call('storeServeKeys', ['00']) } catch (err) {
        if (String(err.message).indexOf('unknown op') >= 0) { console.log('absent'); return }
      }
      console.log('present')
    }).catch((err) => console.log('noengine ' + err.message))`], { encoding: 'utf8' })
  return probe.stdout.trim()
}

async function main () {
  const ops = opsPresent()
  if (ops !== 'present') {
    console.log(`SKIP every check: the loaded engine does not carry the storeServe ops (${ops})`)
    skipped = 1
    return
  }
  const source = join(work, 'data.ttl')
  writeFileSync(source, DATA)

  // --- 1. reference-only queries: server, factoidal query, in-memory ------
  const col3 = join(work, 'ibk3')
  pack(source, col3, 'gen-1', 'ibk3')
  let server = await startServer(col3)
  for (const [name, query] of Object.entries(REFERENCE_QUERIES)) {
    const live = await sparql(server.origin, query)
    const viaQuery = run(process.execPath, [cli, 'query', col3, query, '--format', 'json', '--quiet'])
    const inMemory = run(join(bin, 'l4factoidal'), ['query', source, '--query-string', query])
    const a = live.status === 200 ? rowsOf(live.text) : [`status ${live.status}: ${live.text}`]
    const b = rowsOf(viaQuery)
    const c = rowsOf(inMemory)
    record(`${name}: live server = factoidal query = in-memory engine`,
      a.length > 0 && same(a, b) && same(a, c), `live=${JSON.stringify(a)} query=${JSON.stringify(b)} memory=${JSON.stringify(c)}`)
  }

  // --- 2. update, query, compact, query ----------------------------------
  const probe = `PREFIX ex: <${EX}> SELECT ?o WHERE { ex:e ex:knows ?o }`
  const before = await sparql(server.origin, probe)
  record('before the update the probe answers no row', before.status === 200 && rowsOf(before.text).length === 0)
  const u = await update(server.origin,
    `PREFIX ex: <${EX}> INSERT { ex:e ex:knows ?s } WHERE { ?s ex:age ?a FILTER(?a > 40) }`)
  record('a WHERE-dependent update through the server is accepted', u.status >= 200 && u.status < 300, `status ${u.status} ${u.text}`)
  const after = await sparql(server.origin, probe)
  const expected = [`uri:${EX}c::`]
  record('the server answers the update at once', same(rowsOf(after.text), expected), after.text)
  const inspect = run(join(bin, 'l4block-delta-log'), [join(col3, 'gen-1'), '--inspect'])
  record('the native delta-log tool reads the batch the server wrote',
    /committed-batches=1 /.test(inspect) && /clean-tail=true/.test(inspect), inspect.trim())
  const native = run(join(bin, 'l4block-id-v3-query'), [col3, '--query', probe])
  record('the native IBK3 query replays the same delta log', /delta=base-plus-delta/.test(native) && native.indexOf(`${EX}c`) >= 0, native.trim().slice(0, 300))
  // A named-graph change on an IBK3 generation is refused and stores nothing.
  const refused = await update(server.origin, `INSERT DATA { GRAPH <${EX}g> { <${EX}x> <${EX}y> <${EX}z> } }`)
  const inspect2 = run(join(bin, 'l4block-delta-log'), [join(col3, 'gen-1'), '--inspect'])
  record('an IBK3 generation refuses a named-graph change with 501 and stores nothing',
    refused.status === 501 && /committed-batches=1 /.test(inspect2), `status ${refused.status}; ${inspect2.trim()}`)
  await server.stop()
  run(join(bin, 'l4block-shard-compact'), [join(col3, 'gen-1'), join(col3, 'gen-2')])
  run(join(bin, 'l4block-shard-activate'), [col3, 'gen-2'])
  server = await startServer(col3)
  const compacted = await sparql(server.origin, probe)
  record('after compaction and activation the same query answers the same rows', same(rowsOf(compacted.text), expected), compacted.text)
  const all = await sparql(server.origin, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }')
  record('the compacted generation holds the base plus the update (12 triples)',
    rowsOf(all.text)[0] === 'literal:12::http://www.w3.org/2001/XMLSchema#integer', all.text)

  // --- 4. framing --------------------------------------------------------
  const pipelined = await raw(server.origin,
    'GET /sparql?query=ASK%7B%7D HTTP/1.1\r\nHost: x\r\n\r\n' +
    'GET /sparql?query=ASK%7B%7D HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n')
  record('two pipelined requests get two responses', (pipelined.match(/HTTP\/1\.1 200 OK/g) ?? []).length === 2, pipelined.slice(0, 200))
  const body = `ASK { <${EX}a> ?p ?o }`
  const chunked = await raw(server.origin,
    'POST /sparql HTTP/1.1\r\nHost: x\r\nContent-Type: application/sparql-query\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n' +
    `${Buffer.byteLength(body).toString(16)}\r\n${body}\r\n0\r\n\r\n`)
  record('a chunked request body is read', /HTTP\/1\.1 200 OK/.test(chunked) && /true/.test(chunked), chunked.slice(0, 300))
  const malformed = await raw(server.origin, 'GARBAGE\r\n\r\n')
  record('a malformed request line is refused with 400', /^HTTP\/1\.1 400 /.test(malformed), malformed.slice(0, 120))
  await server.stop()

  // --- 3. a quad generation takes named-graph changes --------------------
  const quads = join(work, 'quads.nq')
  writeFileSync(quads, `<${EX}a> <${EX}p> "x" <${EX}g1> .\n<${EX}b> <${EX}p> "y" .\n`)
  const col5 = join(work, 'ibk5')
  pack(quads, col5, 'gen-1', 'ibk5')
  server = await startServer(col5)
  const q5 = `SELECT ?g ?o WHERE { GRAPH ?g { <${EX}new> <${EX}p> ?o } }`
  const u5 = await update(server.origin, `INSERT DATA { GRAPH <${EX}g2> { <${EX}new> <${EX}p> "z" } }`)
  const r5 = await sparql(server.origin, q5)
  record('a quad generation stores a named-graph change and serves it',
    u5.status >= 200 && u5.status < 300 && same(rowsOf(r5.text), [`uri:${EX}g2::|literal:z::`]), `${u5.status} ${r5.text}`)
  const put = await fetch(`${server.origin}/data?graph=${encodeURIComponent(EX + 'g3')}`,
    { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: `<${EX}s> <${EX}p> <${EX}o> .` })
  const get = await fetch(`${server.origin}/data?graph=${encodeURIComponent(EX + 'g3')}`, { headers: { accept: 'application/n-triples' } })
  const getText = await get.text()
  record('a Graph Store PUT is stored and a GET returns it',
    put.status === 201 && get.status === 200 && getText.trim() === `<${EX}s> <${EX}p> <${EX}o> .`, `${put.status} ${get.status} ${getText}`)
  await server.stop()
  server = await startServer(col5)
  const r5b = await sparql(server.origin, q5)
  record('a restarted server replays the quad generation delta log', same(rowsOf(r5b.text), [`uri:${EX}g2::|literal:z::`]), r5b.text)
  await server.stop()
  const nativeQuad = spawnSync(join(bin, 'l4block-quad-query'), [col5, '--query', q5], { encoding: 'utf8' })
  record('native quad query sees a server update', nativeQuad.stdout.indexOf('"z"') >= 0 || nativeQuad.stdout.indexOf('rows=1') >= 0,
    (nativeQuad.stdout + nativeQuad.stderr).trim().slice(0, 200))
}

function raw (origin, text) {
  const url = new URL(origin)
  return new Promise((resolveRaw, reject) => {
    const socket = connect(Number(url.port), url.hostname, () => socket.write(text))
    let out = ''
    socket.on('data', (chunk) => { out += chunk })
    socket.on('end', () => resolveRaw(out))
    socket.on('error', reject)
    socket.setTimeout(30000, () => { socket.destroy(); resolveRaw(out) })
  })
}

try {
  await main()
} catch (error) {
  fail += 1
  failures.push(`harness: ${error.message}`)
  console.log(`FAIL harness: ${error.stack}`)
} finally {
  if (existsSync(work)) rmSync(work, { recursive: true, force: true })
}
const total = pass + fail + xfail
console.log(`store-serve: ${pass} pass, ${fail} fail, ${xfail} expected failures, ${skipped} skipped (out of ${total})`)
process.exitCode = fail === 0 && skipped === 0 ? 0 : 1
