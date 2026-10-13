// How far `factoidal serve` answers the Apache Jena Fuseki endpoint names.
// Record: docs/fuseki-replacement.md. Each gap is an xfail naming its issue.
// Run: node --test test/fuseki-compat.test.mjs

import test from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { execFileSync, spawn } from 'node:child_process'
import { serveStore } from '../index.mjs'

const cli = join(dirname(fileURLToPath(import.meta.url)), '..', 'bin', 'factoidal.mjs')
const dir = mkdtempSync(join(tmpdir(), 'factoidal-fuseki-'))
writeFileSync(join(dir, 'd.ttl'), '@prefix : <http://ex/> .\n:a :name "Alice" .\n')
const st = join(dir, 'st')
execFileSync(process.execPath, [cli, 'pack', join(dir, 'd.ttl'), join(st, 'gen-1'), '--layout', 'ibk5', '--quiet'])
execFileSync(process.execPath, [cli, 'activate', st, 'gen-1', '--quiet'])

const COUNT = 'SELECT (COUNT(*) AS ?c) WHERE { { ?s ?p ?o } UNION { GRAPH ?g { ?s ?p ?o } } }'
const JSONR = { accept: 'application/sparql-results+json' }
const count = async (base) => {
  const r = await fetch(`${base}/ds/query?query=${encodeURIComponent(COUNT)}`, { headers: JSONR })
  assert.equal(r.status, 200)
  return Number((await r.json()).results.bindings[0].c.value)
}

function xfail (name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async (t) => {
    let failed = false
    try { await fn(t) } catch (error) { failed = true; t.diagnostic(`expected failure: ${String(error.message).slice(0, 160)}`) }
    assert.ok(failed, `unexpected pass: ${name} now works — flip this xfail to an assertion and close ${issueUrl}`)
  })
}

const s = await serveStore(st, { queryPath: '/ds/sparql', gspPath: '/ds/data' })
const base = s.url.replace(/\/ds\/sparql$/, '')
test.after(() => s.close())

test('/ds/query, /ds/update, /ds/get and /ds/data answer as in Fuseki', async () => {
  assert.equal(await count(base), 1)
  let r = await fetch(`${base}/ds/update`, { method: 'POST', headers: { 'content-type': 'application/sparql-update' },
    body: 'INSERT DATA { GRAPH <http://ex/g> { <http://ex/x> <http://ex/p> 1 } }' })
  assert.equal(r.status, 204)
  r = await fetch(`${base}/ds/get?graph=${encodeURIComponent('http://ex/g')}`, { headers: { accept: 'application/n-triples' } })
  assert.equal(r.status, 200)
  assert.match(await r.text(), /<http:\/\/ex\/x>/)
  r = await fetch(`${base}/ds/get?default`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '<http://ex/y> <http://ex/p> 2 .' })
  assert.equal(r.status, 405)
  assert.equal(r.headers.get('allow'), 'GET, HEAD, OPTIONS')
  r = await fetch(`${base}/ds/data?graph=${encodeURIComponent('http://ex/h')}`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '<http://ex/y> <http://ex/p> 2 .' })
  assert.equal(r.status, 201)
  assert.equal(await count(base), 3)
})

test('serve --file DATA /ds: the fuseki-server --file form', async () => {
  const child = spawn(process.execPath, [cli, 'serve', '--file', join(dir, 'd.ttl'), '/ds', '--port', '0', '--no-worker'], { stdio: ['ignore', 'pipe', 'pipe'] })
  try {
    const origin = await new Promise((resolve, reject) => {
      let out = ''
      const onData = (d) => { out += d; const m = out.match(/listening on (http:\/\/\S+)/); if (m) resolve(m[1]) }
      child.stdout.on('data', onData); child.stderr.on('data', onData)
      child.on('exit', (code) => reject(new Error(`serve exited ${code}: ${out}`)))
    })
    assert.equal(await count(origin), 1)
  } finally {
    child.kill()
  }
})

// A store of its own per mutating test, so the counts above stay valid.
async function withServer (turtle, fn) {
  const root = mkdtempSync(join(tmpdir(), 'factoidal-fuseki-w-'))
  writeFileSync(join(root, 'd.ttl'), turtle)
  const store = join(root, 'st')
  execFileSync(process.execPath, [cli, 'pack', join(root, 'd.ttl'), join(store, 'gen-1'), '--layout', 'ibk5', '--quiet'])
  execFileSync(process.execPath, [cli, 'activate', store, 'gen-1', '--quiet'])
  const srv = await serveStore(store, { queryPath: '/ds/sparql', gspPath: '/ds/data' })
  try { await fn(srv.url.replace(/\/ds\/sparql$/, '')) } finally { await srv.close() }
}
const TTL = '@prefix : <http://ex/> .\n:a :name "Alice" .\n'
const NQ = { 'content-type': 'application/n-quads' }

// Issue 829: Graph Store endpoint with no graph parameter.
test('GSP GET with no graph parameter returns the whole dataset (N-Quads, TriG, default graph)', async () => {
  await withServer(TTL, async (b) => {
    let r = await fetch(`${b}/ds/update`, { method: 'POST', headers: { 'content-type': 'application/sparql-update' },
      body: 'INSERT DATA { GRAPH <http://ex/g> { <http://ex/x> <http://ex/p> 1 } }' })
    assert.equal(r.status, 204)
    r = await fetch(`${b}/ds/data`, { headers: { accept: 'application/n-quads' } })
    assert.equal(r.status, 200)
    assert.equal(r.headers.get('content-type'), 'application/n-quads')
    const nq = (await r.text()).split('\n').filter(Boolean).sort()
    assert.deepEqual(nq, [
      '<http://ex/a> <http://ex/name> "Alice" .',
      '<http://ex/x> <http://ex/p> "1"^^<http://www.w3.org/2001/XMLSchema#integer> <http://ex/g> .'
    ])
    r = await fetch(`${b}/ds/data`)
    assert.equal(r.headers.get('content-type'), 'application/n-quads')
    r = await fetch(`${b}/ds/data`, { headers: { accept: 'application/trig' } })
    assert.match(r.headers.get('content-type'), /^application\/trig/)
    assert.match(await r.text(), /<http:\/\/ex\/g> \{/)
    // A triple syntax selects the default graph only.
    r = await fetch(`${b}/ds/data`, { headers: { accept: 'text/turtle' } })
    assert.equal(r.status, 200)
    const ttl = await r.text()
    assert.match(ttl, /Alice/)
    assert.doesNotMatch(ttl, /ex\/x/)
    r = await fetch(`${b}/ds/data`, { method: 'HEAD', headers: { accept: 'application/n-quads' } })
    assert.equal(r.status, 200)
    assert.equal((await r.text()), '')
    // Negative: nothing acceptable.
    r = await fetch(`${b}/ds/data`, { headers: { accept: 'image/png' } })
    assert.equal(r.status, 406)
  })
})

test('GSP PUT with no graph parameter replaces the dataset; POST adds to it', async () => {
  await withServer(TTL, async (b) => {
    let r = await fetch(`${b}/ds/data`, { method: 'PUT', headers: NQ,
      body: '<http://ex/s> <http://ex/p> <http://ex/o> <http://ex/h> .\n<http://ex/s> <http://ex/p> <http://ex/o2> .\n' })
    assert.equal(r.status, 204)
    assert.equal(await count(b), 2)
    // The old default-graph triple is gone.
    r = await fetch(`${b}/ds/query?query=${encodeURIComponent('ASK { <http://ex/a> ?p ?o }')}`, { headers: JSONR })
    assert.equal((await r.json()).boolean, false)
    // POST adds, with TriG as well.
    r = await fetch(`${b}/ds/data`, { method: 'POST', headers: NQ, body: '<http://ex/t> <http://ex/p> <http://ex/o> <http://ex/h> .\n' })
    assert.equal(r.status, 204)
    r = await fetch(`${b}/ds/data`, { method: 'POST', headers: { 'content-type': 'application/trig' },
      body: '<http://ex/k> { <http://ex/u> <http://ex/p> <http://ex/o> . }' })
    assert.equal(r.status, 204)
    assert.equal(await count(b), 4)
    // POST of a triple syntax keeps the Graph Store meaning: a new graph.
    r = await fetch(`${b}/ds/data`, { method: 'POST', headers: { 'content-type': 'text/turtle' }, body: '<http://ex/v> <http://ex/p> 3 .' })
    assert.equal(r.status, 201)
    assert.ok(r.headers.get('location'))
    assert.equal(await count(b), 5)
  })
})

test('GSP on the dataset: refusals', async () => {
  await withServer(TTL, async (b) => {
    let r = await fetch(`${b}/ds/data`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '<http://ex/s> <http://ex/p> 1 .' })
    assert.equal(r.status, 415)
    r = await fetch(`${b}/ds/data`, { method: 'PUT', headers: NQ, body: '<http://ex/s> <http://ex/p>' })
    assert.equal(r.status, 400)
    r = await fetch(`${b}/ds/data`, { method: 'DELETE' })
    assert.equal(r.status, 405)
    assert.equal(r.headers.get('allow'), 'GET, HEAD, POST, PUT, OPTIONS')
    assert.equal(await count(b), 1)
    // DELETE of one graph still works.
    r = await fetch(`${b}/ds/data?default`, { method: 'DELETE' })
    assert.equal(r.status, 204)
    assert.equal(await count(b), 0)
  })
})

// Issue 830: RDF/XML.
const CONSTRUCT = 'CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }'
test('CONSTRUCT, DESCRIBE and the Graph Store answer application/rdf+xml', async () => {
  await withServer(TTL, async (b) => {
    for (const [query, name] of [[CONSTRUCT, 'CONSTRUCT'], ['DESCRIBE <http://ex/a>', 'DESCRIBE']]) {
      const r = await fetch(`${b}/ds/query`, { method: 'POST',
        headers: { 'content-type': 'application/sparql-query', accept: 'application/rdf+xml' }, body: query })
      assert.equal(r.status, 200, name)
      assert.match(r.headers.get('content-type'), /^application\/rdf\+xml/)
      const xml = await r.text()
      assert.match(xml, /<rdf:RDF/)
      assert.match(xml, /rdf:about="http:\/\/ex\/a"/)
      assert.match(xml, /Alice/)
    }
    let r = await fetch(`${b}/ds/data?default`, { headers: { accept: 'application/rdf+xml' } })
    assert.equal(r.status, 200)
    assert.match(r.headers.get('content-type'), /^application\/rdf\+xml/)
    // Unchanged defaults and a refusal.
    r = await fetch(`${b}/ds/query`, { method: 'POST',
      headers: { 'content-type': 'application/sparql-query', accept: '*/*' }, body: CONSTRUCT })
    assert.match(r.headers.get('content-type'), /^text\/turtle/)
    r = await fetch(`${b}/ds/query`, { method: 'POST',
      headers: { 'content-type': 'application/sparql-query', accept: 'application/rdf+xml;q=0' }, body: CONSTRUCT })
    assert.equal(r.status, 406)
  })
})

test('RDF/XML for a graph that has no RDF/XML form: 406, or the next acceptable syntax', async () => {
  // The predicate IRI ends in a digit, so it is no XML QName (RDF/XML 1.1 section 7.2.2).
  await withServer('<http://ex/a> <http://ex/9> <http://ex/b> .\n', async (b) => {
    const post = (accept) => fetch(`${b}/ds/query`, { method: 'POST',
      headers: { 'content-type': 'application/sparql-query', accept }, body: CONSTRUCT })
    assert.equal((await post('application/rdf+xml')).status, 406)
    const r = await post('application/rdf+xml, text/turtle;q=0.5')
    assert.equal(r.status, 200)
    assert.match(r.headers.get('content-type'), /^text\/turtle/)
  })
})

// Issue 831: the read-only administration API.
test('/$/ping, /$/datasets, /$/stats and /$/server answer with the Fuseki JSON members', async () => {
  await withServer(TTL, async (b) => {
    let r = await fetch(`${b}/$/ping`)
    assert.equal(r.status, 200)
    assert.match(r.headers.get('content-type'), /^text\/plain/)
    assert.match(await r.text(), /^\d{4}-\d\d-\d\dT/)
    r = await fetch(`${b}/$/datasets`)
    assert.equal(r.status, 200)
    assert.match(r.headers.get('content-type'), /^application\/json/)
    const ds = await r.json()
    assert.equal(ds.datasets.length, 1)
    assert.equal(ds.datasets[0]['ds.name'], '/ds')
    assert.equal(ds.datasets[0]['ds.state'], true)
    const types = Object.fromEntries(ds.datasets[0]['ds.services'].map((x) => [x['srv.type'], x['srv.endpoints']]))
    assert.deepEqual(types['gsp-rw'], ['data'])
    assert.deepEqual(types.query, ['sparql', 'query'])
    assert.deepEqual(types.update, ['sparql', 'update'])
    assert.equal((await (await fetch(`${b}/$/datasets/ds`)).json())['ds.name'], '/ds')
    // Counters: two good queries and one bad one.
    await count(b)
    await count(b)
    r = await fetch(`${b}/ds/query?query=${encodeURIComponent('NOT SPARQL')}`)
    assert.equal(r.status, 400)
    const stats = (await (await fetch(`${b}/$/stats`)).json()).datasets['/ds']
    assert.equal(stats.Requests, 3)
    assert.equal(stats.RequestsGood, 2)
    assert.equal(stats.RequestsBad, 1)
    assert.equal(stats.endpoints.query.Requests, 3)
    assert.equal(stats.endpoints.query.operation, 'query')
    assert.equal(stats.endpoints.update.Requests, 0)
    assert.equal((await (await fetch(`${b}/$/stats/ds`)).json()).Requests, 3)
    r = await fetch(`${b}/$/server`)
    const server = await r.json()
    assert.match(server.version, /Factoidal/)
    assert.match(server.startDateTime, /^\d{4}-\d\d-\d\dT/)
    assert.equal(typeof server.uptime, 'number')
    assert.equal(server.datasets[0]['ds.name'], '/ds')
  })
})

test('/$/ administration API: the operations that change the server are refused', async () => {
  await withServer(TTL, async (b) => {
    let r = await fetch(`${b}/$/datasets`, { method: 'POST', body: 'dbName=x&dbType=mem',
      headers: { 'content-type': 'application/x-www-form-urlencoded' } })
    assert.equal(r.status, 405)
    assert.equal(r.headers.get('allow'), 'GET, HEAD, OPTIONS')
    assert.equal((await fetch(`${b}/$/datasets/ds`, { method: 'DELETE' })).status, 405)
    assert.equal((await fetch(`${b}/$/datasets/nope`)).status, 404)
    assert.equal((await fetch(`${b}/$/backup/ds`, { method: 'POST' })).status, 404)
    assert.equal((await fetch(`${b}/ping`)).status, 404)
  })
})


xfail('GSP GET in JSON-LD', 'https://github.com/danbri/factoidal/issues/830', async () => {
  const r = await fetch(`${base}/ds/data?default`, { headers: { accept: 'application/ld+json' } })
  assert.equal(r.status, 200)
})

// `fuseki-server --loc DB /ds` serves a TDB2 database in place. The Lean
// decoder reads TDB2 (`l4factoidal tdb2-dump DIR`, `--format tdb2`), but the
// npm `serve` command has no --tdb2 option yet.
xfail('serve --tdb2 DIR /ds (TDB2 database in place)', 'https://github.com/danbri/factoidal/issues/834', async () => {
  const tdb = mkdtempSync(join(tmpdir(), 'factoidal-tdb2-'))
  const p = spawn(process.execPath, [cli, 'serve', '--tdb2', tdb, '/ds', '--port', '0'], { stdio: 'ignore' })
  const code = await new Promise((resolve) => {
    const timer = setTimeout(() => resolve(null), 3000)
    p.on('exit', (c) => { clearTimeout(timer); resolve(c) })
  })
  if (code === null) p.kill()
  assert.equal(code, null, `serve --tdb2 exited with code ${code}`)
})
