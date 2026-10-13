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

xfail('GSP GET with no graph parameter returns the whole dataset', 'https://github.com/danbri/factoidal/issues/829', async () => {
  const r = await fetch(`${base}/ds/data`, { headers: { accept: 'application/n-quads' } })
  assert.equal(r.status, 200)
})

xfail('GSP GET in JSON-LD', 'https://github.com/danbri/factoidal/issues/830', async () => {
  const r = await fetch(`${base}/ds/data?default`, { headers: { accept: 'application/ld+json' } })
  assert.equal(r.status, 200)
})

xfail('GSP GET in RDF/XML', 'https://github.com/danbri/factoidal/issues/830', async () => {
  const r = await fetch(`${base}/ds/data?default`, { headers: { accept: 'application/rdf+xml' } })
  assert.equal(r.status, 200)
})

xfail('Fuseki administration API /$/ping', 'https://github.com/danbri/factoidal/issues/831', async () => {
  const r = await fetch(`${base}/$/ping`)
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
