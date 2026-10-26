// `fuseki-server --loc DB /ds` serves a TDB2 database in place:
// `serve --tdb2 DIR /ds` reads the database with the Lean decoder
// (formal/lean4/L4Factoidal/Tdb2/Read.lean) and serves it read only
// (https://github.com/danbri/factoidal/issues/834). The database is built
// with Apache Jena's own loader, because a TDB2 database is several 8 MiB
// sparse files and cannot be committed as a small fixture.
//
// This file is not in `npm test`: run it with `npm run test:jena` after
// `python3 tools/sota-bench.py --install` (SOTA_DL names the install
// directory, default /tmp/sota-dl). Without Jena the test FAILS; it does not
// skip (https://github.com/danbri/factoidal/issues/1038, P2).

import test from 'node:test'
import assert from 'node:assert/strict'
import { existsSync, mkdtempSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { execFileSync, spawn } from 'node:child_process'
import { serveStore } from '../../index.mjs'

const cli = join(dirname(fileURLToPath(import.meta.url)), '..', '..', 'bin', 'factoidal.mjs')
const dir = mkdtempSync(join(tmpdir(), 'factoidal-tdb2-'))
const jenaBin = join(process.env.SOTA_DL || '/tmp/sota-dl', 'apache-jena-6.2.0', 'bin')

const COUNT = 'SELECT (COUNT(*) AS ?c) WHERE { { ?s ?p ?o } UNION { GRAPH ?g { ?s ?p ?o } } }'
const JSONR = { accept: 'application/sparql-results+json' }
const count = async (base) => {
  const r = await fetch(`${base}/ds/query?query=${encodeURIComponent(COUNT)}`, { headers: JSONR })
  assert.equal(r.status, 200)
  return Number((await r.json()).results.bindings[0].c.value)
}

test('serve --tdb2 DIR /ds: a TDB2 database in place, read only', async () => {
  assert.ok(existsSync(join(jenaBin, 'tdb2.tdbloader')),
    `no Jena at ${jenaBin}: run python3 tools/sota-bench.py --install with SOTA_DL set`)
  const tdbDir = join(dir, 'tdb')
  writeFileSync(join(dir, 'tdb.trig'),
    '@prefix : <http://ex/> .\n:a :name "Alice" ; :age 42 .\n:b :name "Bob" .\n' +
    ':g { :c :name "Carol" ; :height 1.75 . }\n')
  execFileSync(join(jenaBin, 'tdb2.tdbloader'), ['--loc', tdbDir, join(dir, 'tdb.trig')], { stdio: 'ignore' })
  const child = spawn(process.execPath, [cli, 'serve', '--tdb2', tdbDir, '/ds', '--port', '0'], { stdio: ['ignore', 'pipe', 'pipe'] })
  try {
    const origin = await new Promise((resolve, reject) => {
      let buf = ''
      let errText = ''
      child.stdout.on('data', (d) => { buf += d; const m = buf.match(/http:\/\/\S+/); if (m) resolve(m[0]) })
      child.stderr.on('data', (d) => { errText += d })
      child.on('exit', (c) => reject(new Error(`serve --tdb2 exited with code ${c}: ${errText.slice(0, 300)}`)))
      setTimeout(() => reject(new Error('serve --tdb2 did not start in 20 s')), 20000)
    })
    // SPARQL query over the default graph and the named graph.
    assert.equal(await count(origin), 5)
    const q = 'SELECT ?n WHERE { ?s <http://ex/age> ?n }'
    let r = await fetch(`${origin}/ds/sparql?query=${encodeURIComponent(q)}`, { headers: JSONR })
    assert.equal(r.status, 200)
    // TDB2 stores the integer by value and prints it back as "42".
    assert.equal((await r.json()).results.bindings[0].n.value, '42')
    // Graph Store GET of the named graph.
    r = await fetch(`${origin}/ds/data?graph=${encodeURIComponent('http://ex/g')}`, { headers: { accept: 'application/n-triples' } })
    assert.equal(r.status, 200)
    assert.match(await r.text(), /Carol/)
    // Every write answers 501 with a message, and changes nothing.
    r = await fetch(`${origin}/ds/update`, { method: 'POST', headers: { 'content-type': 'application/sparql-update' },
      body: 'INSERT DATA { <http://ex/x> <http://ex/p> 1 }' })
    assert.equal(r.status, 501)
    assert.match(await r.text(), /read-only/)
    r = await fetch(`${origin}/ds/data?graph=${encodeURIComponent('http://ex/h')}`, { method: 'PUT',
      headers: { 'content-type': 'text/turtle' }, body: '<http://ex/y> <http://ex/p> 2 .' })
    assert.equal(r.status, 501)
    assert.equal(await count(origin), 5)
    // The same database through the library entry point.
    const lib = await serveStore(tdbDir, { tdb2: true, queryPath: '/ds/sparql', gspPath: '/ds/data' })
    try {
      assert.equal(await count(lib.url.replace(/\/ds\/sparql$/, '')), 5)
    } finally {
      await lib.close()
    }
  } finally {
    child.kill()
  }
})
