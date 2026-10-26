// The `factoidal` command on an SBM11 store
// (https://github.com/danbri/factoidal/issues/1009, the SBM11 store in npm).
//
// `factoidal pack --layout sbm11` of the input of test/fixtures/sbm11-tiny
// must write every file that native `l4sbm11-pack` wrote for it (root/gen),
// byte for byte. `activate` must check the files (op sbm11Verify) before
// CURRENT moves; `query` and `inspect` must read the store through the ops
// storeLayout and sbm11Open / sbm11Query; `serve` must refuse it.
//
// The package wasm must serve those ops: a wasm without them fails these
// cases, never skips them (https://github.com/danbri/factoidal/issues/1038).
// No RDF logic here: the cases compare bytes and strings the engine wrote.

import test from 'node:test'
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import {
  cpSync, existsSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync
} from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'

const ISSUE = 'https://github.com/danbri/factoidal/issues/1009'
const HERE = dirname(fileURLToPath(import.meta.url))
const CLI = join(HERE, '..', 'bin', 'factoidal.mjs')
const FIX = join(HERE, 'fixtures', 'sbm11-tiny')
const QUERIES = new Map(JSON.parse(readFileSync(join(FIX, 'queries.json'), 'utf8')))

function run (args) {
  const r = spawnSync(process.execPath, [CLI, ...args], { encoding: 'utf8' })
  return { code: r.status, stdout: r.stdout, stderr: r.stderr }
}

function ok (args) {
  const r = run(args)
  assert.equal(r.code, 0, `factoidal ${args.join(' ')} exited ${r.code}: ${r.stderr}`)
  return r
}

function expected (name) {
  return readFileSync(join(FIX, 'expected', name + '.out'), 'utf8')
}

/** A temporary directory with STORE/gen packed from the fixture input. */
function packedStore () {
  const dir = mkdtempSync(join(tmpdir(), 'factoidal-1009-'))
  const store = join(dir, 'store')
  ok(['pack', join(FIX, 'input.nq'), join(store, 'gen'), '--layout', 'sbm11', '--quiet'])
  return { dir, store }
}

test(`pack --layout sbm11 writes the files of l4sbm11-pack, byte for byte (${ISSUE})`, () => {
  const { dir, store } = packedStore()
  try {
    const want = readdirSync(join(FIX, 'root', 'gen')).sort()
    assert.deepEqual(readdirSync(join(store, 'gen')).sort(), want)
    for (const name of want) {
      assert.ok(readFileSync(join(store, 'gen', name)).equals(readFileSync(join(FIX, 'root', 'gen', name))),
        `${name} differs from the native file`)
    }
    assert.equal(existsSync(join(store, 'CURRENT')), false, 'pack does not activate')
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})

test(`activate, query and inspect an SBM11 store give the answers of l4sbm11 query (${ISSUE})`, () => {
  const { dir, store } = packedStore()
  try {
    const act = ok(['activate', store, 'gen', '--json'])
    const verdict = JSON.parse(act.stdout)
    assert.equal(verdict.ok, true)
    assert.equal(verdict.layout, 'sbm11')
    assert.equal(readFileSync(join(store, 'CURRENT'), 'utf8'), 'gen')

    for (const name of ['count', 'names', 'graph', 'ask']) {
      const r = ok(['query', store, QUERIES.get(name), '--json', '--quiet'])
      assert.deepEqual(JSON.parse(r.stdout), JSON.parse(expected(name)), name)
    }
    const c = ok(['query', store, QUERIES.get('construct'), '--format', 'nquads', '--quiet'])
    // the command prints the engine's N-Triples and one line break
    assert.equal(c.stdout.replace(/\n$/, ''), expected('construct').replace(/\n$/, ''))

    const table = ok(['query', store, QUERIES.get('count')])
    assert.match(table.stderr, /^path=ids, /m)

    const inspect = JSON.parse(ok(['inspect', store, '--json']).stdout)
    assert.equal(inspect.layout, 'sbm11')
    assert.equal(inspect.generation, 'gen')
    assert.equal(inspect.activated, true)
    assert.equal(inspect.manifest, 'manifest.sbm11')
    assert.equal(inspect.files, readdirSync(join(FIX, 'root', 'gen')).length)
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})

test(`activate refuses an SBM11 generation with a changed file and leaves CURRENT (${ISSUE})`, () => {
  const { dir, store } = packedStore()
  try {
    cpSync(join(store, 'gen'), join(store, 'bad'), { recursive: true })
    const file = join(store, 'bad', 'dict.gdv1')
    const bytes = readFileSync(file)
    bytes[0] ^= 0xff
    writeFileSync(file, bytes)
    ok(['activate', store, 'gen', '--quiet'])
    const r = run(['activate', store, 'bad'])
    assert.equal(r.code, 1, r.stderr)
    assert.match(r.stderr, /dict\.gdv1/)
    assert.match(r.stderr, /NOT activated/)
    assert.equal(readFileSync(join(store, 'CURRENT'), 'utf8'), 'gen')
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})

test(`query --explain and serve refuse an SBM11 store with a reason (${ISSUE})`, () => {
  const { dir, store } = packedStore()
  try {
    ok(['activate', store, 'gen', '--quiet'])
    const e = run(['query', store, QUERIES.get('count'), '--explain'])
    assert.equal(e.code, 1)
    assert.match(e.stderr, /no plan operation for an SBM11 store/)
    const s = run(['serve', store, '--port', '0'])
    assert.equal(s.code, 1)
    assert.match(s.stderr, /is an SBM11 store/)
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})

test(`pack --layout sbm11 reads RDF/XML and JSON-LD; an IBK layout refuses JSON-LD (${ISSUE})`, () => {
  const dir = mkdtempSync(join(tmpdir(), 'factoidal-1009-'))
  try {
    const xml = join(dir, 'a.rdf')
    writeFileSync(xml, '<?xml version="1.0"?>\n<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" ' +
      'xmlns:e="http://e/"><rdf:Description rdf:about="http://e/s"><e:p>v</e:p></rdf:Description></rdf:RDF>\n')
    const json = join(dir, 'b.jsonld')
    writeFileSync(json, '{"@id": "http://e/s", "http://e/p": [{"@value": "v"}, {"@value": "w"}]}\n')
    for (const [input, n] of [[xml, '1'], [json, '2']]) {
      const store = join(dir, 'st-' + n)
      ok(['pack', input, join(store, 'gen'), '--layout', 'sbm11', '--quiet'])
      ok(['activate', store, 'gen', '--quiet'])
      const srj = JSON.parse(ok(['query', store, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }', '--json', '--quiet']).stdout)
      assert.equal(srj.results.bindings[0].n.value, n, input)
    }
    const r = run(['pack', json, join(dir, 'ibk', 'gen')])
    assert.equal(r.code, 2)
    assert.match(r.stderr, /--layout sbm11 also reads rdfxml and jsonld/)
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})
