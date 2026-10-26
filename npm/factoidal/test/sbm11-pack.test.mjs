// Packing an SBM11 generation in memory through the wasm op sbm11PackFiles,
// and querying it through a reader over the files in memory
// (https://github.com/danbri/factoidal/issues/1009 stage 2).
//
// The fixture (test/fixtures/sbm11-tiny, see its README) was packed by the
// native packer `l4sbm11-pack`. packSbm11 of its input must give every file of
// root/gen byte for byte, and the queries of queries.json over those files
// must give the bytes native `l4sbm11 query` wrote (expected/NAME.out). The
// native comparison of the same packer with `l4sbm11-pack` over the W3C SPARQL
// 1.0 and 1.1 inputs is `SBM11_PACKFILES=1 tests/sbm11/census.sh`.
//
// A wasm module built before stage 2 has no sbm11PackFiles op: the pack cases
// then SKIP with that reason (the module is rebuilt in danbri/factoidal-builds).
// The mapReader cases run on any module that has the sbm11 query ops.
//
// No RDF logic here: the cases compare bytes and strings the engine wrote.

import test from 'node:test'
import assert from 'node:assert/strict'
import { readFileSync, readdirSync } from 'node:fs'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { openSbm11, packSbm11, mapReader, loadEngine } from '../index.mjs'

const FIX = join(dirname(fileURLToPath(import.meta.url)), 'fixtures', 'sbm11-tiny')
const GEN = join(FIX, 'root', 'gen')
const QUERIES = JSON.parse(readFileSync(join(FIX, 'queries.json'), 'utf8'))
const PATHS = JSON.parse(readFileSync(join(FIX, 'expected', 'paths.json'), 'utf8'))

function fixtureFiles () {
  const m = new Map()
  for (const name of readdirSync(GEN)) m.set(name, new Uint8Array(readFileSync(join(GEN, name))))
  return m
}

async function hasPackOp () {
  const eng = await loadEngine()
  const r = eng.call('ops', [])
  const j = typeof r === 'string' ? JSON.parse(r) : r
  return Array.isArray(j.blobIoOps) && j.blobIoOps.includes('sbm11PackFiles')
}

const NO_OP = 'this wasm has no sbm11PackFiles op (built before issue 1009 stage 2; ' +
  'rebuilt in danbri/factoidal-builds)'
const packSkip = (await hasPackOp()) ? false : NO_OP

async function checkQueries (source, files) {
  const st = await openSbm11(source, { reader: mapReader(files) })
  try {
    assert.equal(st.generation, '')
    for (const [name, sparql] of QUERIES) {
      const want = readFileSync(join(FIX, 'expected', `${name}.out`), 'utf8')
      const got = st.query(sparql)
      assert.equal(got.result, want, `query ${name}`)
      assert.equal(got.path.startsWith('path=reference') ? 'path=reference' : got.path, PATHS[name], `path of ${name}`)
    }
  } finally {
    st.close()
  }
}

test('mapReader: the fixture generation held in memory answers every query as native l4sbm11 query', async () => {
  await checkQueries('memory:fixture', fixtureFiles())
})

test('mapReader: a file it does not hold, or a read past the end, answers null', () => {
  const r = mapReader({ a: new Uint8Array([1, 2, 3]) })
  assert.equal(r.size('a'), 3)
  assert.equal(r.size('b'), null)
  assert.deepEqual([...r.readAt('a', 1, 2)], [2, 3])
  assert.equal(r.readAt('a', 2, 2), null)
  assert.equal(r.readAt('b', 0, 1), null)
})

test('packSbm11: every file of the fixture generation, byte for byte', { skip: packSkip }, async () => {
  const want = fixtureFiles()
  const got = await packSbm11(readFileSync(join(FIX, 'input.nq'), 'utf8'), { syntax: 'nquads' })
  assert.deepEqual([...got.keys()].sort(), [...want.keys()].sort())
  for (const [name, bytes] of want) {
    assert.ok(Buffer.from(got.get(name)).equals(Buffer.from(bytes)), `${name} differs`)
  }
})

test('packSbm11 then openSbm11 over the files in memory: the answers of native l4sbm11 query', { skip: packSkip }, async () => {
  const files = await packSbm11(readFileSync(join(FIX, 'input.nq')), { syntax: 'nquads' })
  await checkQueries('memory:packed', files)
})

test('packSbm11: a syntax error is refused with a message', { skip: packSkip }, async () => {
  await assert.rejects(packSbm11('<http://e/a> <http://e/p> .', { syntax: 'nquads' }), /parse error/)
})

test('packSbm11: an unknown syntax is refused', { skip: packSkip }, async () => {
  await assert.rejects(packSbm11('', { syntax: 'no-such-syntax' }), /unknown syntax/)
})

test('packSbm11: no syntax is a TypeError', async () => {
  await assert.rejects(packSbm11('', {}), TypeError)
})

test('packSbm11 on a module without the op names the op', { skip: packSkip ? false : 'this wasm has the op' }, async () => {
  await assert.rejects(packSbm11('', { syntax: 'nquads' }), (e) => e.code === 'SBM11_NO_PACK_OP')
})
