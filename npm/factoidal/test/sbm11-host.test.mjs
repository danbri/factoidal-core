// SPARQL over an SBM11 generation through the wasm ops sbm11Open /
// sbm11Query / sbm11Close and host positioned reads
// (https://github.com/danbri/factoidal/issues/1009 KR1).
//
// The fixture (test/fixtures/sbm11-tiny, see its README) was packed by the
// native packer, and expected/NAME.out holds the bytes native `l4sbm11 query`
// wrote for each query. Each case here must give the same bytes and the same
// path (ids or reference) through the wasm engine. The native comparison over
// the W3C SPARQL 1.0 and 1.1 suites is `SBM11_HOST=1 tests/sbm11/census.sh`.
//
// No RDF logic here: the cases compare strings the engine wrote.

import test from 'node:test'
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { openSbm11, registerSbm11Source, loadEngine } from '../index.mjs'
import { nodeDirectoryReader } from '../lib/sbm11-node.mjs'

const FIX = join(dirname(fileURLToPath(import.meta.url)), 'fixtures', 'sbm11-tiny')
const ROOT = join(FIX, 'root')
const QUERIES = JSON.parse(readFileSync(join(FIX, 'queries.json'), 'utf8'))
const PATHS = JSON.parse(readFileSync(join(FIX, 'expected', 'paths.json'), 'utf8'))

test('the engine has the sbm11 ops', async () => {
  const eng = await loadEngine()
  const r = eng.call('ops', [])
  assert.ok((typeof r === 'string' ? r : JSON.stringify(r)).includes('"sbm11Query"'),
    'this wasm has no sbm11Query: it was built before issue 1009 KR1')
})

test('open a collection root: CURRENT names the generation', async () => {
  const st = await openSbm11(ROOT)
  try {
    assert.equal(st.generation, 'gen')
    assert.ok(st.terms > 0)
  } finally {
    st.close()
  }
})

const st = await openSbm11(ROOT)
for (const [name, sparql] of QUERIES) {
  test(`sbm11Query ${name}: the bytes and path of native l4sbm11 query`, () => {
    const want = readFileSync(join(FIX, 'expected', `${name}.out`), 'utf8')
    const got = st.query(sparql)
    assert.equal(got.result, want)
    assert.equal(got.path.startsWith('path=reference') ? 'path=reference' : got.path, PATHS[name])
  })
}
test('close', () => { st.close() })

test('a registered reader serves a source that is not a path', async () => {
  const r = nodeDirectoryReader(ROOT)
  registerSbm11Source('fixture:tiny', r)
  const s = await openSbm11('fixture:tiny')
  try {
    const got = s.query(QUERIES[0][1])
    assert.equal(got.result, readFileSync(join(FIX, 'expected', `${QUERIES[0][0]}.out`), 'utf8'))
    assert.ok(got.reads > 0)
  } finally {
    s.close()
    registerSbm11Source('fixture:tiny', null)
    r.close()
  }
})

test('a reader that returns short bytes is refused, with the file name', async () => {
  const real = nodeDirectoryReader(ROOT)
  registerSbm11Source('fixture:short', {
    size: (f) => real.size(f),
    readAt: (f, off, len) => (f.endsWith('.prb1') ? real.readAt(f, off, len).subarray(0, len - 1) : real.readAt(f, off, len))
  })
  const s = await openSbm11('fixture:short')
  try {
    assert.throws(() => s.query('SELECT * WHERE { ?s ?p ?o }'), /prb1/)
  } finally {
    s.close()
    registerSbm11Source('fixture:short', null)
    real.close()
  }
})

test('a directory that is not a generation is refused', async () => {
  await assert.rejects(openSbm11(FIX), /manifest\.sbm11/)
})
