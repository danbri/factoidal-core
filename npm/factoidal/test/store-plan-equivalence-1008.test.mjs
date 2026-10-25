// The plan-equality gate through the package
// (https://github.com/danbri/factoidal/issues/1008).
//
// A property-path alternative `?s p|q ?o` and the UNION of the two triple
// patterns have the same solutions (SPARQL 1.1 18.4; the theorem is
// `Query.expandIriAlternatives_eval` in
// formal/lean4/L4Factoidal/SPARQL/PathAlternativeTheorems.lean). On one
// store, the engine's planner must name the same blocks for both forms, and
// the store must answer the same multiset of rows. Before the fix, the path
// form planned every block of the store (1,046 of 1,046 in the londat store,
// 10.9 MB) and the UNION form only the blocks of p and q.
//
// The first pair is the reproduction in the issue (londat
// cwplans/tools/check-factoidal.mjs). The Lean twin of this test, over an
// SBM7 store built in the test, is formal/lean4/Wasm/StorePlanGateTests.lean.
//
// The test packs an IBK5 generation of the N-Quads below with the engine's
// own packer, reads its manifest, and calls the ops storeQueryPlan and
// storeOpen / storeHandleQuery. It is skipped when the loaded engine does
// not serve those ops; a missing engine fails, as every other test here.

import test from 'node:test'
import assert from 'node:assert/strict'
import fs from 'node:fs'
import os from 'node:os'
import path from 'node:path'

import { loadEngine, hexOfBytes } from '../bin/engine.mjs'
import { packFile } from '../bin/pack.mjs'
import factoidal from '../index.js'

const NAME = '<http://ex.org/name>'
const SIZE = '<http://ex.org/size>'
const OTHER = '<http://ex.org/other>'

// Four predicates in one named graph, so four blocks. `<b> name "beta"` and
// `<b> size "beta"` make one solution of multiplicity two under name|size.
const NQUADS = [
  '<http://ex.org/a> <http://ex.org/name> "alpha" <http://ex.org/g> .',
  '<http://ex.org/a> <http://ex.org/size> "3" <http://ex.org/g> .',
  '<http://ex.org/b> <http://ex.org/name> "beta" <http://ex.org/g> .',
  '<http://ex.org/b> <http://ex.org/size> "beta" <http://ex.org/g> .',
  '<http://ex.org/a> <http://ex.org/other> <http://ex.org/c> <http://ex.org/g> .',
  '<http://ex.org/b> <http://ex.org/other> <http://ex.org/c> <http://ex.org/g> .',
  '<http://ex.org/b> <http://ex.org/type> <http://ex.org/T> <http://ex.org/g> .',
  ''
].join('\n')

// Each row: two query texts whose patterns the algebra proves equal, and
// the theorem that proves it.
const PROVED_PAIRS = [
  {
    theorem: 'expandIriAlternatives_lowerWith',
    left: `SELECT * WHERE { GRAPH ?g { ?s ${NAME}|${SIZE} ?o } }`,
    right: `SELECT * WHERE { GRAPH ?g { { ?s ${NAME} ?o } UNION { ?s ${SIZE} ?o } } }`,
    blocks: 2,
    rows: 4
  },
  {
    theorem: 'expandIriAlternatives_lowerWith',
    left: `SELECT * WHERE { GRAPH ?g { ?s ${NAME}|${SIZE}|${OTHER} ?o } }`,
    right: `SELECT * WHERE { GRAPH ?g { { ?s ${NAME} ?o } UNION { ?s ${SIZE} ?o } UNION { ?s ${OTHER} ?o } } }`,
    blocks: 3,
    rows: 6
  },
  {
    theorem: 'expandIriAlternatives_lowerWith',
    left: `SELECT * WHERE { GRAPH ?g { ?s ${OTHER} ?c . ?s ${NAME}|${SIZE} ?o } }`,
    right: `SELECT * WHERE { GRAPH ?g { ?s ${OTHER} ?c . { ?s ${NAME} ?o } UNION { ?s ${SIZE} ?o } } }`,
    blocks: 3,
    rows: 4
  },
  {
    theorem: 'ggpJoin_empty_right',
    left: `SELECT * WHERE { GRAPH ?g { ?s ${NAME} ?o } }`,
    right: `SELECT * WHERE { GRAPH ?g { { ?s ${NAME} ?o } } }`,
    blocks: 1,
    rows: 2
  }
]

const NEEDED_OPS = ['packBegin', 'storeQueryPlan', 'storeOpen', 'storeHandleQuery']

/** Rows as a count per row text: a multiset, order ignored. */
function multiset (rows) {
  const counts = new Map()
  for (const row of rows) {
    const vars = [...row.keys()].sort()
    const text = JSON.stringify(vars.map((v) => [v, row.get(v).termType, row.get(v).value]))
    counts.set(text, (counts.get(text) || 0) + 1)
  }
  return counts
}

function sameMultiset (a, b) {
  if (a.size !== b.size) return false
  for (const [k, n] of a) if (b.get(k) !== n) return false
  return true
}

test('issue 1008: proved-equal queries plan the same blocks and answer the same rows', async (t) => {
  const engine = await loadEngine()
  const ops = engine.call('ops', []).ops
  const missing = NEEDED_OPS.filter((op) => !ops.includes(op))
  if (missing.length > 0) {
    t.skip(`the loaded engine does not serve ${missing.join(', ')}`)
    return
  }
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-1008-'))
  try {
    const input = path.join(root, 'source.nq')
    fs.writeFileSync(input, NQUADS)
    const generation = path.join(root, 'gen-1')
    fs.mkdirSync(generation)
    packFile(engine, input, generation, { layout: 'ibk5', syntax: 'nquads' })
    const manifestHex = hexOfBytes(fs.readFileSync(path.join(generation, 'manifest.sbm2')))
    const plan = (sparql) => engine.call('storeQueryPlan', [manifestHex, sparql])
    assert.equal(plan(`SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }`).keys.length, 4,
      'the store holds four blocks')

    const store = await factoidal.openStore(root, { generation: 'gen-1' })
    try {
      for (const pair of PROVED_PAIRS) {
        const left = plan(pair.left)
        const right = plan(pair.right)
        assert.deepEqual([...left.keys].sort(), [...right.keys].sort(),
          `${pair.theorem}: the two forms plan different blocks\n  ${pair.left}\n  ${pair.right}`)
        assert.equal(left.keys.length, pair.blocks, `${pair.left} plans ${left.keys.length} blocks`)
        const leftRows = await store.query(pair.left)
        const rightRows = await store.query(pair.right)
        assert.equal(leftRows.length, pair.rows, `${pair.left} answers ${leftRows.length} rows`)
        assert.ok(sameMultiset(multiset(leftRows), multiset(rightRows)),
          `${pair.theorem}: the two forms answer different rows`)
      }
    } finally {
      await store.close()
    }
  } finally {
    fs.rmSync(root, { recursive: true, force: true })
  }
})
