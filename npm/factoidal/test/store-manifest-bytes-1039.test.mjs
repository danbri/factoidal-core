// The byte forms of the manifest ops
// (https://github.com/danbri/factoidal/issues/1039).
//
// `storeManifestInspectBytes`, `storeQueryPlanBytes` and `storeOpenBytes`
// take the manifest as the byte region, not as hexadecimal inside the JSON
// arguments, and decode it through a one-entry memo keyed on the bytes
// (formal/lean4/Wasm/Ops/StoreHandles.lean, `resolveManifestBytes_fst`).
// These tests check that each byte op answers what its hexadecimal op
// answers, that the memo does not keep a stale manifest when the host
// switches stores, and that bin/store.mjs still works over an engine that
// has only the hexadecimal ops. The Lean twins are the `#guard`s at the end
// of Wasm/Ops/Store.lean and Wasm/Ops/StoreHandles.lean.

import test from 'node:test'
import assert from 'node:assert/strict'
import fs from 'node:fs'
import os from 'node:os'
import path from 'node:path'

import { loadEngine, hexOfBytes } from '../bin/engine.mjs'
import { packFile } from '../bin/pack.mjs'
import { openStore, openStoreHandle, planQuery, inspectManifest } from '../bin/store.mjs'
import factoidal from '../index.js'

const BYTE_OPS = ['storeManifestInspectBytes', 'storeQueryPlanBytes', 'storeOpenBytes']

const NQUADS_A = [
  '<http://ex.org/a> <http://ex.org/name> "alpha" <http://ex.org/g> .',
  '<http://ex.org/b> <http://ex.org/name> "beta" <http://ex.org/g> .',
  '<http://ex.org/a> <http://ex.org/size> "3" <http://ex.org/g> .',
  '<http://ex.org/a> <http://ex.org/other> <http://ex.org/c> .',
  ''
].join('\n')

const NQUADS_B = [
  '<http://ex.org/x> <http://ex.org/name> "xi" .',
  '<http://ex.org/y> <http://ex.org/colour> "red" .',
  ''
].join('\n')

const QUERIES = [
  'SELECT ?s ?o WHERE { ?s <http://ex.org/name> ?o } ORDER BY ?s',
  'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } } ORDER BY ?s ?p',
  'SELECT * WHERE { ?s <http://ex.org/other> ?o }',
  'ASK { ?s <http://ex.org/size> "3" }',
  'DESCRIBE <http://ex.org/a>'
]

function pack (engine, root, name, nquads) {
  const input = path.join(root, `${name}.nq`)
  fs.writeFileSync(input, nquads)
  const generation = path.join(root, name)
  fs.mkdirSync(generation)
  packFile(engine, input, generation, { layout: 'ibk5', syntax: 'nquads' })
  return openStore(root, name)
}

/** The keys of a full open, from an inspect envelope. */
function allKeys (inspect) {
  const keys = []
  for (const entry of inspect.entries) {
    keys.push(entry.key)
    for (const key of Object.values(entry.sidecars ?? {})) keys.push(key)
  }
  for (const blob of inspect.blobs ?? []) keys.push(blob.key)
  return keys
}

function regionOf (store, keys) {
  const chunks = keys.map((key) => fs.readFileSync(path.join(store.generationDir, key)))
  const blob = new Uint8Array(chunks.reduce((n, c) => n + c.length, 0))
  const artifacts = []
  let offset = 0
  chunks.forEach((chunk, i) => {
    blob.set(chunk, offset)
    artifacts.push({ key: keys[i], offset, len: chunk.length })
    offset += chunk.length
  })
  return { blob, artifacts }
}

/** The open envelope without the handle id, which differs per open. */
function openFields (envelope) {
  const { handle: _handle, ...rest } = envelope
  return rest
}

/** An engine that answers like one built before the byte ops. */
function olderEngine (engine) {
  return {
    call (op, args) {
      const answer = engine.call(op, args)
      if (op !== 'ops') return answer
      return {
        ...answer,
        ops: answer.ops.filter((name) => !BYTE_OPS.includes(name)),
        blobIoOps: answer.blobIoOps.filter((name) => !BYTE_OPS.includes(name))
      }
    },
    callBlob: engine.callBlob,
    callBlobIO (op, args, bytes) {
      if (BYTE_OPS.includes(op)) throw new Error(`the older engine has no op ${op}`)
      return engine.callBlobIO(op, args, bytes)
    }
  }
}

test('issue 1039: the byte manifest ops answer what the hexadecimal ops answer', async () => {
  const engine = await loadEngine()
  const reflection = engine.call('ops', [])
  for (const op of BYTE_OPS) {
    assert.ok(reflection.blobIoOps.includes(op), `the engine lists ${op} in blobIoOps`)
  }
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-1039-'))
  try {
    const a = pack(engine, root, 'gen-a', NQUADS_A)
    const b = pack(engine, root, 'gen-b', NQUADS_B)
    for (const store of [a, b]) {
      const hex = hexOfBytes(store.manifest)
      assert.equal(store.manifestHex, hex, 'the lazy manifestHex is the hexadecimal of the bytes')
      assert.deepEqual(
        engine.callBlobIO('storeManifestInspectBytes', [], store.manifest).envelope,
        engine.call('storeManifestInspect', [hex]))
      for (const sparql of QUERIES) {
        assert.deepEqual(
          engine.callBlobIO('storeQueryPlanBytes', [sparql], store.manifest).envelope,
          engine.call('storeQueryPlan', [hex, sparql]), sparql)
      }
    }

    // The same open, by the two ops: the same envelope and the same answers.
    const inspect = inspectManifest(engine, a)
    const keys = allKeys(inspect)
    const { blob, artifacts } = regionOf(a, keys)
    const hexOpen = engine.callBlobIO('storeOpen', [a.manifestHex, JSON.stringify(artifacts)], blob).envelope
    const region = new Uint8Array(a.manifest.length + blob.length)
    region.set(a.manifest, 0)
    region.set(blob, a.manifest.length)
    const byteOpen = engine.callBlobIO('storeOpenBytes',
      [String(a.manifest.length), JSON.stringify(artifacts)], region).envelope
    assert.deepEqual(openFields(byteOpen), openFields(hexOpen))
    for (const sparql of QUERIES) {
      assert.deepEqual(engine.call('storeHandleQuery', [byteOpen.handle, sparql]),
        engine.call('storeHandleQuery', [hexOpen.handle, sparql]), sparql)
    }
    engine.call('storeHandleClose', [byteOpen.handle])
    engine.call('storeHandleClose', [hexOpen.handle])
  } finally {
    fs.rmSync(root, { recursive: true, force: true })
  }
})

test('issue 1039: the manifest memo answers for the bytes of each call', async () => {
  const engine = await loadEngine()
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-1039-'))
  try {
    const a = pack(engine, root, 'gen-a', NQUADS_A)
    const b = pack(engine, root, 'gen-b', NQUADS_B)
    const sparql = 'SELECT ?s ?o WHERE { ?s <http://ex.org/name> ?o } ORDER BY ?s'
    // Plan A (the memo holds A), then open B: the handle is B's.
    const planA = planQuery(engine, a, sparql)
    const hb = openStoreHandle(engine, b, { sparql })
    const planB = planQuery(engine, b, sparql)
    assert.notDeepEqual(planA.keys, planB.keys, 'the two stores plan different keys')
    const rows = hb.query(sparql).srj.results.bindings.map((row) => row.o.value)
    assert.deepEqual(rows, ['xi'])
    hb.close()
    // And back to A.
    const ha = openStoreHandle(engine, a, { sparql })
    assert.deepEqual(ha.query(sparql).srj.results.bindings.map((row) => row.o.value), ['alpha', 'beta'])
    ha.close()
  } finally {
    fs.rmSync(root, { recursive: true, force: true })
  }
})

test('issue 1039: storeOpenBytes refuses a bad manifest length by name', async () => {
  const engine = await loadEngine()
  const refusal = (args, bytes) => {
    try {
      return engine.callBlobIO('storeOpenBytes', args, bytes).envelope
    } catch (error) {
      return error.envelope
    }
  }
  assert.match(refusal(['x', '[]'], new Uint8Array(4)).error, /is not a decimal byte count/)
  assert.match(refusal(['9', '[]'], new Uint8Array(4)).error, /more than the 4 bytes/)
  assert.match(refusal(['4', '[]'], new Uint8Array(4)).error, /storeOpenBytes: bytes do not decode/)
  let plain
  try {
    plain = engine.call('storeQueryPlanBytes', ['ASK {}'])
  } catch (error) {
    plain = error.envelope
  }
  assert.match(plain.error, /carries a byte region; call it through l4_call_blob_io/)
})

test('issue 1039: bin/store.mjs uses the hexadecimal ops on an engine without the byte ops', async () => {
  const engine = await loadEngine()
  const older = olderEngine(engine)
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-1039-'))
  try {
    const a = pack(engine, root, 'gen-a', NQUADS_A)
    for (const sparql of QUERIES) {
      assert.deepEqual(planQuery(older, a, sparql), planQuery(engine, a, sparql), sparql)
    }
    assert.deepEqual(inspectManifest(older, a), inspectManifest(engine, a))
    const sparql = QUERIES[0]
    const hOld = openStoreHandle(older, a, { sparql })
    const hNew = openStoreHandle(engine, a, { sparql })
    assert.deepEqual(hOld.query(sparql), hNew.query(sparql))
    assert.equal(hOld.rows, hNew.rows)
    hOld.close()
    hNew.close()
  } finally {
    fs.rmSync(root, { recursive: true, force: true })
  }
})

test('issue 1039: the package openStore and Store.inspect over the byte ops', async () => {
  const engine = await loadEngine()
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-1039-'))
  try {
    const a = pack(engine, root, 'gen-a', NQUADS_A)
    const store = await factoidal.openStore(root, { generation: 'gen-a' })
    try {
      const { ok: _ok, ...expected } = engine.call('storeManifestInspect', [a.manifestHex])
      assert.deepEqual(await store.inspect(), expected)
      assert.equal(await store.query('ASK { ?s <http://ex.org/size> "3" }'), true)
    } finally {
      await store.close()
    }
    const scoped = await factoidal.openStore(root, {
      generation: 'gen-a', sparql: 'SELECT ?o WHERE { ?s <http://ex.org/name> ?o }'
    })
    try {
      const rows = await scoped.query('SELECT ?o WHERE { ?s <http://ex.org/name> ?o } ORDER BY ?o')
      assert.deepEqual(rows.map((row) => row.get('o').value), ['alpha', 'beta'])
    } finally {
      await scoped.close()
    }
  } finally {
    fs.rmSync(root, { recursive: true, force: true })
  }
})
