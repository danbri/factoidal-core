// The Merkle check of an SBM11 store opened through the wasm ops
// (openSbm11, `verify: 'merkle'` by default; Lean
// formal/lean4/L4Factoidal/Storage/Sbm11/HostVerify.lean and HostSession.lean;
// https://github.com/danbri/factoidal/issues/1009).
//
// The cases of the external review of 0.18.0: a store packed by packSbm11,
// with one file changed, answered a query with no error (dict.gdv1 with
// "hello" changed to "HELLO"; spo.prb1 with one bit changed; manifest.sbm11
// with one bit changed near its end). Each is now refused, and the error
// names the file. An unchanged store answers as before.
//
// No RDF logic here: the cases change bytes and compare strings the engine wrote.

import test from 'node:test'
import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { packSbm11, mapReader, openSbm11 } from '../index.mjs'

const DOC = '<http://e/s> <http://e/p> "hello" .\n<http://e/s> <http://e/p> "world" .\n'
const Q = 'SELECT ?o WHERE { ?s ?p ?o } ORDER BY ?o'
const WANT = '{"head":{"vars":["o"]},"results":{"bindings":[{"o":{"type":"literal","value":"hello"}},{"o":{"type":"literal","value":"world"}}]}}'

const files = await packSbm11(DOC, { syntax: 'ntriples' })

/** `files` with file `name` changed by `change(bytes)` (a copy). */
function changed (base, name, change) {
  const m = new Map(base)
  const b = new Uint8Array(m.get(name))
  change(b)
  m.set(name, b)
  return m
}

/** Replace the first occurrence of `from` in `b` by `to` (same length). */
function replaceText (from, to) {
  return (b) => {
    const f = new TextEncoder().encode(from)
    const t = new TextEncoder().encode(to)
    for (let i = 0; i + f.length <= b.length; i++) {
      if (f.every((x, k) => b[i + k] === x)) { b.set(t, i); return }
    }
    throw new Error(`${from} is not in the file`)
  }
}

const flipAt = (fromEnd) => (b) => { b[b.length - fromEnd] ^= 1 }

let sourceCount = 0
/** Open `fs` and run `sparql`: { result } or { error } (open or query). */
async function run (fs, sparql, options = {}) {
  let st
  try {
    st = await openSbm11(`mem:verify-${++sourceCount}`, { reader: mapReader(fs), ...options })
    return { result: st.query(sparql).result, verify: st.verify }
  } catch (e) {
    return { error: String(e.message) }
  } finally {
    if (st) st.close()
  }
}

test('an unchanged store answers as before, under the default verify: merkle', async () => {
  const r = await run(files, Q)
  assert.equal(r.error, undefined)
  assert.equal(r.verify, 'merkle', 'this wasm has no Merkle check in sbm11Open')
  assert.equal(r.result, WANT)
  const none = await run(files, Q, { verify: 'none' })
  assert.equal(none.verify, 'none')
  assert.equal(none.result, WANT)
})

test('dict.gdv1 with "hello" changed to "HELLO" is refused, with the file name', async () => {
  const fs = changed(files, 'dict.gdv1', replaceText('hello', 'HELLO'))
  const r = await run(fs, Q)
  assert.equal(r.result, undefined, 'the changed dictionary answered')
  assert.match(r.error, /dict\.gdv1/)
  assert.match(r.error, /Merkle root/)
})

test('spo.prb1 with one changed bit is refused, with the file name', async () => {
  const fs = changed(files, 'spo.prb1', flipAt(3))
  const r = await run(fs, Q)
  assert.equal(r.result, undefined, 'the changed permutation answered')
  assert.match(r.error, /spo\.prb1/)
})

test('manifest.sbm11 with one changed bit near its end is refused at open', async () => {
  // the last bytes are the Merkle root of osp.prb1, which the query does not read
  const fs = changed(files, 'manifest.sbm11', flipAt(3))
  const r = await run(fs, Q)
  assert.equal(r.result, undefined, 'the changed manifest answered')
  assert.match(r.error, /sbm11Open/)
  assert.match(r.error, /osp\.prb1/)
})

test('a changed .merkle sidecar is refused at open, with the file name', async () => {
  const fs = changed(files, 'pso.prm1.merkle', flipAt(1))
  const r = await run(fs, Q)
  assert.equal(r.result, undefined)
  assert.match(r.error, /pso\.prm1\.merkle/)
})

test('a missing .merkle sidecar is refused at open under merkle, and read under none', async () => {
  const fs = new Map(files)
  fs.delete('dict.gdx1.merkle')
  const r = await run(fs, Q)
  assert.match(r.error, /dict\.gdx1\.merkle/)
  assert.equal((await run(fs, Q, { verify: 'none' })).result, WANT)
})

test('verify: none is the opt-out: it reads the changed dictionary with no error', async () => {
  const fs = changed(files, 'dict.gdv1', replaceText('hello', 'HELLO'))
  const r = await run(fs, Q, { verify: 'none' })
  assert.equal(r.verify, 'none')
  assert.match(r.result, /HELLO/)
})

test('an unknown verify value is refused by the engine', async () => {
  const r = await run(files, Q, { verify: 'sha1' })
  assert.match(r.error, /verify is merkle or none/)
})

test('a store of more than one chunk: a changed byte in the last chunk is refused', async () => {
  // 8,000 quads with literals of about 40 bytes: dict.gdv1 has more than
  // one 65,536-byte chunk
  let doc = ''
  for (let i = 0; i < 8000; i++) {
    doc += `<http://e/s${i % 50}> <http://e/p${i % 7}> "literal number ${String(i).padStart(6, '0')} of the test" .\n`
  }
  const big = await packSbm11(doc, { syntax: 'ntriples' })
  assert.ok(big.get('dict.gdv1').length > 65536, `dict.gdv1 has ${big.get('dict.gdv1').length} bytes`)
  const q = 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o FILTER(STRSTARTS(STR(?o), "literal")) }'
  const ok = await run(big, q)
  assert.equal(ok.error, undefined)
  assert.match(ok.result, /"8000"/)
  const bad = await run(changed(big, 'dict.gdv1', flipAt(10)), q)
  assert.equal(bad.result, undefined)
  assert.match(bad.error, /dict\.gdv1: chunk [1-9]/)
})

// The trust anchor of the manifest (openSbm11 `manifestSha256`; Lean
// HostVerify.checkAnchor; https://github.com/danbri/factoidal/issues/1105).
// The SHA-256 here is node:crypto, used only to make the expected value of
// the test; the engine computes its own digest.


const sha256Hex = (b) => createHash('sha256').update(b).digest('hex')
const anchor = sha256Hex(files.get('manifest.sbm11'))

/** The byte offset of the quad count in manifest.sbm11: magic and version
 *  (5), layout string (u32 length + bytes), source length (8), source SHA-256
 *  (32). Read from the bytes, as the engine writes them. */
function quadCountOffset (m) {
  const len = new DataView(m.buffer, m.byteOffset).getUint32(5, true)
  return 5 + 4 + len + 8 + 32
}

test('store.manifestSha256 is the SHA-256 of manifest.sbm11, with and without an anchor', async () => {
  const st = await openSbm11(`mem:verify-${++sourceCount}`, { reader: mapReader(files) })
  assert.equal(st.manifestSha256, anchor, 'this wasm has no manifestSha256 in sbm11Open')
  st.close()
  const r = await run(files, Q, { manifestSha256: anchor })
  assert.equal(r.error, undefined)
  assert.equal(r.result, WANT)
  // either case
  assert.equal((await run(files, Q, { manifestSha256: anchor.toUpperCase() })).result, WANT)
})

test('a changed quad count in the manifest: read with no anchor, refused with the old anchor', async () => {
  // the quad count is bound to no read, so the Merkle check does not see it
  const fs = changed(files, 'manifest.sbm11', (b) => { b[quadCountOffset(b)] ^= 1 })
  assert.notEqual(sha256Hex(fs.get('manifest.sbm11')), anchor)
  assert.equal((await run(fs, Q)).result, WANT)
  const r = await run(fs, Q, { manifestSha256: anchor })
  assert.equal(r.result, undefined, 'the changed manifest opened under its old anchor')
  assert.match(r.error, /manifest\.sbm11/)
  assert.ok(r.error.includes(anchor), r.error)
  assert.ok(r.error.includes(sha256Hex(fs.get('manifest.sbm11'))), r.error)
})

test('a wrong anchor refuses the unchanged store; a malformed anchor is refused', async () => {
  const wrong = anchor.slice(0, 63) + (anchor[63] === '0' ? '1' : '0')
  const r = await run(files, Q, { manifestSha256: wrong })
  assert.equal(r.result, undefined)
  assert.match(r.error, /manifest\.sbm11/)
  assert.ok(r.error.includes(wrong) && r.error.includes(anchor), r.error)
  const bad = await run(files, Q, { manifestSha256: 'sha256-not-hex' })
  assert.match(bad.error, /manifestSha256/)
})

test('the anchor holds under verify: none too', async () => {
  const fs = changed(files, 'manifest.sbm11', (b) => { b[quadCountOffset(b)] ^= 1 })
  const r = await run(fs, Q, { verify: 'none', manifestSha256: anchor })
  assert.match(r.error, /manifest\.sbm11/)
  assert.equal((await run(files, Q, { verify: 'none', manifestSha256: anchor })).result, WANT)
})
