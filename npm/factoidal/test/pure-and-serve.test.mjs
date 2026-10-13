// Tests for the functions added in 0.10.0: lib/pure.mjs (crypto, proof
// bundle, N-Quads ops) and serveStore (SPARQL 1.1 Protocol over a store).
// Run: node --test test/pure-and-serve.test.mjs

import test from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { execFileSync } from 'node:child_process'
import * as f from '../index.mjs'

const key = new Uint8Array(32).fill(7)
const nonce = new Uint8Array(12).fill(1)
const msg = new TextEncoder().encode('hello')

test('aeadSeal then aeadOpen returns the plaintext', async () => {
  const ct = await f.aeadSeal({ key, nonce, plaintext: msg, aad: new Uint8Array([9]) })
  assert.equal(ct.length, msg.length + 16)
  const pt = await f.aeadOpen({ key, nonce, ciphertext: ct, aad: new Uint8Array([9]) })
  assert.deepEqual(pt, msg)
})

test('aeadOpen rejects a changed tag', async () => {
  const ct = await f.aeadSeal({ key, nonce, plaintext: msg })
  ct[ct.length - 1] ^= 1
  await assert.rejects(f.aeadOpen({ key, nonce, ciphertext: ct }))
})

test('hpkeSeal and hpkeOpen, RFC 9180 A.2.1 key pair', async () => {
  // RFC 9180 Appendix A.2.1: skEm and the recipient pair.
  const hex = (s) => Uint8Array.from(s.match(/../g).map((b) => parseInt(b, 16)))
  const skE = hex('f4ec9b33b792c372c1d2c2063507b684ef925b8c75a42dbcbf57d63ccd381600')
  const skR = hex('8057991eef8f1f1af18f4a9491d16a1ce333f695d4db8e38da75975c4478e0fb')
  const pkR = hex('4310ee97d88cc1f088a5576c77ab0cf5c3ac797f3d95139c6c84b5429c59662a')
  const sealed = await f.hpkeSeal({ skE, pkR, plaintext: msg, info: msg })
  const pt = await f.hpkeOpen({ skR, message: sealed.message, info: msg })
  assert.deepEqual(pt, msg)
})

test('proofInspect and proofCheck reject a document with no profile', async () => {
  await assert.rejects(f.proofInspect('{}'), /profile/)
  await assert.rejects(f.proofCheck('{}'), /profile/)
})

test('canonicalizeNQuads relabels blank nodes per RDFC-1.0', async () => {
  assert.equal(await f.canonicalizeNQuads('_:x <http://e/p> _:y .\n'),
    '_:c14n1 <http://e/p> _:c14n0 .\n')
})

test('normalizeNQuads writes N-Quads back', async () => {
  assert.equal(await f.normalizeNQuads('<http://a> <http://b> "c" .\n'),
    '<http://a> <http://b> "c" .\n')
})

test('serveStore answers a SPARQL 1.1 Protocol SELECT', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'factoidal-serve-'))
  writeFileSync(join(dir, 'd.ttl'),
    '@prefix : <http://ex/> .\n:a :name "Alice" .\n:b :name "Bob" .\n')
  const cli = join(dirname(fileURLToPath(import.meta.url)), '..', 'bin', 'factoidal.mjs')
  const st = join(dir, 'st')
  execFileSync(process.execPath, [cli, 'pack', join(dir, 'd.ttl'), join(st, 'gen-1'), '--quiet'])
  execFileSync(process.execPath, [cli, 'activate', st, 'gen-1', '--quiet'])
  const s = await f.serveStore(st)
  try {
    const q = 'SELECT ?n WHERE { ?s <http://ex/name> ?n } ORDER BY ?n'
    const r = await fetch(`${s.url}?query=${encodeURIComponent(q)}`,
      { headers: { accept: 'application/sparql-results+json' } })
    assert.equal(r.status, 200)
    const j = await r.json()
    assert.deepEqual(j.results.bindings.map((b) => b.n.value), ['Alice', 'Bob'])
  } finally {
    await s.close()
  }
})
