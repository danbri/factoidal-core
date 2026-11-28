#!/usr/bin/env node
/** Test only: compare actual AOT Lean sparse projection to a fully materialised independent trie. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { MerklePatriciaTrie, bytes, hex, proofRequest, verifyProofBag, digest, checkSources } from './oracle.mjs'

checkSources()
const binary = fileURLToPath(new URL('../../.lake/build/bin/evm-sparse-probe', import.meta.url))
const opt = '--dangerously-enable-unverified-keccak'
const key = '11'.repeat(31) + '10'
const near = '11'.repeat(31) + '11'
const far = '21' + '11'.repeat(30) + '10'
const missing = '33'.repeat(32)
const rows = []
function call(args, expectedCode = 0) {
  const start = performance.now()
  const p = spawnSync(binary, args, { encoding: 'utf8', timeout: 60000, maxBuffer: 2*1024*1024 })
  assert.ifError(p.error)
  assert.equal(p.status, expectedCode, p.stderr + p.stdout)
  assert.equal(p.stderr, '')
  return { lines: p.stdout.trimEnd().split('\n'), milliseconds: performance.now()-start }
}
function checkProjection(lines, expected) {
  assert.equal(lines[0], 'projected')
  assert.equal(lines[1], expected)
  assert(lines.length >= 3 && lines.length <= 67)
  assert(lines.slice(2).every(s => /^(?:[a-f0-9]{2})+$/.test(s)))
}
for (const siblings of [[], [near], [far], [near, far]]) {
  for (const before of [1, 28, 29, 56]) {
    for (const after of [1, 28, 29, 56]) {
      const t = new MerklePatriciaTrie({ useKeyHashing: false })
      const old = '41'.repeat(before)
      const value = '42'.repeat(after)
      await t.put(bytes(key), bytes(old))
      for (const s of siblings) await t.put(bytes(s), bytes('73'.repeat(40)))
      const request = await proofRequest(t, bytes(key))
      const siblingPaths = await Promise.all(siblings.map(s => proofRequest(t, bytes(s))))
      await t.put(bytes(key), bytes(value))
      const expected = hex(t.root())
      const { lines, milliseconds } = call([opt, request.root, key, old, value, ...request.proof])
      checkProjection(lines, expected)
      const proof = lines.slice(2).map(bytes)
      assert.equal(hex(await verifyProofBag(bytes(key), proof, { root: bytes(expected), useKeyHashing: false })), value)
      for (let i=0; i<siblings.length; i++) {
        // Old sibling proof nodes plus the new target path must still authenticate
        // the original sibling value under the independent new commitment.
        const bag = [...proof, ...siblingPaths[i].proof.map(bytes)]
        assert.equal(hex(await verifyProofBag(bytes(siblings[i]), bag, { root: bytes(expected), useKeyHashing: false })), '73'.repeat(40))
      }
      rows.push({ siblings: siblings.length, before, after, oldRoot: request.root, newRoot: expected,
        nodes: proof.length, milliseconds })
    }
  }
}
const t = new MerklePatriciaTrie({ useKeyHashing: false })
await t.put(bytes(key), bytes('01'))
await t.put(bytes(far), bytes('02'.repeat(40)))
const req = await proofRequest(t, bytes(key))
const unchanged = call([opt, req.root, key, '01', '01', ...req.proof])
checkProjection(unchanged.lines, req.root)
const refusals = [
  ['wrong-old', [opt, req.root, key, '02', '03', ...req.proof], 'witness:old-value-mismatch', 0],
  ['missing-node', [opt, req.root, key, '01', '03', ...req.proof.slice(0,1)], 'witness:missing-referenced-node', 0],
  ['deletion', [opt, req.root, key, '01', '', ...req.proof], 'unsupported:deletion-not-yet', 0],
  ['absence', [opt, req.root, missing, '01', '03', ...req.proof], 'unsupported:insertion-not-yet', 0],
  ['wrong-width', [opt, '00', key, '01', '03', ...req.proof], 'witness:root-or-key-width', 0],
  ['no-opt-in', [req.root, key, '01', '03', ...req.proof], 'inputError:explicit-experimental-opt-in-required', 2],
]
for (const [id, args, expected, code] of refusals) {
  assert.deepEqual(call(args, code).lines, [expected], id + ': no partial projection')
}
assert.throws(() => checkProjection(['projected', '00'.repeat(32), 'c0'], req.root))
assert.throws(() => checkProjection(['projected', req.root], req.root))
assert.equal(rows.length,64)
console.log(JSON.stringify({ scope: 'existing leaf projection only, not execution or block validation',
  nativeComparisons: rows.length+1, refusalControls: refusals.length, comparatorControls: 2,
  executableSha256: digest(readFileSync(binary)), rows }))
