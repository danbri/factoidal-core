/** Test-only independent oracles. Nothing in the Lean runtime imports this file. */
import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { createRequire } from 'node:module'
import { fileURLToPath } from 'node:url'

// Reuse the already approved, exact package-lock. Do not add a runtime package.
const require = createRequire(new URL('../differential/package.json', import.meta.url))
export const { MerklePatriciaTrie, createMerkleProof, verifyMerkleProof, updateMPTFromMerkleProof } = require('@ethereumjs/mpt')
export const { RLP } = require('@ethereumjs/rlp')
export const { bytesToBigInt, ecrecover, publicToAddress } = require('@ethereumjs/util')
export const { keccak_256: keccak } = require('@noble/hashes/sha3.js')
export const evidence = fileURLToPath(new URL('../../evidence/', import.meta.url))
export const hex = bytes => Buffer.from(bytes).toString('hex')
export const bytes = value => {
  assert.equal(typeof value, 'string')
  const raw = value.replace(/^0x/, '')
  assert(/^(?:[0-9a-fA-F]{2})*$/.test(raw), 'complete hexadecimal bytes')
  return Uint8Array.from(Buffer.from(raw, 'hex'))
}
export const nat = value => {
  const n = BigInt(value); assert(n >= 0n)
  if (n === 0n) return new Uint8Array()
  let h = n.toString(16); if (h.length % 2) h = '0' + h
  return bytes(h)
}
export const fixed = (value, width) => {
  const n = BigInt(value); assert(n >= 0n && n < (1n << BigInt(8 * width)))
  return bytes(n.toString(16).padStart(width * 2, '0'))
}
export const digest = data => createHash('sha256').update(data).digest('hex')
export const emptyRoot = '56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421'
export const emptyCode = 'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470'
export const clone = value => structuredClone(value)
export const loadJSON = name => JSON.parse(readFileSync(new URL('../../evidence/' + name, import.meta.url), 'utf8'))

export const sourcePins = [
  { file: 'mpt-upstream-rlp-valid.json', upstream: 'RLPTests/rlptest.json', count: 28,
    blob: 'cb0d9fd399f140d6bab9d411033f8be131df8df0',
    sha256: 'dd11055db749a21d8ee7aae7810ac30d19a89e2c6dadba9967f7bd567ad5fc00' },
  { file: 'mpt-upstream-rlp-invalid.json', upstream: 'RLPTests/invalidRLPTest.json', count: 26,
    blob: '21d0b2d14332292c9a9bd5becb73ad6a5bacba62',
    sha256: 'f90bf5745d21bfa7fbfeabaf5b6d1c66bae10051b1c0a054eecd424d488385d7' },
  { file: 'mpt-upstream-secure-trie.json', upstream: 'TrieTests/hex_encoded_securetrie_test.json', count: 3,
    blob: '473f96419a49ca6493a1460f93f46b254fb095a7',
    sha256: '487f9e1e404e46dc0a54d526b14927d3a5ba90f7f52625e7d49cd170974ce9ff' },
]
export function checkSources() {
  for (const pin of sourcePins) {
    const raw = readFileSync(new URL('../../evidence/' + pin.file, import.meta.url))
    assert.equal(digest(raw), pin.sha256, pin.file + ': upstream byte pin')
    assert.equal(createHash('sha1').update(Buffer.concat([Buffer.from(`blob ${raw.length}\0`), raw])).digest('hex'),
      pin.blob, pin.file + ': upstream Git blob')
    assert.equal(Object.keys(JSON.parse(raw)).length, pin.count, pin.file + ': fixed inventory')
  }
  const lock = readFileSync(new URL('../differential/package-lock.json', import.meta.url))
  assert.equal(digest(lock), 'cc95a62e125486d2de9a28cb5fc61c098b955aa22c2dd0b3dc0b19f2df770425', 'oracle lock pin')
  const packages = JSON.parse(lock).packages
  for (const name of ['mpt', 'rlp', 'util'])
    assert.equal(packages['node_modules/@ethereumjs/' + name].version, '10.1.3')
}

export function rlpView(encoding, integerBytes) {
  const decoded = RLP.decode(bytes(encoding))
  assert.equal(hex(RLP.encode(decoded)), encoding.replace(/^0x/, '').toLowerCase(), 'canonical oracle round trip')
  const isList = Array.isArray(decoded)
  const out = { status: 'decoded', isList,
    payloadHex: isList ? decoded.map(item => hex(RLP.encode(item))).join('') : hex(decoded) }
  if (isList) out.children = decoded.map(item => hex(RLP.encode(item)))
  if (integerBytes !== undefined) {
    assert(!isList && decoded.length <= integerBytes && (!decoded.length || decoded[0] !== 0), 'canonical scalar')
    out.integer = bytesToBigInt(decoded).toString()
  }
  return out
}

export async function proofRequest(trie, key) {
  return { schemaVersion: 1, root: hex(trie.root()), key: hex(key),
    proof: (await createMerkleProof(trie, key)).map(hex) }
}

export async function checkProof(request, expected) {
  const actual = await verifyProofBag(bytes(request.key), request.proof.map(bytes),
    { root: bytes(request.root), useKeyHashing: false })
  if (expected.status === 'absent') assert.equal(actual, null, 'independent nonmembership')
  else assert.equal(hex(actual), expected.valueHex, 'independent membership value')
}

// The convenience verifyMerkleProof API requires the root node first. The
// public DB-population API also permits an unordered bag under an explicit
// root, matching this CLI's documented transport policy without sorting it.
export async function verifyProofBag(key, proof, options) {
  const trie = new MerklePatriciaTrie(options)
  await updateMPTFromMerkleProof(trie, proof, false)
  // EthereumJS's throwIfMissing also throws for its own canonical empty root.
  // Permit its normal empty lookup only for that exact independently derived root.
  const canonicalEmpty = hex(new MerklePatriciaTrie().root())
  assert.equal(canonicalEmpty, emptyRoot)
  return await trie.get(key, hex(options.root) !== canonicalEmpty)
}

/** Build state and storage independently, then expose only keys, code and proofs. */
export async function buildStateWitness(records) {
  const state = new MerklePatriciaTrie({ useKeyHashing: true })
  const slots = new Map()
  for (const record of records) {
    const storage = new MerklePatriciaTrie({ useKeyHashing: true })
    slots.set(record.address, storage)
    if (!record.exists) continue
    for (const slot of record.storage ?? []) if (BigInt(slot.value) !== 0n)
      await storage.put(fixed(slot.key, 32), RLP.encode(nat(slot.value)))
    await state.put(fixed(record.address, 20), RLP.encode([
      nat(record.nonce), nat(record.balance), storage.root(), keccak(bytes(record.codeHex)),
    ]))
  }
  const accounts = []
  for (const record of records) {
    const storage = slots.get(record.address)
    accounts.push({ address: record.address, codeHex: record.codeHex,
      accountProof: (await createMerkleProof(state, fixed(record.address, 20))).map(hex),
      storage: await Promise.all((record.storage ?? []).map(async slot => ({ key: slot.key,
        proof: (await createMerkleProof(storage, fixed(slot.key, 32))).map(hex) }))) })
  }
  return { schemaVersion: 1, stateRoot: hex(state.root()), accounts }
}

export async function checkStateWitness(request, expectedAccounts) {
  assert.equal(request.accounts.length, expectedAccounts.length)
  for (let index = 0; index < request.accounts.length; index++) {
    const account = request.accounts[index], expected = expectedAccounts[index]
    assert.equal(account.address, expected.address)
    const raw = await verifyProofBag(fixed(account.address, 20), account.accountProof.map(bytes),
      { root: bytes(request.stateRoot), useKeyHashing: true })
    if (!expected.exists) { assert.equal(raw, null); continue }
    assert(raw !== null)
    const fields = RLP.decode(raw)
    assert.equal(fields.length, 4)
    assert.equal(bytesToBigInt(fields[0]).toString(), expected.nonce)
    assert.equal(bytesToBigInt(fields[1]).toString(), expected.balance)
    assert.equal(hex(fields[3]), hex(keccak(bytes(expected.codeHex))))
    for (let si = 0; si < account.storage.length; si++) {
      const slot = account.storage[si], value = expected.storage[si]
      assert.equal(slot.key, value.key)
      const encoded = await verifyProofBag(fixed(slot.key, 32), slot.proof.map(bytes),
        { root: fields[2], useKeyHashing: true })
      assert.equal(encoded === null ? '0' : bytesToBigInt(RLP.decode(encoded)).toString(), value.value)
    }
  }
}
