#!/usr/bin/env node
/** Bind captured mainnet runtime code to a pinned header with an EIP-1186 path. */
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import { createBlockHeaderFromRPC } from '@ethereumjs/block'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { verifyMerkleProof } from '@ethereumjs/mpt'
import { RLP } from '@ethereumjs/rlp'
import { bytesToBigInt, bytesToHex, hexToBytes } from '@ethereumjs/util'
import { keccak_256 } from '@noble/hashes/sha3.js'

if (process.argv.length !== 4) {
  throw Error('usage: verify-rpc-code-witness.mjs CAPTURE_JSON WITNESS_JSON')
}
const read = path => JSON.parse(readFileSync(path, 'utf8'))
const [capture, witness] = process.argv.slice(2).map(read)
const { block, call } = capture.providerAssertions
const { accountProof: proof } = witness
assert.equal(capture.expectedProfile.chainId, 1)
assert.equal(capture.provider.chainId, '0x1')
assert.equal(witness.schemaVersion, 1)
assert.equal(witness.chainId, 1)
assert.equal(witness.blockHash, block.hash)
assert.equal(witness.provenance.method, 'eth_getProof')
assert.deepEqual(witness.provenance.params, [call.address, [], {blockHash: block.hash, requireCanonical: true}])
assert.equal(call.executionCode.source, 'provider-chain-code')
assert.equal(call.executionCode.dataHex, call.chainCodeHex)
assert.equal(proof.address.toLowerCase(), call.address)
assert(Array.isArray(proof.accountProof) && proof.accountProof.length > 0)
assert.deepEqual(proof.storageProof, [])
assert.match(call.chainCodeHex, /^0x(?:[0-9a-f]{2})+$/)

const common = new Common({chain: Mainnet, hardfork: Hardfork.Osaka})
const header = createBlockHeaderFromRPC(block, {common})
assert.equal(bytesToHex(header.hash()), block.hash, 'header hash')
const path = proof.accountProof.map(node => {
  assert.match(node, /^0x(?:[0-9a-f]{2})+$/)
  return hexToBytes(node)
})
const verifyPath = root => verifyMerkleProof(hexToBytes(call.address), path,
  {root: hexToBytes(root), useKeyHashing: true})
const account = await verifyPath(block.stateRoot)
assert(account !== null, 'contract account must exist')
const fields = RLP.decode(account)
assert(Array.isArray(fields) && fields.length === 4 && fields.every(f => f instanceof Uint8Array))
const [nonce, balance, storageRoot, codeHash] = fields
assert.equal(storageRoot.length, 32)
assert.equal(codeHash.length, 32)
assert.equal(bytesToBigInt(nonce), BigInt(proof.nonce), 'proven account nonce')
assert.equal(bytesToBigInt(balance), BigInt(proof.balance), 'proven account balance')
assert.equal(bytesToHex(storageRoot), proof.storageHash, 'proven storage root')
assert.equal(bytesToHex(codeHash), proof.codeHash, 'proven code hash')

const runtime = hexToBytes(call.chainCodeHex)
function verifyCode(bytes) {
  assert.equal(bytesToHex(keccak_256(bytes)), proof.codeHash, 'captured runtime Keccak-256')
}
verifyCode(runtime)
const changed = runtime.slice()
changed[0] ^= 1
assert.throws(() => verifyCode(changed), /captured runtime Keccak-256/)
const changedRoot = hexToBytes(block.stateRoot)
changedRoot[0] ^= 1
await assert.rejects(verifyPath(bytesToHex(changedRoot)))

console.log(JSON.stringify({
  status: 'header-and-code-witness-match',
  chainId: 1, blockHash: block.hash, stateRoot: block.stateRoot, address: call.address,
  codeHash: proof.codeHash, codeBytes: runtime.length, accountProofNodes: path.length,
  negativeControls: ['changed-runtime-byte', 'changed-state-root'],
  scope: 'Code and account membership relative to the pinned header hash. Canonicality comes from the providers.'
}))
