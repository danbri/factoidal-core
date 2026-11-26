#!/usr/bin/env node
/** Replay the signed index-zero 1CAT transfer from authenticated Shanghai prestate. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { createBlockFromRPC, createBlockHeaderFromRPC } from '@ethereumjs/block'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createMPT, updateMPTFromMerkleProof, verifyMerkleProof } from '@ethereumjs/mpt'
import { RLP } from '@ethereumjs/rlp'
import { createTxFromRLP } from '@ethereumjs/tx'
import { Account, bigIntToUnpaddedBytes, bytesToBigInt, bytesToHex, createAddressFromString,
  hexToBytes } from '@ethereumjs/util'
import { Bloom, createVM, encodeReceipt, runTx } from '@ethereumjs/vm'
import { keccak_256 } from '@noble/hashes/sha3.js'

if (process.argv.length !== 4) throw Error('usage: replay-authenticated-contract.mjs FIXTURE LEAN_EXE')
const [fixturePath, executable] = process.argv.slice(2)
const fixtureBytes = readFileSync(fixturePath)
const fixture = JSON.parse(fixtureBytes)
const readJSON = path => JSON.parse(readFileSync(path))
const digest = bytes => createHash('sha256').update(bytes).digest('hex')
const dec = n => BigInt(n).toString()
const quantity = n => '0x' + BigInt(n).toString(16)
const fixedHex = (n, bytes) => '0x' + BigInt(n).toString(16).padStart(2 * bytes, '0')
const optIn = '--dangerously-enable-unverified-keccak'
const common = new Common({chain: Mainnet, hardfork: Hardfork.Shanghai})
const {parentHeader, blockHeader, transaction, receipt} = fixture
const txIndex = RLP.encode(0)

assert.equal(fixture.schemaVersion, 1)
assert.equal(fixture.chainId, 1)
assert.equal(fixture.fork, 'shanghai')
assert.equal(fixture.transactionIndex, 0)
assert.equal(blockHeader.hash, '0x9bc80ce85c8b20addd723d3e4848e49a7f15af7565bac87a1c1c5d50741808ae')
assert.equal(BigInt(blockHeader.number), 19100013n)
assert.equal(parentHeader.hash, blockHeader.parentHash)
assert.equal(BigInt(blockHeader.number), BigInt(parentHeader.number) + 1n)
for (const header of [parentHeader, blockHeader]) {
  assert(BigInt(header.timestamp) >= 1681338455n && BigInt(header.timestamp) < 1710338135n)
  assert.equal(bytesToHex(createBlockHeaderFromRPC(header, {common}).hash()), header.hash)
}
const root = hexToBytes(parentHeader.stateRoot)
const tx = createTxFromRLP(hexToBytes(transaction.rawSignedHex), {common})
assert.equal(tx.type, 0)
assert(tx.verifySignature())
assert.equal(bytesToHex(tx.hash()), transaction.hash)
assert.equal(bytesToHex(tx.serialize()), transaction.rawSignedHex)
assert.equal(tx.to.toString(), '0x508e00d5cef397b02d260d035e5ee80775e4c821')
assert.equal(tx.value, 0n)
assert.equal(tx.getSenderAddress().toString(), receipt.record.from)

async function indexLeaf(rootHash, path) {
  const found = await verifyMerkleProof(txIndex, path.map(hexToBytes), {root: hexToBytes(rootHash)})
  assert(found !== null, 'missing index-zero leaf')
  return found
}
const committedTx = await indexLeaf(blockHeader.transactionsRoot, transaction.proof)
assert.deepEqual(committedTx, tx.serialize(), 'signed transaction leaf')
const committedReceipt = await indexLeaf(blockHeader.receiptsRoot, receipt.proof)
const record = receipt.record
assert.equal(record.transactionHash, transaction.hash)
assert.equal(record.blockHash, blockHeader.hash)
assert.equal(BigInt(record.transactionIndex), 0n)
assert.equal(BigInt(record.type), BigInt(tx.type))
assert.equal(BigInt(record.gasUsed), BigInt(record.cumulativeGasUsed))
assert.equal(BigInt(record.effectiveGasPrice), tx.gasPrice)
assert.equal(BigInt(record.status), 1n)
const rpcLogs = logs => logs.map(({address, topics, data}) =>
  [hexToBytes(address), topics.map(hexToBytes), hexToBytes(data)])
const publishedLogs = rpcLogs(record.logs)
assert.deepEqual(committedReceipt, encodeReceipt({
  status: Number(record.status), cumulativeBlockGasUsed: BigInt(record.cumulativeGasUsed),
  bitvector: hexToBytes(record.logsBloom), logs: publishedLogs,
}, tx.type), 'published receipt leaf')
assert.equal(publishedLogs.length, 1)

async function verifiedAccount(stateRoot, proof) {
  const accountPath = proof.accountProof.map(hexToBytes)
  const bytes = await verifyMerkleProof(hexToBytes(proof.address), accountPath, {root: stateRoot, useKeyHashing: true})
  assert(bytes !== null, 'selected witness account must exist')
  const fields = RLP.decode(bytes)
  assert(Array.isArray(fields) && fields.length === 4 && fields.every(x => x instanceof Uint8Array))
  const [nonce, balance, storageRoot, codeHash] = fields
  const account = new Account(bytesToBigInt(nonce), bytesToBigInt(balance), storageRoot, codeHash)
  assert.equal(BigInt(proof.nonce), account.nonce, 'witness account nonce')
  assert.equal(BigInt(proof.balance), account.balance, 'witness account balance')
  assert.equal(proof.storageHash, bytesToHex(storageRoot), 'witness storage root')
  assert.equal(proof.codeHash, bytesToHex(codeHash), 'witness code hash')
  return {account, accountPath}
}

function storageValue(encoded) {
  if (encoded === null) return 0n
  const decoded = RLP.decode(encoded)
  assert(decoded instanceof Uint8Array && decoded.length > 0 && decoded[0] !== 0, 'noncanonical storage leaf')
  return bytesToBigInt(decoded)
}

async function verifiedPrestate(rows) {
  assert.deepEqual(rows.map(x => x.proof.address), [
    tx.getSenderAddress().toString(), tx.to.toString(), blockHeader.miner,
  ])
  const out = []
  for (const {proof, codeHex} of rows) {
    const {account, accountPath} = await verifiedAccount(root, proof)
    const code = hexToBytes(codeHex)
    assert.deepEqual(keccak_256(code), account.codeHash, 'witness runtime Keccak-256')
    const storage = []
    for (const slot of proof.storageProof) {
      assert.match(slot.key, /^0x[0-9a-f]{64}$/)
      assert(!storage.some(s => s.key === slot.key), 'duplicate witness slot')
      const path = slot.proof.map(hexToBytes)
      const encoded = await verifyMerkleProof(hexToBytes(slot.key), path,
        {root: account.storageRoot, useKeyHashing: true})
      const value = storageValue(encoded)
      assert.equal(value, BigInt(slot.value), 'witness storage value')
      storage.push({key: slot.key, path, value})
    }
    out.push({address: proof.address, account, accountPath, code, storage})
  }
  return out
}

const prestate = await verifiedPrestate(fixture.accounts)
const target = prestate[1]
assert.equal(target.code.length, 6583)
assert.equal(target.storage.length, 4)
const {account: finalTarget} = await verifiedAccount(hexToBytes(blockHeader.stateRoot), fixture.finalBlockTargetAccount)
assert.equal(fixture.finalBlockTargetAccount.address, target.address)
const publishedFinalTargetStorageRoot = bytesToHex(finalTarget.storageRoot)

const request = {
  schemaVersion: 1, fork: 'shanghai', fuel: '15000',
  transaction: {type: tx.type, chainId: '1', sender: dec(tx.getSenderAddress().toString()),
    to: dec(tx.to.toString()), nonce: dec(tx.nonce), value: dec(tx.value), gasLimit: dec(tx.gasLimit),
    gasPriceCap: dec(tx.gasPrice), priorityFeeCap: '0', dataHex: bytesToHex(tx.data), accessList: []},
  block: {chainId: '1', coinbase: dec(blockHeader.miner), number: dec(blockHeader.number),
    timestamp: dec(blockHeader.timestamp), gasLimit: dec(blockHeader.gasLimit), gasUsedBefore: '0',
    baseFee: dec(blockHeader.baseFeePerGas), prevRandao: dec(blockHeader.mixHash), blobBaseFee: '0'},
  accounts: prestate.map(({address, account, code, storage}) => ({
    address: dec(address), exists: true, balance: dec(account.balance), nonce: dec(account.nonce),
    codeHex: bytesToHex(code), storage: storage.map(s => ({key: dec(s.key), value: dec(s.value)})),
  })),
}

function validateFrameReceipt(status, cumulativeGas, logs, engine) {
  const bloom = new Bloom()
  for (const [address, topics] of logs) {
    bloom.add(address)
    for (const topic of topics) bloom.add(topic)
  }
  const encoded = encodeReceipt({status, cumulativeBlockGasUsed: BigInt(cumulativeGas),
    bitvector: bloom.bitvector, logs}, tx.type)
  assert.deepEqual(encoded, committedReceipt, engine + ' authenticated receipt')
}

function runNative(directory, input, hashOptIn) {
  const requestFile = join(directory, 'lean-request.json')
  writeFileSync(requestFile, JSON.stringify(input))
  const args = ['--call-transaction', requestFile]
  if (hashOptIn) args.unshift(optIn)
  const p = spawnSync(executable, args, {encoding: 'utf8', timeout: 15000, maxBuffer: 1024 * 1024})
  if (p.error || p.status !== 0) throw Error('Lean transaction failed: ' + String(p.error ?? p.stdout + p.stderr))
  return JSON.parse(p.stdout)
}

async function loadedStorage(row) {
  const st = await createMPT({useKeyHashing: true, root: row.account.storageRoot})
  for (const slot of row.storage) await updateMPTFromMerkleProof(st, slot.path, true)
  assert.deepEqual(st.root(), row.account.storageRoot, 'storage proof import changed root')
  for (const slot of row.storage) {
    assert.equal(storageValue(await st.get(hexToBytes(slot.key), true)), slot.value, 'imported storage value')
  }
  return st
}

async function postRoots(post) {
  assert.equal(post.length, prestate.length)
  const trie = await createMPT({useKeyHashing: true, root})
  for (const row of prestate) await updateMPTFromMerkleProof(trie, row.accountPath, true)
  assert.deepEqual(trie.root(), root, 'world proof import changed parent root')
  let targetStorageRoot
  for (const [i, {address, account, code, storage}] of prestate.entries()) {
    const next = post[i]
    assert.equal(next.address, dec(address))
    assert.equal(next.exists, true)
    assert.equal(next.codeHex, bytesToHex(code).slice(2))
    assert.equal(next.storage.length, storage.length)
    const addressKey = hexToBytes(address)
    assert.deepEqual(await trie.get(addressKey, true), account.serialize(), 'sparse account before update')
    const st = await loadedStorage(prestate[i])
    for (const [k, slot] of storage.entries()) {
      assert.equal(next.storage[k].key, dec(slot.key))
      const value = BigInt(next.storage[k].value)
      const key = hexToBytes(slot.key)
      if (value !== slot.value) {
        if (value === 0n) await st.del(key)
        else await st.put(key, RLP.encode(bigIntToUnpaddedBytes(value)))
      }
      const stored = await st.get(key, true)
      assert.equal(storageValue(stored), value, 'post-write secure slot readback')
      if (value === 0n) assert.equal(stored, null, 'zero slot must be deleted')
    }
    const nextAccount = new Account(BigInt(next.nonce), BigInt(next.balance), st.root(), account.codeHash)
    await trie.put(addressKey, nextAccount.serialize())
    assert.deepEqual(await trie.get(addressKey, true), nextAccount.serialize(), 'post-write account readback')
    if (address === target.address) targetStorageRoot = bytesToHex(st.root())
  }
  return {intermediateStateRoot: bytesToHex(trie.root()), targetStorageRoot}
}

async function runEthereumJS() {
  const vm = await createVM({common})
  const block = await createBlockFromRPC({...blockHeader, transactions: []}, [], {common})
  const state = vm.stateManager
  for (const row of prestate) {
    const address = createAddressFromString(row.address)
    await state.putAccount(address, new Account(row.account.nonce, row.account.balance))
    if (row.code.length) await state.putCode(address, row.code)
    for (const slot of row.storage) {
      await state.putStorage(address, hexToBytes(slot.key), bigIntToUnpaddedBytes(slot.value))
    }
  }
  const reachedSlots = new Set()
  const opcodeNames = new Set()
  let messages = 0
  vm.evm.events.on('beforeMessage', (message, resolve) => {
    messages++
    assert.equal(message.to.toString(), target.address)
    assert.equal(message.depth, 0)
    resolve?.()
  })
  vm.evm.events.on('step', (step, resolve) => {
    opcodeNames.add(step.opcode.name)
    if (step.opcode.code === 0x54 || step.opcode.code === 0x55) {
      assert.equal(step.address.toString(), target.address)
      const key = fixedHex(step.stack.at(-1), 32)
      assert(target.storage.some(slot => slot.key === key), 'oracle reached an unauthenticated slot')
      reachedSlots.add(key)
    }
    resolve?.()
  })
  // The header stores final block gas. Transaction zero begins at zero.
  const result = await runTx(vm, {tx, block, blockGasUsed: 0n})
  assert.equal(messages, 1)
  assert.deepEqual([...reachedSlots].sort(), target.storage.map(s => s.key).sort())
  assert.equal(dec(result.totalGasSpent), dec(record.gasUsed))
  assert.deepEqual(encodeReceipt(result.receipt, tx.type), committedReceipt, 'EthereumJS receipt')
  assert.equal(result.execResult.exceptionError, undefined)
  const accounts = []
  for (const row of prestate) {
    const address = createAddressFromString(row.address)
    const next = await state.getAccount(address)
    const storage = []
    for (const slot of row.storage) {
      const value = await state.getStorage(address, hexToBytes(slot.key))
      storage.push({key: dec(slot.key), value: dec(bytesToBigInt(value))})
    }
    accounts.push({address: dec(row.address), exists: true, balance: dec(next.balance), nonce: dec(next.nonce),
      codeHex: bytesToHex(await state.getCode(address)).slice(2), storage})
  }
  return {accounts, returnBytesHex: bytesToHex(result.execResult.returnValue).slice(2),
    refundGas: dec(result.gasRefund), opcodeNames: [...opcodeNames].sort()}
}

function runGeth(directory) {
  const geth = process.env.EVM_GETH_EXE
  if (!geth) return null
  const sha256 = digest(readFileSync(geth))
  assert.equal(sha256, 'd8cfddad15a8c601e7b069bc5973ad073dbc2d632b8c5ab50e513ef27c53d6da')
  const alloc = Object.fromEntries(prestate.map(({address, account, code, storage}) => [address, {
    balance: quantity(account.balance), nonce: quantity(account.nonce), code: bytesToHex(code),
    storage: Object.fromEntries(storage.map(s => [s.key, fixedHex(s.value, 32)])),
  }]))
  const env = {currentCoinbase: blockHeader.miner, currentNumber: blockHeader.number,
    currentTimestamp: blockHeader.timestamp, currentGasLimit: blockHeader.gasLimit,
    currentBaseFee: blockHeader.baseFeePerGas, currentRandom: blockHeader.mixHash, withdrawals: []}
  for (const [name, input] of [
    ['alloc.json', alloc], ['env.json', env], ['txs.rlp', bytesToHex(RLP.encode([RLP.decode(tx.serialize())]))],
  ]) writeFileSync(join(directory, name), JSON.stringify(input))
  const proc = spawnSync(geth, ['t8n', '--state.fork', 'Shanghai', '--state.chainid', '1',
    '--state.reward=-1', '--input.alloc', join(directory, 'alloc.json'),
    '--input.env', join(directory, 'env.json'), '--input.txs', join(directory, 'txs.rlp'),
    '--output.basedir', directory, '--output.alloc', 'geth-post.json', '--output.result', 'geth-result.json'],
  {encoding: 'utf8', timeout: 15000, maxBuffer: 1024 * 1024})
  if (proc.error || proc.status !== 0) throw Error('Geth t8n failed: ' + String(proc.error ?? proc.stderr))
  const result = readJSON(join(directory, 'geth-result.json'))
  assert.equal(result.receipts.length, 1)
  const actualReceipt = result.receipts[0]
  assert.equal(dec(result.gasUsed), dec(record.gasUsed))
  assert.equal(actualReceipt.transactionHash, transaction.hash)
  assert.equal(actualReceipt.logsBloom, record.logsBloom)
  validateFrameReceipt(Number(actualReceipt.status), actualReceipt.cumulativeGasUsed, rpcLogs(actualReceipt.logs), 'Geth')
  const post = readJSON(join(directory, 'geth-post.json'))
  assert.deepEqual(Object.keys(post).sort(), prestate.map(r => r.address).sort())
  const accounts = prestate.map(({address, storage}) => ({
    address: dec(address), exists: true, balance: dec(post[address].balance), nonce: dec(post[address].nonce),
    codeHex: (post[address].code ?? '0x').slice(2),
    storage: storage.map(s => ({key: dec(s.key), value: dec(post[address].storage?.[s.key] ?? 0)})),
  }))
  return {accounts, sha256}
}

const directory = mkdtempSync(join(tmpdir(), 'evm-authenticated-contract-'))
try {
  const actual = runNative(directory, request, true)
  assert.equal(actual.schemaVersion, 1)
  assert.equal(actual.status, 'executed', JSON.stringify(actual))
  assert.equal(actual.keccakOptIn, true)
  assert.equal(actual.frameStatus, 'returned')
  assert.equal(actual.receiptStatus, 1)
  assert.equal(actual.gasUsed, dec(record.gasUsed))
  assert.equal(actual.effectiveGasPrice, dec(record.effectiveGasPrice))
  const leanLogs = actual.logs.map(({address, topics, dataHex}) => [
    hexToBytes(fixedHex(address, 20)), topics.map(t => hexToBytes(fixedHex(t, 32))),
    hexToBytes('0x' + dataHex),
  ])
  validateFrameReceipt(actual.receiptStatus, actual.cumulativeGasUsed, leanLogs, 'Lean')

  const reference = await runEthereumJS()
  assert.deepEqual(actual.accounts, reference.accounts, 'Lean and EthereumJS account effects')
  assert.equal(actual.returnBytesHex, reference.returnBytesHex)
  assert.equal(actual.returnBytesHex, '0'.repeat(63) + '1')
  assert.equal(actual.refundGas, reference.refundGas)
  const roots = await postRoots(actual.accounts)
  assert.deepEqual(await postRoots(reference.accounts), roots)
  assert.equal(roots.targetStorageRoot, publishedFinalTargetStorageRoot, 'proven final-block target storage root')

  const alternate = runGeth(directory)
  if (alternate) {
    assert.deepEqual(actual.accounts, alternate.accounts, 'Lean and Geth account effects')
    assert.deepEqual(await postRoots(alternate.accounts), roots)
  }

  const withoutHash = runNative(directory, request, false)
  assert.deepEqual(withoutHash, {schemaVersion: 1, status: 'indeterminate', reason: 'unsupportedFork', keccakOptIn: false})
  const missingSlot = structuredClone(request)
  const missingKey = missingSlot.accounts[1].storage.shift().key
  assert.deepEqual(runNative(directory, missingSlot, true), {
    schemaVersion: 1, status: 'indeterminate', reason: 'incompleteState',
    address: dec(target.address), slot: missingKey, keccakOptIn: true,
  })
  const wrongCode = structuredClone(fixture.accounts)
  wrongCode[1].codeHex = '0x00' + wrongCode[1].codeHex.slice(4)
  await assert.rejects(verifiedPrestate(wrongCode), /witness runtime Keccak-256/)
  const wrongStorage = structuredClone(fixture.accounts)
  wrongStorage[1].proof.storageProof[0].value = '0x1'
  await assert.rejects(verifiedPrestate(wrongStorage), /witness storage value/)
  assert.throws(() => validateFrameReceipt(1, BigInt(actual.cumulativeGasUsed) + 1n, leanLogs, 'mutated'), /mutated authenticated receipt/)

  // MPT writes interpret the third argument as skipKeyTransform, unlike get.
  const wrongTrie = await loadedStorage(target)
  const changedSlot = target.storage.find(s => s.value > 0n)
  const wrongKey = hexToBytes(changedSlot.key)
  const wrongValue = changedSlot.value + 1n
  await wrongTrie.put(wrongKey, RLP.encode(bigIntToUnpaddedBytes(wrongValue)), true)
  assert.equal(storageValue(await wrongTrie.get(wrongKey, true)), changedSlot.value)
  assert.notEqual(bytesToHex(wrongTrie.root()), publishedFinalTargetStorageRoot)

  console.log(JSON.stringify({
    status: 'authenticated-shanghai-contract-replay-match',
    fixtureSha256: digest(fixtureBytes), nativeSha256: digest(readFileSync(executable)),
    blockHash: blockHeader.hash, transactionHash: transaction.hash, transactionIndex: 0,
    authenticatedAccounts: prestate.length, authenticatedStorageSlots: target.storage.length,
    gasUsed: actual.gasUsed, refundGas: actual.refundGas, receiptStatus: actual.receiptStatus,
    logCount: leanLogs.length, returnBytesHex: actual.returnBytesHex, keccakOptIn: true,
    roots, publishedFinalTargetStorageRoot, ethereumJS: {matched: true, opcodes: reference.opcodeNames},
    geth: alternate && {matched: true, sha256: alternate.sha256},
    negativeControls: ['without-keccak-opt-in', 'missing-authenticated-slot', 'changed-code',
      'changed-storage-value', 'changed-receipt-gas', 'wrong-skip-key-transform'],
    rootScope: 'Intermediate world root derived from the authenticated parent and index-zero effects. The target storage root also matches its independently proven final-block value.',
  }))
} finally {
  rmSync(directory, {recursive: true, force: true})
}
