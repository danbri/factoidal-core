#!/usr/bin/env node
/**
 * One native invocation executes each whole ordered decoded Cancun list.
 * EthereumJS and Geth execute the same signed envelopes from the same initial
 * state. No intermediate accounts or counters are supplied to the Lean runner.
 * The existing eels dependencies are test oracles/host codecs, not implementation
 * dependencies. Synthetic witnesses, signature recovery and root codecs remain
 * trusted; no header-body authentication, sidecars or full block validation.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { createRequire } from 'node:module'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { openGeth } from './geth-byte-oracle.mjs'

const require = createRequire(new URL('../eels/package.json', import.meta.url))
const { createBlock } = require('@ethereumjs/block')
const { Common, Hardfork, Mainnet } = require('@ethereumjs/common')
const { MerklePatriciaTrie } = require('@ethereumjs/mpt')
const { RLP } = require('@ethereumjs/rlp')
const { createTx, createTxFromRLP } = require('@ethereumjs/tx')
const { Account, bigIntToBytes, bytesToBigInt, bytesToHex, createAddressFromPrivateKey,
  createAddressFromString, hexToBytes, unpadBytes } = require('@ethereumjs/util')
const { Bloom, createVM, encodeReceipt, runBlock } = require('@ethereumjs/vm')
const { keccak_256 } = require('@noble/hashes/sha3.js')

const args = process.argv.slice(2), smoke = args.includes('--smoke'), referencesOnly = args.includes('--references-only')
assert(args.every(x => !x.startsWith('--') || ['--smoke', '--references-only'].includes(x)))
const executable = args.find(x => !x.startsWith('--')) ??
  fileURLToPath(new URL('../../.lake/build/bin/evm-transaction-list', import.meta.url))
const geth = openGeth()
assert(geth, 'EVM_GETH_EXE must name the existing pinned Geth executable')
const directory = mkdtempSync(join(tmpdir(), 'lean-transaction-list-'))
let kzgOperations = 0, nativeInvocations = 0
const forbiddenKzg = new Proxy({}, { get(_target, operation) {
  kzgOperations++; throw Error('KZG sidecars are not part of this execution test: ' + String(operation))
} })
const common = new Common({ chain: Mainnet, hardfork: Hardfork.Cancun, customCrypto: { kzg: forbiddenKzg } })
const dec = value => BigInt(value).toString()
const quantity = value => '0x' + BigInt(value).toString(16)
const address = value => '0x' + BigInt(value).toString(16).padStart(40, '0')
const word = value => '0x' + BigInt(value).toString(16).padStart(64, '0')
const hex = bytes => bytesToHex(bytes).slice(2)
const digest = bytes => createHash('sha256').update(bytes).digest('hex')
const unit = 131072n, byteLimit = 16 * 1024 * 1024, maxWord = (1n << 256n) - 1n
const keys = [1n, 2n].map(n => hexToBytes(word(n))) // Public synthetic fixture keys only.
const senders = keys.map(key => createAddressFromPrivateKey(key).toString())
const parent = address(0xc1), child = address(0xc2), beneficiary = address(0xc4)
const reverter = address(0xc5), invalid = address(0xc6), unsupported = address(0xc7)
const beaconRoots = createAddressFromString('0x000f3df6d732807ef1319fb7b8bb8522d0beac02')
const hashes = Array.from({ length: 6 }, (_, index) => '0x01' +
  Array.from({ length: 31 }, (_, byte) => ((index * 47 + byte * 19) % 256).toString(16).padStart(2, '0')).join(''))
const push = value => {
  const n = BigInt(value); assert(n >= 0n && n <= maxWord)
  if (!n) return '5f'
  let h = n.toString(16); if (h.length % 2) h = '0' + h
  return (0x5f + h.length / 2).toString(16) + h
}
const hashReturn = '5f495f5260205ff3'
const effects = (ending = 'f3') => '5f49805f555f52610abc60205fa160205f' + ending
const storeData = '5f355f555f545f5260205ff3'
const logData = '5f355f52610abc60205fa160205ff3'
const readTwice = '5f545f54505f5260205ff3'
const clearSlot = '5f5f5500'
const slots = [[0, 7], [1, 9], [2, 0], [3, 0]]
const record = (addr, { balance = 0, nonce = 1, code = '', storage = [] } = {}) => ({
  address: dec(addr), exists: true, balance: dec(balance), nonce: dec(nonce), codeHex: code,
  storage: storage.map(([key, value]) => ({ key: dec(key), value: dec(value) })),
})
const tx = (type = 2, options = {}) => ({ type, ...options })
const blob = (list = [hashes[0]], options = {}) => tx(3, { hashes: list, ...options })
const cases = []
const add = (id, entries, options = {}) => cases.push({ id, entries, category: 'execution', code: '00', ...options })
add('single-blobhash', [blob()], { code: effects() })
add('empty-list', [])
add('ordinary-mixed-types', [tx(0, { value: 3 }), tx(1, { value: 4 }), tx(2, { value: 5 })])
add('dependent-nonces', [tx(), tx(), tx()])
add('dependent-recipient-funding', [tx(2, { to: senders[1], value: 1_000_000 }), tx(2, { key: 1, value: 123 })],
  { secondBalance: 0 })
add('beneficiary-tip-funds-next-sender', [tx(2, { gas: 21_000, value: 0 }),
  tx(0, { key: 1, to: child, gas: 21_000, cap: 3, value: 0 })], { coinbase: senders[1], secondBalance: 0 })
add('original-storage-reset', [1, 2, 0, 3].map(n => tx(2, { data: word(n).slice(2) })),
  { code: storeData, initialSlot: 0 })
add('warm-storage-reset', [tx(), tx(), tx()], { code: readTwice })
add('access-list-reset', [tx(1, { accessList: [{ address: parent, storageKeys: [word(0)] }] }),
  tx(), blob([hashes[2]], { accessList: [{ address: parent, storageKeys: [word(0)] }] })], { code: readTwice })
add('refund-reset', [tx(), tx()], { code: clearSlot })
add('receipt-log-reset', [1, 2, 3].map(n => tx(2, { data: word(n).slice(2) })), { code: logData })
add('hash-context-reset', [blob([hashes[0]]), blob([hashes[1]]), tx(0), tx(1), tx(2), blob([hashes[5]])],
  { code: effects() })
add('revert-middle-keeps-blob-burn', [blob(), blob([hashes[1]], { to: reverter }), blob([hashes[2]])],
  { code: effects() })
add('exception-middle-keeps-blob-burn', [tx(), blob([hashes[1]], { to: invalid, gas: 50_000 }), tx()],
  { code: effects() })
add('reverted-value-does-not-credit-target', [tx(0, { to: reverter, value: 1000 }), tx(2, { value: 5 })])
add('sender-is-recipient', [tx(0, { to: senders[0] }), blob([hashes[0]], { to: senders[0] })])
add('sender-is-beneficiary', [tx(), blob()], { coinbase: senders[0], code: effects() })
add('recipient-is-beneficiary', [blob(), tx()], { coinbase: parent, code: effects() })
add('sender-recipient-beneficiary-alias', [tx(0, { to: senders[0] }), blob([hashes[0]], { to: senders[0] })],
  { coinbase: senders[0] })
add('refund-restores-block-gas-pool', [tx(2, { gas: 80_000 }), tx(2, { gas: 76_000, to: child })],
  { code: clearSlot, blockGas: 100_000 })
add('gas-limit-sum-exceeds-block-but-sequentially-fits', [tx(2, { gas: 50_000 }), tx(2, { gas: 50_000 }),
  tx(2, { gas: 50_000 })], { blockGas: 100_000 })
add('six-blob-aggregate', [blob(hashes.slice(0, 2)), blob(hashes.slice(2, 4)), blob(hashes.slice(4, 6))],
  { code: effects() })
add('failed-receipt-still-counts-three-blobs', [blob(hashes.slice(0, 3), { to: invalid, gas: 50_000 }),
  blob(hashes.slice(3, 6))], { code: effects() })
add('nonzero-blob-price-across-failures', [blob(), blob([hashes[1]], { to: reverter }),
  blob([hashes[2]], { to: invalid, gas: 50_000 })], { code: effects(), excess: 80n * unit })
add('maximum-256-entries', Array.from({ length: 256 }, () => tx(2, { gas: 21_000, fuel: 10 })))
add('maximum-reserved-fuel', [tx(2, { fuel: 500_000 }), tx(2, { fuel: 500_000 })])
for (const op of ['call', 'callcode', 'delegatecall', 'staticcall']) {
  const operands = [32, 0, 0, 0]
  if (op === 'call' || op === 'callcode') operands.push(0)
  const code = [...operands, BigInt(child), 30_000].map(push).join('') +
    { call: 'f1', callcode: 'f2', delegatecall: 'f4', staticcall: 'fa' }[op] +
    '6020525f4960405260605ff3'
  add(`nested-${op}-context-reset`, [blob(), tx()], { code, childCode: hashReturn })
}
add('invalid-middle-nonce', [tx(), tx(2, { nonce: 0 }), tx(2, { nonce: 8 })],
  { category: 'admission', rejectIndex: 1, reason: 'invalid-sender-nonce' })
add('invalid-middle-balance', [tx(), tx(2, { key: 1 }), tx(2, { nonce: 8 })],
  { category: 'admission', rejectIndex: 1, reason: 'insufficient-upfront-balance', secondBalance: 0 })
add('invalid-middle-fee-cap', [tx(), tx(2, { cap: 1, priority: 0 }), tx(2, { nonce: 8 })],
  { category: 'admission', rejectIndex: 1, reason: 'price-below-base-fee' })
add('invalid-middle-block-gas-reservation', [tx(2, { gas: 21_000 }), tx(2, { gas: 80_000 }),
  tx(2, { gas: 30_000, nonce: 8 })], { category: 'admission', rejectIndex: 1,
  reason: 'block-gas-exhausted', blockGas: 100_000 })
add('invalid-seven-blob-aggregate', [blob(hashes.slice(0, 4)), blob(hashes.slice(0, 3))],
  { category: 'admission', rejectIndex: 1, reason: 'declared-gas-total-exceeded',
    declaredBlobGas: 6n * unit })
add('unsupported-middle-frame', [tx(), tx(2, { to: unsupported }), tx()],
  { category: 'local-boundary', rejectIndex: 1, nativeStatus: 'indeterminate', reason: 'invalidOpcode' })
assert.equal(cases.length, 36, 'fixed whole-list inventory')
assert.equal(cases.filter(test => test.category === 'execution').length, 30)
assert.equal(new Set(cases.map(test => test.id)).size, cases.length)

function initialAccounts(test) {
  const accounts = new Map()
  const put = row => accounts.set(row.address, row)
  put(record(senders[0], { balance: 10n ** 15n, nonce: 7 }))
  put(record(senders[1], { balance: test.secondBalance ?? 10n ** 15n, nonce: 9 }))
  put(record(parent, { balance: 5000, code: test.code, storage: [[0, test.initialSlot ?? 7], ...slots.slice(1)] }))
  put(record(child, { balance: 100, code: test.childCode ?? '', storage: slots }))
  put(record(reverter, { balance: 100, code: effects('fd'), storage: slots }))
  put(record(invalid, { balance: 100, code: effects('fe'), storage: slots }))
  put(record(unsupported, { balance: 100, code: '5f4000', storage: slots }))
  const coinbase = test.coinbase ?? beneficiary
  if (!accounts.has(dec(coinbase))) put(record(coinbase, { balance: 11 }))
  return [...accounts.values()]
}
function headers(input, gasUsed, blobGasUsed) {
  const nat = value => unpadBytes(bigIntToBytes(BigInt(value)))
  const make = (number, timestamp, used, blobGas) => [new Uint8Array(32), new Uint8Array(32),
    hexToBytes(input.header.coinbase), new Uint8Array(32), new Uint8Array(32), new Uint8Array(32), new Uint8Array(256),
    nat(0), nat(number), nat(input.header.gasLimit), nat(used), nat(timestamp), new Uint8Array(),
    hexToBytes(word(9)), new Uint8Array(8), nat(2), new Uint8Array(32), nat(blobGas),
    nat(input.header.excessBlobGas), new Uint8Array(32)]
  const parentHeader = make(19_500_000, 1_710_338_235, input.header.gasLimit / 2n, 3n * unit)
  const childHeader = make(19_500_001, 1_710_338_236, gasUsed, blobGasUsed)
  childHeader[0] = keccak_256(RLP.encode(parentHeader))
  return { parentHeader: parentHeader.map(hex), childHeader: childHeader.map(hex) }
}
function envelope(tx) {
  const chain = tx.type === 0 ? (tx.v >= 35n ? (tx.v - 35n) / 2n : null) : tx.chainId
  return { type: tx.type, chainId: chain === null ? null : dec(chain), sender: dec(tx.getSenderAddress().toString()),
    to: dec(tx.to.toString()), nonce: dec(tx.nonce), value: dec(tx.value), gasLimit: dec(tx.gasLimit),
    gasPriceCap: dec(tx.type >= 2 ? tx.maxFeePerGas : tx.gasPrice),
    priorityFeeCap: dec(tx.type >= 2 ? tx.maxPriorityFeePerGas : 0), dataHex: hex(tx.data),
    accessList: (tx.accessList ?? []).map(([addr, storage]) => ({ address: dec(bytesToBigInt(addr)),
      storageKeys: storage.map(key => dec(bytesToBigInt(key))) })) }
}
function prepare(test) {
  const accounts = initialAccounts(test)
  const header = { number: 19_500_001n, timestamp: 1_710_338_236n, gasLimit: BigInt(test.blockGas ?? 30_000_000),
    gasUsed: 0n, baseFeePerGas: 2n, coinbase: test.coinbase ?? beneficiary, mixHash: word(9),
    blobGasUsed: 0n, excessBlobGas: test.excess ?? 0n }
  const block = createBlock({ header }, { common }), blobPrice = block.header.getBlobGasPrice()
  const nonces = new Map(accounts.map(row => [row.address, BigInt(row.nonce)]))
  const signed = test.entries.map(spec => {
    const key = spec.key ?? 0, from = dec(senders[key]), nonce = BigInt(spec.nonce ?? nonces.get(from))
    nonces.set(from, nonce + 1n)
    const fee = spec.type >= 2 ? { maxFeePerGas: BigInt(spec.cap ?? 7), maxPriorityFeePerGas: BigInt(spec.priority ?? 3) }
      : { gasPrice: BigInt(spec.cap ?? 7) }
    const fields = { type: spec.type, nonce, gasLimit: BigInt(spec.gas ?? 100_000), value: BigInt(spec.value ?? 7),
      to: spec.to ?? parent, data: '0x' + (spec.data ?? ''), ...fee,
      ...(spec.type ? { accessList: spec.accessList ?? [] } : {}),
      ...(spec.type === 3 ? { blobVersionedHashes: spec.hashes, maxFeePerBlobGas: blobPrice + 5n } : {}) }
    const bytes = createTx(fields, { common }).sign(keys[key]).serialize(), decoded = createTxFromRLP(bytes, { common })
    assert(decoded.verifySignature()); assert.equal(decoded.getSenderAddress().toString(), senders[key])
    assert.deepEqual(decoded.serialize(), bytes)
    const entry = { fuel: dec(spec.fuel ?? 1000), transaction: envelope(decoded),
      ...(decoded.type === 3 ? { blobVersionedHashes: decoded.blobVersionedHashes.map(h => h.slice(2)),
        maxFeePerBlobGas: dec(decoded.maxFeePerBlobGas) } : {}) }
    return { tx: decoded, bytes, entry }
  })
  const input = { test, header, block, blobPrice, signed,
    request: { schemaVersion: 1, accounts, transactions: signed.map(x => x.entry) } }
  Object.assign(input.request, headers(input, 0n, 0n))
  return input
}
function assertBinding(input, request = input.request) {
  assert.equal(request.transactions.length, input.signed.length, 'signed list length')
  input.signed.forEach((signed, index) => {
    const decoded = createTxFromRLP(signed.bytes, { common }), entry = request.transactions[index]
    assert(decoded.verifySignature()); assert.deepEqual(decoded.serialize(), signed.bytes)
    assert.deepEqual(entry.transaction, envelope(decoded), 'exact signed envelope at index ' + index)
    if (decoded.type === 3) {
      assert.deepEqual(entry.blobVersionedHashes, decoded.blobVersionedHashes.map(h => h.slice(2)), 'signed hashes')
      assert.equal(entry.maxFeePerBlobGas, dec(decoded.maxFeePerBlobGas), 'signed blob fee cap')
    } else {
      assert.equal(entry.blobVersionedHashes, undefined); assert.equal(entry.maxFeePerBlobGas, undefined)
    }
  })
}
async function seed(vm, accounts) {
  for (const entry of accounts) {
    if (!entry.exists) continue
    const addr = createAddressFromString(address(entry.address))
    await vm.stateManager.putAccount(addr, new Account(BigInt(entry.nonce), BigInt(entry.balance)))
    if (entry.codeHex) await vm.stateManager.putCode(addr, hexToBytes('0x' + entry.codeHex))
    for (const slot of entry.storage) if (BigInt(slot.value))
      await vm.stateManager.putStorage(addr, hexToBytes(word(slot.key)), unpadBytes(bigIntToBytes(BigInt(slot.value))))
  }
}
async function observeAccounts(vm, accounts) {
  const out = []
  for (const entry of accounts) {
    const addr = createAddressFromString(address(entry.address)), account = await vm.stateManager.getAccount(addr), storage = []
    for (const { key } of entry.storage) storage.push({ key,
      value: dec(bytesToBigInt(await vm.stateManager.getStorage(addr, hexToBytes(word(key))))) })
    out.push({ address: entry.address, exists: account !== undefined, balance: dec(account?.balance ?? 0),
      nonce: dec(account?.nonce ?? 0), codeHex: hex(await vm.stateManager.getCode(addr)), storage })
  }
  return out
}
const logFields = ([addr, topics, data]) => ({ address: dec(bytesToBigInt(addr)),
  topics: topics.map(topic => dec(bytesToBigInt(topic))), dataHex: hex(data) })
function receiptBytes(receipt) {
  const bloom = new Bloom()
  const logs = receipt.logs.map(log => {
    const addr = hexToBytes(address(log.address)), topics = log.topics.map(topic => hexToBytes(word(topic)))
    bloom.add(addr); topics.forEach(topic => bloom.add(topic))
    return [addr, topics, hexToBytes('0x' + log.dataHex)]
  })
  return encodeReceipt({ status: receipt.receiptStatus, cumulativeBlockGasUsed: BigInt(receipt.cumulativeGasUsed),
    bitvector: bloom.bitvector, logs }, receipt.type)
}
const frameError = error => /out of gas/.test(error) ? 'outOfGas' : /stack underflow/.test(error) ? 'stackUnderflow' :
  /stack overflow/.test(error) ? 'stackOverflow' : 'invalidOpcode'
async function reference(input) {
  const vm = await createVM({ common }); await seed(vm, input.request.accounts)
  assert.equal(await vm.stateManager.getAccount(beaconRoots), undefined, 'no beacon-root system contract in this fixture')
  let blobGas = 0n, lastOpcode
  const receipts = [], encoded = []
  vm.evm.events.on('step', event => { if (event.depth === 0) lastOpcode = event.opcode.name })
  vm.events.on('beforeTx', () => { lastOpcode = undefined })
  vm.events.on('afterTx', result => {
    const tx = result.transaction
    assert.deepEqual(tx.serialize(), input.signed[receipts.length].bytes, 'same ordered signed bytes in real runTx')
    const error = result.execResult.exceptionError?.error ?? '', gross = tx.getIntrinsicGas() + result.execResult.executionGasUsed
    const effective = result.amountSpent / result.totalGasSpent
    blobGas += result.receipt.blobGasUsed ?? 0n
    receipts.push({ type: tx.type, receiptStatus: result.receipt.status,
      frameStatus: error === 'revert' ? 'reverted' : error ? 'exceptional' : lastOpcode === 'RETURN' ? 'returned' : 'stopped',
      ...(error && error !== 'revert' ? { frameError: frameError(error) } : {}),
      gasUsedBeforeRefund: dec(gross), refundGas: dec(gross - result.totalGasSpent), gasUsed: dec(result.totalGasSpent),
      cumulativeGasUsed: dec(result.receipt.cumulativeBlockGasUsed), effectiveGasPrice: dec(effective),
      gasWeiReturned: dec((tx.gasLimit - result.totalGasSpent) * effective), beneficiaryTip: dec(result.minerValue),
      baseFeeBurn: dec(result.amountSpent - result.minerValue), returnBytesHex: hex(result.execResult.returnValue),
      logs: result.receipt.logs.map(logFields), blobGasUsed: dec(result.receipt.blobGasUsed ?? 0),
      blobFeeBurn: dec((result.receipt.blobGasUsed ?? 0n) * (result.receipt.blobGasPrice ?? 0n)) })
    encoded.push(encodeReceipt(result.receipt, tx.type))
  })
  const declaredBlobGas = input.test.declaredBlobGas ?? input.signed.reduce((sum, { tx }) =>
    sum + (tx.type === 3 ? unit * BigInt(tx.blobVersionedHashes.length) : 0n), 0n)
  const block = createBlock({ header: { ...input.header, blobGasUsed: declaredBlobGas,
    transactionsTrie: await trieRoot(input.signed.map(x => x.bytes)) },
    transactions: input.signed.map(x => x.tx), withdrawals: [] }, { common })
  assert.deepEqual(block.transactions.map(tx => tx.serialize()), input.signed.map(x => x.bytes))
  // runBlock owns cumulative gas-pool admission and validates the aggregate blob
  // inventory. A bare runTx call does neither. Header ancestry is outside this
  // list-stage fixture; body validation remains enabled. Its Cancun beacon-root
  // operation is a no-op because that account is absent, and withdrawals are empty.
  let result
  try { result = await runBlock(vm, { block, generate: true, skipHeaderValidation: true }) }
  catch (error) {
    const message = String(error), blockIndex = /errors at tx (\d+):/.exec(message)
    return { rejection: blockIndex ? Number(blockIndex[1]) : receipts.length,
      stage: blockIndex ? 'block-data-validation' : 'runBlock', message, receipts, encoded }
  }
  assert.equal(await vm.stateManager.getAccount(beaconRoots), undefined, 'beacon-root operation created no system state')
  assert.equal(result.results.length, input.signed.length)
  assert.deepEqual(result.receipts.map((receipt, index) => encodeReceipt(receipt, input.signed[index].tx.type)), encoded)
  assert.equal(bytesToHex(result.stateRoot), bytesToHex(await vm.stateManager.getStateRoot()))
  return { root: bytesToHex(result.stateRoot), receiptsRoot: bytesToHex(result.receiptsRoot), encoded, systemStateChecked: true,
    response: { schemaVersion: 1, status: 'executed', keccakOptIn: true, gasUsed: dec(result.gasUsed), blobGasUsed: dec(blobGas),
      receipts, accounts: await observeAccounts(vm, input.request.accounts) } }
}
function runGeth(input) {
  const alloc = Object.fromEntries(input.request.accounts.filter(a => a.exists).map(a => [address(a.address), {
    balance: quantity(a.balance), nonce: quantity(a.nonce), code: '0x' + a.codeHex,
    storage: Object.fromEntries(a.storage.map(slot => [word(slot.key), word(slot.value)])) }]))
  const env = { currentCoinbase: input.header.coinbase, currentNumber: quantity(input.header.number),
    currentTimestamp: quantity(input.header.timestamp), currentGasLimit: quantity(input.header.gasLimit),
    currentBaseFee: quantity(input.header.baseFeePerGas), currentRandom: input.header.mixHash,
    currentExcessBlobGas: quantity(input.header.excessBlobGas), parentBeaconBlockRoot: word(0), withdrawals: [] }
  const body = RLP.encode(input.signed.map(x => x.tx.type === 0 ? RLP.decode(x.bytes) : x.bytes))
  for (const [name, value] of [['alloc.json', alloc], ['env.json', env], ['txs.rlp', bytesToHex(body)]])
    writeFileSync(join(directory, name), JSON.stringify(value))
  for (const name of ['post.json', 'result.json', ...input.signed.map((x, index) =>
    `trace-${index}-${bytesToHex(x.tx.hash())}.jsonl`)]) rmSync(join(directory, name), { force: true })
  const p = spawnSync(process.env.EVM_GETH_EXE, ['t8n', '--state.fork', 'Cancun', '--state.chainid', '1', '--state.reward=-1',
    '--trace', '--trace.returndata', '--input.alloc', join(directory, 'alloc.json'), '--input.env', join(directory, 'env.json'),
    '--input.txs', join(directory, 'txs.rlp'), '--output.basedir', directory, '--output.alloc', 'post.json', '--output.result', 'result.json'],
    { encoding: 'utf8', timeout: 30_000, maxBuffer: 8 * 1024 * 1024 })
  if (p.error || p.status !== 0) throw Error('Geth t8n failed: ' + String(p.error ?? p.stdout + p.stderr))
  const result = JSON.parse(readFileSync(join(directory, 'result.json')))
  if ((result.rejected ?? []).length) return { rejected: result.rejected, result }
  assert.equal(result.receipts.length, input.signed.length)
  const post = JSON.parse(readFileSync(join(directory, 'post.json')))
  const accounts = input.request.accounts.map(entry => {
    const value = post[address(entry.address)]
    return { address: entry.address, exists: value !== undefined, balance: dec(value?.balance ?? 0), nonce: dec(value?.nonce ?? 0),
      codeHex: (value?.code ?? '0x').slice(2), storage: entry.storage.map(slot => ({ key: slot.key,
        value: dec(value?.storage?.[word(slot.key)] ?? 0) })) }
  })
  assert.deepEqual(Object.keys(post).sort(), accounts.filter(a => a.exists).map(a => address(a.address)).sort())
  const receipts = input.signed.map((signed, index) => {
    const receipt = result.receipts[index]
    assert.equal(receipt.transactionHash, bytesToHex(signed.tx.hash()), 'same ordered signed bytes')
    const trace = readFileSync(join(directory, `trace-${index}-${bytesToHex(signed.tx.hash())}.jsonl`), 'utf8')
      .trim().split('\n').map(JSON.parse)
    const terminal = trace.at(-1), top = trace.filter(event => event.depth === 1 && event.op !== undefined)
    assert.equal(typeof terminal.output, 'string', 'actual Geth output is required')
    const output = terminal.output.replace(/^0x/, ''); assert.match(output, /^(?:[0-9a-f]{2})*$/)
    const error = terminal.error ?? ''
    return { type: signed.tx.type, receiptStatus: Number(BigInt(receipt.status)),
      frameStatus: error === 'execution reverted' ? 'reverted' : error ? 'exceptional' : top.at(-1)?.op === 0xf3 ? 'returned' : 'stopped',
      returnBytesHex: output, gasUsed: dec(receipt.gasUsed), cumulativeGasUsed: dec(receipt.cumulativeGasUsed),
      logs: (receipt.logs ?? []).map(log => ({ address: dec(log.address), topics: log.topics.map(dec), dataHex: log.data.slice(2) })),
      blobGasUsed: dec(receipt.blobGasUsed ?? 0), blobFeeBurn: dec(BigInt(receipt.blobGasUsed ?? 0) * BigInt(receipt.blobGasPrice ?? 0)),
      traceSha256: digest(JSON.stringify(trace)) }
  })
  return { root: result.stateRoot, receiptsRoot: result.receiptsRoot, txRoot: result.txRoot, gasUsed: dec(result.gasUsed),
    blobGasUsed: dec(result.currentBlobGasUsed ?? receipts.reduce((n, r) => n + BigInt(r.blobGasUsed), 0n)), accounts, receipts }
}
async function trieRoot(values) {
  const trie = new MerklePatriciaTrie({ common })
  for (let index = 0; index < values.length; index++) await trie.put(RLP.encode(index), values[index])
  return bytesToHex(trie.root())
}
async function stateRoot(accounts) {
  const vm = await createVM({ common }); await seed(vm, accounts)
  return bytesToHex(await vm.stateManager.getStateRoot())
}
async function compareClients(input, expected, alternate) {
  if (input.test.category === 'admission') {
    assert.equal(expected.rejection, input.test.rejectIndex, 'EthereumJS rejection must match the native fixture index')
    assert.equal(alternate.rejected?.[0]?.index, input.test.rejectIndex, 'Geth rejection must match the native fixture index')
  } else {
    // A local native boundary is counted only when both clients execute it.
    assert.equal(expected.rejection, undefined, 'the fixture must execute in EthereumJS')
    assert.equal(alternate.rejected, undefined, 'the fixture must execute in Geth')
  }
  if (expected.rejection !== undefined) {
    assert.equal(alternate.rejected?.[0]?.index, expected.rejection, 'first rejected signed transaction')
    return
  }
  assert.equal(alternate.rejected, undefined, 'all reference transactions admitted')
  const out = expected.response
  assert.equal(alternate.gasUsed, out.gasUsed); assert.equal(alternate.blobGasUsed, out.blobGasUsed)
  assert.deepEqual(alternate.accounts, out.accounts); assert.equal(alternate.root, expected.root)
  assert.equal(alternate.receiptsRoot, expected.receiptsRoot)
  assert.equal(expected.receiptsRoot, await trieRoot(expected.encoded))
  assert.equal(alternate.txRoot, await trieRoot(input.signed.map(x => x.bytes)))
  out.receipts.forEach((receipt, index) => {
    const other = alternate.receipts[index]
    for (const field of ['type', 'receiptStatus', 'frameStatus', 'returnBytesHex', 'gasUsed', 'cumulativeGasUsed',
      'logs', 'blobGasUsed', 'blobFeeBurn']) assert.deepEqual(other[field], receipt[field], `${index}/${field}`)
    assert.deepEqual(receiptBytes(receipt), expected.encoded[index])
    assert.deepEqual(receiptBytes(other), expected.encoded[index])
  })
}
async function compareExecution(actual, expected, alternate) {
  assert.deepEqual(actual, expected.response, 'complete ordered-list output')
  assert.equal(await stateRoot(actual.accounts), alternate.root, 'complete final state commitment')
  assert.equal(await trieRoot(actual.receipts.map(receiptBytes)), alternate.receiptsRoot, 'ordered receipt commitment')
}
function runNative(request, { raw, optIn = true } = {}) {
  const path = join(directory, 'list.json')
  writeFileSync(path, raw ?? JSON.stringify(request))
  nativeInvocations++
  const p = spawnSync(executable, [...(optIn ? ['--dangerously-enable-unverified-keccak'] : []), '--transaction-list', path],
    { encoding: 'utf8', timeout: 60_000, maxBuffer: 64 * 1024 * 1024 + 1024 })
  if (p.error) throw p.error
  assert([0, 2].includes(p.status), p.stdout + '\n' + p.stderr)
  assert.equal(p.stderr, '', 'native diagnostic output must be structured')
  return { exitCode: p.status, value: JSON.parse(p.stdout) }
}

const mutationNames = ['changedGas', 'changedSignedChainId', 'changedSignedAccessList', 'changedOutputByte',
  'changedBlobBurn', 'changedBlobGas', 'changedSignedHashByte', 'changedSignedHashOrder', 'changedReceiptStatus',
  'changedStateBalance', 'changedLogData', 'changedStorageWord', 'omittedRow', 'changedFinalGas',
  'changedFinalBlobGas', 'changedCumulativeGas', 'omittedReceipt', 'reorderedTransactions', 'reorderedReceipts',
  'changedSignedNonce', 'omittedSignedTransaction', 'changedSignedBlobFeeCap', 'shiftedReferenceRejectionIndexes',
  'bothReferencesAcceptInvalidList', 'bothReferencesRejectLocalBoundary']
const negativeControls = Object.fromEntries(mutationNames.map(name => [name, false])), localControls = []
async function checkControls(saved) {
  const fixture = id => {
    const found = saved.find(item => item.input.test.id === id)
    assert(found?.actual, 'a fully matched native fixture is required for ' + id)
    return found
  }
  const first = fixture('single-blobhash'), ordinary = fixture('ordinary-mixed-types')
  const context = fixture('hash-context-reset'), pair = fixture('six-blob-aggregate'), warm = fixture('access-list-reset')
  async function changed(name, sample, mutate) {
    const corrupted = structuredClone(sample.actual); mutate(corrupted)
    await assert.rejects(() => compareExecution(corrupted, sample.expected, sample.alternate), undefined, name)
    negativeControls[name] = true
  }
  function binding(name, sample, mutate) {
    const corrupted = structuredClone(sample.input.request), before = nativeInvocations
    mutate(corrupted)
    assert.throws(() => assertBinding(sample.input, corrupted), undefined, name)
    assert.equal(nativeInvocations, before, 'signed binding fails before native execution')
    negativeControls[name] = true
  }
  const increment = (object, field, amount = 1n) => { object[field] = dec(BigInt(object[field]) + amount) }
  const flipByte = value => (value.startsWith('00') ? '01' : '00') + value.slice(2)
  await changed('changedGas', first, value => increment(value.receipts[0], 'gasUsed'))
  binding('changedSignedChainId', first, value => { value.transactions[0].transaction.chainId = '2' })
  binding('changedSignedAccessList', warm, value => { value.transactions[0].transaction.accessList[0].storageKeys[0] = '1' })
  await changed('changedOutputByte', first, value => { value.receipts[0].returnBytesHex = flipByte(value.receipts[0].returnBytesHex) })
  await changed('changedBlobBurn', first, value => increment(value.receipts[0], 'blobFeeBurn'))
  await changed('changedBlobGas', first, value => increment(value.receipts[0], 'blobGasUsed', unit))
  binding('changedSignedHashByte', first, value => {
    const original = value.transactions[0].blobVersionedHashes[0]
    value.transactions[0].blobVersionedHashes[0] = original.slice(0, 2) + flipByte(original.slice(2))
  })
  binding('changedSignedHashOrder', pair, value => { value.transactions[0].blobVersionedHashes.reverse() })
  await changed('changedReceiptStatus', first, value => { value.receipts[0].receiptStatus = 0 })
  await changed('changedStateBalance', first, value => increment(value.accounts[0], 'balance'))
  await changed('changedLogData', first, value => { value.receipts[0].logs[0].dataHex = flipByte(value.receipts[0].logs[0].dataHex) })
  await changed('changedStorageWord', first, value => increment(value.accounts.find(row => row.address === dec(parent)).storage[0], 'value'))
  await changed('omittedRow', first, value => { value.accounts.pop() })
  await changed('changedFinalGas', first, value => increment(value, 'gasUsed'))
  await changed('changedFinalBlobGas', first, value => increment(value, 'blobGasUsed', unit))
  await changed('changedCumulativeGas', context, value => increment(value.receipts[1], 'cumulativeGasUsed'))
  await changed('omittedReceipt', context, value => { value.receipts.splice(1, 1) })
  binding('reorderedTransactions', context, value => { value.transactions.reverse() })
  await changed('reorderedReceipts', context, value => { value.receipts.reverse() })
  binding('changedSignedNonce', first, value => increment(value.transactions[0].transaction, 'nonce'))
  binding('omittedSignedTransaction', context, value => { value.transactions.pop() })
  binding('changedSignedBlobFeeCap', first, value => increment(value.transactions[0], 'maxFeePerBlobGas'))
  {
    const admission = fixture('invalid-middle-nonce')
    const wrongExpected = structuredClone(admission.expected), wrongAlternate = structuredClone(admission.alternate)
    wrongExpected.rejection++; wrongAlternate.rejected[0].index++
    await assert.rejects(() => compareClients(admission.input, wrongExpected, wrongAlternate),
      /EthereumJS rejection must match the native fixture index/)
    negativeControls.shiftedReferenceRejectionIndexes = true
    // Internally agreeing execution observations and the expected signed-body
    // root must not turn a declared admission-refusal fixture into a pass.
    const executed = fixture('dependent-nonces'), acceptedAlternate = structuredClone(executed.alternate)
    acceptedAlternate.txRoot = await trieRoot(admission.input.signed.map(tx => tx.bytes))
    await assert.rejects(() => compareClients(admission.input, executed.expected, acceptedAlternate),
      /EthereumJS rejection must match the native fixture index/)
    negativeControls.bothReferencesAcceptInvalidList = true
    const boundary = fixture('unsupported-middle-frame')
    await assert.rejects(() => compareClients(boundary.input, admission.expected, admission.alternate),
      /the fixture must execute in EthereumJS/)
    negativeControls.bothReferencesRejectLocalBoundary = true
  }
  assert.equal(Object.values(negativeControls).filter(Boolean).length, mutationNames.length)

  function refused(id, request, outcome, { exitCode = 0, reasonPattern } = {}) {
    const before = nativeInvocations, result = runNative(request)
    assert.equal(nativeInvocations - before, 1)
    assert.equal(result.exitCode, exitCode, id)
    assert.equal(result.value.schemaVersion, 1); assert.equal(result.value.keccakOptIn, true)
    for (const [key, value] of Object.entries(outcome)) assert.deepEqual(result.value[key], value, `${id}/${key}`)
    assert.equal(typeof result.value.reason, 'string')
    if (reasonPattern) assert.match(result.value.reason, reasonPattern)
    assert(!('accounts' in result.value) && !('receipts' in result.value) && !('gasUsed' in result.value) &&
      !('blobGasUsed' in result.value), id + ': no accepted partial state, receipts or counters')
    assert(Object.keys(result.value).every(key => ['schemaVersion', 'status', 'keccakOptIn', 'index', 'reason', 'address', 'slot'].includes(key)))
    localControls.push({ id, matched: true, nativeInvocations: 1, requestSha256: digest(JSON.stringify(request)),
      exitCode, ...result.value })
  }
  const natHex = value => hex(unpadBytes(bigIntToBytes(BigInt(value))))
  for (const amount of [1n, -1n]) {
    const request = structuredClone(ordinary.input.request)
    request.childHeader[10] = natHex(BigInt(ordinary.actual.gasUsed) + amount)
    refused(amount > 0n ? 'declared-final-gas-plus-one' : 'declared-final-gas-minus-one', request,
      { status: 'rejected', index: null, reason: 'execution-gas-total-mismatch' })
  }
  for (const amount of [unit, -unit]) {
    const request = structuredClone(first.input.request)
    request.childHeader[17] = natHex(BigInt(first.actual.blobGasUsed) + amount)
    refused(amount > 0n ? 'declared-final-blob-plus-one' : 'declared-final-blob-minus-one', request,
      amount > 0n ? { status: 'rejected', index: null, reason: 'blob-gas-total-mismatch' } :
        { status: 'rejected', index: 0, reason: 'declared-gas-total-exceeded' })
  }
  {
    const request = structuredClone(ordinary.input.request); delete request.transactions[1].fuel
    refused('malformed-middle-entry', request, { status: 'inputError' }, { exitCode: 2, reasonPattern: /fuel/ })
  }
  {
    const request = structuredClone(ordinary.input.request); request.transactions[1].transaction.type = 4
    refused('unsupported-middle-kind', request, { status: 'indeterminate', index: 1, reason: 'unsupported-transaction-type' })
  }
  {
    const request = structuredClone(ordinary.input.request)
    Object.assign(request.transactions[1], { blobVersionedHashes: [hashes[0].slice(2)], maxFeePerBlobGas: '6' })
    refused('ordinary-middle-blob-fields', request, { status: 'rejected', index: 1, reason: 'ordinary-blob-fields' })
  }
  {
    const request = structuredClone(context.input.request)
    delete request.transactions[1].blobVersionedHashes; delete request.transactions[1].maxFeePerBlobGas
    refused('blob-middle-missing-fields', request, { status: 'rejected', index: 1, reason: 'missing-blob-fields' })
  }
  {
    const request = structuredClone(ordinary.input.request); request.transactions[1].fuel = '0'
    refused('middle-fuel-exhaustion', request, { status: 'indeterminate', index: 1, reason: 'stepLimit' })
  }
  {
    const request = structuredClone(ordinary.input.request); request.transactions[1].transaction.to = dec(child)
    request.accounts = request.accounts.filter(row => row.address !== dec(child))
    refused('middle-missing-state-witness', request, { status: 'indeterminate', index: 1,
      reason: 'incompleteState', address: dec(child), slot: null })
  }
  {
    const request = structuredClone(fixture('maximum-reserved-fuel').input.request)
    request.transactions[0].fuel = '500001'
    refused('aggregate-fuel-one-over', request, { status: 'indeterminate', index: null, reason: 'resourceLimit' })
  }
  {
    const request = structuredClone(ordinary.input.request); request.transactions.reverse()
    refused('native-reordered-envelopes', request, { status: 'rejected', index: 0, reason: 'invalid-sender-nonce' })
  }
  for (const [id, timestamp] of [['empty-before-cancun', 1_710_338_134], ['empty-at-prague', 1_746_612_311]]) {
    const request = structuredClone(fixture('empty-list').input.request); request.childHeader[11] = natHex(timestamp)
    refused(id, request, { status: 'indeterminate', index: null, reason: 'outside-cancun-transaction-rules' })
  }
  // These two separately counted resource controls execute valid signed lists
  // in both clients, including their complete actual 16 MiB return data. The
  // final entry returns one additional byte in the second list. Native output
  // is accepted at the bound and refused before any partial output above it.
  for (const extra of [0, 1]) {
    const id = extra ? 'aggregate-observation-one-over' : 'aggregate-observation-exact-cap'
    const test = { id, code: push(65536) + '5ff3', childCode: push(65537) + '5ff3',
      entries: Array.from({ length: 256 }, (_, index) => tx(2, { gas: 60_000, fuel: 10, value: 0,
        to: extra && index === 255 ? child : parent })) }
    const input = prepare(test); assertBinding(input)
    const expected = await reference(input), alternate = runGeth(input)
    await compareClients(input, expected, alternate)
    const outputBytes = expected.response.receipts.reduce((sum, receipt) => sum + receipt.returnBytesHex.length / 2, 0)
    assert.equal(outputBytes, byteLimit + extra)
    Object.assign(input.request, headers(input, BigInt(expected.response.gasUsed), 0n))
    if (extra) {
      refused(id, input.request, { status: 'indeterminate', index: 255, reason: 'resourceLimit' })
      Object.assign(localControls.at(-1), { outputBytes, referenceClientsAgree: true,
        ethereumJSExecuted: true, gethExecuted: true, nativeComparison: 'local-resource-refusal' })
    } else {
      const before = nativeInvocations, result = runNative(input.request)
      assert.equal(nativeInvocations - before, 1); assert.equal(result.exitCode, 0)
      await compareExecution(result.value, expected, alternate)
      localControls.push({ id, matched: true, status: 'executed', nativeInvocations: 1,
        requestSha256: digest(JSON.stringify(input.request)), outputBytes, receipts: result.value.receipts.length,
        gasUsed: result.value.gasUsed, blobGasUsed: result.value.blobGasUsed,
        stateRoot: alternate.root, receiptsRoot: alternate.receiptsRoot, transactionRoot: alternate.txRoot,
        ethereumJSMatched: true, gethMatched: true, referenceClientsAgree: true,
        ethereumJSExecuted: true, gethExecuted: true, nativeComparison: 'exact-execution' })
    }
  }
  assert.equal(localControls.length, 16)
}

const selected = smoke ? cases.slice(0, 1) : cases, rows = [], failures = [], saved = []
let clientAgreement = 0, executionMatches = 0, admissionRefusals = 0, localBoundaries = 0, primaryNativeInvocations = 0
try {
  for (const test of selected) {
    let stage = 'prepare'
    try {
      const input = prepare(test); assertBinding(input)
      stage = 'EthereumJS runBlock with ordered signed runTx'; const expected = await reference(input)
      stage = 'Geth whole-list t8n'; const alternate = runGeth(input)
      stage = 'reference agreement'; await compareClients(input, expected, alternate); clientAgreement++
      const gas = expected.response ? BigInt(expected.response.gasUsed) : BigInt(alternate.result.gasUsed)
      const blobGas = test.declaredBlobGas ?? (expected.response ? BigInt(expected.response.blobGasUsed) :
        BigInt(alternate.result.currentBlobGasUsed ?? 0))
      Object.assign(input.request, headers(input, gas, blobGas))
      if (smoke && process.env.TRANSACTION_LIST_FIXTURE_PATH)
        writeFileSync(process.env.TRANSACTION_LIST_FIXTURE_PATH, JSON.stringify(input.request, null, 2) + '\n')
      saved.push({ input, expected, alternate })
      if (referencesOnly) { rows.push({ id: test.id, category: test.category, transactions: input.signed.length, referencesAgree: true }); continue }
      stage = 'one native whole-list invocation'
      const before = nativeInvocations, actual = runNative(input.request)
      assert.equal(nativeInvocations - before, 1)
      primaryNativeInvocations++
      assert.equal(actual.exitCode, 0)
      if (test.category === 'execution') {
        await compareExecution(actual.value, expected, alternate)
        executionMatches++
      } else {
        assert.deepEqual(actual.value, { schemaVersion: 1, status: test.nativeStatus ?? 'rejected', keccakOptIn: true,
          index: test.rejectIndex, reason: test.reason }, test.id + ': no accepted partial result')
        if (test.category === 'admission') admissionRefusals++; else localBoundaries++
      }
      saved.at(-1).actual = actual.value
      rows.push({ id: test.id, category: test.category, transactions: input.signed.length, nativeInvocations: 1,
        status: actual.value.status, txBytes: input.signed.map(x => bytesToHex(x.bytes)),
        requestSha256: digest(JSON.stringify(input.request)), ...(test.category === 'execution' ? {
          gasUsed: actual.value.gasUsed, blobGasUsed: actual.value.blobGasUsed, stateRoot: alternate.root,
          receiptsRoot: alternate.receiptsRoot, transactionRoot: alternate.txRoot,
          receipts: actual.value.receipts, traceSha256: alternate.receipts.map(receipt => receipt.traceSha256),
          ethereumJSMatched: true, gethMatched: true, systemStateChecked: expected.systemStateChecked } : {
          reason: actual.value.reason, index: actual.value.index,
          ...(test.category === 'admission' ? { ethereumJSRejection: { index: expected.rejection, stage: expected.stage,
            message: expected.message }, gethRejections: alternate.rejected } : {}) }) })
    } catch (error) { failures.push({ id: test.id, stage, message: String(error).slice(0, 7000) }) }
  }
  if (!referencesOnly && !smoke && failures.length === 0) {
    try { await checkControls(saved) }
    catch (error) { failures.push({ id: 'persistent-controls', stage: 'comparator, binding and local bounds', message: String(error).slice(0, 7000) }) }
  }
} finally { rmSync(directory, { recursive: true, force: true }) }
const accepted = saved.filter(item => item.input.test.category === 'execution')
const receiptCounts = accepted.flatMap(item => item.expected.response.receipts)
console.log(JSON.stringify({ kind: 'ordered-cancun-transaction-lists-vs-ethereumjs-and-geth',
  mode: referencesOnly ? 'references-only' : smoke ? 'smoke' : 'full', cases: selected.length, passed: rows.length,
  executionMatches, admissionRefusals, localBoundaries, clientAgreement, nativeInvocations, primaryNativeInvocations,
  rejectedAdmissions: rows.filter(row => row.category === 'admission' && row.status === 'rejected').length,
  indeterminateAdmissions: rows.filter(row => row.category === 'admission' && row.status === 'indeterminate').length,
  controlNativeInvocations: nativeInvocations - primaryNativeInvocations,
  acceptedListTransactions: accepted.reduce((sum, item) => sum + item.input.signed.length, 0),
  allListTransactions: saved.reduce((sum, item) => sum + item.input.signed.length, 0),
  successfulReceipts: receiptCounts.filter(receipt => receipt.receiptStatus === 1).length,
  intentionalFailedReceipts: receiptCounts.filter(receipt => receipt.receiptStatus === 0).length,
  uniqueSignedByteStrings: new Set(saved.flatMap(item => item.input.signed.map(tx => bytesToHex(tx.bytes)))).size,
  controlsRun: !referencesOnly && !smoke && Object.values(negativeControls).every(Boolean),
  negativeControls, localControls,
  localResourceLists: localControls.filter(row => row.id.startsWith('aggregate-observation-')).length,
  localResourceTransactions: 256 * localControls.filter(row => row.id.startsWith('aggregate-observation-')).length,
  failed: failures.length, kzgOperations, nativeSha256: referencesOnly ? null : digest(readFileSync(executable)),
  geth: { version: geth.version, sourceCommit: geth.sourceCommit, sha256: geth.sha256 },
  rows, failures,
  referenceBoundary: 'EthereumJS runBlock performs body validation and cumulative gas-pool admission, with actual per-transaction runTx results. Geth executes the same whole signed list through Cancun t8n. A bare runTx loop failed the 100,000 block gas / 80,000 second reservation control and is not used.',
  systemState: 'Empty withdrawals and no beacon-root contract. EthereumJS runs its Cancun system operations; the beacon-root account remains absent and complete final state roots agree with Geth.',
  scope: 'Synthetic ordered decoded Cancun list transition from one initial witness. Host signature recovery, receipt/trie encoding, compiler/runtime and experimental Keccak remain trusted. Does not authenticate header transaction/state/receipt commitments, process nonempty withdrawals or deployed beacon-root code, verify KZG sidecars or prove chain membership. Local cap and malformed-input controls are separate from the 36-list execution/admission matrix; the independent 22-case transport script covers the exact 16 MiB request-file bound.' }))
if (failures.length || rows.length !== selected.length || kzgOperations !== 0 ||
  (!referencesOnly && !smoke && (Object.values(negativeControls).some(value => value !== true) || localControls.length !== 16))) process.exitCode = 1
