#!/usr/bin/env node
/**
 * Signed Cancun BLOBHASH transactions executed by Lean, EthereumJS and Geth.
 * Existing eels dependencies are test oracles and host codecs only. Lean receives
 * the exact decoded signed envelope and a complete synthetic account witness.
 * Neither signatures, KZG sidecars nor chain membership are proved by this test.
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
const { Bloom, createVM, encodeReceipt, runTx } = require('@ethereumjs/vm')
const { keccak_256 } = require('@noble/hashes/sha3.js')

const args = process.argv.slice(2)
const smoke = args.includes('--smoke')
const referencesOnly = args.includes('--references-only')
const positional = args.filter(x => !x.startsWith('--'))
const executable = positional[0] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-blob-call', import.meta.url))
const ordinaryExecutable = positional[1] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-call-transaction', import.meta.url))
assert(args.every(x => !x.startsWith('--') || ['--smoke', '--references-only'].includes(x)), 'unknown option')
const geth = openGeth()
assert(geth, 'EVM_GETH_EXE must name the existing pinned Geth executable')
const directory = mkdtempSync(join(tmpdir(), 'lean-blobhash-transactions-'))
// Bare signed execution envelopes have no sidecars. No KZG operation may be
// silently accepted; this is the existing Prague fixture gate's sentinel.
let kzgOperations = 0
const forbiddenKzg = new Proxy({}, { get(_target, operation) {
  kzgOperations++
  throw Error('KZG sidecar operation not permitted: ' + String(operation))
} })
const common = new Common({ chain: Mainnet, hardfork: Hardfork.Cancun, customCrypto: { kzg: forbiddenKzg } })
const dec = value => BigInt(value).toString()
const quantity = value => '0x' + BigInt(value).toString(16)
const address = value => '0x' + BigInt(value).toString(16).padStart(40, '0')
const word = value => '0x' + BigInt(value).toString(16).padStart(64, '0')
const hex = bytes => bytesToHex(bytes).slice(2)
const digest = bytes => createHash('sha256').update(bytes).digest('hex')
const unit = 131072n
const maxWord = (1n << 256n) - 1n
const senderKey = hexToBytes('0x' + '00'.repeat(31) + '01') // Public synthetic fixture key only.
const sender = createAddressFromPrivateKey(senderKey).toString()
const parent = address(0xc1), child = address(0xc2), grandchild = address(0xc3), beneficiary = address(0xc4)
const hashes = Array.from({ length: 6 }, (_, index) => '0x01' +
  Array.from({ length: 31 }, (_, byte) => ((index * 47 + byte * 19) % 256).toString(16).padStart(2, '0')).join(''))
const push = value => {
  const n = BigInt(value)
  assert(n >= 0n && n <= maxWord)
  if (n === 0n) return '5f'
  let h = n.toString(16)
  if (h.length % 2) h = '0' + h
  return (0x5f + h.length / 2).toString(16) + h
}
const returnHashes = (indices, ending = 'f3') => indices.map((index, slot) =>
  push(index) + '49' + push(slot * 32) + '52').join('') + push(indices.length * 32) + '5f' + ending
const record = (addr, { exists = true, balance = 0, nonce = 0, code = '', storage = [] } = {}) => ({
  address: dec(addr), exists, balance: dec(balance), nonce: dec(nonce), codeHex: code,
  storage: storage.map(([key, value]) => ({ key: dec(key), value: dec(value) })),
})
const variants = ['call', 'callcode', 'delegatecall', 'staticcall']
function invoke(op, target, { requested = 60_000, value = 0, output = 160 } = {}) {
  const operands = [output, 0, 0, 0]
  if (op === 'call' || op === 'callcode') operands.push(value)
  return [...operands, BigInt(target), requested].map(push).join('') +
    { call: 'f1', callcode: 'f2', delegatecall: 'f4', staticcall: 'fa' }[op]
}
function callerCode(op, target, options = {}) {
  const output = options.output ?? 160
  return invoke(op, target, options) + push(output) + '52' + push(5) + '49' +
    push(output + 32) + '52' + push(output + 64) + '5f' + (options.ending ?? 'f3')
}
function effects(index = 5, ending = 'f3') {
  return push(index) + '49805f555f52' + push(0xabc) + '60205fa1' + '60205f' + ending
}
const cases = []
const add = (id, category, properties) => cases.push({ id, category, type: 3, hashes, ...properties })
const lists = [['one', hashes.slice(0, 1)], ['six', hashes], ['reversed', [...hashes].reverse()],
  ['duplicates', [hashes[0], hashes[0], hashes[3], hashes[3], hashes[5], hashes[0]]]]
const indices = [0n, 1n, 2n, 5n, 6n, 7n, 255n, 256n, (1n << 32n) - 1n, 1n << 32n,
  (1n << 32n) + 1n, (1n << 64n) - 1n, 1n << 64n, (1n << 64n) + 5n, 1n << 128n, 1n << 255n, maxWord]
for (const [name, list] of lists) {
  for (const index of indices) add(`lookup/${name}/${index}`, 'lookup', { hashes: list, code: returnHashes([index]) })
  add(`lookup/${name}/whole-list`, 'list-order', { hashes: list, code: returnHashes([0, 1, 2, 3, 4, 5, 6, maxWord]) })
}
const leaf = returnHashes([0, 1, 5, 6, maxWord])
for (const type of [0, 1, 2]) {
  add(`ordinary/type${type}/direct`, 'ordinary-empty', { type, hashes: [], code: leaf })
  for (const op of variants) add(`ordinary/type${type}/${op}`, 'ordinary-empty',
    { type, hashes: [], code: callerCode(op, child), childCode: leaf, variants: [op] })
}
for (const op of variants) {
  for (const [name, list] of lists.filter(([name]) => name !== 'reversed'))
    add(`nested/${op}/${name}`, 'nested', { hashes: list, code: callerCode(op, child), childCode: leaf, variants: [op] })
  for (const inner of variants) add(`two-layer/${op}/${inner}`, 'two-layer', {
    code: callerCode(op, child, { requested: 150_000, output: 224 }),
    childCode: callerCode(inner, grandchild), grandchildCode: leaf, variants: [op, inner] })
  for (const gas of [4, 5, 6]) add(`child-gas/${op}/${gas}`, 'child-gas',
    { code: callerCode(op, child, { requested: gas }), childCode: '5f4900', variants: [op] })
  for (const gas of [2600, 3000]) add(`parent-gas/${op}/${gas}`, 'parent-gas',
    { code: callerCode(op, child, { requested: maxWord }), childCode: leaf, frameGas: gas, variants: [op] })
}
for (const [index, budget] of [[0, 5], [5, 6]]) for (const delta of [-1, 0, 1])
  add(`direct-gas/${index}/${budget + delta}`, 'direct-gas', { code: push(index) + '4900', frameGas: budget + delta })
add('stack/underflow', 'stack', { code: '49' })
add('stack/full-net-zero', 'stack', { code: '5f'.repeat(1024) + '4900', frameGas: 2051 })
add('stack/overflow-before-lookup', 'stack', { code: '5f'.repeat(1025) + '4900' })
add('gas/repeated-reads', 'direct-gas', { code: (push(5) + '4950').repeat(32) + returnHashes([0]) })
for (const [label, ending] of [['return', 'f3'], ['revert', 'fd'], ['invalid', 'fe']]) {
  add(`effects/direct/${label}`, 'effects', { code: effects(5, ending) })
  for (const op of variants.filter(op => op !== 'staticcall')) add(`effects/${op}/${label}`, 'effects',
    { code: callerCode(op, child, { requested: 100_000 }), childCode: effects(5, ending), variants: [op] })
}
add('effects/refund-clear', 'effects', { code: '5f5f55' + returnHashes([5]) })
add('static/state-write-fails-after-read', 'static-boundary', { code: callerCode('staticcall', child),
  childCode: effects(), variants: ['staticcall'] })
add('static/log-fails-after-read', 'static-boundary', { code: callerCode('staticcall', child),
  childCode: '5f495f5260205fa000', variants: ['staticcall'] })
for (const op of ['call', 'callcode']) for (const value of [7, 10_000])
  add(`value/${op}/${value}`, 'value', { code: callerCode(op, child, { value }), childCode: leaf, variants: [op] })
for (const excess of [30n * unit, 80n * unit, 400n * unit])
  for (const [label, ending] of [['return', 'f3'], ['revert', 'fd'], ['invalid', 'fe']])
    add(`blob-fee/${excess}/${label}`, 'blob-fee', { excess, code: '5f495f524a60205260405f' + ending })
assert.equal(cases.length, 173, 'fixed standalone fixture inventory')
assert.equal(new Set(cases.map(test => test.id)).size, cases.length, 'unique fixtures')
const sequenceCases = [3, 3, 0, 1, 2, 3].map((type, index) => ({
  id: `sequence/${index}/type${type}`, category: 'context-reset', type,
  hashes: type === 3 ? [hashes[index]] : [], code: effects(0),
}))
const inventory = [...cases, ...sequenceCases]
assert.equal(inventory.length, 179, 'fixed full signed transaction inventory')

function headerFields(number, timestamp, gasUsed, blobGas, excess) {
  const nat = value => unpadBytes(bigIntToBytes(BigInt(value)))
  return [new Uint8Array(32), new Uint8Array(32), hexToBytes(beneficiary), new Uint8Array(32),
    new Uint8Array(32), new Uint8Array(32), new Uint8Array(256), nat(0), nat(number), nat(30_000_000),
    nat(gasUsed), nat(timestamp), new Uint8Array(), hexToBytes(word(9)), new Uint8Array(8), nat(2),
    new Uint8Array(32), nat(blobGas), nat(excess), new Uint8Array(32)]
}
function makeHeaders(excess, gasUsed, blobGas) {
  const p = headerFields(19_500_000, 1_710_338_235, 15_000_000, 3n * unit, excess)
  const c = headerFields(19_500_001, 1_710_338_236, gasUsed, blobGas, excess)
  c[0] = keccak_256(RLP.encode(p))
  return { parentHeader: p.map(hex), childHeader: c.map(hex) }
}
function prepare(test, accounts, nonce = 7n, cumulative = 0n, priorBlobGas = 0n) {
  const header = { number: 19_500_001n, timestamp: 1_710_338_236n, gasLimit: 30_000_000n,
    gasUsed: 0n, baseFeePerGas: 2n, coinbase: beneficiary, mixHash: word(9),
    blobGasUsed: 0n, excessBlobGas: test.excess ?? 0n }
  const block = createBlock({ header }, { common })
  const blobPrice = block.header.getBlobGasPrice()
  const fee = test.type >= 2 ? { maxFeePerGas: 7n, maxPriorityFeePerGas: 3n } : { gasPrice: 7n }
  const fields = { type: test.type, nonce, gasLimit: BigInt(test.gas ?? 500_000), value: BigInt(test.value ?? 7),
    to: parent, data: '0x' + (test.data ?? ''), ...fee, ...(test.type ? { accessList: [] } : {}),
    ...(test.type === 3 ? { blobVersionedHashes: test.hashes, maxFeePerBlobGas: blobPrice + 5n } : {}) }
  if (test.frameGas !== undefined)
    fields.gasLimit = createTx(fields, { common }).getIntrinsicGas() + BigInt(test.frameGas)
  const signed = createTx(fields, { common }).sign(senderKey)
  const bytes = signed.serialize()
  const tx = createTxFromRLP(bytes, { common })
  assert(tx.verifySignature(), test.id + ': signed envelope')
  assert.equal(tx.getSenderAddress().toString(), sender)
  assert.deepEqual(tx.serialize(), bytes, 'canonical signed bytes must round-trip')
  if (tx.type === 3) assert.deepEqual(tx.blobVersionedHashes, test.hashes, 'signed hash list and order')
  const state = accounts ?? [record(sender, { balance: 10n ** 15n, nonce }),
    record(parent, { balance: 5000, nonce: 1, code: test.code, storage: [[0, 7], [1, 9], [2, 0], [3, 0]] }),
    record(child, { balance: 100, nonce: 1, code: test.childCode ?? '', storage: [[0, 7], [1, 9], [2, 0], [3, 0]] }),
    record(grandchild, { balance: 100, nonce: 1, code: test.grandchildCode ?? '', storage: [[0, 7], [1, 9], [2, 0], [3, 0]] }),
    record(beneficiary, { balance: 11, nonce: 1 })]
  const request = { schemaVersion: 1, fork: 'cancun', fuel: dec(test.fuel ?? 15_000),
    transaction: { type: tx.type, chainId: '1', sender: dec(sender), to: dec(tx.to.toString()), nonce: dec(tx.nonce),
      value: dec(tx.value), gasLimit: dec(tx.gasLimit), gasPriceCap: dec(tx.type >= 2 ? tx.maxFeePerGas : tx.gasPrice),
      priorityFeeCap: dec(tx.type >= 2 ? tx.maxPriorityFeePerGas : 0), dataHex: hex(tx.data),
      accessList: tx.type ? tx.accessList.map(([addr, keys]) => ({ address: dec(bytesToBigInt(addr)),
        storageKeys: keys.map(key => dec(bytesToBigInt(key))) })) : [] },
    block: { chainId: '1', coinbase: dec(beneficiary), number: dec(header.number), timestamp: dec(header.timestamp),
      gasLimit: dec(header.gasLimit), gasUsedBefore: dec(cumulative), baseFee: dec(header.baseFeePerGas),
      prevRandao: dec(header.mixHash), blobBaseFee: dec(blobPrice) }, accounts: state }
  if (tx.type === 3) Object.assign(request, makeHeaders(header.excessBlobGas, 30_000_000n,
    priorBlobGas + unit * BigInt(tx.blobVersionedHashes.length)), {
    blobVersionedHashes: tx.blobVersionedHashes.map(hash => hash.slice(2)),
    maxFeePerBlobGas: dec(tx.maxFeePerBlobGas), priorBlobGas: dec(priorBlobGas) })
  return { request, tx, bytes, header, block, blobPrice }
}
function assertBinding(input) {
  const decoded = createTxFromRLP(input.bytes, { common })
  assert(decoded.verifySignature(), 'binding: signed envelope')
  assert.deepEqual(decoded.serialize(), input.bytes, 'binding: canonical signed bytes')
  const tx = input.request.transaction
  assert.equal(tx.type, decoded.type, 'binding: transaction type')
  const signedChainId = decoded.type === 0
    ? (decoded.v >= 35n ? (decoded.v - 35n) / 2n : null)
    : decoded.chainId
  assert.equal(tx.chainId, signedChainId === null ? null : dec(signedChainId), 'binding: signed chain ID')
  assert.deepEqual(tx.accessList, (decoded.accessList ?? []).map(([addr, keys]) => ({
    address: dec(bytesToBigInt(addr)), storageKeys: keys.map(key => dec(bytesToBigInt(key))),
  })), 'binding: exact signed access list')
  assert.equal(tx.sender, dec(decoded.getSenderAddress().toString()), 'binding: recovered sender')
  assert.equal(tx.to, dec(decoded.to.toString()), 'binding: recipient')
  for (const key of ['nonce', 'value', 'gasLimit']) assert.equal(tx[key], dec(decoded[key]), 'binding: ' + key)
  assert.equal(tx.gasPriceCap, dec(decoded.type >= 2 ? decoded.maxFeePerGas : decoded.gasPrice), 'binding: fee cap')
  assert.equal(tx.priorityFeeCap, dec(decoded.type >= 2 ? decoded.maxPriorityFeePerGas : 0), 'binding: priority cap')
  assert.equal(tx.dataHex, hex(decoded.data), 'binding: calldata')
  if (decoded.type === 3) {
    assert.deepEqual(input.request.blobVersionedHashes, decoded.blobVersionedHashes.map(h => h.slice(2)),
      'binding: exact signed hash bytes, count and order')
    assert.equal(input.request.maxFeePerBlobGas, dec(decoded.maxFeePerBlobGas), 'binding: blob cap')
  }
}
async function seed(vm, accounts) {
  for (const entry of accounts) {
    if (!entry.exists) continue
    const addr = createAddressFromString(address(entry.address))
    await vm.stateManager.putAccount(addr, new Account(BigInt(entry.nonce), BigInt(entry.balance)))
    if (entry.codeHex) await vm.stateManager.putCode(addr, hexToBytes('0x' + entry.codeHex))
    for (const slot of entry.storage) if (BigInt(slot.value) !== 0n)
      await vm.stateManager.putStorage(addr, hexToBytes(word(slot.key)), unpadBytes(bigIntToBytes(BigInt(slot.value))))
  }
}
async function observeAccounts(vm, accounts) {
  const out = []
  for (const entry of accounts) {
    const addr = createAddressFromString(address(entry.address)), account = await vm.stateManager.getAccount(addr)
    const storage = []
    for (const { key } of entry.storage) storage.push({ key,
      value: dec(bytesToBigInt(await vm.stateManager.getStorage(addr, hexToBytes(word(key))))) })
    out.push({ address: entry.address, exists: account !== undefined, balance: dec(account?.balance ?? 0),
      nonce: dec(account?.nonce ?? 0), codeHex: hex(await vm.stateManager.getCode(addr)), storage })
  }
  return out
}
const logFields = ([addr, topics, data]) => ({ address: dec(bytesToBigInt(addr)),
  topics: topics.map(topic => dec(bytesToBigInt(topic))), dataHex: hex(data) })
function receiptBytes(value, type) {
  const bloom = new Bloom()
  const logs = value.logs.map(log => {
    const addr = hexToBytes(address(log.address)), topics = log.topics.map(t => hexToBytes(word(t)))
    bloom.add(addr); topics.forEach(t => bloom.add(t))
    return [addr, topics, hexToBytes('0x' + log.dataHex)]
  })
  return encodeReceipt({ status: value.receiptStatus, cumulativeBlockGasUsed: BigInt(value.cumulativeGasUsed),
    bitvector: bloom.bitvector, logs }, type)
}
const frameError = error => /out of gas/.test(error) ? 'outOfGas' :
  /stack underflow/.test(error) ? 'stackUnderflow' : /stack overflow/.test(error) ? 'stackOverflow' : 'invalidOpcode'
async function reference(test, input, existingVM) {
  const vm = existingVM ?? await createVM({ common })
  if (!existingVM) await seed(vm, input.request.accounts)
  let lastOpcode
  const step = event => { if (event.depth === 0) lastOpcode = event.opcode.name }
  vm.evm.events.on('step', step)
  const result = await runTx(vm, { tx: input.tx, block: input.block, blockGasUsed: BigInt(input.request.block.gasUsedBefore) })
  vm.evm.events.removeListener('step', step)
  const error = result.execResult.exceptionError?.error ?? ''
  const frameStatus = error === 'revert' ? 'reverted' : error ? 'exceptional' : lastOpcode === 'RETURN' ? 'returned' : 'stopped'
  const gross = input.tx.getIntrinsicGas() + result.execResult.executionGasUsed
  const effective = result.amountSpent / result.totalGasSpent
  const response = { schemaVersion: 1, status: 'executed', keccakOptIn: true,
    receiptStatus: result.receipt.status, frameStatus,
    ...(frameStatus === 'exceptional' ? { frameError: frameError(error) } : {}),
    gasUsedBeforeRefund: dec(gross), refundGas: dec(gross - result.totalGasSpent), gasUsed: dec(result.totalGasSpent),
    cumulativeGasUsed: dec(result.receipt.cumulativeBlockGasUsed), effectiveGasPrice: dec(effective),
    gasWeiReturned: dec((input.tx.gasLimit - result.totalGasSpent) * effective),
    beneficiaryTip: dec(result.minerValue), baseFeeBurn: dec(result.amountSpent - result.minerValue),
    returnBytesHex: hex(result.execResult.returnValue), logs: result.receipt.logs.map(logFields),
    accounts: await observeAccounts(vm, input.request.accounts) }
  const blobGas = result.receipt.blobGasUsed ?? 0n, blobPrice = result.receipt.blobGasPrice ?? 0n
  return { vm, root: bytesToHex(await vm.stateManager.getStateRoot()), receipt: encodeReceipt(result.receipt, input.tx.type),
    response, wrapper: input.tx.type === 3 ? { status: 'executed', blobGasUsed: dec(blobGas),
      blobFeeBurn: dec(blobGas * blobPrice), result: response } : response }
}
function runLean(input) {
  assertBinding(input)
  const path = join(directory, 'lean-request.jsonl')
  writeFileSync(path, JSON.stringify(input.request) + '\n')
  const isBlob = input.tx.type === 3
  const p = spawnSync(isBlob ? executable : ordinaryExecutable,
    ['--dangerously-enable-unverified-keccak', isBlob ? '--batch' : '--call-transaction', path],
    { encoding: 'utf8', timeout: 30_000, maxBuffer: 8 * 1024 * 1024 })
  if (p.error || p.status !== 0) throw Error('Lean entry failed: ' + String(p.error ?? p.stdout + p.stderr))
  return JSON.parse(p.stdout)
}
function runGeth(inputs, initialAccounts) {
  const input = inputs[0]
  const alloc = Object.fromEntries((initialAccounts ?? input.request.accounts).filter(a => a.exists).map(a => [address(a.address), {
    balance: quantity(a.balance), nonce: quantity(a.nonce), code: '0x' + a.codeHex,
    storage: Object.fromEntries(a.storage.map(s => [word(s.key), word(s.value)])) }]))
  const env = { currentCoinbase: beneficiary, currentNumber: quantity(input.header.number),
    currentTimestamp: quantity(input.header.timestamp), currentGasLimit: quantity(input.header.gasLimit),
    currentBaseFee: quantity(input.header.baseFeePerGas), currentRandom: input.header.mixHash,
    currentExcessBlobGas: quantity(input.header.excessBlobGas), parentBeaconBlockRoot: word(0), withdrawals: [] }
  const signed = inputs.map(x => x.tx.type === 0 ? RLP.decode(x.bytes) : x.bytes)
  for (const [name, value] of [['alloc.json', alloc], ['env.json', env], ['txs.rlp', bytesToHex(RLP.encode(signed))]])
    writeFileSync(join(directory, name), JSON.stringify(value))
  for (const name of ['geth-post.json', 'geth-result.json', ...inputs.map((x, index) =>
    `trace-${index}-${bytesToHex(x.tx.hash())}.jsonl`)]) rmSync(join(directory, name), { force: true })
  const p = spawnSync(process.env.EVM_GETH_EXE, ['t8n', '--state.fork', 'Cancun', '--state.chainid', '1',
    '--state.reward=-1', '--trace', '--trace.returndata', '--input.alloc', join(directory, 'alloc.json'),
    '--input.env', join(directory, 'env.json'), '--input.txs', join(directory, 'txs.rlp'), '--output.basedir', directory,
    '--output.alloc', 'geth-post.json', '--output.result', 'geth-result.json'],
    { encoding: 'utf8', timeout: 15_000, maxBuffer: 8 * 1024 * 1024 })
  if (p.error || p.status !== 0) throw Error('Geth t8n failed: ' + String(p.error ?? p.stdout + p.stderr))
  const result = JSON.parse(readFileSync(join(directory, 'geth-result.json')))
  assert.equal(result.receipts.length, inputs.length, 'all signed transactions must have Geth receipts')
  assert.equal((result.rejected ?? []).length, 0, 'no reference admission failures')
  const post = JSON.parse(readFileSync(join(directory, 'geth-post.json')))
  const accounts = inputs.at(-1).request.accounts.map(entry => {
    const a = post[address(entry.address)]
    return { address: entry.address, exists: a !== undefined, balance: dec(a?.balance ?? 0), nonce: dec(a?.nonce ?? 0),
      codeHex: (a?.code ?? '0x').slice(2), storage: entry.storage.map(s => ({ key: s.key, value: dec(a?.storage?.[word(s.key)] ?? 0) })) }
  })
  assert.deepEqual(Object.keys(post).sort(), accounts.filter(a => a.exists).map(a => address(a.address)).sort(),
    'all Geth post-state accounts must be observed')
  const transactions = inputs.map((x, index) => {
    const receipt = result.receipts[index]
    assert.equal(receipt.transactionHash, bytesToHex(x.tx.hash()), 'Geth executes the exact signed transaction')
    const logs = (receipt.logs ?? []).map(log => ({ address: dec(log.address), topics: log.topics.map(dec), dataHex: log.data.slice(2) }))
    const trace = readFileSync(join(directory, `trace-${index}-${bytesToHex(x.tx.hash())}.jsonl`), 'utf8')
      .trim().split('\n').map(JSON.parse)
    const terminal = trace.at(-1)
    assert.equal(typeof terminal.output, 'string', 'Geth must provide actual terminal return bytes')
    const returnBytesHex = terminal.output.replace(/^0x/, '')
    assert.match(returnBytesHex, /^(?:[0-9a-f]{2})*$/, 'complete Geth output encoding')
    const top = trace.filter(event => event.depth === 1 && event.op !== undefined)
    const last = top.at(-1)
    const error = terminal.error ?? ''
    return { returnBytesHex, frameStatus: error === 'execution reverted' ? 'reverted' : error ? 'exceptional' :
      last?.op === 0xf3 ? 'returned' : 'stopped', receiptStatus: Number(BigInt(receipt.status)),
      gasUsed: dec(receipt.gasUsed), cumulativeGasUsed: dec(receipt.cumulativeGasUsed), logs,
      blobGasUsed: dec(receipt.blobGasUsed ?? 0), blobGasPrice: dec(receipt.blobGasPrice ?? 0),
      receipt: receiptBytes({ receiptStatus: Number(BigInt(receipt.status)),
        cumulativeGasUsed: dec(receipt.cumulativeGasUsed), logs }, x.tx.type), traceSha256: digest(JSON.stringify(trace)) }
  })
  return { root: result.stateRoot, receiptsRoot: result.receiptsRoot, txRoot: result.txRoot,
    gasUsed: dec(result.gasUsed), accounts, transactions }
}
async function trieRoot(values) {
  const trie = new MerklePatriciaTrie({ common })
  for (let index = 0; index < values.length; index++) await trie.put(RLP.encode(index), values[index])
  return bytesToHex(trie.root())
}
async function rootOf(accounts) {
  const vm = await createVM({ common }); await seed(vm, accounts)
  return bytesToHex(await vm.stateManager.getStateRoot())
}
async function compareClients(expected, alternate, input, priorReceipts = [], priorInputs = []) {
  const other = alternate.transactions.at(-1), actual = expected.response
  for (const field of ['returnBytesHex', 'frameStatus', 'receiptStatus', 'gasUsed', 'cumulativeGasUsed', 'logs'])
    assert.deepEqual(other[field], actual[field], 'independent clients: ' + field)
  assert.deepEqual(alternate.accounts, actual.accounts, 'independent clients: all accounts')
  assert.deepEqual(other.receipt, expected.receipt, 'independent clients: receipt bytes')
  assert.equal(alternate.root, expected.root, 'independent clients: state root')
  assert.equal(alternate.receiptsRoot, await trieRoot([...priorReceipts, expected.receipt]), 'independent clients: receipt root')
  assert.equal(alternate.txRoot, await trieRoot([...priorInputs.map(x => x.bytes), input.bytes]), 'Geth signed transaction root')
  if (input.tx.type === 3) {
    assert.equal(other.blobGasUsed, expected.wrapper.blobGasUsed)
    assert.equal(dec(BigInt(other.blobGasUsed) * BigInt(other.blobGasPrice)), expected.wrapper.blobFeeBurn)
  }
}
const rows = [], failures = [], observations = [], negativeControls = {}
let missingWitnessRefused = false
const clients = { ethereumJS: { executed: 0, compared: 0, matched: 0 },
  geth: { executed: 0, compared: 0, matched: 0 }, agreement: { compared: 0, matched: 0 } }
const selected = smoke ? cases.slice(0, 1) : cases
async function challenge(actual, expected, alternate, input) {
  const nativeResult = wrapper => input.tx.type === 3 ? wrapper.result : wrapper
  const assertion = { code: 'ERR_ASSERTION' }
  if (!negativeControls.changedGas) {
    const changed = structuredClone(actual)
    nativeResult(changed).gasUsed = dec(BigInt(nativeResult(changed).gasUsed) + 1n)
    assert.throws(() => assert.deepEqual(changed, expected.wrapper), assertion)
    negativeControls.changedGas = true
  }
  if (!negativeControls.changedSignedChainId) {
    const changedChain = structuredClone(input.request)
    changedChain.transaction.chainId = '2'
    assert.throws(() => assertBinding({ ...input, request: changedChain }), assertion)
    negativeControls.changedSignedChainId = true
    const changedAccess = structuredClone(input.request)
    changedAccess.transaction.accessList.push({ address: dec(child), storageKeys: ['1'] })
    assert.throws(() => assertBinding({ ...input, request: changedAccess }), assertion)
    negativeControls.changedSignedAccessList = true
  }
  if (!negativeControls.changedOutputByte && nativeResult(actual).returnBytesHex.length > 0) {
    const changed = structuredClone(actual), value = nativeResult(changed)
    value.returnBytesHex = (parseInt(value.returnBytesHex.slice(0, 2), 16) ^ 1).toString(16).padStart(2, '0') +
      value.returnBytesHex.slice(2)
    assert.throws(() => assert.deepEqual(changed, expected.wrapper), assertion)
    negativeControls.changedOutputByte = true
  }
  if (input.tx.type === 3 && !negativeControls.changedBlobBurn) {
    for (const [field, name] of [['blobFeeBurn', 'changedBlobBurn'], ['blobGasUsed', 'changedBlobGas']]) {
      const changed = structuredClone(actual); changed[field] = dec(BigInt(changed[field]) + 1n)
      assert.throws(() => assert.deepEqual(changed, expected.wrapper), assertion)
      negativeControls[name] = true
    }
    const request = structuredClone(input.request), hash = request.blobVersionedHashes[0]
    request.blobVersionedHashes[0] = hash.slice(0, -2) + (hash.endsWith('ff') ? 'fe' : 'ff')
    assert.throws(() => assertBinding({ ...input, request }), assertion)
    negativeControls.changedSignedHashByte = true
  }
  if (input.tx.type === 3 && input.tx.blobVersionedHashes.length > 1 && !negativeControls.changedSignedHashOrder) {
    const request = structuredClone(input.request)
    request.blobVersionedHashes.reverse()
    assert.throws(() => assertBinding({ ...input, request }), assertion)
    negativeControls.changedSignedHashOrder = true
  }
  if (!negativeControls.changedReceiptStatus) {
    const changed = structuredClone(nativeResult(actual)); changed.receiptStatus = 1 - changed.receiptStatus
    assert.throws(() => assert.deepEqual(receiptBytes(changed, input.tx.type), expected.receipt), assertion)
    assert.notEqual(await trieRoot([receiptBytes(changed, input.tx.type)]), alternate.receiptsRoot)
    negativeControls.changedReceiptStatus = true
    const accounts = structuredClone(nativeResult(actual).accounts)
    accounts[0].balance = dec(BigInt(accounts[0].balance) + 1n)
    assert.notEqual(await rootOf(accounts), alternate.root)
    negativeControls.changedStateBalance = true
  }
  if (!negativeControls.changedLogData && nativeResult(actual).logs.length > 0) {
    const changed = structuredClone(nativeResult(actual))
    changed.logs[0].dataHex = (parseInt(changed.logs[0].dataHex.slice(0, 2), 16) ^ 1).toString(16).padStart(2, '0') +
      changed.logs[0].dataHex.slice(2)
    assert.throws(() => assert.deepEqual(receiptBytes(changed, input.tx.type), expected.receipt), assertion)
    negativeControls.changedLogData = true
    const accounts = structuredClone(nativeResult(actual).accounts)
    const slot = accounts.find(a => a.address === dec(parent)).storage[0]
    slot.value = dec(BigInt(slot.value) + 1n)
    assert.notEqual(await rootOf(accounts), alternate.root)
    negativeControls.changedStorageWord = true
  }
}
async function assess(test, input, expected, alternate, priorReceipts = [], priorInputs = []) {
  clients.agreement.compared++
  await compareClients(expected, alternate, input, priorReceipts, priorInputs)
  clients.agreement.matched++
  if (referencesOnly) {
    rows.push({ id: test.id, category: test.category, type: test.type, referencesAgree: true,
      gasUsed: expected.response.gasUsed, output: expected.response.returnBytesHex })
    return null
  }
  const actual = runLean(input)
  observations.push({ id: test.id, status: actual.status, reason: actual.reason })
  clients.ethereumJS.compared++
  assert.deepEqual(actual, expected.wrapper, test.id + ': full native result')
  clients.ethereumJS.matched++
  const result = input.tx.type === 3 ? actual.result : actual
  clients.geth.compared++
  const receipt = receiptBytes(result, test.type), root = await rootOf(result.accounts)
  const other = alternate.transactions.at(-1)
  assert.deepEqual(receipt, other.receipt)
  assert.equal(result.returnBytesHex, other.returnBytesHex)
  assert.deepEqual(result.accounts, alternate.accounts)
  assert.equal(root, alternate.root)
  assert.equal(await trieRoot([...priorReceipts, receipt]), alternate.receiptsRoot)
  clients.geth.matched++
  await challenge(actual, expected, alternate, input)
  if (!missingWitnessRefused && test.category === 'nested') {
    const request = structuredClone(input.request)
    request.accounts = request.accounts.filter(a => a.address !== dec(child))
    const refused = runLean({ ...input, request })
    assert.deepEqual(refused, { schemaVersion: 1, status: 'indeterminate', keccakOptIn: true,
      reason: 'incompleteState', address: dec(child), slot: null })
    missingWitnessRefused = true
  }
  rows.push({ id: test.id, category: test.category, type: test.type, txBytes: bytesToHex(input.bytes),
    requestSha256: digest(JSON.stringify(input.request)), receiptStatus: result.receiptStatus,
    gasUsed: result.gasUsed, cumulativeGasUsed: result.cumulativeGasUsed, refundGas: result.refundGas,
    output: result.returnBytesHex, ...(input.tx.type === 3 ? { blobGasUsed: actual.blobGasUsed,
      blobFeeBurn: actual.blobFeeBurn } : {}), receipt: bytesToHex(receipt), receiptsRoot: alternate.receiptsRoot,
    stateRoot: root, transactionRoot: alternate.txRoot, gethTraceSha256: other.traceSha256,
    ethereumJSMatched: true, gethMatched: true })
  return result
}
try {
  for (const test of selected) {
    let stage = 'prepare'
    try {
      const input = prepare(test)
      stage = 'EthereumJS runTx'
      const expected = await reference(test, input); clients.ethereumJS.executed++
      if (input.tx.type === 3) Object.assign(input.request, makeHeaders(input.header.excessBlobGas,
        BigInt(expected.response.cumulativeGasUsed), unit * BigInt(input.tx.blobVersionedHashes.length)))
      if (smoke && process.env.BLOBHASH_FIXTURE_PATH)
        writeFileSync(process.env.BLOBHASH_FIXTURE_PATH, JSON.stringify(input.request, null, 2) + '\n')
      stage = 'Geth t8n'
      const alternate = runGeth([input]); clients.geth.executed++
      stage = 'complete comparison'
      await assess(test, input, expected, alternate)
    } catch (error) {
      failures.push({ id: test.id, stage, message: String(error).slice(0, 5000) })
    }
  }
  if (!smoke) {
    const prepared = [], references = []
    let accounts, cumulative = 0n, priorBlobGas = 0n, vm
    for (const [index, test] of sequenceCases.entries()) {
      try {
        const input = prepare(test, accounts, 7n + BigInt(index), cumulative, priorBlobGas)
        const expected = await reference(test, input, vm)
        clients.ethereumJS.executed++
        vm = expected.vm; accounts = expected.response.accounts
        cumulative = BigInt(expected.response.cumulativeGasUsed)
        priorBlobGas += BigInt(test.hashes.length) * unit
        prepared.push(input); references.push(expected)
      } catch (error) {
        failures.push({ id: test.id, stage: 'prefix preparation', message: String(error) }); break
      }
    }
    for (const input of prepared) if (input.tx.type === 3)
      Object.assign(input.request, makeHeaders(input.header.excessBlobGas, cumulative, priorBlobGas))
    let nativeAccounts = prepared[0]?.request.accounts, brokenNativePrefix = false
    for (const [index, input] of prepared.entries()) {
      const test = sequenceCases[index], expected = references[index]
      try {
        const alternate = runGeth(prepared.slice(0, index + 1), prepared[0].request.accounts)
        clients.geth.executed++
        if (!referencesOnly) {
          assert(!brokenNativePrefix, 'previous native prefix transaction did not match')
          assert.deepEqual(nativeAccounts, input.request.accounts, 'native transactions use the preceding native post-state')
        }
        const result = await assess(test, input, expected, alternate,
          references.slice(0, index).map(x => x.receipt), prepared.slice(0, index))
        if (result) nativeAccounts = result.accounts
      } catch (error) {
        brokenNativePrefix = true
        failures.push({ id: test.id, stage: 'real prefix sequence', message: String(error).slice(0, 5000) })
      }
    }
  }
  if (!referencesOnly && !smoke) {
    const ids = rows.map(row => row.id), expectedIds = inventory.map(test => test.id)
    if (rows.length === inventory.length) {
      assert.deepEqual(ids, expectedIds, 'all named cases, in order')
      assert.throws(() => assert.deepEqual(ids.slice(0, -1), expectedIds), { code: 'ERR_ASSERTION' })
      negativeControls.omittedRow = true
    }
    const required = ['changedGas', 'changedSignedChainId', 'changedSignedAccessList',
      'changedOutputByte', 'changedBlobBurn', 'changedBlobGas',
      'changedSignedHashByte', 'changedSignedHashOrder', 'changedReceiptStatus', 'changedStateBalance',
      'changedLogData', 'changedStorageWord', 'omittedRow']
    if (!required.every(name => negativeControls[name] === true) || !missingWitnessRefused)
      failures.push({ id: 'required controls', negativeControls, missingWitnessRefused })
  }
} finally { rmSync(directory, { recursive: true, force: true }) }
const completeInventory = smoke ? selected : inventory
const counts = key => Object.fromEntries([...new Set(completeInventory.map(test => test[key]))]
  .map(value => [value, completeInventory.filter(test => test[key] === value).length]))
console.log(JSON.stringify({ kind: 'signed-blobhash-transactions-vs-ethereumjs-runTx-and-geth-t8n',
  fork: 'Cancun', mode: referencesOnly ? 'references-only' : smoke ? 'smoke' : 'full',
  cases: completeInventory.length, matched: rows.length, failed: failures.length,
  standaloneCases: selected.length, sequenceCases: smoke ? 0 : sequenceCases.length,
  categories: counts('category'), types: counts('type'), observations,
  notExecuted: referencesOnly ? completeInventory.length : completeInventory.length - observations.length,
  localRefusals: observations.filter(row => row.status === 'indeterminate').length,
  ethereumJS: { version: '@ethereumjs/vm@10.1.3', ...clients.ethereumJS },
  geth: { version: geth.version, sourceCommit: geth.sourceCommit, sha256: geth.sha256, ...clients.geth },
  clientAgreement: clients.agreement, nativeSha256: referencesOnly ? null : digest(readFileSync(executable)),
  ordinaryNativeSha256: referencesOnly || smoke ? null : digest(readFileSync(ordinaryExecutable)),
  negativeControls, missingWitnessRefused, kzgOperations, rows, failures,
  scope: 'Synthetic signed Cancun execution envelopes. Both independent clients execute identical signed bytes. Lean receives decoded envelopes and complete synthetic witnesses. Host signature recovery, receipt/trie codecs, compiler/runtime and experimental Keccak remain trusted; no sidecar verification or chain membership claim.' }))
if (failures.length || rows.length !== completeInventory.length || kzgOperations !== 0) process.exitCode = 1
