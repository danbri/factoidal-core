#!/usr/bin/env node
/**
 * Signed synthetic identity-precompile transactions, with three real executors.
 *
 * The existing native transaction entry point receives a decoded signed envelope
 * and an explicit synthetic state witness. EthereumJS runTx and pinned Geth t8n
 * independently execute the same signed bytes. The test host still supplies
 * signature recovery, receipt encoding and post-state trie encoding for Lean.
 * These are synthetic Shanghai cases, not authenticated mainnet or EELS cases.
 * Uses the existing ../eels/package.json dependencies; adds no implementation
 * or package dependency to the independent Lean client.
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

const executable = process.argv[2] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-call-transaction', import.meta.url))
const geth = openGeth()
assert(geth, 'EVM_GETH_EXE must name the pinned existing Geth t8n executable')
const directory = mkdtempSync(join(tmpdir(), 'lean-identity-transaction-'))
const common = new Common({ chain: Mainnet, hardfork: Hardfork.Shanghai })
const dec = value => BigInt(value).toString()
const quantity = value => '0x' + BigInt(value).toString(16)
const address = value => '0x' + BigInt(value).toString(16).padStart(40, '0')
const word = value => '0x' + BigInt(value).toString(16).padStart(64, '0')
const hex = bytes => bytesToHex(bytes).slice(2)
const senderKey = hexToBytes('0x' + '00'.repeat(31) + '01') // Public synthetic fixture key only.
const sender = createAddressFromPrivateKey(senderKey).toString()
const parent = address(0xc1)
const identity = address(4)
const beneficiary = address(0xc4)
const maxWord = (1n << 256n) - 1n
const prefill = '7f' + '000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f' +
  '5f527f' + 'ffeeddccbbaa99887766554433221100'.repeat(2) + '602052'
const push = value => {
  const n = BigInt(value)
  assert(n >= 0n && n <= maxWord)
  if (n === 0n) return '5f'
  let h = n.toString(16)
  if (h.length % 2) h = '0' + h
  return (0x5f + h.length / 2).toString(16) + h
}
function invoke({ op = 'call', value = 0, requested = 30_000, input = 1, inputSize = 33,
  output = 64, outputSize = 5 } = {}) {
  const args = [outputSize, output, inputSize, input]
  if (op === 'call' || op === 'callcode') args.push(value)
  return [...args, 4, requested].map(push).join('') +
    { call: 'f1', callcode: 'f2', delegatecall: 'f4', staticcall: 'fa' }[op]
}
function body(options = {}, ending = 'f3') {
  // Persist the child status for comparison, and expose full returndata length
  // next to caller memory; output copying and its preserved tail stay observable.
  return prefill + invoke(options) + '5f553d60205260805f' + ending
}
const record = (addr, { exists = true, balance = 0, nonce = 0, code = '', storage = [] } = {}) => ({
  address: dec(addr), exists, balance: dec(balance), nonce: dec(nonce), codeHex: code,
  storage: storage.map(([key, value]) => ({ key: dec(key), value: dec(value) })),
})

const nested = [
  ['empty exact gas', { requested: 15, inputSize: 0, outputSize: 0 }],
  ['one byte underfunded', { requested: 17, inputSize: 1 }],
  ['one byte exact gas', { requested: 18, inputSize: 1 }],
  ['33 byte exact gas and output truncation', { requested: 21 }],
  ['overlapping memory and preserved tail', { input: 0, output: 1, outputSize: 40, requested: 21 }],
  ['empty maximal-offset windows', { input: maxWord, inputSize: 0, output: maxWord, outputSize: 0, requested: 15 }],
  ['value credits existing target', { value: 7, requested: 21 }],
  ['value creates absent target', { value: 7, requested: 21 }, { targetAbsent: true }],
  ['insufficient parent funds', { value: 1000 }],
  ['value stipend executes identity', { value: 7, requested: 0, inputSize: 1 }],
  ['value stipend one gas short rolls back', { value: 7, requested: 0, inputSize: 24_353 }],
  ['value stipend plus one exact gas', { value: 7, requested: 1, inputSize: 24_353 }],
  ['parent REVERT rolls back existing target credit', { value: 7, requested: 21 }, { ending: 'fd' }],
  ['parent REVERT removes created target', { value: 7, requested: 21 }, { ending: 'fd', targetAbsent: true }],
  ['parent INVALID rolls back target credit', { value: 7, requested: 21 }, { ending: 'fe' }],
  ['CALLCODE does not transfer value', { op: 'callcode', value: 7, requested: 21 }],
  ['DELEGATECALL inherited value has no stipend', { op: 'delegatecall', requested: 20 }],
  ['STATICCALL exact gas', { op: 'staticcall', requested: 21 }],
  ['target code and storage are ignored', { value: 7, requested: 21 }, { targetCode: '6001600055fe' }],
].map(([name, options, rest = {}]) => ({ name, kind: 'nested', code: body(options, rest.ending),
  options, ...rest }))
const direct = [
  { name: 'empty exact frame gas', data: '', frameGas: 15 },
  { name: 'empty one gas short', data: '', frameGas: 14 },
  { name: 'one byte exact frame gas', data: '00', frameGas: 18 },
  { name: 'one byte underfunded value rolls back', data: '00', frameGas: 17 },
  { name: '33 bytes exact frame gas', data: '000102' + '7f'.repeat(30), frameGas: 21 },
  { name: 'value creates absent target', data: '0001', frameGas: 18, targetAbsent: true },
  { name: 'underfunded call preserves absent target', data: '0001', frameGas: 17, targetAbsent: true },
  { name: 'target code is ignored', data: '00deadbeef', frameGas: 18, targetCode: '6001600055fe' },
  { name: 'zero instruction fuel still runs precompile', data: '0001', frameGas: 18, fuel: 0 },
].map(item => ({ ...item, kind: 'direct' }))
const cases = [0, 1, 2].flatMap(type => [...nested, ...direct].map(test => ({
  ...test, type, id: `type${type}/${test.kind}/${test.name}`,
})))

function prepare(test) {
  const to = test.kind === 'direct' ? identity : parent
  const data = test.kind === 'direct' ? test.data : '0001020000ff'
  const fee = test.type === 2 ? { maxFeePerGas: 7n, maxPriorityFeePerGas: 3n } : { gasPrice: 7n }
  const fields = { type: test.type, nonce: 7n, gasLimit: 500_000n, value: 5n,
    to, data: '0x' + data, ...fee, ...(test.type ? { accessList: [] } : {}) }
  if (test.frameGas !== undefined) {
    const unsigned = createTx(fields, { common })
    fields.gasLimit = unsigned.getIntrinsicGas() + BigInt(test.frameGas)
  }
  const tx = createTx(fields, { common }).sign(senderKey)
  const bytes = tx.serialize()
  const decoded = createTxFromRLP(bytes, { common })
  assert(decoded.verifySignature(), test.id + ': verify signed fixture')
  assert.equal(decoded.getSenderAddress().toString(), sender)
  const header = { number: 19_000_000n, timestamp: 1_706_000_000n, gasLimit: 30_000_000n,
    gasUsed: 0n, baseFeePerGas: 2n, coinbase: beneficiary, mixHash: word(9) }
  const accounts = [record(sender, { balance: 10_000_000, nonce: 7 })]
  if (test.kind === 'nested') accounts.push(record(parent, {
    balance: 50, nonce: 1, code: test.code, storage: [[0, 0], [1, 7]],
  }))
  accounts.push(test.targetAbsent ? record(identity, { exists: false }) : record(identity, {
    balance: 9, code: test.targetCode ?? '', storage: [[0, 77]],
  }))
  accounts.push(record(beneficiary, { exists: false }))
  const request = {
    schemaVersion: 1, fork: 'shanghai', fuel: dec(test.fuel ?? 5000),
    transaction: {
      type: tx.type, chainId: '1', sender: dec(sender), to: dec(to), nonce: dec(tx.nonce),
      value: dec(tx.value), gasLimit: dec(tx.gasLimit),
      gasPriceCap: dec(tx.type === 2 ? tx.maxFeePerGas : tx.gasPrice),
      priorityFeeCap: dec(tx.type === 2 ? tx.maxPriorityFeePerGas : 0),
      dataHex: hex(tx.data), accessList: [],
    },
    block: { chainId: '1', coinbase: dec(beneficiary), number: dec(header.number),
      timestamp: dec(header.timestamp), gasLimit: dec(header.gasLimit), gasUsedBefore: '0',
      baseFee: dec(header.baseFeePerGas), prevRandao: dec(header.mixHash), blobBaseFee: '0' },
    accounts,
  }
  return { request, tx: decoded, bytes, header, block: createBlock({ header }, { common }) }
}
async function seed(vm, records) {
  for (const entry of records) {
    if (!entry.exists) continue
    const addr = createAddressFromString(address(entry.address))
    await vm.stateManager.putAccount(addr, new Account(BigInt(entry.nonce), BigInt(entry.balance)))
    if (entry.codeHex) await vm.stateManager.putCode(addr, hexToBytes('0x' + entry.codeHex))
    for (const slot of entry.storage) if (BigInt(slot.value) !== 0n)
      await vm.stateManager.putStorage(addr, hexToBytes(word(slot.key)), unpadBytes(bigIntToBytes(BigInt(slot.value))))
  }
}
async function observeAccounts(vm, records) {
  const out = []
  for (const entry of records) {
    const addr = createAddressFromString(address(entry.address))
    const account = await vm.stateManager.getAccount(addr)
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
    const addr = hexToBytes(address(log.address))
    const topics = log.topics.map(t => hexToBytes(word(t)))
    bloom.add(addr)
    topics.forEach(t => bloom.add(t))
    return [addr, topics, hexToBytes('0x' + log.dataHex)]
  })
  return encodeReceipt({ status: value.receiptStatus, cumulativeBlockGasUsed: BigInt(value.cumulativeGasUsed),
    bitvector: bloom.bitvector, logs }, type)
}
async function reference(test, input) {
  const vm = await createVM({ common })
  await seed(vm, input.request.accounts)
  let lastOpcode
  vm.evm.events.on('step', step => { if (step.depth === 0) lastOpcode = step.opcode.name })
  const result = await runTx(vm, { tx: input.tx, block: input.block, blockGasUsed: 0n })
  const error = result.execResult.exceptionError?.error
  const frameStatus = error === 'revert' ? 'reverted' : error ? 'exceptional' :
    (test.kind === 'direct' || lastOpcode === 'RETURN' ? 'returned' : 'stopped')
  const frameError = error === 'out of gas' ? 'outOfGas' : error ? 'invalidOpcode' : undefined
  const gross = input.tx.getIntrinsicGas() + result.execResult.executionGasUsed
  const effective = result.amountSpent / result.totalGasSpent
  return { root: bytesToHex(await vm.stateManager.getStateRoot()), receipt: encodeReceipt(result.receipt, input.tx.type),
    response: { schemaVersion: 1, status: 'executed', keccakOptIn: false,
      receiptStatus: result.receipt.status, frameStatus,
      ...(frameStatus === 'exceptional' ? { frameError } : {}),
      gasUsedBeforeRefund: dec(gross), refundGas: dec(gross - result.totalGasSpent), gasUsed: dec(result.totalGasSpent),
      cumulativeGasUsed: dec(result.receipt.cumulativeBlockGasUsed), effectiveGasPrice: dec(effective),
      gasWeiReturned: dec((input.tx.gasLimit - result.totalGasSpent) * effective),
      beneficiaryTip: dec(result.minerValue), baseFeeBurn: dec(result.amountSpent - result.minerValue),
      returnBytesHex: hex(result.execResult.returnValue), logs: result.receipt.logs.map(logFields),
      accounts: await observeAccounts(vm, input.request.accounts) } }
}
function runLean(request) {
  const path = join(directory, 'lean-request.json')
  writeFileSync(path, JSON.stringify(request))
  const p = spawnSync(executable, ['--call-transaction', path], {
    encoding: 'utf8', timeout: 30_000, maxBuffer: 4 * 1024 * 1024,
  })
  if (p.error || p.status !== 0) throw Error('Lean transaction entry failed: ' + String(p.error ?? p.stdout + p.stderr))
  return JSON.parse(p.stdout)
}
function runGeth(input) {
  const alloc = Object.fromEntries(input.request.accounts.filter(a => a.exists).map(a => [address(a.address), {
    balance: quantity(a.balance), nonce: quantity(a.nonce), code: '0x' + a.codeHex,
    storage: Object.fromEntries(a.storage.map(s => [word(s.key), word(s.value)])),
  }]))
  const env = { currentCoinbase: beneficiary, currentNumber: quantity(input.header.number),
    currentTimestamp: quantity(input.header.timestamp), currentGasLimit: quantity(input.header.gasLimit),
    currentBaseFee: quantity(input.header.baseFeePerGas), currentRandom: input.header.mixHash, withdrawals: [] }
  // Legacy transactions are an RLP list item; typed transactions are a byte
  // string containing the EIP-2718 type byte and its payload.
  const signed = input.tx.type === 0 ? RLP.decode(input.bytes) : input.bytes
  for (const [name, value] of [['alloc.json', alloc], ['env.json', env],
    ['txs.rlp', bytesToHex(RLP.encode([signed]))]]) writeFileSync(join(directory, name), JSON.stringify(value))
  const p = spawnSync(process.env.EVM_GETH_EXE, ['t8n', '--state.fork', 'Shanghai', '--state.chainid', '1',
    '--state.reward=-1', '--input.alloc', join(directory, 'alloc.json'), '--input.env', join(directory, 'env.json'),
    '--input.txs', join(directory, 'txs.rlp'), '--output.basedir', directory,
    '--output.alloc', 'geth-post.json', '--output.result', 'geth-result.json'],
  { encoding: 'utf8', timeout: 15_000, maxBuffer: 4 * 1024 * 1024 })
  if (p.error || p.status !== 0) throw Error('Geth t8n failed: ' + String(p.error ?? p.stdout + p.stderr))
  const result = JSON.parse(readFileSync(join(directory, 'geth-result.json')))
  assert.equal(result.receipts.length, 1, 'exactly one Geth receipt')
  assert.equal((result.rejected ?? []).length, 0, 'signed synthetic transaction must be admitted')
  const receipt = result.receipts[0]
  assert.equal(receipt.transactionHash, bytesToHex(input.tx.hash()))
  const post = JSON.parse(readFileSync(join(directory, 'geth-post.json')))
  const accounts = input.request.accounts.map(entry => {
    const a = post[address(entry.address)]
    return { address: entry.address, exists: a !== undefined, balance: dec(a?.balance ?? 0), nonce: dec(a?.nonce ?? 0),
      codeHex: (a?.code ?? '0x').slice(2),
      storage: entry.storage.map(s => ({ key: s.key, value: dec(a?.storage?.[word(s.key)] ?? 0) })) }
  })
  assert.deepEqual(Object.keys(post).sort(), accounts.filter(a => a.exists).map(a => address(a.address)).sort(),
    'all post-state accounts must be observed')
  const rpcLogs = (receipt.logs ?? []).map(log => ({ address: dec(log.address),
    topics: log.topics.map(dec), dataHex: log.data.slice(2) }))
  return { root: result.stateRoot, receiptsRoot: result.receiptsRoot, gasUsed: dec(result.gasUsed), accounts,
    receipt: receiptBytes({ receiptStatus: Number(BigInt(receipt.status)),
      cumulativeGasUsed: dec(receipt.cumulativeGasUsed), logs: rpcLogs }, input.tx.type) }
}
async function rootOf(accounts) {
  const vm = await createVM({ common })
  await seed(vm, accounts)
  return bytesToHex(await vm.stateManager.getStateRoot())
}
async function receiptRootOf(receipt) {
  // One transaction at index zero. The host encodes Lean's receipt, while
  // Geth supplies its independently computed commitment to the signed run.
  const trie = new MerklePatriciaTrie({ common })
  await trie.put(RLP.encode(0), receipt)
  return bytesToHex(trie.root())
}

const rows = []
const failures = []
const observations = []
const negativeControls = {}
let missingWitnessRefused = false
try {
  for (const test of cases) {
    try {
      const input = prepare(test)
      const expected = await reference(test, input)
      const alternate = runGeth(input)
      const actual = runLean(input.request)
      observations.push({ id: test.id, status: actual.status, reason: actual.reason })
      assert.deepEqual(actual, expected.response, test.id + ': full native transaction output')
      const receipt = receiptBytes(actual, test.type)
      const root = await rootOf(actual.accounts)
      const receiptsRoot = await receiptRootOf(receipt)
      assert.deepEqual(receipt, expected.receipt, test.id + ': EthereumJS receipt bytes')
      assert.equal(root, expected.root, test.id + ': EthereumJS complete post-state root')
      assert.equal(actual.gasUsed, alternate.gasUsed, test.id + ': Geth exact receipt gas')
      assert.deepEqual(actual.accounts, alternate.accounts, test.id + ': Geth complete account observations')
      assert.deepEqual(receipt, alternate.receipt, test.id + ': reconstructed Geth receipt fields')
      assert.equal(receiptsRoot, alternate.receiptsRoot, test.id + ': independent Geth receipt-trie commitment')
      assert.equal(root, alternate.root, test.id + ': Geth complete post-state root')
      if (!negativeControls.changedGas) {
        const forged = structuredClone(actual)
        forged.gasUsed = dec(BigInt(forged.gasUsed) + 1n)
        assert.throws(() => assert.deepEqual(forged, expected.response), { code: 'ERR_ASSERTION' })
        negativeControls.changedGas = true
        const badReceipt = structuredClone(actual)
        badReceipt.receiptStatus = 1 - badReceipt.receiptStatus
        assert.throws(() => assert.deepEqual(receiptBytes(badReceipt, test.type), expected.receipt), { code: 'ERR_ASSERTION' })
        assert.notEqual(await receiptRootOf(receiptBytes(badReceipt, test.type)), alternate.receiptsRoot)
        negativeControls.changedReceiptStatus = true
        const badState = structuredClone(actual.accounts)
        const target = badState.find(a => a.address === '4')
        target.balance = dec(BigInt(target.balance) + 1n)
        target.exists = true
        assert.notEqual(await rootOf(badState), root)
        negativeControls.changedTargetCredit = true
        const badBytes = structuredClone(actual)
        badBytes.returnBytesHex += '00'
        assert.throws(() => assert.deepEqual(badBytes, expected.response), { code: 'ERR_ASSERTION' })
        negativeControls.changedOutputBytes = true
      }
      if (!missingWitnessRefused && test.kind === 'nested') {
        const missing = structuredClone(input.request)
        missing.accounts = missing.accounts.filter(a => a.address !== '4')
        assert.deepEqual(runLean(missing), { schemaVersion: 1, status: 'indeterminate', keccakOptIn: false,
          reason: 'incompleteState', address: '4', slot: null })
        missingWitnessRefused = true
      }
      rows.push({ id: test.id, kind: test.kind, type: test.type, txBytes: bytesToHex(input.bytes),
        requestSha256: createHash('sha256').update(JSON.stringify(input.request)).digest('hex'),
        receiptStatus: actual.receiptStatus, gasUsed: actual.gasUsed, refundGas: actual.refundGas,
        identityBalance: actual.accounts.find(a => a.address === '4').balance,
        identityExists: actual.accounts.find(a => a.address === '4').exists,
        receipt: bytesToHex(receipt), receiptsRoot, stateRoot: root, ethereumJSMatched: true, gethMatched: true })
    } catch (error) {
      failures.push({ id: test.id, message: String(error).slice(0, 4000) })
    }
  }
} finally {
  rmSync(directory, { recursive: true, force: true })
}
if (Object.keys(negativeControls).length !== 4 || !Object.values(negativeControls).every(Boolean) || !missingWitnessRefused)
  failures.push({ id: 'required controls', negativeControls, missingWitnessRefused })
const unsupported = observations.filter(row => row.status === 'indeterminate' && row.reason === 'unsupportedFork').length
const localRefusals = observations.filter(row => row.status === 'indeterminate' && row.reason !== 'unsupportedFork').length
const notExecuted = cases.length - observations.length
console.log(JSON.stringify({
  kind: 'signed-identity-transactions-vs-ethereumjs-runTx-and-geth-t8n', fork: 'Shanghai',
  compared: cases.length, matched: rows.length,
  failed: cases.length - rows.length - unsupported - localRefusals - notExecuted,
  unsupported, localRefusals, notExecuted, nestedCases: nested.length * 3, directCases: direct.length * 3,
  ethereumJS: { version: '@ethereumjs/vm@10.1.3', matched: rows.length },
  geth: { version: geth.version, sourceCommit: geth.sourceCommit, sha256: geth.sha256, matched: rows.length },
  nativeSha256: createHash('sha256').update(readFileSync(executable)).digest('hex'),
  negativeControls, missingWitnessRefused, rows, failures,
  scope: 'Synthetic Shanghai transaction types 0/1/2. Both independent clients execute signed bytes. Lean executes decoded envelopes and supplied state witnesses; host signature recovery, receipt encoding and trie construction remain trusted. Geth independently supplies state and receipt-trie roots; its RPC receipt fields are host reconstructed. No mainnet authentication or full fork-conformance claim.',
}))
if (failures.length || rows.length !== cases.length) process.exitCode = 1
