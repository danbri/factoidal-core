#!/usr/bin/env node
/**
 * Compare signed synthetic contract-creation transactions (destination absent)
 * on Lean and EthereumJS runTx.
 *
 * Both engines receive the same signed envelope, header fields and complete
 * synthetic prestate. The Lean request carries `"to": null`; Lean derives the
 * new address itself. The expected address here comes from EthereumJS
 * (`createContractAddress`), independently of Lean. The host codec encodes
 * Lean's receipt fields and post-state trie for exact byte and root
 * comparisons. EthereumJS is a test oracle only. No network is used.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { createBlock } from '@ethereumjs/block'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createTx, createTxFromRLP } from '@ethereumjs/tx'
import {
  Account, bigIntToBytes, bytesToBigInt, bytesToHex, createAddressFromPrivateKey,
  createAddressFromString, createContractAddress, hexToBytes, unpadBytes,
} from '@ethereumjs/util'
import { Bloom, createVM, encodeReceipt, runTx } from '@ethereumjs/vm'

const binary = process.argv[2] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-subset', import.meta.url))
const directory = mkdtempSync(join(tmpdir(), 'lean-create-tx-'))
const schemaVersion = 1
const optIn = '--dangerously-enable-unverified-keccak'
const senderKey = hexToBytes('0x' + '00'.repeat(31) + '01') // Public synthetic fixture key.
const senderAddress = createAddressFromPrivateKey(senderKey)
const sender = senderAddress.toString()
const address = value => '0x' + BigInt(value).toString(16).padStart(40, '0')
const keyWord = value => '0x' + BigInt(value).toString(16).padStart(64, '0')
const child = address(0xc3)
const beneficiary = address(0xc4)
const bytesHex = bytes => bytesToHex(bytes).slice(2)
const decimal = value => BigInt(value).toString()
const created = (nonce, from = senderAddress) => createContractAddress(from, BigInt(nonce)).toString()
const push = number => {
  if (number === 0n) return '5f'
  let hex = BigInt(number).toString(16)
  if (hex.length % 2) hex = '0' + hex
  return (0x5f + hex.length / 2).toString(16) + hex
}
const store = (key, value) => push(value) + push(key) + '55'
const logByte = (topic, byte) => push(byte) + '5f53' + push(topic) + '60015fa1'
const call = (target, value = 0n, gas = 50_000n) =>
  '5f'.repeat(4) + push(value) + push(BigInt(target)) + push(gas) + 'f1'
/** Initcode: run `prelude`, then return `runtime` (at most 255 bytes) as the code. */
const deploy = (runtime, prelude = '') => {
  const size = runtime.length / 2, offset = prelude.length / 2 + 10
  assert(size < 256 && offset < 256)
  const byte = n => n.toString(16).padStart(2, '0')
  return prelude + '60' + byte(size) + '60' + byte(offset) + '5f39' + '60' + byte(size) + '5ff3' + runtime
}
/** Initcode returning `size` zero bytes of memory as the code. */
const zeros = size => push(BigInt(size)) + '5ff3'
const runtime = '602a5f5260205ff3'

function fixture(name, changes = {}) {
  return {
    name, fork: 'cancun', type: 2, init: '', frame: 'stopped',
    txNonce: 7n, stateNonce: 7n, funds: 10n ** 9n, beneficiary,
    value: 0n, gas: 200_000n, cap: 7n, priority: 3n, baseFee: 2n, accesses: [],
    blockGas: 30_000_000n, gasUsedBefore: 1_000n, targetSlots: [], extraAccounts: [],
    ...changes,
  }
}

function prestate(test) {
  const accounts = new Map()
  const add = (addr, fields = {}) => {
    if (!accounts.has(addr)) accounts.set(addr, {
      address: addr, exists: false, balance: 0n, nonce: 0n, code: '', slots: [], ...fields,
    })
  }
  add(sender, { exists: true, balance: test.funds, nonce: test.stateNonce })
  // The new address is always witnessed: absent, or as the given prestate.
  add(created(test.txNonce), { slots: test.targetSlots.map(key => [key, 0n]), ...(test.target ?? {}) })
  add(test.beneficiary)
  for (const account of test.extraAccounts) add(account.address, account)
  return accounts
}

function context(test) {
  const common = new Common({ chain: Mainnet, hardfork: test.fork === 'shanghai' ? Hardfork.Shanghai : Hardfork.Cancun })
  const header = {
    number: test.fork === 'shanghai' ? 19_000_000n : 20_000_000n,
    timestamp: test.fork === 'shanghai' ? 1_706_000_000n : 1_720_000_000n,
    gasLimit: test.blockGas, gasUsed: test.gasUsedBefore, baseFeePerGas: test.baseFee,
    coinbase: test.beneficiary, mixHash: keyWord(9n),
    ...(test.fork === 'cancun' ? { blobGasUsed: 0n, excessBlobGas: 0n } : {}),
  }
  return { common, header, block: createBlock({ header }, { common }) }
}

function signedTransaction(test, common, options = {}) {
  const fee = test.type === 2
    ? { maxFeePerGas: test.cap, maxPriorityFeePerGas: test.priority }
    : { gasPrice: test.cap }
  const tx = createTx({
    type: test.type, nonce: test.txNonce, gasLimit: test.gas, value: test.value,
    data: '0x' + test.init, ...fee, ...(test.type !== 0 ? { accessList: test.accesses } : {}),
  }, { common, ...options }).sign(senderKey)
  const decoded = createTxFromRLP(tx.serialize(), { common, ...options })
  assert.equal(decoded.to, undefined, 'a creation has no destination')
  assert.equal(decoded.getSenderAddress().toString(), sender)
  return decoded
}

function request(test, header, state, decoded) {
  const type = decoded.type
  const signChain = type === 0 ? (decoded.v >= 35n ? (decoded.v - 35n) / 2n : null) : decoded.chainId
  return {
    schemaVersion, fork: test.fork, fuel: decimal(test.fuel ?? 100_000n),
    transaction: {
      type, chainId: signChain === null ? null : decimal(signChain),
      sender: decimal(sender), to: null,
      nonce: decimal(decoded.nonce), value: decimal(decoded.value), gasLimit: decimal(decoded.gasLimit),
      gasPriceCap: decimal(type === 2 ? decoded.maxFeePerGas : decoded.gasPrice),
      priorityFeeCap: decimal(type === 2 ? decoded.maxPriorityFeePerGas : 0n),
      dataHex: bytesHex(decoded.data),
      accessList: (decoded.accessList ?? []).map(([addr, keys]) => ({
        address: decimal(bytesToBigInt(addr)), storageKeys: keys.map(key => decimal(bytesToBigInt(key))),
      })),
    },
    block: {
      chainId: '1', coinbase: decimal(header.coinbase), number: decimal(header.number),
      timestamp: decimal(header.timestamp), gasLimit: decimal(header.gasLimit),
      gasUsedBefore: decimal(header.gasUsed), baseFee: decimal(header.baseFeePerGas),
      prevRandao: decimal(header.mixHash), blobBaseFee: test.fork === 'cancun' ? '1' : '0',
    },
    accounts: [...state.values()].map(account => ({
      address: decimal(account.address), exists: account.exists, balance: decimal(account.balance),
      nonce: decimal(account.nonce), codeHex: account.code,
      storage: account.slots.map(([key, value]) => ({ key: decimal(key), value: decimal(value) })),
    })),
  }
}

async function seedState(vm, records) {
  for (const record of records) {
    if (!record.exists) continue
    const addr = createAddressFromString(address(record.address))
    await vm.stateManager.putAccount(addr, new Account(BigInt(record.nonce), BigInt(record.balance)))
    if (record.codeHex !== '') await vm.stateManager.putCode(addr, hexToBytes('0x' + record.codeHex))
    for (const { key, value } of record.storage) {
      if (BigInt(value) !== 0n) await vm.stateManager.putStorage(addr,
        hexToBytes(keyWord(key)), unpadBytes(bigIntToBytes(BigInt(value))))
    }
  }
}

async function observedAccounts(vm, accounts) {
  const observed = []
  for (const entry of accounts) {
    const addr = createAddressFromString(address(entry.address))
    const account = await vm.stateManager.getAccount(addr)
    const storage = []
    for (const { key } of entry.storage) {
      const value = await vm.stateManager.getStorage(addr, hexToBytes(keyWord(key)))
      storage.push({ key, value: decimal(bytesToBigInt(value)) })
    }
    observed.push({
      address: entry.address, exists: account !== undefined, balance: decimal(account?.balance ?? 0n),
      nonce: decimal(account?.nonce ?? 0n), codeHex: bytesHex(await vm.stateManager.getCode(addr)), storage,
    })
  }
  return observed
}

/** Every storage slot and account the reference touches must be in the Lean witness. */
function observeLookups(vm, accounts) {
  const expected = new Map(accounts.map(entry => [entry.address, new Set(entry.storage.map(s => s.key))]))
  const observed = { unmodelled: [], lastTopOpcode: undefined }
  const account = (opcode, word) => {
    const target = decimal(word % (1n << 160n))
    if (!expected.has(target)) observed.unmodelled.push({ opcode, target })
  }
  vm.evm.events.on('step', step => {
    const opcode = step.opcode.name
    if (step.depth === 0) observed.lastTopOpcode = opcode
    if ((opcode === 'SLOAD' && step.stack.length >= 1) || (opcode === 'SSTORE' && step.stack.length >= 2)) {
      const owner = decimal(step.address.toString()), key = decimal(step.stack.at(-1))
      if (!expected.get(owner)?.has(key)) observed.unmodelled.push({ opcode, owner, key })
    } else if (['CALL', 'STATICCALL', 'DELEGATECALL', 'CALLCODE'].includes(opcode) && step.stack.length >= 2) {
      account(opcode, step.stack.at(-2))
    } else if (['BALANCE', 'EXTCODESIZE', 'EXTCODEHASH', 'SELFDESTRUCT'].includes(opcode) && step.stack.length >= 1) {
      account(opcode, step.stack.at(-1))
    }
  })
  return observed
}

async function executeReference(test, env, input, signed, vm) {
  if (!vm) {
    vm = await createVM({ common: env.common })
    await seedState(vm, input.accounts)
  }
  const lookups = observeLookups(vm, input.accounts)
  const result = await runTx(vm, { tx: signed, block: env.block, blockGasUsed: env.header.gasUsed })
  vm.evm.events.removeAllListeners('step')
  assert.deepEqual(lookups.unmodelled, [], test.name + ' must cover all reference state reads')
  return { vm, result, accounts: await observedAccounts(vm, input.accounts), lookups }
}

function lean(input, flags = [optIn]) {
  const path = join(directory, 'request.json')
  writeFileSync(path, JSON.stringify(input) + '\n')
  const result = spawnSync(binary, [...flags, '--call-transaction', path], {
    encoding: 'utf8', timeout: 60_000, maxBuffer: 16 * 1024 * 1024,
  })
  assert.equal(result.error, undefined)
  assert.equal(result.status, 0, result.stdout + '\n' + result.stderr)
  return JSON.parse(result.stdout)
}

const logFields = ([addr, topics, data]) => ({
  address: decimal(bytesToBigInt(addr)), topics: topics.map(word => decimal(bytesToBigInt(word))), dataHex: bytesHex(data),
})

/** Lean's diagnostic name for the reference's failure, by the reference's own message. */
const frameErrors = [
  [/create collision/i, 'addressCollision'],
  [/invalid bytecode|invalid EOF|0xef/i, 'invalidContractPrefix'],
  [/code store out of gas|code size to deposit|out of gas/i, 'outOfGas'],
  [/invalid opcode/i, 'invalidOpcode'],
  [/stack underflow/i, 'stackUnderflow'],
]

function observeReference(test, signed, ref) {
  const { result } = ref
  const error = result.execResult.exceptionError?.error
  const frameStatus = error === 'revert' ? 'reverted'
    : (error ? 'exceptional' : (ref.lookups.lastTopOpcode === 'RETURN' ? 'returned' : 'stopped'))
  const frameError = frameStatus === 'exceptional'
    ? (frameErrors.find(([pattern]) => pattern.test(error)) ?? [null, 'unmapped: ' + error])[1] : undefined
  const gross = signed.getIntrinsicGas() + result.execResult.executionGasUsed
  const effective = result.amountSpent / result.totalGasSpent
  const success = result.receipt.status === 1
  // The reference names the attempted address even when the creation fails.
  if (success) assert.equal(result.createdAddress?.toString(), created(signed.nonce), test.name)
  return {
    schemaVersion, status: 'executed', keccakOptIn: true,
    receiptStatus: result.receipt.status, frameStatus,
    ...(frameError ? { frameError } : {}),
    gasUsedBeforeRefund: decimal(gross), refundGas: decimal(gross - result.totalGasSpent),
    gasUsed: decimal(result.totalGasSpent), cumulativeGasUsed: decimal(result.receipt.cumulativeBlockGasUsed),
    effectiveGasPrice: decimal(effective), gasWeiReturned: decimal((signed.gasLimit - result.totalGasSpent) * effective),
    beneficiaryTip: decimal(result.minerValue), baseFeeBurn: decimal(result.amountSpent - result.minerValue),
    // Lean reports the deployed code on success, the REVERT data on a revert
    // and nothing otherwise. The reference's return value is not a consensus
    // observable for a creation and is compared only on a revert.
    returnBytesHex: frameStatus === 'reverted' ? bytesHex(result.execResult.returnValue)
      : (success ? ref.accounts.find(a => a.address === decimal(created(signed.nonce))).codeHex : ''),
    logs: result.receipt.logs.map(logFields), accounts: ref.accounts,
    createdAddress: success ? decimal(created(signed.nonce)) : null,
  }
}

function encodeLeanReceipt(record, type) {
  const bloom = new Bloom()
  const logs = record.logs.map(log => {
    const addr = hexToBytes(address(log.address))
    const topics = log.topics.map(word => hexToBytes(keyWord(word)))
    bloom.add(addr)
    for (const topic of topics) bloom.add(topic)
    return [addr, topics, hexToBytes('0x' + log.dataHex)]
  })
  return encodeReceipt({
    status: record.receiptStatus, cumulativeBlockGasUsed: BigInt(record.cumulativeGasUsed),
    bitvector: bloom.bitvector, logs,
  }, type)
}

async function observeRoot(common, accounts) {
  const projection = await createVM({ common })
  await seedState(projection, accounts)
  return projection.stateManager.getStateRoot()
}

const present = (addr, fields = {}) => ({ address: addr, exists: true, nonce: 1n, balance: 0n, code: '', slots: [], ...fields })
const keys = (...items) => items.map(keyWord)
const access = (addr, ...storageKeys) => ({ address: addr, storageKeys: keys(...storageKeys) })
const constructor = store(0n, 42n) + logByte(1n, 0x7an)
const programs = [
  ['empty-initcode', '', 'stopped', []],
  ['constructor-writes-logs-returns-runtime', deploy(runtime, constructor), 'returned', [0n]],
  ['constructor-writes-logs-reverts', constructor + '60015ffd', 'reverted', [0n]],
  ['constructor-writes-logs-invalid', constructor + 'fe', 'exceptional', [0n]],
]
const executions = ['shanghai', 'cancun'].flatMap(fork => [0, 1, 2].flatMap(type =>
  programs.map(([name, init, frame, targetSlots]) =>
    fixture(fork + '/type' + type + '/' + name, { fork, type, init, frame, targetSlots }))))
const contextOps = ['30', '33', '32', '34', '36', '38', '3a', '47']
executions.push(
  fixture('constructor context: address, caller, origin, value, calldatasize, codesize, gasprice, selfbalance', {
    init: deploy(runtime, contextOps.map((op, index) => op + push(BigInt(index)) + '55').join('')),
    frame: 'returned', value: 5n, targetSlots: contextOps.map((_, index) => BigInt(index)), gas: 400_000n,
  }),
  fixture('value endowment kept on success', { init: deploy(runtime), frame: 'returned', value: 12_345n }),
  fixture('value endowment returned on revert', { init: '5f5ffd', frame: 'reverted', value: 12_345n }),
  fixture('value endowment returned on exceptional halt', { init: '50', frame: 'exceptional', value: 12_345n }),
  fixture('exact upfront funds including value', { init: deploy(runtime), frame: 'returned', value: 5n, funds: 1_400_005n }),
  fixture('target already holds a balance (no collision, balance kept)', {
    init: deploy(runtime), frame: 'returned', value: 3n, target: { exists: true, balance: 77n },
  }),
  fixture('collision: target has a nonce', { init: deploy(runtime), frame: 'exceptional', target: { exists: true, nonce: 1n } }),
  fixture('collision: target has code', {
    init: deploy(runtime), frame: 'exceptional', value: 9n, target: { exists: true, nonce: 0n, code: '00' },
  }),
  fixture('collision: target has storage only (EIP-7610)', {
    init: deploy(runtime), frame: 'exceptional', target: { exists: true, balance: 1n, slots: [[3n, 4n]] },
  }),
  fixture('deposit of 0xEF-prefixed code fails (EIP-3541)', { init: '60ef5f5360015ff3', frame: 'exceptional' }),
  fixture('deposit of 24576 bytes succeeds (EIP-170)', { init: zeros(24576), frame: 'returned', gas: 6_000_000n }),
  fixture('deposit of 24577 bytes fails (EIP-170)', { init: zeros(24577), frame: 'exceptional', gas: 6_000_000n }),
  fixture('initcode of exactly 49152 bytes is admitted (EIP-3860)', { init: '00'.repeat(49152), gas: 400_000n }),
  fixture('initcode word cost rounds up (33 bytes)', { init: '5b'.repeat(32) + '00', gas: 53_520n + 32n }),
  fixture('gas limit exactly intrinsic, empty initcode', { gas: 53_000n }),
  fixture('initcode runs out of gas', { init: '5b5f56', frame: 'exceptional', gas: 60_000n }),
  fixture('new address is warm for the constructor', { init: '303150' + '303b50' + '00', gas: 60_000n }),
  fixture('sender and beneficiary are warm for the constructor', {
    init: '333150' + '413150' + '00', gas: 60_000n,
  }),
  fixture('access list names the new address and a slot (type 1)', {
    type: 1, init: deploy(runtime, store(0n, 4n)), frame: 'returned', targetSlots: [0n],
    accesses: [access(created(7n), 0n)],
  }),
  fixture('access list warms a child the constructor calls (type 2)', {
    init: deploy(runtime, call(child) + '50'), frame: 'returned',
    accesses: [access(child, 0n), access(child)],
    extraAccounts: [present(child, { code: store(0n, 31n) + '00', slots: [[0n, 0n]] })],
  }),
  fixture('constructor calls a cold child with value', {
    init: deploy(runtime, call(child, 2n) + '50'), frame: 'returned', value: 10n,
    extraAccounts: [present(child, { code: store(0n, 31n) + '00', slots: [[0n, 0n]] })],
  }),
  fixture('constructor refund: set then clear a slot', {
    init: deploy(runtime, store(0n, 1n) + store(0n, 0n)), frame: 'returned', targetSlots: [0n],
  }),
  fixture('nested CREATE in the constructor uses the new account nonce 1', {
    init: deploy(runtime, '5f5f5ff0' + '5f55'), frame: 'returned', targetSlots: [0n], gas: 400_000n,
    extraAccounts: [{ address: created(1n, createAddressFromString(created(7n))) }],
  }),
  fixture('constructor self-destructs to the sender (EIP-6780, created in this transaction)', {
    init: '33ff', value: 9n, gas: 100_000n,
  }),
  fixture('Cancun transient storage in a constructor', {
    init: deploy(runtime, '602a5f5d5f5c5f55'), frame: 'returned', targetSlots: [0n],
  }),
  fixture('legacy creation with a nonzero sender nonce far from 7', {
    type: 0, txNonce: 0x1234n, stateNonce: 0x1234n, init: deploy(runtime), frame: 'returned',
  }),
  fixture('sender nonce zero (address preimage uses the empty scalar)', {
    txNonce: 0n, stateNonce: 0n, init: deploy(runtime), frame: 'returned',
  }),
)

const admissionCases = [
  [fixture('gas one below the creation intrinsic cost', { gas: 52_999n }), 'below-intrinsic-gas', /intrinsic/i],
  [fixture('gas pays the call cost but not the 32000 creation cost', { gas: 21_000n }), 'below-intrinsic-gas', /intrinsic/i],
  [fixture('gas one below the initcode word cost', { init: '5b'.repeat(32) + '00', gas: 53_519n }),
    'below-intrinsic-gas', /intrinsic/i],
  [fixture('value not covered by the balance', { value: 5n, funds: 1_400_004n }), 'insufficient-upfront-balance', /enough funds/i],
  [fixture('nonce too high', { txNonce: 8n }), 'invalid-sender-nonce', /correct nonce/i],
]

const removeAddress = (input, addr) => {
  input.accounts = input.accounts.filter(record => record.address !== decimal(addr))
}
const boundaryCases = [
  [fixture('new address not covered by the witness', { init: deploy(runtime), frame: 'returned' }),
    input => removeAddress(input, created(7n)), [optIn],
    { reason: 'incompleteState', address: decimal(created(7n)), slot: null }, true],
  [fixture('address derivation without the Keccak opt-in', { init: deploy(runtime), frame: 'returned' }),
    () => {}, [], { reason: 'unsupportedFork' }, false],
  [fixture('fuel exhaustion in the constructor', { init: deploy(runtime, constructor), frame: 'returned', targetSlots: [0n] }),
    input => { input.fuel = '3' }, [optIn], { reason: 'stepLimit' }, true],
]

const matches = [], rejections = [], boundaries = [], gasBoundaries = [], failures = []
let negativeControls, oversizeInitcode, sequence

async function compareExecution(test, vm, accounts) {
  const env = context(test)
  const decoded = signedTransaction(test, env.common)
  const input = request(test, env.header, prestate(test), decoded)
  if (accounts) input.accounts = accounts
  const ref = await executeReference(test, env, input, decoded, vm)
  const expected = observeReference(test, decoded, ref)
  assert.equal(expected.frameStatus, test.frame, test.name + ': reference frame status')
  const actual = lean(input)
  assert.deepEqual(actual, expected)
  const receipt = encodeLeanReceipt(actual, decoded.type)
  assert.deepEqual(receipt, encodeReceipt(ref.result.receipt, decoded.type))
  const root = await observeRoot(env.common, actual.accounts)
  if (!vm) assert.deepEqual(root, await ref.vm.stateManager.getStateRoot())
  if (!negativeControls && actual.logs.length > 0 && actual.createdAddress !== null) {
    const rejects = mutate => {
      const bad = structuredClone(actual)
      mutate(bad)
      assert.throws(() => assert.deepEqual(bad, expected), error => error?.code === 'ERR_ASSERTION')
      return true
    }
    const badCode = structuredClone(actual)
    badCode.accounts.find(a => a.address === actual.createdAddress).codeHex += '00'
    assert.notDeepEqual(await observeRoot(env.common, badCode.accounts), root)
    negativeControls = {
      changedGas: rejects(bad => { bad.gasUsed = decimal(BigInt(bad.gasUsed) + 1n) }),
      changedCreatedAddress: rejects(bad => { bad.createdAddress = decimal(BigInt(bad.createdAddress) + 1n) }),
      droppedCreatedAddress: rejects(bad => { bad.createdAddress = null }),
      changedDeployedCode: rejects(bad => { bad.accounts.find(a => a.address === bad.createdAddress).codeHex += '00' }),
      changedDeployedCodeRoot: true,
      changedSenderNonce: rejects(bad => { bad.accounts[0].nonce = decimal(BigInt(bad.accounts[0].nonce) + 1n) }),
    }
  }
  return {
    summary: {
      name: test.name, fork: test.fork, type: test.type, receipt: bytesToHex(receipt), stateRoot: bytesToHex(root),
      status: actual.receiptStatus, frame: actual.frameStatus, gasUsed: actual.gasUsed, createdAddress: actual.createdAddress,
    },
    vm: ref.vm, accounts: actual.accounts, actual,
  }
}

async function compareAdmission(test, reason, oracleMessage) {
  const env = context(test)
  const decoded = signedTransaction(test, env.common)
  const input = request(test, env.header, prestate(test), decoded)
  await assert.rejects(() => executeReference(test, env, input, decoded), oracleMessage)
  assert.deepEqual(lean(input), { schemaVersion, status: 'rejected', reason, keccakOptIn: true })
  return { name: test.name, reason, oracleStage: 'runTx' }
}

/** The complete request executes on both; the obscured request must be refused by Lean. */
async function compareBoundary(test, obscure, flags, expected, completeRuns) {
  const { actual } = completeRuns ? await compareExecution(test) : { actual: null }
  const env = context(test)
  const input = request(test, env.header, prestate(test), signedTransaction(test, env.common))
  obscure(input)
  const refused = lean(input, flags)
  assert.equal(refused.status, 'indeterminate', test.name)
  assert.deepEqual(refused, { schemaVersion, status: 'indeterminate', keccakOptIn: flags.includes(optIn), ...expected })
  return { name: test.name, reason: refused.reason, completeRequestMatched: actual !== null }
}

/** Exact gas for success, taken from the reference, then one unit less on both engines. */
async function compareGasBoundary(test) {
  const ample = await compareExecution(test)
  assert.equal(ample.actual.receiptStatus, 1)
  assert.equal(ample.actual.refundGas, '0')
  const exact = BigInt(ample.actual.gasUsed)
  const enough = await compareExecution({ ...test, name: test.name + ' (exact gas)', gas: exact })
  assert.equal(enough.actual.receiptStatus, 1)
  assert.equal(enough.actual.gasWeiReturned, '0')
  const short = await compareExecution({ ...test, name: test.name + ' (one short)', gas: exact - 1n, frame: 'exceptional' })
  assert.deepEqual([short.actual.receiptStatus, short.actual.gasUsed, short.actual.createdAddress, short.actual.frameError],
    [0, decimal(exact - 1n), null, 'outOfGas'])
  return { name: test.name, exactGas: decimal(exact), compared: 3 }
}

async function report(name, results, action) {
  try {
    results.push(await action())
  } catch (error) {
    failures.push({ name, message: String(error).slice(0, 1800) })
  }
}

try {
  for (const test of executions) await report(test.name, matches, async () => (await compareExecution(test)).summary)
  for (const [test, reason, message] of admissionCases)
    await report(test.name, rejections, () => compareAdmission(test, reason, message))
  for (const [test, obscure, flags, expected, completeRuns] of boundaryCases)
    await report(test.name, boundaries, () => compareBoundary(test, obscure, flags, expected, completeRuns))
  for (const test of [
    fixture('code deposit gas boundary, 8-byte runtime', { init: deploy(runtime), frame: 'returned' }),
    fixture('code deposit gas boundary, 255-byte runtime', { init: deploy('5b'.repeat(255)), frame: 'returned', gas: 400_000n }),
    fixture('code deposit gas boundary after a constructor write', {
      init: deploy(runtime, store(0n, 42n)), frame: 'returned', targetSlots: [0n],
    }),
  ]) await report(test.name, gasBoundaries, () => compareGasBoundary(test))

  // EIP-3860 admission: 49153 bytes. The reference refuses to build the
  // envelope; with its size check disabled it signs the same bytes for Lean.
  await report('initcode of 49153 bytes is rejected', [], async () => {
    const test = fixture('initcode of 49153 bytes is rejected', { init: '00'.repeat(49153), gas: 400_000n })
    const env = context(test)
    assert.throws(() => signedTransaction(test, env.common), /initcode|init code/i)
    const decoded = signedTransaction(test, env.common, { allowUnlimitedInitCodeSize: true })
    const input = request(test, env.header, prestate(test), decoded)
    assert.deepEqual(lean(input), { schemaVersion, status: 'rejected', reason: 'initcode-too-large', keccakOptIn: true })
    oversizeInitcode = { name: test.name, reason: 'initcode-too-large', oracleStage: 'signed-envelope-construction' }
  })

  // Three creations by one sender, one after another, on one reference state.
  // Each Lean request starts from the accounts Lean reported for the previous one.
  await report('nonce progression over three creations', [], async () => {
    const nonces = [7n, 8n, 9n]
    const slots = [[0n, 0n]]
    const base = fixture('sequence', {
      targetSlots: [0n],
      extraAccounts: nonces.map(nonce => ({ address: created(nonce), slots })),
    })
    let vm, accounts = request(base, context(base).header, prestate(base), signedTransaction(base, context(base).common)).accounts
    const addresses = []
    for (const [index, nonce] of nonces.entries()) {
      const step = await compareExecution(fixture('sequence step ' + index, {
        txNonce: nonce, stateNonce: nonce, init: deploy(runtime, store(0n, nonce)), frame: 'returned',
        gasUsedBefore: 1_000n + BigInt(index),
      }), vm, accounts)
      vm = step.vm
      accounts = step.accounts
      addresses.push(step.actual.createdAddress)
    }
    assert.deepEqual(addresses, nonces.map(nonce => decimal(created(nonce))))
    assert.equal(new Set(addresses).size, 3)
    assert.deepEqual(await observeRoot(context(base).common, accounts), await vm.stateManager.getStateRoot())
    sequence = { creations: 3, addresses, finalStateRootMatches: true }
  })
} finally {
  rmSync(directory, { recursive: true, force: true })
}

if (!negativeControls) failures.push({ name: 'comparator negative controls', message: 'no successful creation had logs' })
console.log(JSON.stringify({
  kind: 'synthetic-signed-creation-transactions-vs-ethereumjs-runTx',
  oracle: '@ethereumjs/vm@10.1.3',
  compared: executions.length, matched: matches.length, receiptAndStateRootMatches: matches.length,
  independentAdmissionRejections: rejections.length,
  oversizeInitcodeRejections: Number(Boolean(oversizeInitcode)),
  boundaryRefusals: boundaries.length,
  gasBoundaryTriples: gasBoundaries.length,
  sequenceCreations: sequence?.creations ?? 0,
  negativeControls,
  failures,
  matches, rejections, oversizeInitcode, boundaries, gasBoundaries, sequence,
}))
if (failures.length > 0) process.exitCode = 1
