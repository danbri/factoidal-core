#!/usr/bin/env node
/**
 * Compare signed synthetic ordinary transactions on Lean and EthereumJS.
 *
 * Both engines receive the same envelope, header fields, and complete synthetic
 * prestate. EthereumJS actually executes runTx. For Lean, the host transports
 * the verified decoded envelope and explicit account/slot coverage. The same
 * trusted host codec encodes Lean's receipt fields and post-state trie for exact
 * byte/root comparisons. No network or historical state is used.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { createBlock } from '@ethereumjs/block'
import { Common, Hardfork, Mainnet, createCustomCommon } from '@ethereumjs/common'
import { createTx, createTxFromRLP } from '@ethereumjs/tx'
import {
  Account, bigIntToBytes, bytesToBigInt, bytesToHex, createAddressFromPrivateKey,
  createAddressFromString, hexToBytes, unpadBytes,
} from '@ethereumjs/util'
import { Bloom, createVM, encodeReceipt, runTx } from '@ethereumjs/vm'

const binary = process.argv[2] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-subset', import.meta.url))
const directory = mkdtempSync(join(tmpdir(), 'lean-call-tx-'))
const schemaVersion = 1
const senderKey = hexToBytes('0x' + '00'.repeat(31) + '01') // Public synthetic fixture key.
const sender = createAddressFromPrivateKey(senderKey).toString()
const address = value => '0x' + BigInt(value).toString(16).padStart(40, '0')
const keyWord = value => '0x' + BigInt(value).toString(16).padStart(64, '0')
const to = address(0xc1)
const child = address(0xc3)
const beneficiary = address(0xc4)
const extra = address(0xc5)
const maxNonce = (1n << 64n) - 1n
const bytesHex = bytes => bytesToHex(bytes).slice(2)
const decimal = value => BigInt(value).toString()
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
const returnByte = '60015ff3'
const logAndReturn = store(0n, 42n) + logByte(1n, 0x7an) + returnByte

function fixture(name, changes = {}) {
  return {
    name, fork: 'shanghai', type: 2, code: '00', frame: 'stopped',
    txNonce: 7n, stateNonce: 7n, funds: 1_000_000n, to, beneficiary,
    recipientBalance: 11n, recipientSlots: [[0n, 0n], [1n, 7n]],
    value: 5n, gas: 100_000n, cap: 7n, priority: 3n, baseFee: 2n,
    data: '0001020000ff', accesses: [],
    blockGas: 30_000_000n, gasUsedBefore: 1_000n,
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
  add(sender, { exists: true, balance: test.funds, nonce: test.stateNonce, code: test.senderCode ?? '' })
  add(test.to, test.absent ? {} : {
    exists: true, balance: test.recipientBalance, nonce: 1n, code: test.code, slots: test.recipientSlots,
  })
  add(test.beneficiary, test.beneficiaryBalance !== undefined
    ? { exists: true, balance: test.beneficiaryBalance } : {})
  for (const account of test.extraAccounts ?? []) add(account.address, account)
  return accounts
}

function context(test) {
  const hardfork = test.fork === 'shanghai' ? Hardfork.Shanghai : Hardfork.Cancun
  const common = new Common({ chain: Mainnet, hardfork })
  const header = {
    number: test.fork === 'shanghai' ? 19_000_000n : 20_000_000n,
    timestamp: test.fork === 'shanghai' ? 1_706_000_000n : 1_720_000_000n,
    gasLimit: test.blockGas, gasUsed: test.gasUsedBefore,
    baseFeePerGas: test.baseFee,
    coinbase: test.beneficiary,
    mixHash: keyWord(9n),
    ...(test.fork === 'cancun' ? { blobGasUsed: 0n, excessBlobGas: 0n } : {}),
  }
  return { common, header, block: createBlock({ header }, { common }) }
}

function signedTransaction(test, common) {
  const signingCommon = test.unprotected
    ? new Common({ chain: Mainnet, hardfork: Hardfork.Homestead })
    : (test.wrongChain
      ? createCustomCommon({ chainId: 2 }, Mainnet, { hardfork: common.hardfork() })
      : common)
  const fee = test.type === 2
    ? { maxFeePerGas: test.cap, maxPriorityFeePerGas: test.priority }
    : { gasPrice: test.cap }
  const tx = createTx({
    type: test.type, nonce: test.txNonce, gasLimit: test.gas, value: test.value,
    to: test.to, data: '0x' + test.data, ...fee,
    ...(test.type !== 0 ? { accessList: test.accesses } : {}),
  }, { common: signingCommon }).sign(senderKey)
  const bytes = tx.serialize()
  const decoded = createTxFromRLP(bytes, { common: test.wrongChain ? signingCommon : common })
  assert.equal(decoded.verifySignature(), true)
  assert.equal(decoded.getSenderAddress().toString(), sender)
  return { bytes, decoded }
}

function request(test, header, state, decoded) {
  const type = decoded.type
  const signChain = type === 0
    ? (decoded.v >= 35n ? (decoded.v - 35n) / 2n : null)
    : decoded.chainId
  return {
    schemaVersion, fork: test.fork, fuel: decimal(test.fuel ?? 4096n),
    transaction: {
      type, chainId: signChain === null ? null : decimal(signChain),
      sender: decimal(decoded.getSenderAddress().toString()), to: decimal(decoded.to.toString()),
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
    const balance = await vm.stateManager.getAccount(addr)
    const storage = []
    for (const { key } of entry.storage) {
      const value = await vm.stateManager.getStorage(addr, hexToBytes(keyWord(key)))
      storage.push({ key, value: decimal(bytesToBigInt(value)) })
    }
    observed.push({
      address: entry.address, exists: balance !== undefined, balance: decimal(balance?.balance ?? 0n),
      nonce: decimal(balance?.nonce ?? 0n), codeHex: bytesHex(await vm.stateManager.getCode(addr)), storage,
    })
  }
  return observed
}

function observeLookups(vm, accounts) {
  const expected = new Map(accounts.map(entry => [entry.address, new Set(entry.storage.map(s => s.key))]))
  const observed = { account: new Set(), storage: new Set(), unmodelled: [], lastTopOpcode: undefined }
  vm.evm.events.on('step', step => {
    const opcode = step.opcode.name
    if (step.depth === 0) observed.lastTopOpcode = opcode
    if (opcode === 'SLOAD' || opcode === 'SSTORE') {
      const owner = decimal(step.address.toString())
      if (step.stack.length >= (opcode === 'SLOAD' ? 1 : 2)) {
        const key = decimal(step.stack.at(-1))
        observed.storage.add(owner + ':' + key)
        if (!expected.get(owner)?.has(key)) observed.unmodelled.push({ opcode, owner, key })
      }
    } else if (opcode === 'CALL' && step.stack.length >= 7) {
      const target = decimal(step.stack.at(-2) % (1n << 160n))
      observed.account.add(target)
      if (!expected.has(target)) observed.unmodelled.push({ opcode, target })
    }
  })
  return observed
}

async function executeReference(test, env, request, signed) {
  const vm = await createVM({ common: env.common })
  await seedState(vm, request.accounts)
  const lookups = observeLookups(vm, request.accounts)
  const result = await runTx(vm, { tx: signed, block: env.block, blockGasUsed: env.header.gasUsed })
  assert.deepEqual(lookups.unmodelled, [], test.name + ' must cover all reference state reads')
  const accounts = await observedAccounts(vm, request.accounts)
  return { vm, result, accounts, lookups }
}

function lean(request, enableKeccak = false) {
  const path = join(directory, 'request.json')
  writeFileSync(path, JSON.stringify(request) + '\n')
  const flags = enableKeccak ? ['--dangerously-enable-unverified-keccak'] : []
  const result = spawnSync(binary, [...flags, '--call-transaction', path], {
    encoding: 'utf8', timeout: 15_000, maxBuffer: 4 * 1024 * 1024,
  })
  assert.equal(result.error, undefined)
  assert.equal(result.status, 0, result.stdout + '\n' + result.stderr)
  return JSON.parse(result.stdout)
}

const logFields = ([addr, topics, data]) => ({
  address: decimal(bytesToBigInt(addr)), topics: topics.map(word => decimal(bytesToBigInt(word))), dataHex: bytesHex(data),
})

function observeReference(test, signed, result, accounts, frameStatus) {
  const gross = signed.getIntrinsicGas() + result.execResult.executionGasUsed
  const effective = result.amountSpent / result.totalGasSpent
  return {
    schemaVersion, status: 'executed', keccakOptIn: Boolean(test.keccak),
    receiptStatus: result.receipt.status,
    frameStatus,
    ...(test.frame === 'exceptional' ? { frameError: test.frameError ?? 'invalidOpcode' } : {}),
    gasUsedBeforeRefund: decimal(gross), refundGas: decimal(gross - result.totalGasSpent),
    gasUsed: decimal(result.totalGasSpent), cumulativeGasUsed: decimal(result.receipt.cumulativeBlockGasUsed),
    effectiveGasPrice: decimal(effective), gasWeiReturned: decimal((signed.gasLimit - result.totalGasSpent) * effective),
    beneficiaryTip: decimal(result.minerValue), baseFeeBurn: decimal(result.amountSpent - result.minerValue),
    returnBytesHex: bytesHex(result.execResult.returnValue), logs: result.receipt.logs.map(logFields), accounts,
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

const contextOps = ['32', '33', '34', '46', '41', '43', '42', '44', '45', '48', '3a', '47']
const contextCode = contextOps.map((op, index) => op + push(BigInt(index * 32)) + '52').join('') +
  push(BigInt(contextOps.length * 32)) + '5ff3'
const programs = [
  ['header-context', contextCode, 'returned'],
  ['write-log-return', logAndReturn, 'returned'],
  ['write-log-revert', logAndReturn.slice(0, -2) + 'fd', 'reverted'],
  ['write-log-invalid', logAndReturn.slice(0, -2) + 'fe', 'exceptional'],
]
const executions = ['shanghai', 'cancun'].flatMap(fork => [0, 1, 2].flatMap(type =>
  programs.map(([name, code, frame]) => fixture(fork + '/type' + type + '/' + name, { fork, type, code, frame }))))
const keys = (...items) => items.map(keyWord)
const access = (addr, ...storageKeys) => ({ address: addr, storageKeys: keys(...storageKeys) })
const saveClear = store(0n, 1n) + store(0n, 0n)
const childCode = store(0n, 31n) + logByte(0x12n, 0x34n)
const childAccount = (code, balance = 4n) => ({
  address: child, exists: true, nonce: 1n, balance, code, slots: [[0n, 0n]],
})
const loggedCall = logByte(1n, 0xaan) + call(child, 2n) + '50' + logByte(3n, 0xccn)
executions.push(
  fixture('unprotected legacy replay domain', { type: 0, unprotected: true, data: '', code: '00' }),
  fixture('last incrementable sender nonce', { txNonce: maxNonce - 1n, stateNonce: maxNonce - 1n }),
  fixture('calldata zero single', { data: '00', gas: 21_004n, code: '' }),
  fixture('calldata nonzero single', { data: 'fe', gas: 21_016n, code: '' }),
  fixture('calldata larger than word', { data: '002a'.repeat(40), code: '365f355f5260205ff3', frame: 'returned' }),
  fixture('fee market cap binds', { cap: 4n, priority: 3n }),
  fixture('effective fee equals base fee', { cap: 2n, priority: 2n }),
  fixture('declared gas equal to block remainder', { gas: 70_000n, blockGas: 71_000n }),
  fixture('exact upfront funds including value', { funds: 700_005n }),
  fixture('sender, recipient and beneficiary alias', {
    to: sender, code: '', frame: 'stopped', beneficiary: sender,
  }),
  fixture('sender is beneficiary after storage transfer', { beneficiary: sender, code: logAndReturn, frame: 'returned' }),
  fixture('recipient is beneficiary and sees value not tip', {
    beneficiary: to, code: '475f5260205ff3', frame: 'returned',
  }),
  fixture('beneficiary already funded', { beneficiaryBalance: 123n }),
  fixture('absent recipient zero value and absent beneficiary zero tip', {
    absent: true, value: 0n, priority: 0n, cap: 2n, data: '',
  }),
  fixture('absent recipient receives value', { absent: true, data: '' }),
  fixture('cold SLOAD then same-key SSTORE', { code: '5f5450' + store(0n, 4n) + '00' }),
  fixture('warm SSTORE from type 1 access list', { type: 1, accesses: [access(to, 0n)], code: store(0n, 4n) + '00' }),
  fixture('warm SSTORE duplicate address cost from type 2', {
    accesses: [access(to, 0n), access(to, 0n)], code: store(0n, 4n) + '00',
  }),
  fixture('warm SSTORE duplicate slot cost from type 2', {
    accesses: [access(to, 0n, 0n)], code: store(0n, 4n) + '00',
  }),
  fixture('separate access-list addresses and key zero', {
    accesses: [access(to, 0n, 1n), access(child, 0n)], code: store(1n, 5n) + store(0n, 8n) + '00',
  }),
  fixture('SSTORE zero to nonzero to zero refund cap', { code: saveClear + '00' }),
  fixture('SSTORE nonzero to zero fixed refund', { code: store(1n, 0n) + '00' }),
  fixture('SSTORE reset nonzero original within transaction', { code: store(1n, 0n) + store(1n, 7n) + '00' }),
  fixture('SSTORE refund disappears on top-level revert', { code: saveClear + '5f5ffd', frame: 'reverted' }),
  fixture('nested value and chronological logs survive', {
    code: loggedCall + '00', extraAccounts: [childAccount(childCode + '00')],
  }),
  fixture('nested value and descendant logs rolled back by child REVERT', {
    code: loggedCall + '00', extraAccounts: [childAccount(childCode + '5f5ffd')],
  }),
  fixture('nested value and descendant logs rolled back by child INVALID', {
    code: loggedCall + '00', extraAccounts: [childAccount(childCode + 'fe')],
  }),
  fixture('successful descendant rolled back by ancestor REVERT', {
    code: loggedCall + '5f5ffd', frame: 'reverted', extraAccounts: [childAccount(childCode + '00')],
  }),
  fixture('successful descendant rolled back by ancestor INVALID', {
    code: loggedCall + 'fe', frame: 'exceptional', extraAccounts: [childAccount(childCode + '00')],
  }),
  fixture('prewarmed child via access list and repeated CALL', {
    code: call(child) + '50' + call(child) + '5000', accesses: [access(child, 0n)],
    extraAccounts: [childAccount(childCode + '00')],
  }),
  fixture('beneficiary is warm as nested CALL target', { code: call(beneficiary) + '00' }),
  fixture('nested zero-value CALL to proved absence', { code: call(extra) + '00', extraAccounts: [{ address: extra }] }),
  fixture('nested value CALL creates proved absent account', {
    code: call(extra, 1n) + '00', extraAccounts: [{ address: extra }],
  }),
  fixture('nested value CALL with insufficient funds', {
    code: call(extra, 1000n) + '00', extraAccounts: [{ address: extra }],
  }),
  fixture('opted-in Keccak executes then emits digest', {
    code: '5f5f205f52600160205fa160205ff3', frame: 'returned', keccak: true,
  }),
  fixture('Cancun blob price in ordinary call transaction', {
    fork: 'cancun', code: '4a5f5260205ff3', frame: 'returned',
  }),
)

const admissionCases = [
  [fixture('nonce too high', { txNonce: 8n }), 'invalid-sender-nonce', /correct nonce/i],
  [fixture('nonce too low', { txNonce: 6n }), 'invalid-sender-nonce', /correct nonce/i],
  [fixture('cap exceeds funds even when effective price fits', { cap: 30n }), 'insufficient-upfront-balance', /enough funds/i],
  [fixture('max fee funded but value unfunded', { funds: 700_004n }), 'insufficient-upfront-balance', /enough funds/i],
  [fixture('cap below base fee', { cap: 1n, priority: 1n }), 'price-below-base-fee', /baseFee|base fee/i],
  [fixture('calldata makes intrinsic gas unaffordable', { gas: 21_000n }), 'below-intrinsic-gas', /intrinsic/i],
  [fixture('sender has deployed code', { senderCode: '00' }), 'sender-has-code', /EOA|sender.*code/i],
  [fixture('typed signature for another network', { wrongChain: true }), 'chain-id-mismatch', /chain ID|chainId/i],
]

const removeAddress = (request, addr) => {
  request.accounts = request.accounts.filter(record => record.address !== decimal(addr))
}
const removeSlot = (request, addr, key) => {
  const record = request.accounts.find(item => item.address === decimal(addr))
  record.storage = record.storage.filter(item => item.key !== decimal(key))
}
const boundaryCases = [
  [fixture('missing SLOAD slot', { code: '5f5400' }), r => removeSlot(r, to, 0n),
    { reason: 'incompleteState', address: decimal(to), slot: '0' }],
  [fixture('missing SSTORE slot', { code: store(0n, 1n) + '00' }), r => removeSlot(r, to, 0n),
    { reason: 'incompleteState', address: decimal(to), slot: '0' }],
  [fixture('missing nested CALL target', { code: call(child) + '00', extraAccounts: [childAccount('00')] }),
    r => removeAddress(r, child), { reason: 'incompleteState', address: decimal(child), slot: null }],
  [fixture('missing beneficiary witness'), r => removeAddress(r, beneficiary),
    { reason: 'incompleteState', address: decimal(beneficiary), slot: null }],
  [fixture('fuel exhaustion', { code: logAndReturn }), r => { r.fuel = '1' }, { reason: 'stepLimit' }],
  [fixture('simulation gas cap', { gas: 100_000_001n, blockGas: 150_000_000n, funds: 1_000_000_000n }),
    () => {}, { reason: 'resourceLimit' }],
  [fixture('simulation fuel cap'), r => { r.fuel = '1000001' }, { reason: 'resourceLimit' }],
  [fixture('Keccak without explicit permission', { code: '5f5f205000' }), () => {}, { reason: 'unsupportedFork' }],
  [fixture('scope refuses valid CREATE', { code: '5f5f5ff05000' }), () => {}, { reason: 'invalidOpcode' }],
  [fixture('scope refuses identity precompile', { to: address(4), absent: true }), () => {}, { reason: 'unsupportedFork' }],
  [fixture('scope refuses present-empty witness', { absent: true, data: '', value: 0n }),
    r => { r.accounts.find(a => a.address === decimal(to)).exists = true }, { reason: 'invalidWitness' }],
]

const matches = []
const rejections = []
const boundaries = []
const failures = []
let negativeControls
let preSerializationRejection

async function compareExecution(test) {
  const env = context(test)
  const { bytes, decoded } = signedTransaction(test, env.common)
  const input = request(test, env.header, prestate(test), decoded)
  const ref = await executeReference(test, env, input, decoded)
  const referenceError = ref.result.execResult.exceptionError?.error
  if (test.frame === 'reverted') assert.equal(referenceError, 'revert')
  else if (test.frame === 'exceptional') assert.match(referenceError, /invalid opcode/)
  else assert.equal(referenceError, undefined)
  const frameStatus = referenceError === 'revert' ? 'reverted' :
    (referenceError ? 'exceptional' : (ref.lookups.lastTopOpcode === 'RETURN' ? 'returned' : 'stopped'))
  assert.equal(frameStatus, test.frame)
  const expected = observeReference(test, decoded, ref.result, ref.accounts, frameStatus)
  const actual = lean(input, test.keccak)
  assert.deepEqual(actual, expected)
  const receipt = encodeLeanReceipt(actual, decoded.type)
  assert.deepEqual(receipt, encodeReceipt(ref.result.receipt, decoded.type))
  const root = await observeRoot(env.common, actual.accounts)
  assert.deepEqual(root, await ref.vm.stateManager.getStateRoot())
  if (!negativeControls && actual.logs.length > 0) {
    const badGas = structuredClone(actual)
    badGas.gasUsed = decimal(BigInt(actual.gasUsed) + 1n)
    const badLog = structuredClone(actual)
    badLog.logs[0].topics[0] = decimal(BigInt(actual.logs[0].topics[0]) + 1n)
    const badState = structuredClone(actual)
    badState.accounts[0].balance = decimal(BigInt(actual.accounts[0].balance) + 1n)
    const badRoot = await observeRoot(env.common, badState.accounts)
    const isComparatorRejection = error => error?.code === 'ERR_ASSERTION'
    assert.throws(() => assert.deepEqual(badGas, expected), isComparatorRejection)
    assert.throws(() => assert.deepEqual(encodeLeanReceipt(badLog, decoded.type), receipt), isComparatorRejection)
    assert.throws(() => assert.deepEqual(badRoot, root), isComparatorRejection)
    negativeControls = { changedGas: true, changedReceiptLog: true, changedStateBalance: true }
  }
  return {
    name: test.name, fork: test.fork, type: test.type, txBytes: bytesToHex(bytes),
    receipt: bytesToHex(receipt), stateRoot: bytesToHex(root),
    status: actual.receiptStatus, gasUsed: actual.gasUsed, logs: actual.logs.length,
    witnessedReadSlots: ref.lookups.storage.size, witnessedCallTargets: ref.lookups.account.size,
  }
}

async function compareAdmission(test, reason, oracleMessage) {
  const env = context(test)
  const { bytes, decoded } = signedTransaction(test, env.common)
  const input = request(test, env.header, prestate(test), decoded)
  if (test.wrongChain) assert.throws(() => createTxFromRLP(bytes, { common: env.common }), oracleMessage)
  else await assert.rejects(() => executeReference(test, env, input, decoded), oracleMessage)
  assert.deepEqual(lean(input), { schemaVersion, status: 'rejected', reason, keccakOptIn: false })
  return { name: test.name, reason, oracleStage: test.wrongChain ? 'signed-envelope-decode' : 'runTx' }
}

async function compareBoundary(test, obscure, expected) {
  const env = context(test)
  const { decoded } = signedTransaction(test, env.common)
  const input = request(test, env.header, prestate(test), decoded)
  const reference = await executeReference(test, env, input, decoded)
  assert.equal(reference.result.receipt.status, 1, test.name)
  obscure(input)
  assert.deepEqual(lean(input), {
    schemaVersion, status: 'indeterminate', keccakOptIn: false, ...expected,
  })
  return { name: test.name, reason: expected.reason, oracleRanWithCompleteSyntheticState: true }
}

async function report(name, results, action) {
  try {
    results.push(await action())
  } catch (error) {
    failures.push({ name, message: String(error).slice(0, 1800) })
  }
}

try {
  for (const test of executions) await report(test.name, matches, () => compareExecution(test))
  for (const [test, reason, message] of admissionCases)
    await report(test.name, rejections, () => compareAdmission(test, reason, message))
  for (const [test, obscure, expected] of boundaryCases)
    await report(test.name, boundaries, () => compareBoundary(test, obscure, expected))
  const overNonce = fixture('sender nonce cannot be incremented', { txNonce: maxNonce, stateNonce: maxNonce })
  try {
    const env = context(overNonce)
    assert.throws(() => signedTransaction(overNonce, env.common), /nonce/i)
    const signable = signedTransaction(fixture('nonce control'), env.common)
    const input = request(overNonce, env.header, prestate(overNonce), signable.decoded)
    // The independent library refuses to serialise this nonce. Challenge the
    // direct decoded Lean boundary separately without calling it a signed case.
    input.transaction.nonce = decimal(maxNonce)
    assert.deepEqual(lean(input), {
      schemaVersion, status: 'rejected', reason: 'invalid-sender-nonce', keccakOptIn: false,
    })
    preSerializationRejection = { name: overNonce.name, reason: 'invalid-sender-nonce' }
  } catch (error) {
    failures.push({ name: overNonce.name, message: String(error).slice(0, 1800) })
  }
} finally {
  rmSync(directory, { recursive: true, force: true })
}

if (!negativeControls) failures.push({ name: 'comparator negative controls', message: 'no receipt had logs' })
console.log(JSON.stringify({
  kind: 'synthetic-signed-call-transactions-vs-ethereumjs-runTx',
  oracle: '@ethereumjs/vm@10.1.3',
  compared: executions.length, matched: matches.length, receiptAndStateRootMatches: matches.length,
  independentAdmissionRejections: rejections.length,
  preSerializationRejections: Number(Boolean(preSerializationRejection)),
  boundaryRefusals: boundaries.length,
  negativeControls,
  failures,
  matches,
  rejections,
  preSerializationRejection,
  boundaries,
}))
if (failures.length > 0) process.exitCode = 1
