#!/usr/bin/env node
/**
 * Independently execute identity (0x04) through all four CALL instructions.
 * EIP-2929 specifies transaction-initial precompile warmth; the identity gas
 * rule is Yellow Paper Appendix E.4. References execute the same bytecode.
 * This is a selected integration corpus, not an official EELS fixture suite.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { isDeepStrictEqual } from 'node:util'
import { fileURLToPath } from 'node:url'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createEVM } from '@ethereumjs/evm'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'
import { openGeth } from './geth-byte-oracle.mjs'

const executable = process.argv[2] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-subset', import.meta.url))
const lockSha256 = 'cc95a62e125486d2de9a28cb5fc61c098b955aa22c2dd0b3dc0b19f2df770425'
assert.equal(createHash('sha256').update(readFileSync(new URL('./package-lock.json', import.meta.url)))
  .digest('hex'), lockSha256, 'EthereumJS dependency lock')
const A = 0xc1, B = 0xc3, C = 0xc4, sender = 0xc2
const address = n => createAddressFromString('0x' + n.toString(16).padStart(40, '0'))
const maxWord = (1n << 256n) - 1n
const variants = ['call', 'callcode', 'delegatecall', 'staticcall']
const opcodes = {call: 'f1', callcode: 'f2', delegatecall: 'f4', staticcall: 'fa'}
const observationLimit = 4096
const bytes = data => hexToBytes('0x' + data)
const hex = data => Buffer.from(data).toString('hex')
const decimal = data => data.length ? BigInt('0x' + hex(data)).toString() : '0'
const word = n => BigInt(n).toString(16).padStart(64, '0')
function push(n) {
  const v = BigInt(n)
  assert(v >= 0n && v <= maxWord)
  if (!v) return '5f'
  const raw = v.toString(16), padded = raw.padStart(raw.length + raw.length % 2, '0')
  return (0x5f + padded.length / 2).toString(16) + padded
}
function invoke(op, {target = 4, value = 0, requested = 50000,
  input = 0, inputSize = 0, output = 0, outputSize = 0} = {}) {
  const args = [outputSize, output, inputSize, input]
  if (op === 'call' || op === 'callcode') args.push(value)
  else assert.equal(value, 0)
  return [...args, target, requested].map(push).join('') + opcodes[op]
}
const halt = (op, offset, size) => push(size) + push(offset) + op
const store = (n, offset) => push(n) + push(offset) + '52'
// Distinct words detect a 32-byte offset error; the first byte is zero.
const initialBytes = Array.from({length: 192}, (_, i) => i.toString(16).padStart(2, '0')).join('')
const prefill = Array.from({length: 6}, (_, i) =>
  store(BigInt('0x' + initialBytes.slice(64 * i, 64 * (i + 1))), 32 * i)).join('')
const inputBytes = (offset, size) => initialBytes.padEnd(2 * (offset + size), '0').slice(2 * offset, 2 * (offset + size))
const defaults = {gas: 220000, fuel: 500, parentBalance: 19, childBalance: 7,
  childNonce: 1, child: '', grandchild: '', prewarmParent: true}
const cases = []
function add(category, variant, name, parent, extra = {}) {
  cases.push({...defaults, category, variant, id: variant + ':' + name, parent, ...extra})
}

// For every word boundary, exercise no gas, one below, exact, one above, and
// ample gas. Output windows include zero length at a maximal offset, overlap,
// and both shorter and longer windows with a pre-existing nonzero tail.
for (const op of variants) {
  for (const size of [0, 1, 31, 32, 33, 64, 65, 257, 1024]) {
    const cost = 15 + 3 * Math.ceil(size / 32)
    for (const requested of [0, cost - 1, cost, cost + 1, 20000]) {
      for (const [name, output, outputSize] of [
        ['empty', maxWord, 0], ['short-overlap', 7, Math.min(size, 3)], ['long-overlap', 29, size + 9],
      ]) {
        const succeeds = requested >= cost
        add('bytes-and-gas', op, `${size}:${requested}:${name}`,
          prefill + invoke(op, {requested, input: 1, inputSize: size, output, outputSize}) + '3d00', {
            expect: {status: 'stopped', stack: [String(succeeds ? size : 0), succeeds ? '1' : '0'],
              returnDataHex: succeeds ? inputBytes(1, size) : ''},
          })
      }
    }
  }
  add('mask-and-repeat', op, 'high-address-bits', prefill +
    invoke(op, {target: (1n << 200n) + 4n, inputSize: 31, output: 33, outputSize: 31}) + '3d00',
  {expect: {stack: ['31', '1'], returnDataHex: inputBytes(0, 31)}})
  add('mask-and-repeat', op, 'failure-clears-prior-return-data', prefill +
    invoke(op, {inputSize: 33, output: 7, outputSize: 3}) +
    invoke(op, {requested: 14, output: 0, outputSize: 9}) + '3d00',
  {expect: {stack: ['0', '0', '1'], returnDataHex: ''}})
  add('mask-and-repeat', op, 'repeated-call-stays-warm', prefill +
    invoke(op, {inputSize: 31, output: 65, outputSize: 31}) +
    invoke(op, {input: 65, inputSize: 31, output: 97, outputSize: 31}) + '3d00',
  {expect: {stack: ['31', '1', '1'], returnDataHex: inputBytes(0, 31)}})
  add('return-data', op, 'copy-past-output-window', prefill +
    invoke(op, {inputSize: 33, output: 9, outputSize: 1}) +
    push(32) + push(1) + push(193) + '3e' + halt('f3', 193, 32),
  {expect: {status: 'returned', returnBytesHex: inputBytes(1, 32)}})
  for (const [name, ending, status] of [
    ['parent-return', halt('f3', 23, 41), 'returned'],
    ['parent-revert', halt('fd', 23, 41), 'reverted'], ['parent-exception', 'fe', 'exceptional'],
  ]) add('rollback', op, name, prefill + invoke(op, {input: 2, inputSize: 33, output: 23, outputSize: 33}) + ending,
    {expect: {status}})
  for (const gas of [115, 116, 117, 131, 132, 133, 163, 164, 165, 195, 196, 197]) {
    add('eip150', op, 'all-gas-' + gas, invoke(op, {requested: maxWord}) + '00', {gas})
  }
  for (const depth of [1023, 1024]) {
    add('depth', op, 'depth-' + depth, prefill + invoke(op, {inputSize: 33, outputSize: 33}) + '3d00', {
      depth, expect: {stack: depth === 1023 ? ['33', '1'] : ['0', '0']},
    })
  }
  add('static', op, 'static-root', prefill + invoke(op, {inputSize: 33, outputSize: 33}) + '3d00', {
    readOnly: true, expect: {stack: ['33', '1'], parentBalance: '19'},
  })
  for (const [name, ending, status] of [
    ['nested-success', halt('f3', 64, 33), '1'],
    ['nested-revert', halt('fd', 64, 33), '0'], ['nested-exception', 'fe', '0'],
  ]) {
    add('nested', op, name, invoke('call', {target: B, requested: 90000, output: 11, outputSize: 33}) + '3d00', {
      child: prefill + invoke(op, {inputSize: 33, output: 64, outputSize: 33}) + ending,
      expect: {stack: [name === 'nested-exception' ? '0' : '33', status]},
    })
  }
  add('nested', op, 'inherited-static', invoke('staticcall', {target: B, requested: 90000, outputSize: 33}) + '3d00', {
    child: prefill + invoke(op, {inputSize: 33, outputSize: 33}) + halt('f3', 0, 33),
    expect: {stack: ['33', '1'], returnDataHex: inputBytes(0, 33)},
  })
}
for (const op of ['call', 'callcode']) {
  for (const value of [1, 19, 20]) {
    for (const requested of [0, 15]) {
      add('value', op, 'stipend-' + value + '-' + requested, prefill +
        invoke(op, {value, requested, inputSize: 33, output: 11, outputSize: 33}) + '3d00', {
          expect: {stack: value > 19 ? ['0', '0'] : ['33', '1'],
            parentBalance: String(op === 'call' && value <= 19 ? 19 - value : 19)},
        })
    }
  }
  for (const [name, end] of [['revert', '5f5ffd'], ['exception', 'fe']]) {
    add('value', op, 'root-' + name, invoke(op, {value: 3, requested: 0}) + end,
      {expect: {parentBalance: '19'}})
  }
}

const exceptionNames = new Map([['out of gas', 'outOfGas'], ['invalid opcode', 'invalidOpcode'],
  ['static state change', 'writeProtection'], ['stack underflow', 'stackUnderflow']])
function snapshot(out, name, data) {
  assert(data.length <= observationLimit, name + ' complete observation')
  out[name + 'Hex'] = hex(data)
  out[name + 'Size'] = String(data.length)
  out[name + 'Truncated'] = false
}
async function ethereumJS(c, warmPrecompiles = true) {
  const common = new Common({chain: Mainnet, hardfork: Hardfork.Shanghai})
  const evm = await createEVM({common})
  if (warmPrecompiles) {
    // https://eips.ethereum.org/EIPS/eip-2929#specification
    for (const target of evm.precompiles.keys()) evm.journal.addAlwaysWarmAddress(target)
  }
  if (c.prewarmParent) evm.journal.addAlwaysWarmAddress(address(A).toString())
  for (const [n, code, balance, nonce] of [
    [A, c.parent, c.parentBalance, 0], [B, c.child, c.childBalance, c.childNonce], [C, c.grandchild, 0, 0],
  ]) {
    if (code || balance || nonce) await evm.stateManager.putAccount(address(n), new Account(BigInt(nonce), BigInt(balance)))
    if (code) await evm.stateManager.putCode(address(n), bytes(code))
  }
  let lastOpcode
  evm.events.on('step', (step, resolve) => {
    if (step.depth === (c.depth ?? 0)) lastOpcode = step.opcode.code
    resolve?.()
  })
  const gas = BigInt(c.gas)
  const {execResult: ex} = await evm.runCall({caller: address(sender), origin: address(sender),
    to: address(A), gasLimit: gas, isStatic: c.readOnly ?? false, depth: c.depth ?? 0})
  const error = ex.exceptionError?.error
  const status = error === 'revert' ? 'reverted' : error ? 'exceptional' : lastOpcode === 0xf3 ? 'returned' : 'stopped'
  const parent = await evm.stateManager.getAccount(address(A)), child = await evm.stateManager.getAccount(address(B))
  const key = new Uint8Array(32)
  const out = {schemaVersion: 2, status, gasRemaining: String(gas - ex.executionGasUsed),
    entryParentWarm: c.prewarmParent, parentBalance: String(parent?.balance ?? 0),
    childBalance: String(child?.balance ?? 0), childNonce: String(child?.nonce ?? 0), refund: String(ex.gasRefund ?? 0),
    parentSlot0: decimal(await evm.stateManager.getStorage(address(A), key)),
    slot0: decimal(await evm.stateManager.getStorage(address(B), key)),
    grandchildSlot0: decimal(await evm.stateManager.getStorage(address(C), key)),
    warmAddress: evm.journal.isWarmedAddress(address(B).bytes),
    warmSlot: evm.journal.isWarmedStorage(address(B).bytes, key),
    warmGrandchildAddress: evm.journal.isWarmedAddress(address(C).bytes),
    warmGrandchildSlot: evm.journal.isWarmedStorage(address(C).bytes, key)}
  snapshot(out, 'returnBytes', ex.returnValue)
  if (status === 'exceptional') {
    assert(exceptionNames.has(error), 'mapped exception ' + error)
    out.reason = exceptionNames.get(error)
  } else {
    out.stack = ex.runState.stack.peek(ex.runState.stack.length).map(String)
    snapshot(out, 'parentMemory', ex.runState.memory.read(0, Number(ex.runState.memoryWordCount * 32n)))
    snapshot(out, 'returnData', ex.runState.returnBytes)
  }
  for (const [field, value] of Object.entries(c.expect ?? {})) assert.deepEqual(out[field], value, c.id + ': ' + field)
  return out
}
function lean(c) {
  const args = ['--call-opcode', c.parent, c.child, String(c.gas), String(c.fuel),
    String(c.parentBalance), String(c.childBalance), String(c.childNonce), c.readOnly ? '1' : '0',
    'shanghaiPlus', String(c.depth ?? 0), c.grandchild, c.prewarmParent ? '1' : '0', String(sender), String(sender)]
  const p = spawnSync(executable, args, {encoding: 'utf8', timeout: 10000, maxBuffer: 128 * 1024})
  assert.ifError(p.error)
  assert.equal(p.status, 0, 'Lean process: ' + p.stderr)
  const out = JSON.parse(p.stdout)
  assert.notEqual(out.status, 'indeterminate', c.id + ': executable integration outcome')
  assert.notEqual(out.status, 'inputError', c.id + ': accepted fixture')
  for (const name of ['returnBytes', ...(out.status === 'exceptional' ? [] : ['parentMemory', 'returnData'])]) {
    assert.equal(out[name + 'Truncated'], false, c.id + ': ' + name + ' complete')
    assert.match(out[name + 'Hex'], /^(?:[0-9a-f]{2})*$/)
    assert.equal(out[name + 'Size'], String(out[name + 'Hex'].length / 2))
  }
  return out
}
const geth = openGeth()
function gethReference(c) {
  const g = geth.run({code: c.parent, gas: c.gas, accounts: [
    [A, c.parent, c.parentBalance, 0], [B, c.child, c.childBalance, c.childNonce], [C, c.grandchild, 0, 0],
  ]})
  const pa = g.account(A), ca = g.account(B)
  const out = {status: g.status, gasRemaining: g.gasRemaining, returnBytesHex: g.bytesHex,
    parentBalance: pa.balance, childBalance: ca.balance, childNonce: ca.nonce,
    parentSlot0: pa.slot0, slot0: ca.slot0, grandchildSlot0: g.account(C).slot0}
  if (g.status === 'stopped') Object.assign(out, {stack: g.stack, parentMemoryHex: g.memoryHex, parentMemorySize: g.memorySize})
  if (g.returnDataHex !== undefined) out.returnDataHex = g.returnDataHex
  if (g.refund !== undefined) out.refund = g.refund
  return out
}
const differences = (expected, actual) => Object.keys(expected).filter(key => !isDeepStrictEqual(expected[key], actual[key]))
const counts = () => ({compared: 0, matched: 0, mismatches: 0, errors: 0})
const results = {ethereumJS: counts(), geth: counts(), crossOracle: counts()}
const categories = {}, variantCounts = {}, failures = [], observations = new Map(), inventory = []
const excluded = {staticEntry: 0, nonzeroDepth: 0}
function compare(c, label, expected, actual) {
  const groups = [results[label], categories[c.category][label], variantCounts[c.variant][label]]
  if (!expected || !actual) {
    for (const group of groups) group.errors++
    return false
  }
  const fields = differences(expected, actual)
  for (const group of groups) { group.compared++; group[fields.length ? 'mismatches' : 'matched']++ }
  if (fields.length) failures.push({id: c.id, oracle: label, fields, expected, actual})
  return fields.length === 0
}
async function observe(c, source, operation) {
  try { return await operation() }
  catch (error) { failures.push({id: c.id, source, error: String(error)}); return undefined }
}
assert.equal(new Set(cases.map(c => c.id)).size, cases.length, 'unique fixture names')
assert.equal(cases.length, 660, 'complete selected integration inventory')
for (const c of cases) {
  categories[c.category] ??= {ethereumJS: counts(), geth: counts(), crossOracle: counts()}
  variantCounts[c.variant] ??= {ethereumJS: counts(), geth: counts(), crossOracle: counts()}
  const record = {id: c.id, category: c.category, variant: c.variant}
  inventory.push(record)
  const expected = await observe(c, 'EthereumJS', () => ethereumJS(c))
  const actual = await observe(c, 'Lean', () => lean(c))
  record.ethereumJS = compare(c, 'ethereumJS', expected, actual)
  if (record.ethereumJS) observations.set(c.id, {expected, actual})
  if (geth) {
    const why = c.readOnly ? 'staticEntry' : c.depth ? 'nonzeroDepth' : undefined
    if (why) { excluded[why]++; record.gethExcluded = why }
    else {
      const second = await observe(c, 'Geth', () => gethReference(c))
      record.geth = compare(c, 'geth', second, actual)
      record.crossOracle = compare(c, 'crossOracle', second, expected)
    }
  }
}
// This intentionally incomplete raw-message context is a test control only.
// Omitting transaction precompile warmth must reproduce the 2,500 gas error.
const warmthFixture = {...defaults, id: 'initial-warmth-control', parent: invoke('call', {requested: 30000}) + '00'}
const warm = await ethereumJS(warmthFixture), cold = await ethereumJS(warmthFixture, false)
const warmthControl = {warmGas: warm.gasRemaining, coldGas: cold.gasRemaining,
  extraColdGas: String(BigInt(warm.gasRemaining) - BigInt(cold.gasRemaining))}
assert.equal(warmthControl.extraColdGas, '2500')
const negativeControls = {}
const example = observations.get('call:33:21:long-overlap')
for (const [name, field, mutation] of [
  ['gas', 'gasRemaining', out => String(BigInt(out.gasRemaining) + 1n)],
  ['successBit', 'stack', out => ['33', '0']],
  ['returnData', 'returnDataHex', out => 'ff' + out.returnDataHex.slice(2)],
  ['copiedMemory', 'parentMemoryHex', out => 'ff' + out.parentMemoryHex.slice(2)],
]) negativeControls[name] = !!example && isDeepStrictEqual(differences(example.expected,
  {...example.actual, [field]: mutation(example.actual)}), [field])
const gethEligible = cases.filter(c => !c.readOnly && !c.depth).length
const report = {kind: 'identity-precompile-through-actual-call-family', fork: 'Shanghai',
  leanSha256: createHash('sha256').update(readFileSync(executable)).digest('hex'),
  ethereumJS: {version: '@ethereumjs/evm@10.1.3', lockSha256, ...results.ethereumJS},
  geth: geth ? {version: geth.version, sourceCommit: geth.sourceCommit, sha256: geth.sha256,
    ...results.geth, crossOracle: results.crossOracle, eligible: gethEligible, excluded} : null,
  cases: cases.length, categories, variants: variantCounts, warmthControl, negativeControls,
  failed: failures.length, firstFailures: failures.slice(0, 12), inventory,
  comparedFields: ['outcome', 'gas', 'full return bytes', 'full non-exceptional memory and returndata',
    'CALL success bits', 'payer balances', 'observed storage', 'warmth', 'refund'],
  boundary: 'Decoded message execution; arbitrary identity-account state and receipt accounting are checked by identity-transaction.mjs.'}
console.log(JSON.stringify(report))
if (failures.length || results.ethereumJS.matched !== cases.length ||
  (geth && (results.geth.matched !== gethEligible || results.crossOracle.matched !== gethEligible)) ||
  !Object.values(negativeControls).every(Boolean)) process.exitCode = 1
