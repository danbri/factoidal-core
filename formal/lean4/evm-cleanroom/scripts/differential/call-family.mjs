#!/usr/bin/env node
/**
 * Differential fixtures for actual CALLCODE, DELEGATECALL and STATICCALL bytecode.
 * Semantic reference: ethereum/execution-specs at
 * 1da5a11ca8cd3a4ad00fd1821c27ef01a4b18653, src/ethereum/forks/cancun/vm/instructions/system.py.
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
const variants = ['callcode', 'delegatecall', 'staticcall']
const opcodes = {call: 'f1', callcode: 'f2', delegatecall: 'f4', staticcall: 'fa'}
const address = n => createAddressFromString('0x' + n.toString(16).padStart(40, '0'))
const maxWord = (1n << 256n) - 1n
const addressLimit = 1n << 160n
const observationLimit = 4096
const hex = data => Buffer.from(data).toString('hex')
const bytes = data => hexToBytes('0x' + data)
const decimal = data => data.length ? BigInt('0x' + hex(data)).toString() : '0'
const word = n => BigInt(n).toString(16).padStart(64, '0')
function push(n) {
  const value = BigInt(n)
  assert(value >= 0n && value <= maxWord)
  if (value === 0n) return '5f'
  const raw = value.toString(16)
  const even = raw.padStart(raw.length + raw.length % 2, '0')
  return (0x5f + even.length / 2).toString(16) + even
}
function invoke(op, {
  target = B, value = 0, requested = 50000, input = 0, inputSize = 0, output = 0, outputSize = 0,
} = {}) {
  const args = [outputSize, output, inputSize, input]
  if (op === 'call' || op === 'callcode') args.push(value)
  else assert.equal(value, 0)
  return [...args, target, requested].map(push).join('') + opcodes[op]
}
const halt = (op, offset, size) => push(size) + push(offset) + op
const store = (value, offset) => push(value) + push(offset) + '52'
const sstore = value => push(value) + '5f55'
const returnWord = expression => expression + '5f52' + halt('f3', 0, 32)
const echo = '365f5f37365ff3'
const revertEcho = echo.slice(0, -2) + 'fd'
const pattern = '102132435465768798a9bacbdcedfe0f1a2b3c4d5e6f708192a3b4c5d6e7f809'
const prefill = store(BigInt('0x' + pattern), 0) + store(BigInt('0x' + pattern), 32)
const payload = store(0xd1e2f3, 0) + halt('f3', 29, 3)
const log = (payload, topic) => store(payload, 0) + push(topic) + push(2) + push(30) + 'a1'
const observedLog = (address, payload, topic) => ({
  address: String(address), topics: [String(topic)], dataHex: payload.toString(16).padStart(4, '0'),
})
const childLog = log(0x1234, 0xabc)
const contextOps = ['30', '33', '34', '47', '38', '32']
const contextSize = 32 * contextOps.length
const context = contextOps.map((op, i) => op + push(32 * i) + '52').join('') + halt('f3', 0, contextSize)
const copySelf = '385f5f39385ff3' // CODESIZE; CODECOPY; RETURN
const slotCost = '5a5f54505a9003' // Difference between GAS observations around SLOAD.
function selectInput(empty, nonempty) {
  return '3661' + (5 + empty.length / 2).toString(16).padStart(4, '0') + '57' + empty + '5b' + nonempty
}

const cases = []
const defaults = {gas: 220000, fuel: 500, prewarmParent: true}
function add(category, variant, name, parent, child, options = {}) {
  cases.push({...defaults, id: variant + ':' + name, category, variant, parent, child, ...options})
}
for (const op of variants) {
  const value = op === 'callcode' ? 5 : 0
  const caller = op === 'delegatecall' ? sender : A
  const environment = {parentBalance: 19, childBalance: 3, childNonce: 2}
  const contextBytes = [op === 'staticcall' ? B : A, caller, value,
    op === 'staticcall' ? environment.childBalance : environment.parentBalance, context.length / 2, sender]
    .map(word).join('')
  add('context', op, 'context-and-output-tail', prefill +
    invoke(op, {value, output: 7, outputSize: contextSize + 9}) + '3d00', context,
  {...environment, expect: {stack: [String(contextSize), '1'], returnDataHex: contextBytes}})
  add('context', op, 'codecopy-masks-address', prefill +
    invoke(op, {target: (1n << 200n) + BigInt(B), output: 9, outputSize: 3}) + '3d00',
  copySelf, {...environment, expect: {returnDataHex: copySelf}})
  add('context', op, 'call-value-then-nested-context', invoke('call', {value: 7, requested: 120000,
    outputSize: contextSize}) + '3d00', invoke(op, {target: C, value, outputSize: contextSize}) + halt('f3', 0, contextSize), {
    ...environment, grandchild: context,
    expect: {parentBalance: '12', childBalance: '10', returnDataHex: [
      op === 'staticcall' ? C : B, op === 'delegatecall' ? A : B,
      op === 'delegatecall' ? 7 : value, op === 'staticcall' ? 0 : 10, context.length / 2, sender,
    ].map(word).join('')},
  })

  for (const [name, windows, child, ending] of [
    ['full-output-with-tail', {input: 1, inputSize: 19, output: 33, outputSize: 28}, echo, '3d00'],
    ['short-output-full-returndata', {input: 31, inputSize: 37, output: 2, outputSize: 5}, echo, '3d00'],
    ['revert-copies-prefix', {input: 5, inputSize: 7, output: 11, outputSize: 12}, revertEcho, '3d00'],
    ['exception-keeps-output', {inputSize: 13, output: 7, outputSize: 9}, 'fe', '3d00'],
    ['empty-result-keeps-output', {input: 9, inputSize: 13, output: 7, outputSize: 9}, '00', '3d00'],
    ['huge-empty-windows', {input: maxWord, output: maxWord}, payload, '3d00'],
    ['huge-input-window', {input: maxWord, inputSize: 1}, '00', '00'],
    ['huge-output-window', {output: maxWord, outputSize: 1}, '00', '00'],
    ['huge-size', {inputSize: maxWord}, '00', '00'],
    ['parent-returns-overlap', {input: 9, inputSize: 33, output: 18, outputSize: 10}, echo, halt('f3', 14, 29)],
    ['parent-reverts-output', {input: 24, inputSize: 23, output: 51, outputSize: 9}, echo, halt('fd', 48, 16)],
  ]) add('bytes', op, name, push(0x2a) + prefill + invoke(op, windows) + ending, child)
  add('bytes', op, 'returndatacopy-outside-short-window', prefill +
    invoke(op, {inputSize: 11, output: 12, outputSize: 1}) +
    push(7) + push(2) + push(37) + '3e3d00', revertEcho,
  {expect: {stack: ['11', '0'], returnDataHex: pattern.slice(0, 22)}})
  add('bytes', op, 'empty-call-clears-previous-returndata', prefill +
    invoke(op, {output: 20, outputSize: 7}) +
    invoke(op, {target: C, requested: 0, output: 21, outputSize: 5}) + '3d00', payload,
  {expect: {stack: ['0', '1', '1'], returnDataHex: ''}})

  for (const [name, prior, childEnd, parentEnd] of [
    ['cold-slot-commit', '', '00', '00'],
    ['warm-slot-commit', '5f5450', '00', '00'],
    ['cold-slot-child-revert', '', '5f5ffd', '00'],
    ['cold-slot-child-fault', '', 'fe', '00'],
    ['root-reverts-slot-warmth', '', '00', '5f5ffd'],
  ]) {
    const readSlot = '5f5450'
    const sameSlotWarmed = prior || (op !== 'staticcall' && childEnd === '00')
    add('journal', op, name, prior + invoke(op) + slotCost + parentEnd, readSlot + childEnd, {
      expect: {stack: [sameSlotWarmed ? '106' : '2106', childEnd === '00' ? '1' : '0']},
    })
  }

  for (const [name, effect, ending] of [
    ['nested-read', returnWord('47'), halt('f3', 0, 32)],
    ['nested-store', sstore(9), returnWord('')],
    ['nested-log', childLog + '00', returnWord('')],
    ['nested-positive-call', invoke('call', {target: A, value: 1}) + '00', returnWord('')],
  ]) {
    // Root STATICCALL makes B read-only. Each variant must keep C's frame read-only.
    add('static', op, name, invoke('staticcall', {outputSize: 32, requested: 100000}) + '3d00',
      invoke(op, {target: C, value, outputSize: 32}) + ending, {
        ...environment, childBalance: 8, grandchild: effect, observeLogs: true, enteredDepths: [0, 1, 2],
        expect: {childBalance: '8', grandchildSlot0: '0', logs: [],
          returnDataHex: word(name === 'nested-read' && op !== 'staticcall' ? 8 : 0)},
      })
  }
  add('static', op, 'read-only-entry-context', invoke(op, {outputSize: contextSize, value}) + '3d00', context,
    {...environment, readOnly: true, expect: {returnDataHex: contextBytes}})

  const arity = op === 'callcode' ? 7 : 6
  for (const count of [0, arity - 1]) {
    add('arity', op, 'stack-underflow-' + count, '5f'.repeat(count) + opcodes[op] + '00', payload)
  }
  add('arity', op, 'extra-stack-item-preserved', push(maxWord) + invoke(op) + '00', payload,
    {expect: {stack: ['1', String(maxWord)]}})
  for (const depth of [1023, 1024]) {
    add('depth', op, 'boundary-' + depth, prefill + invoke(op, {value, output: 31, outputSize: 7}) + '3d00',
      payload, {...environment, depth, enteredDepths: depth === 1023 ? [1023, 1024] : [1024],
        expect: {stack: depth === 1023 ? ['3', '1'] : ['0', '0']}})
  }

  add('depth', op, 'nested-at-1022', invoke(op, {outputSize: 32}) + '3d00',
    invoke(op, {target: C, outputSize: 32}) + halt('f3', 0, 32), {
      depth: 1022, grandchild: invoke(op, {target: A}) + returnWord(''),
      enteredDepths: [1022, 1023, 1024], expect: {stack: ['32', '1'], returnDataHex: word(0)},
    })

  const emptyCall = invoke(op, {requested: 0})
  add('gas', op, 'zero-request-stop', emptyCall + '00', '00')
  add('gas', op, 'zero-request-insufficient-for-first-op', emptyCall + '00', payload)
  add('gas', op, 'zero-entry-gas', emptyCall + '00', '00', {gas: 0})
  add('gas', op, 'repeat-cold-then-warm', invoke(op, {outputSize: 32}) + invoke(op, {outputSize: 32}) + '00',
    returnWord('5a'))
  add('gas', op, 'warm-self-sufficient', selectInput(prefill +
    invoke(op, {target: A, inputSize: 1, outputSize: 3}) + '3d00', payload), '',
  {expect: {returnDataHex: 'd1e2f3'}})
  add('gas', op, 'cold-self-sufficient', selectInput(prefill +
    invoke(op, {target: A, inputSize: 1, outputSize: 3}) + '3d00', payload), '',
  {prewarmParent: false, expect: {returnDataHex: 'd1e2f3'}})
  for (const requested of [14, 15, 16]) {
    add('gas', op, 'child-exact-' + requested, invoke(op, {requested, outputSize: 32}) + '00',
      returnWord('5a'), {expect: {stack: [requested < 15 ? '0' : '1']}})
  }
}

for (const [name, balance, targetCode, childBalance, childNonce] of [
  ['funded-empty-account', 7, '', 0, 0],
  ['funded-nonce-only-target', 7, '', 0, 1],
  ['funded-balance-only-target', 7, '', 11, 0],
  ['funded-code-stipend', 7, payload, 11, 0],
  ['insufficient-code-target', 6, payload, 11, 0],
  ['no-execution-balance', 0, payload, 11, 0],
]) add('funds', 'callcode', name, prefill + invoke('callcode', {value: 7, requested: 0,
  outputSize: 7, output: 13}) + '3d00', targetCode, {parentBalance: balance, childBalance, childNonce,
  expect: {parentBalance: String(balance), childBalance: String(childBalance), stack: [
    balance >= 7 && targetCode ? '3' : '0', balance >= 7 ? '1' : '0',
  ]}})
add('funds', 'delegatecall', 'inherited-value-does-not-fund-zero-request',
  invoke('call', {value: 7, requested: 100000, outputSize: 32}) + '00',
  invoke('delegatecall', {target: C, requested: 0, outputSize: 3}) + returnWord(''), {
    parentBalance: 7, grandchild: payload, expect: {returnDataHex: word(0), parentBalance: '0', childBalance: '7'},
  })
add('funds', 'delegatecall', 'zero-execution-balance-with-funded-code-address',
  invoke('delegatecall', {outputSize: 32}) + '00', returnWord('47'),
  {childBalance: 11, expect: {childBalance: '11', returnDataHex: word(0)}})
add('static', 'callcode', 'nested-static-funded-value-stipend',
  invoke('staticcall', {outputSize: 3, requested: 80000}) + '3d00',
  invoke('callcode', {target: C, value: 5, requested: 0, outputSize: 3}) + halt('f3', 0, 3),
  {childBalance: 5, grandchild: payload, expect: {childBalance: '5', returnDataHex: 'd1e2f3'}})
add('static', 'callcode', 'nested-static-insufficient-value',
  invoke('staticcall', {outputSize: 32, requested: 80000}) + '3d00',
  invoke('callcode', {target: C, value: 5, requested: 0}) + returnWord(''),
  {childBalance: 4, grandchild: payload, expect: {childBalance: '4',
    warmGrandchildAddress: true, returnDataHex: word(0)}})

for (const op of ['callcode', 'delegatecall']) {
  for (const [name, ending, parentEnd] of [
    ['committed-emitter-and-refund', '00', '00'],
    ['reverted-emitter-and-refund', '5f5ffd', '00'],
    ['exceptional-emitter-and-refund', 'fe', '00'],
    ['root-reverts-emitter-and-refund', '00', '5f5ffd'],
    ['root-faults-after-log', '00', 'fe'],
  ]) {
    const value = op === 'callcode' ? 2 : 0
    const rootCommits = parentEnd === '00'
    const childCommits = ending === '00'
    const logs = rootCommits ? [
      observedLog(A, 0xface, 1),
      ...(childCommits ? [observedLog(A, 0x1234, 0xabc)] : []),
      observedLog(A, 0xcafe, 2),
    ] : []
    add('log-and-refund', op, name, log(0xface, 1) + invoke(op, {value}) + log(0xcafe, 2) + parentEnd,
      sstore(17) + childLog + sstore(0) + ending, {parentBalance: 5, observeLogs: true,
        expect: {logs, refund: rootCommits && childCommits ? '19900' : '0'}})
  }
  for (const [name, ending] of [
    ['commits-transfer-and-storage', '00'],
    ['reverts-transfer-and-storage', '5f5ffd'],
    ['faults-after-transfer-and-storage', 'fe'],
  ]) {
    // C's nonempty-input branch reads its balance after B commits or rolls back.
    const grant = sstore(9) + childLog + '00'
    const probe = selectInput(grant, returnWord('47'))
    add('descendant', op, name, prefill + invoke(op, {requested: 90000}) +
      invoke('staticcall', {target: C, inputSize: 1, outputSize: 32}) + '3d00',
    invoke('call', {target: C, value: 3, requested: 60000}) + ending, {
      parentBalance: 11, childBalance: 7, grandchild: probe, observeLogs: true,
      expect: {childBalance: '7', parentBalance: name.startsWith('commits') ? '8' : '11',
        returnDataHex: word(name.startsWith('commits') ? 3 : 0),
        logs: name.startsWith('commits') ? [observedLog(C, 0x1234, 0xabc)] : []},
    })
  }
  add('journal', op, 'writes-execution-storage', invoke(op) + '5f5400', sstore(7) + '00',
    {expect: {parentSlot0: '7', slot0: '0', warmAddress: true, warmSlot: false, stack: ['7', '1']}})
}
add('journal', 'staticcall', 'target-slot-read-keeps-namespaces-distinct', sstore(7) +
  invoke('staticcall', {outputSize: 32}) + '5f5400', returnWord('5f54'),
{expect: {parentSlot0: '7', slot0: '0', warmSlot: true, returnDataHex: word(0), stack: ['7', '1']}})

const exceptionNames = new Map([
  ['out of gas', 'outOfGas'], ['invalid opcode', 'invalidOpcode'],
  ['static state change', 'writeProtection'], ['stack underflow', 'stackUnderflow'],
])
function snapshot(out, field, data) {
  assert(data.length <= observationLimit, field + ' complete oracle observation')
  out[field + 'Hex'] = hex(data)
  out[field + 'Size'] = String(data.length)
  out[field + 'Truncated'] = false
}
async function ethereumJS(c) {
  const common = new Common({chain: Mainnet, hardfork: c.profile === 'osaka' ? Hardfork.Osaka : Hardfork.Shanghai})
  const evm = await createEVM({common})
  const [parent, child, third, caller] = [A, B, C, sender].map(address)
  if (c.prewarmParent) evm.journal.addAlwaysWarmAddress(parent.toString())
  for (const [who, code, balance, nonce] of [
    [parent, c.parent, c.parentBalance ?? 0, 0],
    [child, c.child, c.childBalance ?? 0, c.childNonce ?? 0],
    [third, c.grandchild, 0, 0],
  ]) {
    if (code || balance || nonce) await evm.stateManager.putAccount(who, new Account(BigInt(nonce), BigInt(balance)))
    if (code) await evm.stateManager.putCode(who, bytes(code))
  }
  let lastOpcode
  const depths = []
  evm.events.on('step', (step, resolve) => {
    if (step.depth === (c.depth ?? 0)) lastOpcode = step.opcode.code
    resolve?.()
  })
  evm.events.on('beforeMessage', (msg, resolve) => {
    depths.push(msg.depth)
    resolve?.()
  })
  const gasLimit = BigInt(c.gas)
  const {execResult: ex} = await evm.runCall({
    caller, origin: caller, to: parent, gasLimit, isStatic: c.readOnly ?? false, depth: c.depth ?? 0,
  })
  if (c.enteredDepths) assert.deepEqual(depths, c.enteredDepths, c.id + ' oracle frame depths')
  const error = ex.exceptionError?.error
  const status = error === 'revert' ? 'reverted' : error ? 'exceptional' :
    lastOpcode === 0xf3 ? 'returned' : 'stopped'
  const pa = await evm.stateManager.getAccount(parent)
  const ca = await evm.stateManager.getAccount(child)
  const key = new Uint8Array(32)
  const out = {
    schemaVersion: 2, status, gasRemaining: String(gasLimit - ex.executionGasUsed),
    entryParentWarm: c.prewarmParent,
    parentBalance: String(pa?.balance ?? 0), childBalance: String(ca?.balance ?? 0),
    childNonce: String(ca?.nonce ?? 0), refund: String(ex.gasRefund ?? 0),
    parentSlot0: decimal(await evm.stateManager.getStorage(parent, key)),
    slot0: decimal(await evm.stateManager.getStorage(child, key)),
    grandchildSlot0: decimal(await evm.stateManager.getStorage(third, key)),
    warmAddress: evm.journal.isWarmedAddress(child.bytes),
    warmSlot: evm.journal.isWarmedStorage(child.bytes, key),
    warmGrandchildAddress: evm.journal.isWarmedAddress(third.bytes),
    warmGrandchildSlot: evm.journal.isWarmedStorage(third.bytes, key),
  }
  snapshot(out, 'returnBytes', ex.returnValue)
  if (status === 'exceptional') {
    assert(exceptionNames.has(error), 'unmapped EthereumJS exception: ' + error)
    out.reason = exceptionNames.get(error)
  } else {
    const {memory, memoryWordCount, stack, returnBytes} = ex.runState
    assert(memoryWordCount <= BigInt(observationLimit / 32), 'full oracle memory observation')
    out.stack = stack.peek(stack.length).map(String)
    snapshot(out, 'parentMemory', memory.read(0, Number(32n * memoryWordCount)))
    snapshot(out, 'returnData', returnBytes)
  }
  if (c.observeLogs) {
    out.logsTruncated = false
    out.logs = (ex.logs ?? []).map(([who, topics, data]) => ({
      address: decimal(who), topics: topics.map(decimal), dataHex: hex(data),
    }))
  }
  for (const [field, value] of Object.entries(c.expect ?? {})) {
    assert.deepEqual(out[field], value, c.id + ' oracle ' + field)
  }
  return out
}

// Derive the overhead from a no-op child and zero requested gas. For valued
// CALLCODE an invalid child consumes the full stipend, exposing the gross charge.
const gasBoundaryGroups = []
for (const op of variants) {
  for (const [name, prelude, windows, value] of [
    ['cold', '', {}, 0],
    ['warm', invoke(op, {requested: 0}) + '50', {}, 0],
    ['memory', '', {input: 705, inputSize: 33, output: 901, outputSize: 32}, 0],
    ...(op === 'callcode' ? [['value', '', {input: 901, inputSize: 32, output: 705, outputSize: 33}, 5]] : []),
  ]) {
    const parent = prelude + invoke(op, {...windows, value, requested: 0}) + '00'
    const child = value ? 'fe' : '00'
    const options = {parentBalance: 5}
    const setup = await ethereumJS({...defaults, parent, child, ...options})
    const exact = defaults.gas - Number(setup.gasRemaining)
    assert.equal(setup.status, 'stopped', op + ':' + name + ' overhead probe')
    gasBoundaryGroups.push({variant: op, group: name, gas: exact})
    for (const delta of [-1, 0, 1]) {
      add('overhead', op, name + ':' + delta, parent, child, {...options, gas: exact + delta,
        expect: delta < 0 ? {status: 'exceptional', reason: 'outOfGas'} : {stack: [value ? '0' : '1']}})
    }
    for (const residual of [63, 64, 65]) {
      // PUSH32 replaces PUSH0 and costs one more gas. GAS charges its own two.
      const maximum = prelude + invoke(op, {...windows, value, requested: maxWord}) + '00'
      add('cap', op, name + ':' + residual, maximum, returnWord('5a'), {
        ...options, gas: exact + 1 + residual,
        expect: {returnDataHex: word(residual - Math.floor(residual / 64) - 2 + (value ? 2300 : 0))},
      })
    }
  }
}

const clz = returnWord('5f1e')
add('context', 'staticcall', 'osaka-propagates-to-delegated-code',
  invoke('staticcall', {outputSize: 32}) + '00',
  invoke('delegatecall', {target: C, outputSize: 32}) + halt('f3', 0, 32), {
    profile: 'osaka', grandchild: clz, expect: {returnDataHex: word(256)},
  })

function spawnLean(c, rootContext = [String(sender), String(sender)]) {
  const args = [
    ...(c.observeLogs ? ['--observe-logs'] : []),
    '--call-opcode', c.parent, c.child, String(c.gas), String(c.fuel),
    String(c.parentBalance ?? 0), String(c.childBalance ?? 0), String(c.childNonce ?? 0),
    c.readOnly ? '1' : '0', c.profile ?? 'shanghaiPlus', String(c.depth ?? 0), c.grandchild ?? '',
    c.prewarmParent ? '1' : '0', ...rootContext,
  ]
  return spawnSync(executable, args, {encoding: 'utf8', timeout: 10000, maxBuffer: 128 * 1024})
}
function runLean(c) {
  const p = spawnLean(c)
  if (p.error || p.status !== 0) throw Error(`Lean process failed (${p.status}): ${p.error ?? (p.stdout + p.stderr)}`)
  return JSON.parse(p.stdout)
}
function checkSnapshots(out) {
  for (const name of ['parentMemory', 'returnData', 'returnBytes']) {
    assert.equal(out[name + 'Truncated'], false, name + ' complete Lean observation')
    assert.match(out[name + 'Hex'], /^(?:[0-9a-f]{2})*$/, name + ' bytes')
    assert.equal(out[name + 'Size'], String(out[name + 'Hex'].length / 2), name + ' size')
  }
}

const diff = (expected, actual) => Object.keys(expected)
  .filter(field => !isDeepStrictEqual(expected[field], actual[field]))
const geth = openGeth()
const gethExcluded = {staticEntry: 0, osaka: 0, nonzeroDepth: 0, coldParent: 0, zeroGas: 0}
function exclusion(c) {
  if (c.readOnly) return 'staticEntry'
  if (c.profile === 'osaka') return 'osaka'
  if (c.depth) return 'nonzeroDepth'
  if (!c.prewarmParent) return 'coldParent'
  if (c.gas === 0) return 'zeroGas'
}
function gethReference(c) {
  const g = geth.run({code: c.parent, gas: c.gas, accounts: [
    [A, c.parent, c.parentBalance ?? 0, 0],
    [B, c.child, c.childBalance ?? 0, c.childNonce ?? 0],
    [C, c.grandchild ?? '', 0, 0],
  ]})
  const pa = g.account(A), ca = g.account(B), ga = g.account(C)
  const out = {status: g.status, gasRemaining: g.gasRemaining, returnBytesHex: g.bytesHex,
    parentBalance: pa.balance, parentSlot0: pa.slot0, childBalance: ca.balance,
    childNonce: ca.nonce, slot0: ca.slot0, grandchildSlot0: ga.slot0}
  if (g.status === 'stopped') Object.assign(out, {
    stack: g.stack, parentMemoryHex: g.memoryHex, parentMemorySize: g.memorySize,
  })
  if (g.returnDataHex !== undefined) out.returnDataHex = g.returnDataHex
  if (g.refund !== undefined) out.refund = g.refund
  return out
}
const count = () => ({compared: 0, matched: 0, mismatches: 0, errors: 0})
const counts = {ethereumJS: count(), geth: count()}
const categories = {}, variantsCompared = {}, casesCompared = []
const failures = [], observations = new Map()
function compare(c, oracle, expected, actual) {
  const scopes = [counts[oracle], categories[c.category][oracle], variantsCompared[c.variant][oracle]]
  if (!expected || !actual) {
    for (const scope of scopes) scope.errors++
    return false
  }
  const fields = diff(expected, actual)
  if (fields.length) failures.push({id: c.id, oracle, fields, expected, actual})
  for (const scope of scopes) {
    scope.compared++
    scope[fields.length ? 'mismatches' : 'matched']++
  }
  return fields.length === 0
}
async function observe(c, source, operation) {
  try {
    return await operation()
  } catch (error) {
    failures.push({id: c.id, source, error: String(error)})
    return undefined
  }
}
assert.equal(new Set(cases.map(c => c.id)).size, cases.length, 'unique fixture names')
let crossOracleMatched = 0
for (const c of cases) {
  categories[c.category] ??= {ethereumJS: count(), geth: count()}
  variantsCompared[c.variant] ??= {ethereumJS: count(), geth: count()}
  const record = {id: c.id, category: c.category, variant: c.variant}
  casesCompared.push(record)
  const expected = await observe(c, 'ethereumJS', () => ethereumJS(c))
  const actual = await observe(c, 'Lean', () => {
    const result = runLean(c)
    if (result.status !== 'indeterminate') checkSnapshots(result)
    return result
  })
  record.ethereumJS = compare(c, 'ethereumJS', expected, actual)
  if (record.ethereumJS) observations.set(c.id, {expected, actual})
  if (geth) {
    const excluded = exclusion(c)
    if (excluded) {
      gethExcluded[excluded]++
      record.gethExcluded = excluded
    } else {
      const g = await observe(c, 'geth', () => gethReference(c))
      record.geth = compare(c, 'geth', g, actual)
      if (g && expected) {
        const fields = diff(g, expected)
        if (fields.length) failures.push({id: c.id, oracle: 'geth-vs-ethereumJS', fields, geth: g, ethereumJS: expected})
        else crossOracleMatched++
      }
    }
  }
}

const boundaries = []
for (const op of variants) {
  for (const [name, parent, child, extra, reason] of [
    ['identity-precompile', prefill + invoke(op, {target: 4, inputSize: 5, outputSize: 5}) + '00', '',
      {expect: {stack: ['1'], returnDataHex: pattern.slice(0, 10)}}, 'unsupportedFork'],
    ['unchecked-keccak', invoke(op) + '00', '5f5f2000',
      {expect: {stack: ['1']}}, 'unsupportedFork'],
    ['simulation-fuel', invoke(op) + '00', payload, {fuel: 8, expect: {stack: ['1']}}, 'stepLimit'],
  ]) {
    const c = {...defaults, id: op + ':' + name, parent, child, ...extra}
    try {
      const expected = await ethereumJS(c)
      const actual = runLean(c)
      assert.deepEqual(actual, {status: 'indeterminate', reason}, c.id)
      boundaries.push({id: c.id, oracleStatus: expected.status, ...actual})
    } catch (error) {
      failures.push({id: c.id, error: String(error)})
    }
  }
}
const parserChecks = []
const rootProbe = {...defaults, parent: '333200', child: ''} // CALLER; ORIGIN; STOP
const maximumAddress = String(addressLimit - 1n)
for (const [id, rootContext, expectedStack] of [
  ['legacy-context', [], ['0', '0']],
  ['caller-only', ['194'], ['0', '194']],
  ['largest-caller', [maximumAddress, '195'], ['195', maximumAddress]],
  ['largest-origin', ['194', maximumAddress], [maximumAddress, '194']],
  ['oversized-caller', [String(addressLimit), '195'], undefined],
  ['oversized-origin', ['194', String(addressLimit)], undefined],
  ['malformed-caller', ['0xc2', '195'], undefined],
  ['negative-origin', ['194', '-1'], undefined],
]) {
  try {
    const p = spawnLean(rootProbe, rootContext)
    assert.ifError(p.error)
    const out = JSON.parse(p.stdout)
    if (expectedStack) {
      assert.equal(p.status, 0, id)
      assert.equal(out.status, 'stopped', id)
      assert.deepEqual(out.stack, expectedStack, id)
    } else {
      assert.equal(p.status, 2, id)
      assert.equal(out.status, 'inputError', id)
      const reason = id.startsWith('oversized') ? 'call-context-out-of-range' : 'bad CALL bytecode, gas or account fields'
      assert.equal(out.reason, reason, id)
    }
    parserChecks.push({id, exitCode: p.status, status: out.status})
  } catch (error) {
    failures.push({id, source: 'Lean CLI parser', error: String(error)})
  }
}
const negativeControls = {}
for (const [kind, name, field, mutate] of [
  ['gas', 'callcode:context-and-output-tail', 'gasRemaining', n => (BigInt(n) + 1n).toString()],
  ['storageOwner', 'delegatecall:writes-execution-storage', 'parentSlot0', (_, out) => out.slot0],
  ['context', 'staticcall:context-and-output-tail', 'returnDataHex', data => word(A) + data.slice(64)],
  ['returnBytes', 'delegatecall:parent-returns-overlap', 'returnBytesHex', data =>
    (Number.parseInt(data.slice(0, 2), 16) ^ 1).toString(16).padStart(2, '0') + data.slice(2)],
]) {
  const control = observations.get(name)
  negativeControls[kind] = !!control && isDeepStrictEqual(
    diff(control.expected, {...control.actual, [field]: mutate(control.actual[field], control.actual)}), [field])
}

const gethEligible = cases.filter(c => !exclusion(c)).length
console.log(JSON.stringify({
  kind: 'independent-call-family-differential',
  leanSha256: createHash('sha256').update(readFileSync(executable)).digest('hex'),
  semanticReference: 'ethereum/execution-specs@1da5a11ca8cd3a4ad00fd1821c27ef01a4b18653 (Cancun system.py)',
  ethereumJS: {version: '@ethereumjs/evm@10.1.3', lockSha256, ...counts.ethereumJS,
    fields: ['status and exception category', 'gas', 'return bytes', 'stack, memory and returndata on non-exceptional exit',
      'A/B balances and A/B/C storage', 'B/C address and slot warmth', 'refund', 'logs on selected fixtures']},
  geth: geth && {version: geth.version, sourceCommit: geth.sourceCommit, sha256: geth.sha256, fork: geth.fork,
    ...counts.geth, eligible: gethEligible, crossOracleMatched, excluded: gethExcluded,
    fields: ['status', 'gas', 'return bytes', 'stack and memory on STOP', 'returndata on non-exceptional exit',
      'A/B balances and A/B/C storage', 'refund on STOP/RETURN']},
  inventory: {execution: cases.length, boundaries: 9, categories, variants: variantsCompared, cases: casesCompared},
  probes: {executionSlotWarmth: 'measured by GAS around SLOAD', grandchildBalance: 'SELFBALANCE in a read-only call'},
  gasBoundaryGroups, boundaries, parserChecks, negativeControls, failures,
}))
if (failures.length || counts.ethereumJS.matched !== cases.length ||
    (geth && counts.geth.matched !== gethEligible) || boundaries.length !== 9 || parserChecks.length !== 8 ||
    !Object.values(negativeControls).every(Boolean)) process.exitCode = 1
