#!/usr/bin/env node
/**
 * Compare real CALL bytecode and transaction journals with EthereumJS.
 * Semantic reference: ethereum/execution-specs at
 * 1da5a11ca8cd3a4ad00fd1821c27ef01a4b18653, Cancun vm/instructions/{system,environment}.py.
 * Message fixtures start with a cold access set or explicitly seed the parent.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createEVM } from '@ethereumjs/evm'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'
import { openGeth } from './geth-byte-oracle.mjs'

const executable = process.argv[2] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-subset', import.meta.url))
const A = 0xc1, B = 0xc3, C = 0xc4, sender = 0xc2
const address = n => createAddressFromString('0x' + n.toString(16).padStart(40, '0'))
const max = (1n << 256n) - 1n
const addressHighBits = 1n << 200n
const observationLimit = 4096
const hex = bytes => Buffer.from(bytes).toString('hex')
const bytes = data => hexToBytes('0x' + data)
const decimal = data => data.length === 0 ? '0' : BigInt('0x' + hex(data)).toString()
function push(n) {
  const value = BigInt(n)
  assert(value >= 0n && value <= max)
  if (value === 0n) return '5f'
  const raw = value.toString(16)
  const word = raw.padStart(raw.length + raw.length % 2, '0')
  return (0x5f + word.length / 2).toString(16) + word
}
const store = (value, offset, op = '52') => push(value) + push(offset) + op
const exit = (op, offset, length) => push(length) + push(offset) + op
const copy = (op, dest, source, length) => push(length) + push(source) + push(dest) + op
const slot0 = value => store(value, 0, '55')
const callValueReturn = '345f5247602052' + exit('f3', 0, 64)
function call({
  target = B, value = 0, requested = 50000, input = 0, inputSize = 0, output = 0, outputSize = 0
} = {}) {
  return [outputSize, output, inputSize, input, value, target, requested].map(push).join('') + 'f1'
}
function whenData(empty, nonempty) {
  const location = 5 + empty.length / 2
  return '3661' + location.toString(16).padStart(4, '0') + '57' + empty + '5b' + nonempty
}
function payload(data, offset = 0) {
  return store(BigInt('0x' + data.padEnd(64, '0')), offset)
}
const sequence = '102132435465768798a9bacbdcedfe0f1a2b3c4d5e6f708192a3b4c5d6e7f809'
const prefill = payload(sequence)
const echo = '365f5f37365ff3'
const shiftedEcho = '366001600537366005f3'
const returned = payload('d1e2f3') + exit('f3', 0, 3)
const reverted = returned.slice(0, -2) + 'fd'
const cases = []
function add(category, id, parent, child, options = {}) {
  cases.push({category, id, parent, child, gas: 120000, fuel: 300, prewarmParent: true, ...options})
}

for (const [name, output, outputSize] of [
  ['zero', max, 0], ['short', 13, 3], ['exact', 13, 7], ['long', 13, 12],
  ['overlap-left', 1, 7], ['overlap-right', 5, 7], ['word-edge', 31, 9]
]) {
  for (const [mode, op] of [['return', 'f3'], ['revert', 'fd']]) {
    add('windows', name + ':' + mode,
      prefill + call({input: 3, inputSize: 7, output, outputSize}) + '3d00',
      shiftedEcho.slice(0, -2) + op, {
        expect: {status: 'stopped', stack: ['7', mode === 'return' ? '1' : '0'],
          returnDataHex: '5465768798a900', parentMemorySize: name === 'word-edge' ? '64' : '32'}
      })
  }
}
add('windows', 'long-output-preserves-tail',
  prefill + call({output: 4, outputSize: 9}) + '00', returned, {
    expect: {parentMemoryHex: sequence.slice(0, 8) + 'd1e2f3' + sequence.slice(14)}
  })
add('windows', 'input-expanded-with-zeros',
  prefill + call({input: 29, inputSize: 11, output: 37, outputSize: 11}) + '00', echo, {
    expect: {returnDataHex: sequence.slice(58) + '00'.repeat(8), parentMemorySize: '64'}
  })
add('windows', 'word-masked-target',
  call({target: addressHighBits + BigInt(B), output: 3, outputSize: 3}) + '00', returned,
  {expect: {returnDataHex: 'd1e2f3'}})
add('windows', 'zero-windows-max-offset', call({input: max, output: max}) + '3d5900', echo,
  {expect: {stack: ['0', '0', '1'], parentMemorySize: '0', returnDataHex: ''}})
for (const [id, options] of [
  ['full-width-input-offset', {input: max, inputSize: 2}],
  ['full-width-input-size', {input: 1, inputSize: max}],
  ['full-width-output-offset', {output: max, outputSize: 2}],
  ['full-width-output-size', {output: 1, outputSize: max}],
]) add('windows', id, call(options) + '00', echo,
  {expect: {status: 'exceptional', reason: 'outOfGas'}, enteredDepths: [0]})

const retain = call({output: 15, outputSize: 1})
add('returndata', 'copy-full-independent-of-output-window',
  retain + copy('3e', 31, 0, 3) + '3d' + exit('f3', 31, 3), returned,
  {expect: {returnDataHex: 'd1e2f3', returnBytesHex: 'd1e2f3', status: 'returned'}})
add('returndata', 'copy-part-and-revert',
  retain + copy('3e', 5, 1, 2) + exit('fd', 5, 2), reverted,
  {expect: {returnDataHex: 'd1e2f3', returnBytesHex: 'e2f3', status: 'reverted'}})
add('returndata', 'zero-copy-at-end-max-dest',
  retain + copy('3e', max, 3, 0) + '3d5900', reverted,
  {expect: {stack: ['32', '3', '0'], parentMemorySize: '32'}})
for (const [name, src, len] of [
  ['zero-past-end', 4, 0], ['cross-end', 2, 2], ['max-offset-zero', max, 0],
  ['addition-no-wrap', max, 1], ['length-no-wrap', 1, max],
]) add('returndata', name, retain + copy('3e', 0, src, len) + '00', returned, {
  expect: {status: 'exceptional', reason: name === 'length-no-wrap' ? 'outOfGas' : 'returnDataOutOfBounds'}
})
add('returndata', 'reset-on-empty-code',
  prefill + retain + call({target: C, output: 71, outputSize: 5}) + '3d00', returned,
  {expect: {stack: ['0', '1', '1'], parentMemorySize: '96', returnDataHex: '', warmGrandchildAddress: true}})
add('returndata', 'reset-on-empty-stop',
  retain + call({target: C, output: 51, outputSize: 6}) + '3d00', returned,
  {grandchild: '00', expect: {stack: ['0', '1', '1'], returnDataHex: '', parentMemorySize: '64'}})
add('returndata', 'reset-on-exception',
  prefill + retain + call({input: 1, inputSize: 1, output: 41, outputSize: 5}) + '3d00',
  whenData(returned, 'fe'),
  {expect: {stack: ['0', '0', '1'], returnDataHex: '', parentMemorySize: '64'}})
add('returndata', 'reset-on-insufficient-funds',
  retain + call({value: 9, input: 71, inputSize: 5, output: 9, outputSize: 5}) + '3d00', returned, {
    parentBalance: 8, enteredDepths: [0, 1],
    expect: {stack: ['0', '0', '1'], returnDataHex: '', parentMemorySize: '96',
      parentBalance: '8', childBalance: '0'}
  })
add('returndata', 'child-has-empty-buffer',
  retain + call({target: C, output: 5, outputSize: 32}) + '3d00', returned,
  {grandchild: '3d5f52' + exit('f3', 0, 32), expect: {returnDataHex: '00'.repeat(32)}})

const relayChild = '365f5f37' + call({target: C, value: 2, input: 0, inputSize: 7, output: 13, outputSize: 0}) +
  '3d805f60113e6011f3'
const relayParent = prefill + call({value: 5, input: 1, inputSize: 7, output: 31, outputSize: 9}) +
  '3d805f60413e6041f3'
add('nested', 'three-accounts-relay-bytes-and-value', relayParent, relayChild, {
  grandchild: '5f355f55' + callValueReturn, parentBalance: 9, enteredDepths: [0, 1, 2],
  expect: {status: 'returned', returnBytesHex: ('00'.repeat(31) + '02').repeat(2),
    returnDataSize: '64', parentBalance: '4', childBalance: '3',
    grandchildSlot0: BigInt('0x' + sequence.slice(2, 16).padEnd(64, '0')).toString()}
})
const callback = slot0(0) + returned
const callbacks = prefill + slot0(9) + call({value: 7, inputSize: 1, output: 3, outputSize: 3})
const callbackChild = prefill + slot0(4) + call({target: A, value: 3, inputSize: 1, output: 5, outputSize: 3})
for (const [name, ending] of [['stop', '00'], ['revert', exit('fd', 3, 3)], ['exception', 'fe']]) {
  add('nested', 'A-B-A-ancestor-' + name, whenData(callbacks + ending, callback), callbackChild + exit('f3', 5, 3), {
    parentBalance: 20, enteredDepths: [0, 1, 2],
    expect: name === 'stop' ? {parentSlot0: '0', slot0: '4', refund: '19900', parentBalance: '16',
      childBalance: '4', returnDataHex: 'd1e2f3'} :
      {parentSlot0: '0', slot0: '0', refund: '0', parentBalance: '20', childBalance: '0', warmAddress: false}
  })
}
for (const [name, ending] of [['revert', exit('fd', 5, 3)], ['exception', 'fe']]) {
  add('nested', 'A-B-A-middle-' + name, whenData(callbacks + '5f543d00', callback),
    callbackChild + ending, {
      parentBalance: 20, enteredDepths: [0, 1, 2],
      expect: {stack: [name === 'revert' ? '3' : '0', '9', '0'], parentSlot0: '9', slot0: '0',
        refund: '0', parentBalance: '20', childBalance: '0', warmAddress: true, warmSlot: false}
    })
}
add('nested', 'self-call-resumes-latest-slot-and-balance',
  whenData(prefill + slot0(9) + call({target: A, value: 3, inputSize: 1, output: 12, outputSize: 3}) +
    '475f543d00', slot0(1) + returned), '', {
    parentBalance: 7, enteredDepths: [0, 1],
    expect: {stack: ['3', '1', '7', '1'], parentSlot0: '1', parentBalance: '7', refund: '0'}
  })
for (const prewarmParent of [false, true]) {
  add('journal', prewarmParent ? 'seeded-warm-self-call' : 'raw-cold-self-call',
    whenData(prefill + call({target: A, inputSize: 1, output: 12, outputSize: 3}) + '00', returned),
    '', {prewarmParent, enteredDepths: [0, 1], expect: {stack: ['1'], returnDataHex: 'd1e2f3'}})
}

for (const [name, childEnd] of [['commits', '00'], ['reverts', '5f5ffd'], ['exception', 'fe']]) {
  add('journal', 'nested-address-and-slot-warmth:' + name,
    call() + call({target: C, output: 16, outputSize: 3}) + '3d00',
    call({target: C}) + childEnd, {
      grandchild: '5f5450' + returned, enteredDepths: [0, 1, 2, 1],
      expect: {stack: ['3', '1', name === 'commits' ? '1' : '0'], warmGrandchildAddress: true,
        warmGrandchildSlot: true}
    })
}
add('journal', 'failed-grandchild-keeps-address-warm-and-slot-cold',
  call() + '00', call({target: C}) + '00', {
    grandchild: slot0(4) + reverted, enteredDepths: [0, 1, 2],
    expect: {warmGrandchildAddress: true, warmGrandchildSlot: false, grandchildSlot0: '0'}
  })
add('journal', 'refund-restoration-does-not-erase-previous-refund',
  slot0(9) + slot0(0) + call() + '00', slot0(7) + slot0(0) + reverted, {
    expect: {refund: '19900', parentSlot0: '0', slot0: '0', stack: ['0'], warmSlot: false}
  })

for (const depth of [1023, 1024]) {
  add('depth', 'call-depth-' + depth, prefill +
    call({value: 2, input: 31, inputSize: 7, output: 68, outputSize: 3}) + '3d00',
    slot0(7) + returned, {
      depth, parentBalance: 3, enteredDepths: depth === 1023 ? [1023, 1024] : [1024],
      expect: {parentMemorySize: '96', stack: depth === 1023 ? ['3', '1'] : ['0', '0'],
        slot0: depth === 1023 ? '7' : '0', parentBalance: depth === 1023 ? '1' : '3',
        childBalance: depth === 1023 ? '2' : '0', warmAddress: true, warmSlot: depth === 1023}
    })
}
add('depth', '1022-enters-1024-but-refuses-next-call',
  call({output: 3, outputSize: 32}) + '00',
  call({target: C, output: 3, outputSize: 32}) + '5f52' + exit('f3', 0, 32), {
    grandchild: call({target: A}) + '5f52' + exit('f3', 0, 32), depth: 1022,
    enteredDepths: [1022, 1023, 1024], expect: {stack: ['1'], returnDataHex: '00'.repeat(31) + '01'}
})
const fullDepthGas = 2 ** 50
const fullDepthFuel = 9225
const fullDepthCode = call({target: A, requested: max}) + '00'
add('depth', 'full-self-call-continuation-stack', fullDepthCode, '', {
  gas: fullDepthGas, fuel: fullDepthFuel, enteredDepths: Array.from({length: 1025}, (_, i) => i),
  // Each of 1,025 frames spends 16 on arguments and 100 on the warm call.
  expect: {stack: ['1'], gasRemaining: String(fullDepthGas - 1025 * 116)}
})

add('context', 'static-successful-nested-bytes', prefill + call({inputSize: 5, outputSize: 5}) + '3d00',
  '365f5f37' + call({target: C, inputSize: 5, outputSize: 5}) + exit('f3', 0, 5), {
    readOnly: true, grandchild: echo, enteredDepths: [0, 1, 2],
    expect: {returnDataHex: sequence.slice(0, 10), stack: ['5', '1']}
  })
add('context', 'static-inherited-to-grandchild-write', call() + '3d00',
  call({target: C, outputSize: 32}) + '5f52' + exit('f3', 0, 32), {
    readOnly: true, grandchild: slot0(5) + returned, enteredDepths: [0, 1, 2],
    expect: {returnDataHex: '00'.repeat(32), stack: ['32', '1'], grandchildSlot0: '0'}
  })
add('context', 'static-child-cannot-forward-value', call() + '3d00',
  call({target: C, value: 1}) + '00', {
    readOnly: true, childBalance: 2, grandchild: echo, enteredDepths: [0, 1],
    expect: {stack: ['0', '0'], childBalance: '2', warmGrandchildAddress: false}
  })
add('context', 'static-parent-cannot-forward-value', call({value: 1}) + '00', returned, {
  readOnly: true, parentBalance: 2, enteredDepths: [0],
  expect: {status: 'exceptional', reason: 'writeProtection'}
})
add('context', 'static-parent-cannot-afford-call', call({value: 1}) + '00', returned, {
  gas: 20, readOnly: true, parentBalance: 2, enteredDepths: [0], oracleError: 'static state change',
  expect: {status: 'exceptional', reason: 'outOfGas'}
})
const clz = '5f1e5f52' + exit('f3', 0, 32)
const osakaParent = call({output: 9, outputSize: 32}) + '00'
const osakaChild = call({target: C, output: 9, outputSize: 32}) + exit('f3', 9, 32)
add('context', 'osaka-profile-inherited-to-grandchild', osakaParent, osakaChild, {
  grandchild: clz, profile: 'osaka', enteredDepths: [0, 1, 2],
  expect: {stack: ['1'], returnDataHex: '00'.repeat(30) + '0100'}
})

const seed = 20261122
let rng = seed
function next() {
  rng ^= rng << 13
  rng ^= rng >>> 17
  rng ^= rng << 5
  return rng >>> 0
}
for (let i = 0; i < 48; i++) {
  const data = hex(Uint8Array.from({length: 32}, () => next() % 256))
  const input = next() % 40
  const inputSize = next() % 44
  const output = next() % 80
  const outputSize = next() % 56
  const requested = [0, 9, 18, 39, 400, 50000][next() % 6]
  add('seeded', 'seeded-' + i, payload(data) +
    call({input, inputSize, output, outputSize, requested}) + '3d00',
    i % 2 === 0 ? echo : shiftedEcho.slice(0, -2) + 'fd')
}

const errorNames = new Map([
  ['out of gas', 'outOfGas'], ['invalid opcode', 'invalidOpcode'], ['static state change', 'writeProtection']
])
const oracleExceptions = {}
function snapshot(out, field, data, id) {
  assert(data.length <= observationLimit, id + ' oracle observation bound')
  out[field + 'Hex'] = hex(data)
  out[field + 'Size'] = String(data.length)
  out[field + 'Truncated'] = false
}
async function reference(c) {
  const common = new Common({chain: Mainnet, hardfork: c.profile === 'osaka' ? Hardfork.Osaka : Hardfork.Shanghai})
  const evm = await createEVM({common})
  // EIP-2929: active precompiles start warm even in a raw message fixture.
  // runCall does not perform this transaction-level initialisation.
  for (const target of evm.precompiles.keys()) evm.journal.addAlwaysWarmAddress(target)
  const [parent, child, third, caller] = [A, B, C, sender].map(address)
  if (c.prewarmParent) evm.journal.addAlwaysWarmAddress(parent.toString())
  const key = new Uint8Array(32)
  for (const [who, code, balance, nonce] of [
    [parent, c.parent, c.parentBalance, 0],
    [child, c.child, c.childBalance, c.childNonce],
    [third, c.grandchild, 0, 0],
  ]) {
    if (code || balance || nonce) await evm.stateManager.putAccount(who, new Account(BigInt(nonce ?? 0), BigInt(balance ?? 0)))
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
    caller, to: parent, gasLimit, isStatic: c.readOnly ?? false, depth: c.depth ?? 0
  })
  if (c.enteredDepths) assert.deepEqual(depths, c.enteredDepths, c.id + ' reference frames')
  const jsError = ex.exceptionError?.error
  const status = jsError === 'revert' ? 'reverted' : jsError ? 'exceptional' :
    lastOpcode === 0xf3 ? 'returned' : 'stopped'
  const pa = await evm.stateManager.getAccount(parent)
  const ca = await evm.stateManager.getAccount(child)
  const expected = {
    schemaVersion: 2, status, gasRemaining: String(gasLimit - ex.executionGasUsed),
    entryParentWarm: c.prewarmParent ?? false,
    parentBalance: String(pa?.balance ?? 0), childBalance: String(ca?.balance ?? 0),
    childNonce: String(ca?.nonce ?? 0), refund: String(ex.gasRefund ?? 0),
    parentSlot0: decimal(await evm.stateManager.getStorage(parent, key)),
    slot0: decimal(await evm.stateManager.getStorage(child, key)),
    grandchildSlot0: decimal(await evm.stateManager.getStorage(third, key)),
    warmAddress: evm.journal.isWarmedAddress(child.bytes),
    warmSlot: evm.journal.isWarmedStorage(child.bytes, key),
    warmGrandchildAddress: evm.journal.isWarmedAddress(third.bytes),
    warmGrandchildSlot: evm.journal.isWarmedStorage(third.bytes, key)
  }
  snapshot(expected, 'returnBytes', ex.returnValue, c.id)
  if (status === 'exceptional') {
    assert(errorNames.has(jsError), c.id + ' oracle exception ' + jsError)
    expected.reason = c.expect?.reason === 'returnDataOutOfBounds'
      ? 'returnDataOutOfBounds' : errorNames.get(jsError)
    if (expected.reason === 'returnDataOutOfBounds') assert.equal(jsError, 'out of gas', c.id)
    if (c.oracleError) {
      assert.equal(jsError, c.oracleError, c.id)
      expected.reason = c.expect.reason
    }
    oracleExceptions[jsError] ??= {}
    oracleExceptions[jsError][expected.reason] = (oracleExceptions[jsError][expected.reason] ?? 0) + 1
  } else {
    const { memory, memoryWordCount, stack, returnBytes } = ex.runState
    const size = Number(32n * memoryWordCount)
    assert(Number.isSafeInteger(size) && size <= observationLimit, c.id + ' oracle memory bound')
    expected.stack = stack.peek(stack.length).map(String)
    snapshot(expected, 'parentMemory', memory.read(0, size), c.id)
    snapshot(expected, 'returnData', returnBytes, c.id)
  }
  for (const [key, value] of Object.entries(c.expect ?? {})) {
    assert.deepEqual(expected[key], value, c.id + ' reference ' + key)
  }
  return expected
}

function lean(c) {
  const args = [
    '--call-opcode', c.parent, c.child, String(c.gas), String(c.fuel),
    String(c.parentBalance ?? 0), String(c.childBalance ?? 0), String(c.childNonce ?? 0),
    c.readOnly ? '1' : '0', c.profile ?? 'shanghaiPlus', String(c.depth ?? 0), c.grandchild ?? '',
  ]
  if (c.prewarmParent) args.push('1')
  const p = spawnSync(executable, args, {encoding: 'utf8', timeout: 10000, maxBuffer: 128 * 1024})
  if (p.error || p.status !== 0) throw Error('Lean CALL process failed: ' + String(p.error ?? (p.stdout + p.stderr)))
  return JSON.parse(p.stdout)
}
function requireFullSnapshots(out, id) {
  for (const field of ['parentMemory', 'returnData', 'returnBytes']) {
    assert.equal(out[field + 'Truncated'], false, id + ' ' + field + ' observation')
    assert.match(out[field + 'Hex'], /^(?:[0-9a-f]{2})*$/, id + ' ' + field + ' bytes')
    assert.equal(out[field + 'Size'], String(out[field + 'Hex'].length / 2), id + ' ' + field + ' size')
  }
}

// Use the oracle's actual gas consumption of a zero-request, no-op CALL to
// find the boundary after charging both ranges, including quadratic expansion.
const windows = [
  {input: 705, inputSize: 33, output: 901, outputSize: 32},
  {input: 901, inputSize: 32, output: 705, outputSize: 33},
]
for (const [i, ranges] of windows.entries()) {
  const setup = call({...ranges, requested: 0}) + '00'
  const observed = await reference({id: 'memory-boundary-setup', parent: setup, child: '00', gas: 50000})
  const exact = 50000 - Number(observed.gasRemaining)
  for (const delta of [-1, 0, 1]) {
    add('gas', 'memory-boundary-' + i + ':' + delta, setup, '00', {
      gas: exact + delta, expect: delta < 0 ? {status: 'exceptional', reason: 'outOfGas'} : {stack: ['1']}
    })
  }
  for (const residual of [63, 64, 65]) {
    // PUSH32 costs one gas more than the PUSH0 in the no-op control.
    add('gas', 'gas-cap-' + i + ':' + residual, call({...ranges, requested: max}) + '00',
      '5a5f52' + exit('f3', 0, 32), {gas: exact + 1 + residual,
        expect: {stack: ['1'], returnDataHex: (BigInt(residual - Math.floor(residual / 64) - 2)).toString(16).padStart(64, '0')}})
  }
}
for (const requested of [14, 15, 16]) {
  add('gas', 'child-exact-gas:' + requested, call({input: 3, inputSize: 33, output: 31, outputSize: 32, requested}) + '00',
    '5a5f52' + exit('f3', 0, 32),
    {expect: {stack: [requested < 15 ? '0' : '1'], returnDataSize: requested < 15 ? '0' : '32'}})
}

const diff = (expected, actual) => Object.keys(expected)
  .filter(key => JSON.stringify(expected[key]) !== JSON.stringify(actual[key]))
const observations = new Map()
const failures = []
const categories = {}
const geth = openGeth()
const gethFailures = []
const gethExcluded = {staticEntry: 0, osaka: 0, nonzeroDepth: 0, coldParent: 0, zeroGas: 0}
let gethCompared = 0
function compareGeth(c, actual) {
  if (c.readOnly) { gethExcluded.staticEntry++; return }
  if (c.profile === 'osaka') { gethExcluded.osaka++; return }
  if (c.depth) { gethExcluded.nonzeroDepth++; return }
  if (!c.prewarmParent) { gethExcluded.coldParent++; return }
  if (c.gas === 0) { gethExcluded.zeroGas++; return }
  gethCompared++
  try {
    const g = geth.run({code: c.parent, gas: c.gas, accounts: [
      [A, c.parent, c.parentBalance ?? 0, 0],
      [B, c.child, c.childBalance ?? 0, c.childNonce ?? 0],
      [C, c.grandchild ?? '', 0, 0],
    ]})
    const pa = g.account(A), ca = g.account(B), grandchild = g.account(C)
    const expected = {status: g.status, gasRemaining: g.gasRemaining, returnBytesHex: g.bytesHex,
      parentBalance: pa.balance, parentSlot0: pa.slot0, childBalance: ca.balance, childNonce: ca.nonce,
      slot0: ca.slot0, grandchildSlot0: grandchild.slot0}
    if (g.status === 'stopped') Object.assign(expected, {
      stack: g.stack, parentMemoryHex: g.memoryHex, parentMemorySize: g.memorySize
    })
    if (g.returnDataHex !== undefined) expected.returnDataHex = g.returnDataHex
    if (g.refund !== undefined) expected.refund = g.refund
    const fields = diff(expected, actual)
    if (fields.length) gethFailures.push({id: c.id, fields, expected, actual})
  } catch (error) {
    gethFailures.push({id: c.id, error: String(error)})
  }
}
for (const c of cases) {
  categories[c.category] ??= {compared: 0, matched: 0}
  categories[c.category].compared++
  try {
    assert(!observations.has(c.id), c.id)
    const expected = await reference(c)
    const actual = lean(c)
    requireFullSnapshots(actual, c.id)
    const fields = diff(expected, actual)
    observations.set(c.id, {expected, actual})
    if (fields.length) failures.push({id: c.id, fields, expected, actual})
    else categories[c.category].matched++
    if (geth) compareGeth(c, actual)
  } catch (error) {
    failures.push({id: c.id, error: String(error)})
  }
}

const refusalChecks = []
const executedPrecompileChecks = []
for (const c of [
  {id: 'identity-precompile', parent: prefill + call({target: 4, inputSize: 5, outputSize: 5}) + '3d00',
    child: '', expect: {status: 'stopped', stack: ['5', '1'], returnDataHex: sequence.slice(0, 10)}},
  {id: 'nested-precompile', parent: call() + '00', child: call({target: 4}) + '00',
    expect: {status: 'stopped', stack: ['1']}, enteredDepths: [0, 1, 2]},
  {id: 'osaka-opcode-under-shanghai', parent: osakaParent, child: osakaChild, grandchild: clz,
    expect: {status: 'stopped', stack: ['1'], returnDataHex: '00'.repeat(32)}},
]) {
  const {id} = c
  const input = {gas: 120000, fuel: 300, prewarmParent: true, ...c}
  try {
    const expected = await reference(input)
    const actual = lean(input)
    if (id === 'osaka-opcode-under-shanghai') {
      assert.deepEqual(actual, {status: 'indeterminate', reason: 'unsupportedFork'}, id)
      refusalChecks.push({id, expectedStatus: expected.status, ...actual})
    } else {
      requireFullSnapshots(actual, id)
      const fields = diff(expected, actual)
      if (fields.length) failures.push({id, fields, expected, actual})
      executedPrecompileChecks.push({id, expectedStatus: expected.status,
        status: actual.status, matched: fields.length === 0})
    }
  } catch (error) {
    failures.push({id, error: String(error)})
  }
}
let globalFuelBoundary = false
try {
  const input = {id: 'full-depth-one-step-short', parent: fullDepthCode, child: '',
    gas: fullDepthGas, fuel: fullDepthFuel - 1, prewarmParent: true}
  assert.deepEqual(lean(input), {status: 'indeterminate', reason: 'stepLimit'})
  globalFuelBoundary = true
} catch (error) {
  failures.push({id: 'full-depth-one-step-short', error: String(error)})
}
const control = observations.get('copy-full-independent-of-output-window')
const revertControl = observations.get('copy-part-and-revert')
const negativeControls = {
  byte: control !== undefined && diff(control.expected, {...control.actual,
    returnBytesHex: '00' + control.actual.returnBytesHex.slice(2)}).includes('returnBytesHex'),
  gas: control !== undefined && diff(control.expected, {...control.actual,
    gasRemaining: (BigInt(control.expected.gasRemaining) + 1n).toString()}).includes('gasRemaining'),
  status: control !== undefined && revertControl !== undefined &&
    diff(control.expected, revertControl.actual).includes('status')
}
const matched = Object.values(categories).reduce((sum, c) => sum + c.matched, 0)
console.log(JSON.stringify({
  kind: 'independent-call-bytes-and-nested-journal-differential',
  oracle: '@ethereumjs/evm@10.1.3 Shanghai runCall and one Osaka CLZ fixture',
  seed, compared: cases.length, matched, mismatches: cases.length - matched,
  categories, refusalChecks, executedPrecompileChecks, globalFuelBoundary, negativeControls, oracleExceptions,
  initialState: 'Fixtures seed the executing parent address except the named raw-cold self-call control.',
  observedFields: ['status', 'gasRemaining', 'frame output and size', 'account balances/nonce/storage',
    'journal warmth and refund', 'stack, memory and child returndata on STOP/RETURN/REVERT'],
  geth: geth && {version: geth.version, sourceCommit: geth.sourceCommit, sha256: geth.sha256, fork: geth.fork,
    compared: gethCompared, matched: gethCompared - gethFailures.length, mismatches: gethFailures.length,
    excluded: gethExcluded, initialWarmth: 'Geth seeds parent and sender. Only explicitly seeded fixtures call the parent.',
    observedFields: ['status', 'gasRemaining', 'frame output', 'account balances/nonce/storage',
      'child returndata on STOP/RETURN/REVERT', 'stack and memory on STOP', 'refund on STOP/RETURN'],
    firstFailures: gethFailures.slice(0, 8)},
  firstFailures: failures.slice(0, 10)
}))
if (failures.length || gethFailures.length || refusalChecks.length !== 1 ||
    executedPrecompileChecks.length !== 2 ||
    !executedPrecompileChecks.every(c => c.matched) ||
    !Object.values(negativeControls).every(Boolean)) process.exitCode = 1
