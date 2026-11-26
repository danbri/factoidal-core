#!/usr/bin/env node
/**
 * Compare bounded frame snapshots with EthereumJS Shanghai. Pinned EELS
 * (1da5a11ca8cd3a4ad00fd1821c27ef01a4b18653) specifies the copy operations.
 * call-data.mjs exercises nonempty RETURNDATACOPY through real CALL bytecode.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createEVM } from '@ethereumjs/evm'
import { hexToBytes } from '@ethereumjs/util'
import { openGeth } from './geth-byte-oracle.mjs'

const executable = process.argv[2] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-subset', import.meta.url))
const evm = await createEVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Shanghai }) })
const max = (1n << 256n) - 1n
const observationLimit = 4096
const hex = bytes => Buffer.from(bytes).toString('hex')
const bytes = data => hexToBytes('0x' + data)
const push = n => '7f' + n.toString(16).padStart(64, '0')
const copy = (op, dest, source, length) => push(length) + push(source) + push(dest) + op
const returnAt = (offset, length, op = 'f3') => push(length) + push(offset) + op
const sequence = length => hex(Uint8Array.from({ length }, (_, i) => (37 * i + 19) % 256))
const cases = []
const boundaries = []
const add = (category, id, code, { data = '', gas = 2500, error, expect } = {}) =>
  cases.push({ category, id, code, data, gas, error, expect })
const boundary = (category, id, code, data = '') => boundaries.push({category, id, code, data})

const sentinels = '7f' + 'a5'.repeat(32) + '5f52'
for (const [op, kind] of [['37', 'calldata'], ['39', 'code']]) {
  for (const [name, dest, source, length] of [
    ['one', 0, 0, 1], ['unaligned', 3, 2, 14], ['cross-word', 31, 1, 33],
    ['at-word', 32, 0, 32], ['late-word', 33, 32, 31],
    ['length-at-end', 5, 68, 5], ['far-source', 5, 120, 7],
    ['max-source', 4, max, 3], ['max-plus-copy', 4, max - 1n, 5],
    ['over-53-bit-source', 4, (1n << 53n) + 1n, 5],
    ['max-zero', max, max, 0], ['zero-does-not-expand', 2049, 0, 0],
    ['quadratic-memory', 705, 0, 33]
  ]) {
    add(kind, kind + '-' + name, sentinels + copy(op, dest, source, length) + '5900',
      { data: sequence(68) })
  }
  add(kind, kind + '-empty-data', sentinels + copy(op, 0, 0, 4) + '5900')
  add(kind, kind + '-overlapping-writes', sentinels +
    copy(op, 7, 2, 21) + copy(op, 15, 5, 33) + '5900', { data: sequence(68) })
  for (const [name, dest, source, length] of [
    ['max-dest', max, 0, 1], ['max-length', 1, 0, max], ['all-big', max, max, max]
  ]) add(kind, kind + '-' + name, copy(op, dest, source, length) + '00', {error: 'outOfGas'})
  add(kind, kind + '-underflow', '5f5f' + op, {error: 'stackUnderflow'})
  boundary(kind, kind + '-new-word-gas', copy(op, 31, 1, 33) + '00', sequence(68))
  boundary(kind, kind + '-existing-memory-gas', sentinels + copy(op, 1, 1, 31) + '00', sequence(68))
  boundary(kind, kind + '-quadratic-gas', copy(op, 705, 1, 33) + '00', sequence(68))
}
add('code', 'code-copy-tail', copy('39', 3, 102, 8) + '00aabbccddee',
  {expect: {memoryHex: '000000bbccddee' + '00'.repeat(25)}})
add('code', 'codesize-counts-bytes-after-stop', '3800aabbcc', {expect: {stack: ['5']}})
add('code', 'codesize-exact-gas', '3800', {gas: 2, expect: {stack: ['2']}})
add('code', 'codesize-out-of-gas', '3800', {gas: 1, error: 'outOfGas'})
add('calldata', 'observed-return', '366000600337' + returnAt(3, 11), { data: sequence(11) })
add('calldata', 'observed-revert', '366000600337' + returnAt(3, 11, 'fd'), { data: sequence(11) })
add('returndata', 'returndatasize-empty', '3d00', {gas: 2, expect: {stack: ['0']}})
add('returndata', 'returndatasize-out-of-gas', '3d00', {gas: 1, error: 'outOfGas'})
add('returndata', 'returndatasize-stack-overflow', '5f'.repeat(1024) + '3d', {error: 'stackOverflow'})
add('returndata', 'returndatacopy-underflow', '5f5f3e', {error: 'stackUnderflow'})
add('returndata', 'empty-copy-max-dest-valid', copy('3e', max, 0, 0) + '5900',
  {expect: {stack: ['0'], memorySizeBytes: '0'}})
add('returndata', 'empty-copy-source-past-end', copy('3e', max, 1, 0), {error: 'returnDataOutOfBounds'})
add('returndata', 'empty-copy-max-source', copy('3e', 0, max, 0), {error: 'returnDataOutOfBounds'})
add('returndata', 'empty-copy-no-wrap', copy('3e', 0, max, 1), {error: 'returnDataOutOfBounds'})
add('returndata', 'empty-copy-positive-length', copy('3e', 0, 0, 1), {error: 'returnDataOutOfBounds'})
// EELS charges gas before its distinct bounds error. EthereumJS exposes both as OOG.
const unaffordableOob = copy('3e', 1, 1, 1)
add('returndata', 'empty-copy-oob-but-unaffordable', unaffordableOob, {gas: 17, error: 'outOfGas'})
add('returndata', 'empty-copy-oob-and-affordable', unaffordableOob, {gas: 18, error: 'returnDataOutOfBounds'})
boundary('returndata', 'empty-copy-exact-gas', copy('3e', max, 0, 0) + '00')

const seed = 20261122
let rng = seed
function next() {
  rng ^= rng << 13
  rng ^= rng >>> 17
  rng ^= rng << 5
  return rng >>> 0
}
for (let i = 0; i < 48; i++) {
  const op = i % 2 === 0 ? '37' : '39'
  const data = hex(Uint8Array.from({length: next() % 97}, () => next() % 256))
  add('seeded', 'seeded-' + i, sentinels +
    copy(op, next() % 131, next() % 129, next() % 83) + '5900', {data})
}

let lastOpcode
evm.events.on('step', ({ opcode }, resolve) => {
  lastOpcode = opcode.code
  resolve?.()
})
async function runReference({code, data, gas}) {
  lastOpcode = undefined
  return evm.runCode({ code: bytes(code), data: bytes(data), gasLimit: BigInt(gas) })
}
for (const { category, id, code, data } of boundaries) {
  const high = await runReference({code, data, gas: 2500})
  assert.equal(high.exceptionError, undefined, id)
  const exact = Number(high.executionGasUsed)
  for (const delta of [-1, 0, 1]) {
    add(category, id + ':' + delta, code, {data, gas: exact + delta,
      error: delta < 0 ? 'outOfGas' : undefined})
  }
}

const errorNames = new Map([
  ['out of gas', 'outOfGas'], ['stack underflow', 'stackUnderflow'], ['stack overflow', 'stackOverflow']
])
const oracleExceptions = {}
async function expectedFrame(c) {
  const result = await runReference(c)
  const jsError = result.exceptionError?.error
  const status = jsError === 'revert' ? 'reverted' : jsError ? 'exceptional' :
    lastOpcode === 0xf3 ? 'returned' : 'stopped'
  assert(result.returnValue.length <= observationLimit, c.id)
  const expected = {
    status,
    gasRemaining: (BigInt(c.gas) - result.executionGasUsed).toString(),
    returnDataHex: hex(result.returnValue),
    returnDataLength: String(result.returnValue.length),
    returnDataTruncated: false
  }
  if (status === 'exceptional') {
    assert.equal(errorNames.get(jsError), c.error === 'returnDataOutOfBounds' ? 'outOfGas' : c.error, c.id)
    expected.error = c.error
    oracleExceptions[jsError] ??= {}
    oracleExceptions[jsError][c.error] = (oracleExceptions[jsError][c.error] ?? 0) + 1
  } else {
    assert.equal(c.error, undefined, c.id)
    const { memory, memoryWordCount, stack } = result.runState
    const size = Number(32n * memoryWordCount)
    assert(Number.isSafeInteger(size) && size <= observationLimit, c.id)
    const contents = memory.read(0, size)
    const word0 = hex(contents.subarray(0, 32))
    Object.assign(expected, {
      stack: stack.peek(stack.length).map(String),
      memorySizeBytes: String(size),
      memoryObservedBytes: String(size),
      memoryTruncated: false,
      memoryWord0: word0 ? BigInt('0x' + word0).toString() : '0',
      memoryHex: hex(contents)
    })
  }
  for (const [key, value] of Object.entries(c.expect ?? {})) {
    assert.deepEqual(expected[key], value, c.id + ' reference ' + key)
  }
  return expected
}

function leanFrame(c) {
  const child = spawnSync(executable, ['--frame-call', c.code, c.data, String(c.gas), '1030'],
    { encoding: 'utf8', timeout: 10000, maxBuffer: 128 * 1024 })
  if (child.error || child.status !== 0) {
    throw Error('Lean frame process failed: ' + String(child.error ?? child.stderr))
  }
  const outcome = JSON.parse(child.stdout)
  assert.equal(outcome.memoryTruncated, false, c.id + ' memory observation')
  assert.equal(outcome.returnDataTruncated, false, c.id + ' output observation')
  return outcome
}

const diff = (expected, actual) => Object.keys(expected)
  .filter(key => JSON.stringify(expected[key]) !== JSON.stringify(actual[key]))
const observations = new Map()
const failures = []
const categories = {}
const geth = openGeth()
const gethFailures = []
let gethCompared = 0
let gethZeroGasExcluded = 0
for (const c of cases) {
  categories[c.category] ??= {compared: 0, matched: 0}
  categories[c.category].compared++
  try {
    assert(!observations.has(c.id), c.id)
    const expected = await expectedFrame(c)
    const actual = leanFrame(c)
    const fields = diff(expected, actual)
    observations.set(c.id, {expected, actual})
    if (fields.length) failures.push({id:c.id, fields, expected, actual})
    else categories[c.category].matched++
    if (geth && c.gas === 0) gethZeroGasExcluded++
    if (geth && c.gas > 0) {
      gethCompared++
      try {
        const g = geth.run(c)
        const expected = {status: g.status, gasRemaining: g.gasRemaining, returnDataHex: g.bytesHex}
        if (g.status === 'stopped') Object.assign(expected, {
          stack: g.stack, memoryHex: g.memoryHex, memorySizeBytes: g.memorySize
        })
        const fields = diff(expected, actual)
        if (fields.length) gethFailures.push({id:c.id, fields, expected, actual})
      } catch (error) {
        gethFailures.push({id:c.id, error:String(error)})
      }
    }
  } catch (error) {
    failures.push({id:c.id, error:String(error)})
  }
}

const control = observations.get('observed-return')
const negativeControls = {
  byte: control !== undefined && diff(control.expected, {...control.actual,
    returnDataHex: '00' + control.actual.returnDataHex.slice(2)}).includes('returnDataHex'),
  gas: control !== undefined && diff(control.expected, {...control.actual,
    gasRemaining: (BigInt(control.expected.gasRemaining) + 1n).toString()}).includes('gasRemaining'),
  status: control !== undefined && observations.has('observed-revert') &&
    diff(control.expected, observations.get('observed-revert').actual).includes('status')
}
console.log(JSON.stringify({
  kind: 'independent-byte-copy-frame-differential', oracle: '@ethereumjs/evm@10.1.3 Shanghai runCode',
  seed, compared: cases.length, matched: cases.length - failures.length, mismatches: failures.length,
  categories, gasBoundaryTriplets: boundaries.length, negativeControls,
  oracleExceptions,
  observedFields: ['status', 'gasRemaining', 'frame output and size', 'stack and memory on STOP/RETURN/REVERT'],
  geth: geth && {version: geth.version, sourceCommit: geth.sourceCommit, sha256: geth.sha256, fork: geth.fork,
    compared: gethCompared, matched: gethCompared - gethFailures.length, mismatches: gethFailures.length,
    zeroGasExcluded: gethZeroGasExcluded,
    observedFields: ['status', 'gasRemaining', 'frame output', 'stack and memory on STOP'],
    firstFailures: gethFailures.slice(0, 6)},
  firstFailures: failures.slice(0, 6)
}))
if (failures.length || gethFailures.length || !Object.values(negativeControls).every(Boolean)) process.exitCode = 1
