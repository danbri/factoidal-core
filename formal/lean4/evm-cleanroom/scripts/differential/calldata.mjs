#!/usr/bin/env node
/** Compare a compiled evm-subset with the pinned EthereumJS Shanghai interpreter. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { hexToBytes } from '@ethereumjs/util'

const executable = process.argv[2] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-subset', import.meta.url))
const evm = await createEVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Shanghai }) })
const observationLimit = 4096
const highBit = 1n << 255n
const max = 2n * highBit - 1n
const toWordHex = n => n.toString(16).padStart(64, '0')
const push = n => '7f' + toWordHex(n)
const asHex = bytes => Buffer.from(bytes).toString('hex')
const asDecimal = bytes => bytes.length ? BigInt('0x' + asHex(bytes)).toString() : '0'
const sequence = length => asHex(Uint8Array.from({ length }, (_, i) => (13 * i + 31) % 256))
const cases = []
const add = (id, code, data = '', gas = 1000, fuel = 100) => cases.push({ id, code, data, gas, fuel })

for (const length of [0, 1, 4, 31, 32, 33, 68]) {
  const data = sequence(length)
  add(`size-${length}`, '3600', data, 2)
  for (const offset of new Set([
    0n, 1n, 4n, 31n, 32n, 36n, BigInt(Math.max(0, length - 1)), BigInt(length), BigInt(length + 1),
    (1n << 53n) + 1n, (1n << 64n) + 4n, highBit, max - 15n, max
  ])) {
    add(`load-${length}-${offset}`, push(offset) + '3500', data, 6)
  }
}
add('calldataload-oog', '5f3500', 'ffee', 4)
add('calldataload-underflow', '3500', 'ffee', 3)
add('calldatasize-oog', '3600', 'ffee', 1)
add('calldatasize-overflow', '5f'.repeat(1024) + '3600', 'ffee', 2500, 1030)
add('repeated-loads-and-size', '5f35601f356020353600', sequence(33))

const pairs = [
  [0n, 0n], [0n, max], [max, 0n], [max, max], [highBit, highBit - 1n],
  [highBit - 1n, highBit], [highBit + 1n, 1n], [1n, highBit + 1n],
  [0xaaaaaaaaaaaaaaaan, 0x5555555555555555n]
]
const numberedWord = BigInt('0x' + sequence(32))
const bytePairs = [0n, 1n, 15n, 30n, 31n, 32n, 33n, 256n, highBit, max].flatMap(index => [
  [numberedWord, index], [max, index]
])
const shiftPairs = [0n, 1n, 7n, 8n, 63n, 64n, 127n, 128n, 255n, 256n, 257n, 65536n, highBit, max]
  .flatMap(count => [0n, 1n, highBit, max].map(value => [value, count]))

for (const [op, name, operands] of [
  ['10', 'lt', pairs], ['11', 'gt', pairs], ['14', 'eq', pairs], ['16', 'and', pairs],
  ['17', 'or', pairs], ['18', 'xor', pairs], ['1a', 'byte', bytePairs],
  ['1b', 'shl', shiftPairs], ['1c', 'shr', shiftPairs]
]) {
  for (const [second, top] of operands) {
    add(`${name}-${second}-${top}`, push(second) + push(top) + op + '00', '', 9)
  }
  add(`${name}-oog`, '60016002' + op + '00', '', 8)
  add(`${name}-underflow`, '6001' + op + '00', '', 6)
}
for (const [op, name] of [['15', 'iszero'], ['19', 'not']]) {
  for (const [i, value] of [0n, 1n, highBit, highBit + 1n, max].entries()) {
    add(`${name}-${i}`, push(value) + op + '00', '', 6)
  }
  add(`${name}-oog`, '6001' + op + '00', '', 5)
  add(`${name}-underflow`, op + '00', '', 3)
}

// Compare two ABI uint256 arguments and return their a >= b predicate.
const abiProgram = '6004356024359010155f5260205ff3'
const abiData = (a, b) => '11223344' + toWordHex(a) + toWordHex(b)
add('abi-high-low', abiProgram, abiData(highBit + 1n, highBit))
add('abi-low-high', abiProgram, abiData(highBit, highBit + 1n))
add('abi-equal', abiProgram, abiData(max, max))
add('abi-selector-only', abiProgram, '0X11223344')
add('abi-partial-argument', abiProgram, '11223344ffff0f')
add('abi-exact-gas', abiProgram, abiData(1n, 2n), 34)
add('abi-out-of-gas', abiProgram, abiData(1n, 2n), 33)
add('abi-revert', abiProgram.slice(0, -2) + 'fd', abiData(2n, 1n))
add('nonzero-return-offset', '5f355f5260046005f3', sequence(32))
add('empty-return-at-max-offset', '5f' + push(max) + 'f3')
add('return-limit', '602a5f536110005ff3')
add('return-truncated', '602a5f536110015ff3')
add('revert-truncated', '602a5f536110015ffd')
add('huge-return-out-of-gas', push(max) + '5ff3')

let lastOpcode
evm.events.on('step', ({ opcode }, resolve) => {
  lastOpcode = opcode.code
  resolve?.()
})

const errorNames = new Map([
  ['out of gas', 'outOfGas'], ['stack underflow', 'stackUnderflow'], ['stack overflow', 'stackOverflow']
])

async function expectedFrame(c) {
  lastOpcode = undefined
  const result = await evm.runCode({
    code: hexToBytes('0x' + c.code),
    data: hexToBytes('0x' + c.data.replace(/^0x/i, '')),
    gasLimit: BigInt(c.gas)
  })
  const error = result.exceptionError?.error
  const status = error === 'revert' ? 'reverted' : error ? 'exceptional' :
    lastOpcode === 0xf3 ? 'returned' : 'stopped'
  const expected = {
    status,
    gasRemaining: (BigInt(c.gas) - result.executionGasUsed).toString(),
    returnDataHex: asHex(result.returnValue.subarray(0, observationLimit)),
    returnDataLength: String(result.returnValue.length),
    returnDataTruncated: result.returnValue.length > observationLimit
  }
  if (status === 'exceptional') {
    assert(errorNames.has(error), `${c.id}: unexpected oracle error ${error}`)
    expected.error = errorNames.get(error)
  } else {
    const { memory, memoryWordCount, stack } = result.runState
    const size = Number(32n * memoryWordCount)
    assert(Number.isSafeInteger(size), `${c.id}: oracle memory size exceeds fixture bound`)
    const observed = Math.min(size, observationLimit)
    const bytes = memory.read(0, observed)
    Object.assign(expected, {
      stack: stack.peek(stack.length).map(String),
      memorySizeBytes: String(size),
      memoryWord0: asDecimal(bytes.subarray(0, 32)),
      memoryObservedBytes: String(observed),
      memoryTruncated: size > observationLimit,
      memoryHex: asHex(bytes)
    })
  }
  return expected
}

function leanFrame(...args) {
  const child = spawnSync(executable, ['--frame-call', ...args], { encoding: 'utf8', timeout: 10000 })
  if (child.error || child.signal) throw new Error(String(child.error ?? child.signal))
  return { code: child.status, output: JSON.parse(child.stdout.trim()) }
}

const diff = (expected, actual) => Object.keys(expected)
  .filter(key => JSON.stringify(expected[key]) !== JSON.stringify(actual[key]))

const observations = new Map()
const discrepancies = []
for (const c of cases) {
  const expected = await expectedFrame(c)
  const lean = leanFrame(c.code, c.data, String(c.gas), String(c.fuel))
  assert.equal(lean.code, 0, c.id)
  const fields = diff(expected, lean.output)
  if (fields.length) discrepancies.push({ id: c.id, fields })
  observations.set(c.id, { expected, actual: lean.output })
}

// The same program with swapped ABI words must be rejected by the comparison.
const abiDiff = diff(observations.get('abi-high-low').expected, observations.get('abi-low-high').actual)
assert(abiDiff.includes('returnDataHex') && abiDiff.includes('memoryHex'))
const shiftDiff = diff(observations.get('shl-1-255').expected, observations.get('shl-1-256').actual)
assert.deepEqual(shiftDiff, ['stack'])
const gasDiff = diff(observations.get('abi-exact-gas').expected, observations.get('abi-low-high').actual)
assert.deepEqual(gasDiff, ['gasRemaining'])

const badArgs = [
  [], ['00', '', '100'], ['0', '', '100', '10'], ['00', 'f', '100', '10'],
  ['00', '0xgg', '100', '10'], ['00', '', '-1', '10'], ['00', '', '100', 'nan'],
  ['00', '', '100', '10', 'extra']
]
for (const args of badArgs) {
  const lean = leanFrame(...args)
  assert.equal(lean.code, 2, JSON.stringify(args))
  assert.equal(lean.output.status, 'inputError', JSON.stringify(args))
}
assert.deepEqual(leanFrame('00', '', '100', '0'), {
  code: 0, output: { status: 'unsupported', error: 'stepLimit' }
})

console.log(JSON.stringify({
  kind: 'independent-calldata-and-word-operations-differential',
  oracle: '@ethereumjs/evm@10.1.3 Shanghai runCode',
  compared: cases.length,
  matched: cases.length - discrepancies.length,
  mismatches: discrepancies.length,
  negativeControls: 3,
  inputErrors: badArgs.length,
  fuelLimitChecks: 1,
  observationLimit,
  fields: ['status', 'gasRemaining', 'stack', 'memorySizeBytes', 'memoryWord0', 'memoryObservedBytes',
    'memoryTruncated', 'memoryHex', 'returnDataHex', 'returnDataLength', 'returnDataTruncated', 'error'],
  firstDiscrepancies: discrepancies.slice(0, 10)
}))
if (discrepancies.length) process.exitCode = 1
