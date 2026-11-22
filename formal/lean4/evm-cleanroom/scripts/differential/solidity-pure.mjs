#!/usr/bin/env node
/** Compare signed words and an original Solidity runtime with EthereumJS Shanghai. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFile } from 'node:fs/promises'
import { fileURLToPath } from 'node:url'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createEVM } from '@ethereumjs/evm'
import { hexToBytes } from '@ethereumjs/util'

const executable = process.argv[2] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-subset', import.meta.url))
const fixtureURL = new URL('./fixtures/solidity-pure/fixture.json', import.meta.url)
const fixture = JSON.parse(await readFile(fixtureURL, 'utf8'))
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex')
assert.equal(fixture.schemaVersion, 1)
assert.equal(fixture.settings.evmVersion, 'shanghai')
assert.equal(fixture.settings.metadata.appendCBOR, true)
assert.match(fixture.runtimeHex, /^(?:[0-9a-f]{2})+$/)
assert.match(fixture.methodIdentifier, /^[0-9a-f]{8}$/)
assert.equal(sha256(await readFile(new URL(fixture.sourceFile, fixtureURL))), fixture.sourceSha256)
assert.equal(sha256(Buffer.from(fixture.runtimeHex, 'hex')), fixture.runtimeSha256)

const evm = await createEVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Shanghai }) })
const context = 'zero-value-context-free-v1'
const signBit = 1n << 255n
const maxWord = 2n * signBit - 1n
const wordHex = word => word.toString(16).padStart(64, '0')
const push = word => '7f' + wordHex(word)
const abi = (a, b) => fixture.methodIdentifier + wordHex(a) + wordHex(b)
const runtime = fixture.runtimeHex

let reached = []
evm.events.on('step', ({ opcode }, done) => {
  reached.push(opcode.code)
  done?.()
})

const errors = new Map([
  ['out of gas', 'outOfGas'], ['stack underflow', 'stackUnderflow'], ['invalid JUMP', 'invalidJump']
])

async function oracle({ code, data, gas }) {
  reached = []
  const input = {
    code: hexToBytes('0x' + code), data: hexToBytes('0x' + data), gasLimit: BigInt(gas), value: 0n,
  }
  const result = await evm.runCode(input)
  const error = result.exceptionError?.error
  const status = error === 'revert' ? 'reverted' : error ? 'exceptional' :
    reached.at(-1) === 0xf3 ? 'returned' : 'stopped'
  const observed = {
    schemaVersion: 1, comparisonContext: context, status,
    gasRemaining: (input.gasLimit - result.executionGasUsed).toString(),
    returnDataHex: Buffer.from(result.returnValue).toString('hex'),
    returnDataLength: String(result.returnValue.length), returnDataTruncated: false,
  }
  if (status === 'exceptional') {
    const errorKind = error.startsWith('invalid JUMP at ') ? 'invalid JUMP' : error
    assert(errors.has(errorKind), `Unexpected oracle error: ${error}`)
    observed.error = errors.get(errorKind)
  } else {
    const { memory, memoryWordCount, stack } = result.runState
    const size = Number(memoryWordCount * 32n)
    assert(size <= 4096, 'Oracle fixture exceeds the memory observation limit')
    Object.assign(observed, {
      memorySizeBytes: String(size), memoryObservedBytes: String(size), memoryTruncated: false,
      memoryHex: Buffer.from(memory.read(0, size)).toString('hex'),
      stack: stack.peek(stack.length).map(String),
    })
  }
  return { observed, reached, gasUsed: Number(result.executionGasUsed) }
}

function lean({ code, data, gas }, command = '--pure-frame-call') {
  const child = spawnSync(executable, [command, code, data, String(gas), '1000'],
    { encoding: 'utf8', timeout: 10000 })
  assert(!child.error && child.status === 0, `Lean ${command} failed: ${child.error ?? child.stderr}`)
  return JSON.parse(child.stdout)
}

const cases = []
const add = (id, code, data = '', gas = 1000) => cases.push({ id, code, data, gas })

const words = [0n, 1n, 2n, signBit - 1n, signBit, signBit + 1n, maxWord - 1n, maxWord]
for (const [i, a] of words.entries()) {
  for (const [j, b] of words.entries()) add(`slt-${i}-${j}`, push(b) + push(a) + '1200', '', 9)
}
add('slt-out-of-gas', push(maxWord) + push(signBit) + '1200', '', 8)
add('slt-one-operand', '60011200', '', 6)
add('slt-no-operands', '1200', '', 3)

// Signed division and remainder use truncated magnitudes, and SAR uses
// sign extension even when the full-width shift operand exceeds 255.
// Every case runs a real Lean frame against the independent EthereumJS EVM.
let newSignedCases = 0
const signedAdd = (id, code, gas = 1000) => {
  add(id, code, '', gas)
  newSignedCases++
}
for (const [op, name] of [['05', 'sdiv'], ['07', 'smod']]) {
  for (const [i, a] of words.entries()) {
    for (const [j, b] of words.entries()) {
      signedAdd(`${name}-${i}-${j}`, push(b) + push(a) + op + '00', 11)
    }
  }
  signedAdd(`${name}-out-of-gas`, '60036002' + op + '00', 10)
  signedAdd(`${name}-underflow`, '6001' + op + '00', 100)
}
const shifts = [0n, 1n, 31n, 128n, 255n, 256n, signBit, maxWord]
for (const [i, shift] of shifts.entries()) {
  for (const [j, value] of words.entries()) {
    signedAdd(`sar-${i}-${j}`, push(value) + push(shift) + '1d00', 9)
  }
}
signedAdd('sar-out-of-gas', '600360021d00', 8)
signedAdd('sar-underflow', '60011d00', 100)

// SIGNEXTEND is a pre-EIP instruction: byte index counts from the low end.
// Matrix crosses 0x7f/0x80, 0x7fff/0x8000, 31/32 and 256-bit limits.
// The EVM oracle is independent; there is no JS implementation of the opcode.
const signExtendIndexes = [0n, 1n, 2n, 15n, 30n, 31n, 32n, 33n, 255n, 256n, signBit, maxWord]
const signExtendValues = [0n, 1n, 0x7fn, 0x80n, 0xffn, 0x100n,
  0x7fffn, 0x8000n, signBit - 1n, signBit, signBit + 1n, maxWord]
let signExtendCases = 0
for (const [i, index] of signExtendIndexes.entries()) {
  for (const [j, value] of signExtendValues.entries()) {
    add(`signextend-${i}-${j}`, push(value) + push(index) + '0b00', '', 11)
    signExtendCases++
  }
}
add('signextend-out-of-gas', '608060000b00', '', 10)
add('signextend-underflow', '60010b00', '', 100)
signExtendCases += 2

// ADDMOD/MULMOD must retain full-precision intermediate values. Each triple
// is executed by the pinned independent EthereumJS oracle and by actual Lean.
const modularPairs = [
  [0n, 0n], [1n, 2n], [maxWord, maxWord], [maxWord, 2n],
  [signBit, signBit], [signBit + 1n, 7n], [7n, maxWord], [maxWord, 0n],
]
const modularModuli = [0n, 1n, 3n, 7n, signBit, maxWord]
let modularCases = 0
for (const [op, name] of [['08', 'addmod'], ['09', 'mulmod']]) {
  for (const [i, [a, b]] of modularPairs.entries()) {
    for (const [j, m] of modularModuli.entries()) {
      add(`${name}-${i}-${j}`, push(m) + push(b) + push(a) + op + '00', '', 17)
      modularCases++
    }
  }
  add(`${name}-out-of-gas`, '600360026001' + op + '00', '', 16)
  add(`${name}-underflow`, '60016002' + op + '00', '', 100)
  modularCases += 2
}

const highToLow = abi(signBit + 1n, signBit)
const lowToHigh = abi(signBit, signBit + 1n)
const baseline = await oracle({ code: runtime, data: highToLow, gas: 1000 })
assert.equal(baseline.observed.status, 'returned')
assert(baseline.reached.includes(0x12), 'Compiled Solidity should execute the signed ABI bounds check')
assert(baseline.reached.includes(0x34), 'Compiled Solidity should check the explicit zero call value')
assert(Buffer.from(runtime, 'hex').includes(0xfe) && !baseline.reached.includes(0xfe),
  'Pinned runtime should retain its unreachable Solidity metadata separator')

add('solidity-high-low', runtime, highToLow)
add('solidity-low-high', runtime, lowToHigh)
add('solidity-high-equality', runtime, abi(maxWord, maxWord))
add('solidity-zero-vs-max', runtime, abi(0n, maxWord))
add('solidity-max-vs-zero', runtime, abi(maxWord, 0n))
add('solidity-wrong-selector', runtime, '00000000' + highToLow.slice(8))
add('solidity-no-data', runtime)
add('solidity-selector-only', runtime, fixture.methodIdentifier)
add('solidity-short-calldata', runtime, highToLow.slice(0, -2))
add('solidity-exact-gas', runtime, highToLow, baseline.gasUsed)
add('solidity-one-gas-short', runtime, highToLow, baseline.gasUsed - 1)
add('solidity-unreachable-suffix', runtime + '30f154', highToLow)
add('push-data-is-not-an-opcode', '603000')
add('jump-past-forbidden-opcodes', '60065630f1545b00')
add('calldata-branch-avoids-address', '5f35600657005b3000')
add('jump-into-push-data-still-invalid', '600456605b00')

const observations = new Map()
for (const test of cases) {
  const expected = (await oracle(test)).observed
  const actual = lean(test)
  assert.deepEqual(Object.fromEntries(Object.keys(expected).map(key => [key, actual[key]])), expected, test.id)
  observations.set(test.id, actual)
}
assert.notEqual(observations.get('solidity-high-low').returnDataHex,
  observations.get('solidity-low-high').returnDataHex, 'Swapped ABI arguments must change the observed result')
assert.equal(observations.get('solidity-exact-gas').gasRemaining, '0')
assert.equal(observations.get('solidity-one-gas-short').error, 'outOfGas')

const forbidden = [
  { code: '5f35600657005b3000', data: '01', gas: 1000 }, // Reached ADDRESS.
  { code: '5f5400', data: '', gas: 1000 }, // SLOAD.
  { code: '5a00', data: '', gas: 1000 }, // GAS.
  { code: 'f100', data: '', gas: 1000 }, // CALL, before stack checks.
  { code: 'fe', data: '', gas: 1000 }, // INVALID is outside the comparison policy.
]
for (const test of forbidden) {
  assert.deepEqual(lean(test), {
    status: 'unsupported', error: 'framePolicyViolation', comparisonContext: context,
  }, test.code)
}
const legacyAddress = lean(forbidden[0], '--frame-call')
assert.equal(legacyAddress.status, 'stopped')
assert.equal(Object.hasOwn(legacyAddress, 'comparisonContext'), false)

console.log(JSON.stringify({
  kind: 'solidity-pure-frame-differential', oracle: '@ethereumjs/evm@10.1.3 Shanghai runCode',
  compiler: fixture.compiler.version, runtimeSha256: fixture.runtimeSha256,
  compared: cases.length, matched: cases.length, mismatches: 0,
  signedCases: words.length ** 2 + 3 + newSignedCases, signExtendCases,
  modularCases, forbiddenRefusals: forbidden.length,
  compiledExactGas: baseline.gasUsed, legacyCompatibility: 1,
}))
