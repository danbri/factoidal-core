#!/usr/bin/env node
/** Compare actual Lean KECCAK256 and LOG instructions with pinned Cancun EthereumJS. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createEVM } from '@ethereumjs/evm'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'
import { keccak_256 } from '@noble/hashes/sha3.js'

const executable = process.argv[2] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-subset', import.meta.url))
const common = new Common({ chain: Mainnet, hardfork: Hardfork.Cancun })
const fixtureUrl = new URL('../../evidence/frontier-keccak-vectors.json', import.meta.url)
const fixtureBytes = readFileSync(fixtureUrl)
const fixtureSha256 = createHash('sha256').update(fixtureBytes).digest('hex')
assert.equal(fixtureSha256, 'cd13f0935b1015ba15470b49b2c66c60d5d8cdd024747afe61e68edbdf9ffd0c')
const xkcp = JSON.parse(fixtureBytes)
assert.equal(xkcp.vectors.length, 24)
assert.equal(xkcp.algorithm.delimitedSuffix, '0x01')

const maxWord = (1n << 256n) - 1n
const emptyHash = 'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470'
const abcHash = '4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45'
const hex = b => Buffer.from(b).toString('hex')
const bytes = h => hexToBytes('0x' + h)
const decimal = b => BigInt('0x' + hex(b)).toString()
const address = n => createAddressFromString('0x' + n.toString(16).padStart(40, '0'))
const push = n => {
  if (BigInt(n) === 0n) return '5f'
  const digits = n.toString(16)
  const data = digits.length % 2 ? '0' + digits : digits
  return (0x5f + data.length / 2).toString(16) + data
}
const putByte = (o, b) => push(b) + push(o) + '53'
const copyInput = (offset, length) => push(length) + push(0) + push(offset) + '37'
const hashAt = (offset, length) => push(length) + push(offset) + '20'
const outputHash = '5f5260205ff3'
const logAt = (offset, length, topics, count = topics.length) =>
  [...topics].reverse().map(push).join('') + push(length) + push(offset) + (0xa0 + count).toString(16)
const rawCall = target => '5f'.repeat(5) + push(target) + push(60000) + 'f1'
const labels = new Map([['stack underflow', 'stackUnderflow'], ['out of gas', 'outOfGas'],
  ['static state change', 'writeProtection'], ['invalid opcode', 'invalidOpcode']])

const cases = []
const gasBoundaries = []
const add = (category, id, code, options = {}) => cases.push({ category, id, code, ...options })
const hashCase = (category, id, input, expected, offset = 0, options = {}) => {
  const data = hex(input)
  const digest = hex(keccak_256(input))
  if (expected !== undefined) assert.equal(digest, expected, id + ' noble versus known answer')
  add(category, id, copyInput(offset, input.length) + hashAt(offset, input.length) + outputHash,
    { data, hash: true, expect: { outputHex: digest }, ...options })
}

for (const { pattern, inputLengthBytes: length, digestHex } of xkcp.vectors) {
  assert(['ascii-a', 'byte-ramp'].includes(pattern))
  const input = Uint8Array.from({ length }, (_, i) => pattern === 'ascii-a' ? 0x61 : i % 256)
  hashCase('xkcp', `xkcp-${pattern}-${length}`, input, digestHex, 3)
}
hashCase('hash', 'abc', bytes('616263'), abcHash)
hashCase('hash', 'distinct-32-byte-word', Uint8Array.from({ length: 32 }, (_, i) => 255 - i), undefined, 31)
hashCase('hash', '33-byte-word-rounded', Uint8Array.from({ length: 33 }, (_, i) => i), undefined, 32)
hashCase('hash', 'pure-frame-hash', bytes('616263'), abcHash, 0, { pure: true })
add('hash', 'max-offset-empty', hashAt(maxWord, 0) + outputHash,
  { hash: true, expect: { outputHex: emptyHash } })
add('hash', 'unwritten-data-expansion', putByte(31, 0x61) + hashAt(31, 3) + outputHash,
  { hash: true, expect: { outputHex: hex(keccak_256(bytes('610000'))) } })
add('hash', 'max-offset-nonempty', hashAt(maxWord, 1) + '00', { hash: true, error: 'outOfGas' })
add('hash', 'max-length-gas-failure', hashAt(0, maxWord) + '00', { hash: true, error: 'outOfGas' })
add('hash', 'hash-underflow-zero', '2000', { hash: true, error: 'stackUnderflow' })
add('hash', 'hash-underflow-one', '5f2000', { hash: true, error: 'stackUnderflow' })
for (const [id, code] of [
  ['hash-empty', hashAt(0, 0) + '00'],
  ['hash-expansion-and-rounding', putByte(31, 0xab) + hashAt(31, 34) + '00'],
]) gasBoundaries.push({ category: 'hash-gas', id, code, hash: true })

const topics = [123n, maxWord, 256n, 9n]
const expectedLog = (address, topics, dataHex) => ({ address: String(address), topics: topics.map(String), dataHex })
for (let n = 0; n <= 4; n++) {
  const ts = topics.slice(0, n)
  const emit = logAt(31, 3, ts)
  add('log', `log${n}-data-topics`, putByte(31, 0x61) + emit + '00',
    { expect: { logs: [expectedLog(0, ts, '610000')] } })
  add('static', `log${n}-static`, emit + '00', { world: true, readOnly: true, error: 'writeProtection' })
  add('underflow', `log${n}-underflow`, (n === 0 ? '5fa0' : logAt(0, 0, ts.slice(1), n)) + '00',
    { error: 'stackUnderflow' })
  gasBoundaries.push({ category: 'log-gas', id: `log${n}-expansion`, code: emit + '00' })
}
add('log', 'log-max-offset-empty', logAt(maxWord, 0, []) + '00',
  { expect: { logs: [expectedLog(0, [], '')], memorySize: '0' } })
add('log', 'log-far-nonempty', logAt(maxWord, 1, []) + '00', { error: 'outOfGas' })
add('log', 'write-after-log-snapshot', putByte(0, 0xaa) + logAt(0, 1, [1n]) +
  putByte(0, 0xbb) + logAt(0, 1, [2n]) + '00',
  { expect: { logs: [expectedLog(0, [1n], 'aa'), expectedLog(0, [2n], 'bb')] } })
add('rollback', 'standalone-revert', logAt(0, 0, [1n]) + '5f5ffd', { expect: { status: 'reverted', logs: [] } })
add('rollback', 'standalone-exception', logAt(0, 0, [1n]) + 'fe', { error: 'invalidOpcode' })

// Actual world-aware CALL commits child logs in order, or discards them on failure.
const parentProgram = logAt(0, 0, [1n]) + rawCall(0xc3) + logAt(0, 0, [3n])
const childProgram = putByte(0, 0x2a) + logAt(0, 1, [2n])
const outerLogs = [expectedLog(0xc1, [1n], ''), expectedLog(0xc1, [3n], '')]
const childLog = expectedLog(0xc3, [2n], '2a')
add('rollback', 'nested-child-commits-in-order', parentProgram + '00',
  { world: true, child: childProgram + '00', expect: { logs: [outerLogs[0], childLog, outerLogs[1]] } })
add('rollback', 'nested-child-revert-restores-parent', parentProgram + '00',
  { world: true, child: childProgram + '5f5ffd', expect: { logs: outerLogs } })
add('rollback', 'nested-child-exception-restores-parent', parentProgram + '00',
  { world: true, child: childProgram + 'fe', expect: { logs: outerLogs } })
add('rollback', 'parent-revert-discards-successful-child-logs', parentProgram + '5f5ffd',
  { world: true, child: childProgram + '00', expect: { status: 'reverted', logs: [] } })

const hashChild = putByte(0, 0x61) + putByte(1, 0x62) + putByte(2, 0x63) + hashAt(0, 3) + outputHash
const hashParent = rawCall(0xc3) + '3d5f5f3e60205ff3'
add('hash', 'child-inherits-hash-opt-in', hashParent,
  { world: true, child: hashChild, hash: true, expect: { outputHex: abcHash } })

async function reference(c) {
  const evm = await createEVM({ common })
  const emitter = address(c.world ? 0xc1 : 0)
  const caller = address(0xc2)
  await evm.stateManager.putAccount(emitter, new Account())
  await evm.stateManager.putCode(emitter, bytes(c.code))
  if (c.child !== undefined) {
    const child = address(0xc3)
    await evm.stateManager.putAccount(child, new Account())
    await evm.stateManager.putCode(child, bytes(c.child))
  }
  let lastOpcode
  evm.events.on('step', (step, finish) => {
    if (step.depth === 0) lastOpcode = step.opcode.code
    finish?.()
  })
  const gasLimit = BigInt(c.gas ?? 120000)
  const { execResult: out } = await evm.runCall({ caller, to: emitter,
    data: bytes(c.data ?? ''), gasLimit, isStatic: c.readOnly ?? c.pure ?? false })
  const jsError = out.exceptionError?.error
  const status = jsError === 'revert' ? 'reverted' : jsError ? 'exceptional' :
    lastOpcode === 0xf3 ? 'returned' : 'stopped'
  const expected = {
    status, gasRemaining: String(gasLimit - out.executionGasUsed), outputHex: hex(out.returnValue),
    logs: (out.logs ?? []).map(([who, ts, data]) => ({ address: decimal(who), topics: ts.map(decimal), dataHex: hex(data) })),
  }
  if (status === 'exceptional') {
    assert.equal(labels.get(jsError), c.error, c.id + ' independent error category')
    expected.error = c.error
  } else {
    assert.equal(c.error, undefined, c.id + ' must fail in the reference')
    const { stack, memory, memoryWordCount } = out.runState
    const memorySize = Number(memoryWordCount) * 32
    assert(memorySize <= 4096, c.id + ' full memory observation')
    expected.stack = stack.peek(stack.length).map(String)
    expected.memorySize = String(memorySize)
    expected.memoryHex = hex(memory.read(0, memorySize))
  }
  for (const [key, value] of Object.entries(c.expect ?? {})) assert.deepEqual(expected[key], value, c.id + ' ' + key)
  return { expected, gasUsed: out.executionGasUsed }
}

for (const boundary of gasBoundaries) {
  const { gasUsed } = await reference(boundary)
  for (const delta of [-1n, 0n, 1n]) add(boundary.category, `${boundary.id}${delta < 0n ? '' : '+'}${delta}`,
    boundary.code, { hash: boundary.hash, gas: gasUsed + delta, error: delta < 0n ? 'outOfGas' : undefined })
}

function runNative(c) {
  const gas = String(c.gas ?? 120000)
  const fuel = '1024'
  const flags = [
    ...(c.hash ? ['--dangerously-enable-unverified-keccak'] : []),
    ...(c.observeLogs === false ? [] : ['--observe-logs']),
  ]
  const args = c.world
    ? ['--call-opcode', c.code, c.child ?? '', gas, fuel, '0', '0', '0', c.readOnly ? '1' : '0', 'shanghaiPlus', '0']
    : [c.pure ? '--pure-frame-call' : '--frame-call', c.code, c.data ?? '', gas, fuel]
  const result = spawnSync(executable, [...flags, ...args], { encoding: 'utf8', timeout: 10000, maxBuffer: 128 * 1024 })
  if (result.error || result.status !== 0) {
    throw Error(`Lean process failed (${result.status}): ${result.error ?? result.stdout ?? result.stderr}`)
  }
  const out = JSON.parse(result.stdout)
  if (c.hash) assert.equal(out.keccakOptIn, true, c.id + ' experimental opt-in is recorded')
  return out
}

function observation(c, out) {
  assert.equal(out.logsTruncated, false, c.id + ' complete log output')
  assert.equal(c.world ? out.returnBytesTruncated : out.returnDataTruncated, false, c.id + ' complete frame output')
  const observed = { status: out.status, gasRemaining: out.gasRemaining, logs: out.logs,
    outputHex: c.world ? out.returnBytesHex : out.returnDataHex }
  if (out.status === 'exceptional') observed.error = c.world ? out.reason : out.error
  else {
    assert.equal(c.world ? out.parentMemoryTruncated : out.memoryTruncated, false, c.id + ' complete memory')
    observed.stack = out.stack
    observed.memorySize = c.world ? out.parentMemorySize : out.memorySizeBytes
    observed.memoryHex = c.world ? out.parentMemoryHex : out.memoryHex
  }
  return observed
}

const counts = {}
const observations = new Map()
const failures = []
assert.equal(new Set(cases.map(c => c.id)).size, cases.length, 'unique case identities')
for (const c of cases) {
  counts[c.category] ??= { compared: 0, matched: 0 }
  counts[c.category].compared++
  try {
    const { expected } = await reference(c)
    const actual = observation(c, runNative(c))
    assert.deepEqual(actual, expected, c.id)
    counts[c.category].matched++
    observations.set(c.id, actual)
  } catch (error) {
    failures.push({ id: c.id, error: String(error) })
  }
}

const length = 17n * 1024n * 1024n
const words = length / 32n
// Include the two PUSH charges, the hash base/word costs and quadratic memory expansion.
const funded = 5n + 30n + 6n * words + 3n * words + words * words / 512n
const nativeBoundaries = []
for (const [id, code, hash, gas, status, error] of [
  ['hash-default-disabled', hashAt(0, 0) + '00', false, 1000n, 'unsupported', 'unsupportedFork'],
  ['hash-funded-seventeen-mib', hashAt(0, length) + '00', true, funded, 'unsupported', 'resourceLimit'],
  ['hash-funded-seventeen-mib-one-gas-short', hashAt(0, length) + '00', true, funded - 1n, 'exceptional', 'outOfGas'],
  ['hash-full-word-length-with-huge-gas', hashAt(0, maxWord) + '00', true, 1n << 256n, 'exceptional', 'outOfGas'],
]) {
  try {
    const actual = runNative({ id, code, hash, gas })
    assert.equal(actual.status, status, id)
    assert.equal(actual.error, error, id)
    nativeBoundaries.push({ id, status, error })
  } catch (failure) {
    failures.push({ id, error: String(failure) })
  }
}

const disabledChild = 'hash-child-default-disabled'
try {
  const actual = runNative({ id: disabledChild, code: hashParent, child: hashChild, world: true })
  assert.equal(actual.status, 'indeterminate', disabledChild)
  assert.equal(actual.reason, 'unsupportedFork', disabledChild)
  nativeBoundaries.push({ id: disabledChild, status: actual.status, error: actual.reason })
} catch (failure) {
  failures.push({ id: disabledChild, error: String(failure) })
}

const largeLog = 'logs-over-observation-budget'
try {
  const code = logAt(0, length, []) + '00'
  const gas = 5n + 375n + 8n * length + 3n * words + words * words / 512n
  const unobserved = runNative({ id: largeLog, code, gas, observeLogs: false })
  assert.equal(unobserved.status, 'stopped', largeLog + ' execution')
  assert.equal(unobserved.gasRemaining, '0', largeLog + ' exact gas')
  assert.equal(unobserved.memoryTruncated, true, largeLog + ' memory observation')
  const observed = runNative({ id: largeLog, code, gas })
  assert.deepEqual(observed, { status: 'indeterminate', reason: 'resourceLimit' }, largeLog)
  nativeBoundaries.push({ id: largeLog, status: observed.status, error: observed.reason })
} catch (failure) {
  failures.push({ id: largeLog, error: String(failure) })
}

const h = observations.get('abc')
const l = observations.get('write-after-log-snapshot')
const mutationRejected = (expected, mutant) => {
  try { assert.deepEqual(expected, mutant); return false } catch { return true }
}
const negativeControls = {
  hash: !!h && mutationRejected(h, { ...h, outputHex: '00' + h.outputHex.slice(2) }),
  gas: !!h && mutationRejected(h, { ...h, gasRemaining: String(BigInt(h.gasRemaining) + 1n) }),
  logPayload: !!l && mutationRejected(l, { ...l, logs: [{ ...l.logs[0], dataHex: '00' }, l.logs[1]] }),
  logTopic: !!l && mutationRejected(l, { ...l, logs: [{ ...l.logs[0], topics: ['3'] }, l.logs[1]] }),
}
const matched = Object.values(counts).reduce((n, c) => n + c.matched, 0)
console.log(JSON.stringify({ kind: 'evm-hash-log-differential',
  oracle: '@ethereumjs/evm@10.1.3 Cancun runCall; @noble/hashes@2.4.0 for direct Keccak known answers',
  scope: 'Lean frame and world fixtures use the shared KECCAK256/LOG rules of the Shanghai-plus profile.',
  fixture: { xkcpVectors: xkcp.vectors.length, sha256: fixtureSha256 },
  experimentalHashFlag: '--dangerously-enable-unverified-keccak',
  compared: cases.length, matched, mismatches: cases.length - matched, counts,
  gasBoundaryTriplets: gasBoundaries.length, nativeBoundaries, negativeControls,
  firstFailures: failures.slice(0, 12),
}))
if (failures.length || !Object.values(negativeControls).every(Boolean)) process.exitCode = 1
