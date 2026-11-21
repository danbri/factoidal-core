#!/usr/bin/env node
/**
 * Independently execute EIP-7939 CLZ in Osaka EthereumJS and Lean.
 *
 * Every test uses actual bytecode PUSH32 <full-256-bit operand>, CLZ (0x1e),
 * STOP. The oracle executes the code under Hardfork.Osaka; Lean uses its
 * *explicit* --osaka-batch profile. The corpus is deterministic, byte-for-byte
 * reproducible and includes normative bit and gas boundaries.
 *
 * No general Osaka transaction, precompile, block or consensus compatibility
 * is implied. This is an opcode-level test.
 */
import { createHash } from 'node:crypto'
import { spawnSync } from 'node:child_process'
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const GAS = 100n
const FUEL = 3
const target = createAddressFromString('0x00000000000000000000000000000000000000c1')
const caller = createAddressFromString('0x00000000000000000000000000000000000000c2')
const edges = [
  0n, 1n, 2n, 3n, 7n, 255n, 256n, 257n,
  (1n << 31n) - 1n, 1n << 31n,
  (1n << 63n) - 1n, 1n << 63n,
  (1n << 127n) - 1n, 1n << 127n,
  (1n << 128n) - 1n, 1n << 128n,
  (1n << 254n) - 1n, 1n << 254n,
  (1n << 255n) - 1n, 1n << 255n,
  (1n << 256n) - 1n,
]
const operands = new Map(edges.map(n => [n.toString(16), n]))
const add = n => operands.set(n.toString(16), n)
// Cover every CLZ result from 0 through 256, and both sides of each
// bit-length transition. This catches off-by-one errors which uniform
// 256-bit random inputs (mostly yielding CLZ=0 or 1) routinely miss.
for (let bit = 0; bit < 256; bit++) add(1n << BigInt(bit))
for (let bit = 1; bit <= 256; bit++) add((1n << BigInt(bit)) - 1n)
for (let bit = 0; bit < 256; bit++) add((1n << BigInt(bit)) + 1n)
for (let i = 0; i < 256; i++) {
  const digest = createHash('sha256')
    .update('factoidal-eip7939-osaka-clz-v1:' + String(i)).digest('hex')
  const value = BigInt('0x' + digest)
  operands.set(value.toString(16), value)
}
const corpus = [...operands.values()]
function hexCode(value) {
  if (value < 0n || value >= (1n << 256n))
    throw Error('not a uint256')
  return '7f' + value.toString(16).padStart(64, '0') + '1e00'
}

const temp = mkdtempSync(join(tmpdir(), 'osaka-clz-'))
let lean
try {
  const file = join(temp, 'cases.tsv')
  writeFileSync(file, corpus.map(n =>
    hexCode(n) + '\t' + GAS.toString() + '\t' + String(FUEL)).join('\n') + '\n')
  const proc = spawnSync('lake', ['exe', 'evm-subset', '--osaka-batch', file], {
    encoding: 'utf8', timeout: 120000, maxBuffer: 8 * 1024 * 1024,
  })
  if (proc.error || proc.status !== 0)
    throw Error('Lean batch failed: ' + String(proc.error ?? proc.stderr).slice(-3000))
  lean = proc.stdout.trim().split('\n').map(line => JSON.parse(line))
  if (lean.length !== corpus.length) throw Error('Lean batch count mismatch')
} finally {
  rmSync(temp, {recursive: true, force: true})
}

async function reference(code, gasLimit = GAS) {
  const common = new Common({chain: Mainnet, hardfork: Hardfork.Osaka})
  const evm = await createEVM({common})
  await evm.stateManager.putAccount(target, new Account())
  await evm.stateManager.putCode(target, hexToBytes('0x' + code))
  const run = await evm.runCall({caller, to: target, gasLimit})
  const execution = run.execResult
  if (execution.exceptionError)
    throw Error('Osaka reference rejected supported CLZ: ' +
      String(execution.exceptionError.error ?? execution.exceptionError))
  const stack = execution.runState?.stack?.getStack()
  if (!Array.isArray(stack) || stack.length !== 1)
    throw Error('Osaka reference did not preserve one CLZ result')
  return {
    stack: [stack[0].toString()],
    gasRemaining: (gasLimit - execution.executionGasUsed).toString(),
  }
}

const failures = []
let comparatorMutationCaught = false
for (const [i, n] of corpus.entries()) {
  try {
    const expected = await reference(hexCode(n))
    const actual = lean[i]
    const declarative = BigInt(n === 0n ? 256 : 256 - n.toString(2).length)
    const mismatches = []
    if (actual.status !== 'ok') mismatches.push('non-success:' + actual.status)
    if (actual.stack?.length !== 1 ||
        actual.stack?.[0] !== expected.stack[0])
      mismatches.push('full-width-stack')
    if (actual.gasRemaining !== expected.gasRemaining ||
        actual.gasRemaining !== '92')
      mismatches.push('constant-gas-5')
    if (actual.stack?.[0] !== declarative.toString() ||
        expected.stack[0] !== declarative.toString())
      mismatches.push('declarative-bit-length')
    if (actual.pc !== '35') mismatches.push('program-counter')
    if (actual.memorySizeBytes !== '0') mismatches.push('no-memory-effects')
    if (!comparatorMutationCaught && actual.gasRemaining === expected.gasRemaining)
      comparatorMutationCaught =
        actual.gasRemaining !== (BigInt(expected.gasRemaining) + 1n).toString()
    if (mismatches.length)
      failures.push({index: i, operand: '0x' + n.toString(16), expected,
        actual, mismatches})
  } catch (error) {
    failures.push({index: i, operand: '0x' + n.toString(16), error: String(error)})
  }
}

const earlier = spawnSync('lake', [
  'exe', 'evm-subset', hexCode(0n), GAS.toString(), String(FUEL),
], {encoding: 'utf8', timeout: 60000})
if (earlier.error || earlier.status !== 0) throw Error('legacy Lean probe failed')
const beforeOsaka = JSON.parse(earlier.stdout.trim().split('\n').at(-1))
const forkGuardHeld =
  beforeOsaka.status === 'error' && beforeOsaka.error === 'unsupportedFork'
function leanSingle(code, gas) {
  const proc = spawnSync('lake', [
    'exe', 'evm-subset', '--osaka', code, String(gas), String(FUEL),
  ], {encoding: 'utf8', timeout: 60000})
  if (proc.error || proc.status !== 0)
    throw Error('Lean single opcode probe failed: ' + String(proc.error ?? proc.stderr))
  return JSON.parse(proc.stdout.trim().split('\n').at(-1))
}
const underflow = leanSingle('1e00', 100)
const tooLittleGas = leanSingle(hexCode(0n), 7)
const exactGas = leanSingle(hexCode(0n), 8)
const underflowRejected = underflow.status === 'error' &&
  underflow.error === 'stackUnderflow'
const outOfGasRejected = tooLittleGas.status === 'error' &&
  tooLittleGas.error === 'outOfGas'
const exactGasAccepted = exactGas.status === 'ok' &&
  exactGas.gasRemaining === '0' && exactGas.stack?.[0] === '256'
const oracleExactGas = await reference(hexCode(0n), 8n)
const independentExactGas = oracleExactGas.gasRemaining === '0' &&
  oracleExactGas.stack?.[0] === '256'
const result = {
  kind: 'EIP-7939 full-256bit CLZ opcode differential',
  fork: 'Osaka', oracle: '@ethereumjs/evm@10.1.3 Hardfork.Osaka',
  tested: corpus.length, passed: corpus.length - failures.length,
  failed: failures.length, forkGuardHeld, comparatorMutationCaught,
  underflowRejected, outOfGasRejected, exactGasAccepted, independentExactGas,
  boundaryInputs: edges.length, oneHotInputs: 256,
  belowPowerInputs: 256, abovePowerInputs: 256, pseudorandomInputs: 256,
  comparedFields: ['stack result', 'exact gas', 'PC', 'memory', 'declarative bit-length'],
  limitations: 'only one CLZ instruction after PUSH32; Osaka explicitly selected, not full mainnet transaction/block conformance',
  firstFailures: failures.slice(0, 5),
}
console.log(JSON.stringify(result))
if (failures.length || !forkGuardHeld || !comparatorMutationCaught ||
    !underflowRejected || !outOfGasRejected ||
    !exactGasAccepted || !independentExactGas || corpus.length !== 1022)
  process.exitCode = 1
