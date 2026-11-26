#!/usr/bin/env node
/**
 * Differentially check actual Lean GASPRICE 0x3a and post-Merge
 * PREVRANDAO 0x44 against pinned EthereumJS 10.1.3 Shanghai.
 *
 * The values are synthetic: neither a signed EIP-1559 transaction nor an
 * authenticated beacon/EL block is proved by this opcode-level test.
 * GASPRICE is the effective tx price, not the transaction's max-fee cap.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { hexToBytes } from '@ethereumjs/util'

const common = new Common({ chain: Mainnet, hardfork: Hardfork.Shanghai })
const evm = await createEVM({ common })
const context = {
  effectiveGasPrice: 1_234_567_890n,
  prevRandao: BigInt('0x' + '12'.repeat(31) + '34'),
}
const syntheticBlock = { header: {
  prevRandao: hexToBytes('0x' + context.prevRandao.toString(16).padStart(64, '0')),
}}
function lean(code, gas, input = context) {
  const p = spawnSync('lake', [
    'exe', 'evm-subset', '--tx-env', code, String(gas), '60',
    String(input.effectiveGasPrice), String(input.prevRandao),
  ], { encoding: 'utf8', timeout: 60000, maxBuffer: 1024 * 1024 })
  if (p.error || p.status !== 0) {
    throw Error('Lean CLI failed: ' + String(p.error ?? p.stderr))
  }
  return JSON.parse(p.stdout.trim().split('\n').at(-1))
}
async function reference(code, gas) {
  const r = await evm.runCode({
    code: hexToBytes('0x' + code),
    gasLimit: BigInt(gas),
    gasPrice: context.effectiveGasPrice,
    block: syntheticBlock,
  })
  const fault = String(r.exceptionError?.error ?? '')
  if (fault) {
    if (!/out of gas/i.test(fault)) throw Error('Unexpected oracle exception: ' + fault)
    return { status: 'error', error: 'outOfGas' }
  }
  const size = Number(r.runState.memoryWordCount * 32n)
  if (size > 4096) throw Error('Oracle memory observation limit exceeded')
  return {
    status: 'ok',
    gasRemaining: String(BigInt(gas) - r.executionGasUsed),
    stack: r.runState.stack.getStack().map(String).reverse(),
    memorySizeBytes: String(size),
    memoryHex: Buffer.from(r.runState.memory.read(0, size)).toString('hex'),
  }
}
const examples = [
  { id: 'gasprice', code: '3a00' },
  { id: 'prevrandao', code: '4400' },
  { id: 'both', code: '3a4400' },
  { id: 'price-pop', code: '3a5000' },
  { id: 'randao-pop', code: '445000' },
  { id: 'price-memory-byte', code: '3a60005300' },
  { id: 'randao-memory-byte', code: '4460005300' },
  { id: 'price-in-add', code: '60023a0100' },
  { id: 'randao-in-add', code: '6002440100' },
]
const gasCases = [1, 2, 3, 11, 100]
let compared = 0
const failures = []
for (const item of examples) {
  for (const gas of gasCases) {
    const id = item.id + ':' + gas
    compared++
    try {
      const actual = lean(item.code, gas)
      const expected = await reference(item.code, gas)
      const fields = expected.status === 'error'
        ? ['status', 'error']
        : ['status', 'gasRemaining', 'stack', 'memorySizeBytes', 'memoryHex']
      const mismatched = fields.filter(k => JSON.stringify(actual[k]) !== JSON.stringify(expected[k]))
      if (mismatched.length) failures.push({ id, mismatched, actual, expected })
    } catch (e) {
      failures.push({ id, problem: String(e) })
    }
  }
}
const priceOracle = await reference('3a00', 100)
const randaoOracle = await reference('4400', 100)
const wrongPrice = lean('3a00', 100, { ...context, effectiveGasPrice: context.effectiveGasPrice + 1n })
const wrongRandao = lean('4400', 100, { ...context, prevRandao: context.prevRandao + 1n })
const negativeControls = {
  effectivePrice: priceOracle.stack?.[0] === String(context.effectiveGasPrice) &&
    wrongPrice.stack?.[0] === String(context.effectiveGasPrice + 1n) &&
    wrongPrice.stack?.[0] !== priceOracle.stack?.[0],
  prevRandao: randaoOracle.stack?.[0] === String(context.prevRandao) &&
    wrongRandao.stack?.[0] === String(context.prevRandao + 1n) &&
    wrongRandao.stack?.[0] !== randaoOracle.stack?.[0],
}
const report = {
  schemaVersion: 1,
  kind: 'synthetic effective GASPRICE and post-Merge PREVRANDAO EVM differential',
  fork: 'Shanghai',
  oracle: '@ethereumjs/evm@10.1.3',
  compared, matched: compared - failures.length, mismatches: failures.length,
  negativeControls,
  observedFields: ['status', 'error', 'remaining gas', 'complete stack', 'allocated memory bytes'],
  limitations: 'Effective gas price and prevRandao are externally supplied; no signed transaction, authenticated header, actual beacon state, pre-Merge DIFFICULTY or all-fork claim.',
  firstFailures: failures.slice(0, 8),
}
console.log(JSON.stringify(report))
if (compared !== 45 || failures.length || !Object.values(negativeControls).every(Boolean)) {
  process.exitCode = 1
}
