#!/usr/bin/env node
/**
 * Independent block-environment opcode matrix against @ethereumjs/evm 10.1.3.
 * The header is a synthetic, explicitly supplied oracle fixture, not a
 * canonical block or an authenticated transaction/consensus environment.
 * Run with pinned scripts/differential/package-lock.json installed.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createAddressFromString, hexToBytes } from '@ethereumjs/util'

const common = new Common({ chain: Mainnet, hardfork: Hardfork.Shanghai })
const evm = await createEVM({ common })
const data = {
  coinbase: 0x1234n,
  timestamp: 1700000000n,
  number: 19000000n,
  gasLimit: 30000000n,
  baseFee: 1234567890n,
}
// EVM.runCode uses only these header values for the selected opcodes;
// it does not validate the header or verify block hashes.
const syntheticBlock = { header: {
  coinbase: createAddressFromString('0x0000000000000000000000000000000000001234'),
  timestamp: data.timestamp,
  number: data.number,
  gasLimit: data.gasLimit,
  baseFeePerGas: data.baseFee,
}}
function lean(hex, gas, inputs = data) {
  const p = spawnSync('lake', [
    'exe', 'evm-subset', '--block-env', hex, String(gas), '60',
    String(inputs.coinbase), String(inputs.timestamp), String(inputs.number),
    String(inputs.gasLimit), String(inputs.baseFee),
  ], { encoding: 'utf8', timeout: 60000, maxBuffer: 1024 * 1024 })
  if (p.error || p.status !== 0) throw Error('Lean CLI failure ' + String(p.error ?? p.stderr))
  return JSON.parse(p.stdout.trim().split('\n').at(-1))
}
async function reference(hex, gas) {
  const r = await evm.runCode({
    code: hexToBytes('0x' + hex),
    gasLimit: BigInt(gas),
    block: syntheticBlock,
  })
  const failure = String(r.exceptionError?.error ?? '')
  if (failure) {
    if (!/out of gas/i.test(failure)) throw Error('oracle exception ' + failure)
    return { status: 'error', error: 'outOfGas' }
  }
  const size = Number(r.runState.memoryWordCount * 32n)
  if (size > 4096) throw Error('oracle allocated unexpected memory')
  return {
    status: 'ok',
    stack: r.runState.stack.getStack().map(String).reverse(),
    gasRemaining: String(BigInt(gas) - r.executionGasUsed),
    memorySizeBytes: String(size),
    memoryHex: Buffer.from(r.runState.memory.read(0, size)).toString('hex'),
  }
}
const samples = [
  { id: 'coinbase', hex: '4100' },
  { id: 'timestamp', hex: '4200' },
  { id: 'number', hex: '4300' },
  { id: 'gaslimit', hex: '4500' },
  { id: 'basefee', hex: '4800' },
  { id: 'five-fields', hex: '414243454800' },
  { id: 'compare-number', hex: '6042431400' },
  { id: 'timestamp-byte-memory', hex: '4260005300' },
]
const gasCases = [1, 2, 3, 11, 100]
const failures = []
let compared = 0
for (const sample of samples) {
  for (const gas of gasCases) {
    const id = sample.id + ':' + gas
    compared++
    try {
      const actual = lean(sample.hex, gas)
      const expected = await reference(sample.hex, gas)
      const fields = expected.status === 'error'
        ? ['status', 'error']
        : ['status', 'gasRemaining', 'stack', 'memorySizeBytes', 'memoryHex']
      const wrong = fields.filter(f => JSON.stringify(actual[f]) !== JSON.stringify(expected[f]))
      if (wrong.length) failures.push({ id, wrong, actual, expected })
    } catch (e) {
      failures.push({ id, problem: String(e) })
    }
  }
}
const oracleTimestamp = await reference('4200', 100)
const altered = lean('4200', 100, { ...data, timestamp: data.timestamp + 1n })
const negativeControl = oracleTimestamp.stack?.[0] === String(data.timestamp) &&
  altered.stack?.[0] === String(data.timestamp + 1n) &&
  altered.stack?.[0] !== oracleTimestamp.stack?.[0]
const report = {
  schemaVersion: 1,
  kind: 'synthetic Shanghai block-environment opcode differential',
  oracle: '@ethereumjs/evm@10.1.3',
  compared, matched: compared - failures.length, mismatches: failures.length,
  negativeControl,
  observedFields: ['status', 'error', 'full stack', 'remaining gas', 'memory size', 'memory bytes'],
  limits: 'Supplied synthetic block header; no header validation, signed transaction, historical fork replay, PREVRANDAO/BLOCKHASH or consensus.',
  firstFailures: failures.slice(0, 6),
}
console.log(JSON.stringify(report))
if (compared !== 40 || failures.length || !negativeControl) process.exitCode = 1
