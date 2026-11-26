#!/usr/bin/env node
/** Cancun EIP-7516 opcode-only differential against independently implemented
 * EthereumJS 10.1.3. Both sides get the same synthetic blob price from the
 * harness. Neither side authenticates a block or derives its blob base fee. */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { hexToBytes } from '@ethereumjs/util'

const evm = await createEVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Cancun }) })
const fee = 7n
const block = { header: { getBlobGasPrice: () => fee } }
function lean(code, gas, value = fee, profile = 'cancun') {
  const p = spawnSync('lake', ['exe', 'evm-subset', '--blobbasefee', code,
    String(gas), '60', String(value), profile],
    { encoding: 'utf8', timeout: 60000, maxBuffer: 1024 * 1024 })
  if (p.status !== 0 || p.error) throw Error('Lean failed: ' + String(p.error ?? p.stderr))
  return JSON.parse(p.stdout.trim().split('\n').at(-1))
}
async function reference(code, gas) {
  const r = await evm.runCode({ code: hexToBytes('0x' + code), gasLimit: BigInt(gas), block })
  const fault = String(r.exceptionError?.error ?? '')
  if (fault) {
    if (!/out of gas/i.test(fault)) throw Error('Unexpected reference fault: ' + fault)
    return { status: 'error', error: 'outOfGas' }
  }
  const size = Number(r.runState.memoryWordCount * 32n)
  if (size > 4096) throw Error('Reference memory limit exceeded')
  return { status: 'ok', gasRemaining: String(BigInt(gas) - r.executionGasUsed),
    stack: r.runState.stack.getStack().map(String).reverse(), memorySizeBytes: String(size),
    memoryHex: Buffer.from(r.runState.memory.read(0, size)).toString('hex') }
}
const examples = [
  { id: 'push', code: '4a00' }, { id: 'pop', code: '4a5000' },
  { id: 'memory-byte', code: '4a60005300' }, { id: 'add', code: '60014a0100' },
  { id: 'iszero', code: '4a1500' }, { id: 'twice', code: '4a4a00' },
  { id: 'add-two', code: '4a60010100' },
]
const gases = [1, 2, 4, 7, 11, 100]
function differingFields(a, b) {
  const fields = b.status === 'error' ? ['status', 'error']
    : ['status', 'gasRemaining', 'stack', 'memorySizeBytes', 'memoryHex']
  return fields.filter(k => JSON.stringify(a[k]) !== JSON.stringify(b[k]))
}
let compared = 0
const failures = []
for (const x of examples) for (const gas of gases) {
  compared++
  try {
    const a = lean(x.code, gas), b = await reference(x.code, gas)
    const mismatch = differingFields(a, b)
    if (mismatch.length) failures.push({ id: x.id + ':' + gas, mismatch, actual: a, expected: b })
  } catch (e) { failures.push({ id: x.id + ':' + gas, error: String(e) }) }
}
const expected = await reference('4a00', 100)
const forged = lean('4a00', 100, fee + 1n)
const baseline = lean('4a00', 100)
const forgedGasOracle = { ...expected, gasRemaining: '97' }
const old = lean('4a00', 100, fee, 'shanghai')
const negativeControls = {
  changedFeeDetected: expected.stack?.[0] === String(fee) &&
    forged.stack?.[0] !== expected.stack?.[0],
  changedGasDetected: expected.gasRemaining === '98' &&
    differingFields(baseline, expected).length === 0 &&
    differingFields(baseline, forgedGasOracle).includes('gasRemaining'),
}
const report = { schemaVersion: 1, reference: '@ethereumjs/evm@10.1.3 Cancun',
  compared, matched: compared - failures.length, mismatches: failures.length,
  negativeControls, ambiguousOldForkRefused:
    old.status === 'error' && old.error === 'unsupportedFork',
  observedFields: ['status', 'error', 'gasRemaining', 'stack', 'memorySizeBytes', 'memoryHex'],
  limitations: 'Synthetic blob fee; no authenticated excessBlobGas, blob transaction, KZG, EELS full transition or beacon consensus.',
  failures: failures.slice(0, 8) }
console.log(JSON.stringify(report))
if (compared !== 42 || failures.length || !report.ambiguousOldForkRefused ||
  !Object.values(negativeControls).every(Boolean)) process.exitCode = 1
