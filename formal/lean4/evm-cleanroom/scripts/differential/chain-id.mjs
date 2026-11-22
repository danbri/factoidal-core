#!/usr/bin/env node
/**
 * EIP-1344 CHAINID (0x46) independent single-frame differential.
 * EthereumJS Mainnet Shanghai fixes chainId=1. Lean receives 1 as an
 * explicit, unauthenticated input. These cases do not authenticate
 * a signed transaction, block header, provider or consensus state.
 *
 * Run from formal/lean4/evm-cleanroom after npm ci under scripts/differential:
 *   node scripts/differential/chain-id.mjs
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { hexToBytes } from '@ethereumjs/util'

const common = new Common({ chain: Mainnet, hardfork: Hardfork.Shanghai })
const evm = await createEVM({ common })
const examples = [
  { name: 'only', hex: '4600', gas: [0, 1, 2, 3, 30] },
  { name: 'two', hex: '464600', gas: [2, 3, 4, 5, 30] },
  { name: 'pop', hex: '465000', gas: [2, 3, 4, 5, 30] },
  { name: 'compare-one', hex: '6001461400', gas: [6, 7, 8, 9, 30] },
  { name: 'store-low-byte', hex: '4660005300', gas: [8, 9, 10, 11, 30] },
  { name: 'chain-in-arithmetic', hex: '6002460100', gas: [6, 7, 8, 9, 30] },
]
function lean(code, gas, chainId = '1') {
  const p = spawnSync('lake',
    ['exe', 'evm-subset', '--chainid', code, String(gas), '50', chainId],
    { encoding: 'utf8', timeout: 60000, maxBuffer: 1024 * 1024 })
  if (p.error || p.status !== 0)
    throw Error('Lean CLI failed: ' + String(p.error ?? p.stderr))
  const line = p.stdout.trim().split('\n').at(-1)
  return JSON.parse(line)
}
async function reference(code, gas) {
  const r = await evm.runCode({
    code: hexToBytes('0x' + code),
    gasLimit: BigInt(gas),
  })
  const error = String(r.exceptionError?.error ?? '')
  if (error) {
    if (!/out of gas/i.test(error))
      throw Error('unexpected oracle exception ' + error)
    return { status: 'error', error: 'outOfGas' }
  }
  return {
    status: 'ok',
    stack: r.runState.stack.getStack().map(String).reverse(),
    gasRemaining: String(BigInt(gas) - r.executionGasUsed),
  }
}

let compared = 0
const failures = []
for (const example of examples) {
  for (const gas of example.gas) {
    const id = example.name + ':' + gas
    compared++
    try {
      const actual = lean(example.hex, gas)
      const expected = await reference(example.hex, gas)
      const fields = expected.status === 'error'
        ? ['status', 'error'] : ['status', 'gasRemaining', 'stack']
      const diffs = fields.filter(f =>
        JSON.stringify(actual[f]) !== JSON.stringify(expected[f]))
      if (diffs.length) failures.push({ id, diffs, expected, actual })
    } catch (e) { failures.push({ id, error: String(e) }) }
  }
}
// The comparator must detect an intentionally false chain context, not
// merely agree on a constant zero or on program gas with no opcode value.
const oracleOne = await reference('4600', 30)
const wrongChain = lean('4600', 30, '2')
const negativeControl =
  oracleOne.stack?.[0] === '1' &&
  wrongChain.stack?.[0] === '2' &&
  wrongChain.stack?.[0] !== oracleOne.stack[0]

const report = {
  schemaVersion: 1,
  kind: 'EIP-1344 CHAINID actual-opcode differential',
  executionContext: 'synthetic Mainnet Shanghai, chainId 1',
  oracle: '@ethereumjs/evm@10.1.3',
  compared, matched: compared - failures.length, mismatches: failures.length,
  negativeControl,
  fields: ['status', 'exception kind', 'full stack', 'remaining gas'],
  limitations: 'Frame CHAINID is externally supplied; no signed transaction or block/consensus authentication; preShanghai profile refuses CHAINID.',
  firstFailures: failures.slice(0, 8),
}
console.log(JSON.stringify(report))
if (compared !== 30 || failures.length || !negativeControl) process.exitCode = 1
