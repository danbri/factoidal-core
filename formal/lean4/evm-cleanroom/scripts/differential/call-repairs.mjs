#!/usr/bin/env node
/**
 * Compare caller resumption and static/profile propagation with EthereumJS.
 * The identity precompile has its own boundary check because Lean does not
 * execute it. Build EVMCleanroom.CallBoundaryTests before running this probe.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const parent = createAddressFromString('0x00000000000000000000000000000000000000c1')
const sender = createAddressFromString('0x00000000000000000000000000000000000000c2')
const child = createAddressFromString('0x00000000000000000000000000000000000000c3')
const identity = createAddressFromString('0x0000000000000000000000000000000000000004')
const gasLimit = 100000n
const zeroCall = '5f5f5f5f5f60c3617530f100'
const write = '600160005500'
const clzWrite = '5f1e5f5500'
const fixtures = [
  {
    name: 'self-call', parentCode: '346011575f5f5f5f600160c1617530f1005b602a5f5500',
    balance: 1n, observed: parent, bit: '1', slot0: '42',
  },
  {
    name: 'static-parent', parentCode: zeroCall, childCode: write, isStatic: true,
    bit: '0', slot0: '0',
  },
  {
    name: 'mutable-parent', parentCode: zeroCall, childCode: write, bit: '1', slot0: '1',
  },
  {
    name: 'osaka-child', parentCode: zeroCall, childCode: clzWrite,
    hardfork: Hardfork.Osaka, bit: '1', slot0: '256',
  },
  {
    name: 'osaka-child-with-value', parentCode: '5f5f5f5f600160c3617530f100',
    childCode: clzWrite, balance: 1n, hardfork: Hardfork.Osaka, bit: '1', slot0: '256',
  },
  {
    name: 'identity-zero-gas', parentCode: '5f5f5f5f5f60045ff100', observed: identity,
    bit: '0', slot0: '0', boundary: true,
  },
]

function leanObservations() {
  const proc = spawnSync('lake', [
    '-d', 'evm-cleanroom', 'env', 'lean', '--run',
    fileURLToPath(new URL('CallRepairsProbe.lean', import.meta.url)),
  ], {
    cwd: new URL('../../../', import.meta.url),
    encoding: 'utf8',
    timeout: 60000,
    maxBuffer: 1024 * 1024,
  })
  if (proc.error || proc.status !== 0)
    throw Error('Lean probe failed: ' + String(proc.error ?? (proc.stdout + proc.stderr)))
  return JSON.parse(proc.stdout.trim().split('\n').at(-1))
}

async function reference(fixture) {
  const common = new Common({chain: Mainnet, hardfork: fixture.hardfork ?? Hardfork.Cancun})
  const evm = await createEVM({common})
  await evm.stateManager.putAccount(parent, new Account(0n, fixture.balance ?? 0n))
  await evm.stateManager.putCode(parent, hexToBytes('0x' + fixture.parentCode))
  if (fixture.childCode) {
    await evm.stateManager.putAccount(child, new Account())
    await evm.stateManager.putCode(child, hexToBytes('0x' + fixture.childCode))
  }
  const {execResult} = await evm.runCall({
    caller: sender, to: parent, gasLimit, isStatic: fixture.isStatic ?? false,
  })
  assert.equal(execResult.exceptionError, undefined, 'reference parent should stop')
  const stack = execResult.runState?.stack?.getStack()
  assert.ok(Array.isArray(stack), 'reference parent stack is missing')
  const stored = await evm.stateManager.getStorage(fixture.observed ?? child, new Uint8Array(32))
  const parentAccount = await evm.stateManager.getAccount(parent)
  return {
    status: 'stopped',
    stack: stack.map(String).reverse(),
    gasRemaining: (gasLimit - execResult.executionGasUsed).toString(),
    slot0: stored.length ? BigInt('0x' + Buffer.from(stored).toString('hex')).toString() : '0',
    parentBalance: (parentAccount?.balance ?? 0n).toString(),
  }
}

const actual = leanObservations()
const comparisons = []
const boundaries = []
const failures = []
for (const fixture of fixtures) {
  const {name} = fixture
  const measured = actual[name]
  try {
    const expected = await reference(fixture)
    assert.deepEqual(expected.stack, [fixture.bit])
    assert.equal(expected.slot0, fixture.slot0)
    if (fixture.boundary) {
      boundaries.push({name, expected, actual: measured})
      assert.deepEqual(measured, {
        status: 'indeterminate', reason: 'EVMCleanroom.Error.unsupportedFork',
      })
    } else {
      comparisons.push({name, expected, actual: measured})
      assert.deepEqual(measured, expected)
    }
  } catch (error) {
    failures.push({name, error: String(error)})
  }
}
console.log(JSON.stringify({
  oracle: '@ethereumjs/evm@10.1.3 runCall',
  compared: comparisons.length,
  matched: comparisons.filter(({name}) => !failures.some(failure => failure.name === name)).length,
  comparisons,
  boundaries,
  failures,
}))
if (failures.length) process.exitCode = 1
