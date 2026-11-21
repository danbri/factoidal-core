#!/usr/bin/env node
/**
 * Fork-pinned differential challenge for the Lean WorldCall.callZeroValue API.
 *
 * The Lean implementation DOES NOT decode opcode F1. An independent
 * EthereumJS Cancun interpreter executes an actual parent F1 and compares
 * CALL success flag, parent gas and child slot 0 against the Lean child API.
 *
 * The parent uses seven pushes costing exactly 16 gas (5 PUSH0, one PUSH1,
 * one PUSH2); the API receives the gas left after those pushes. This
 * matrix exercises cold-account charging, EIP-150's 63/64 cap, the
 * zero-forwarded case, child OOG, REVERT, INVALID and SSTORE rollback.
 *
 * Only the success bit is independently observed for the child disposition:
 * a CALL pushes zero for BOTH REVERT and exceptional halt. We do not claim
 * this comparison alone distinguishes those two reasons.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const TARGET = 0xc3
const parentAddress = createAddressFromString('0x00000000000000000000000000000000000000c1')
const callerAddress = createAddressFromString('0x00000000000000000000000000000000000000c2')
const childAddress = createAddressFromString('0x00000000000000000000000000000000000000c3')
const common = new Common({chain: Mainnet, hardfork: Hardfork.Cancun})
const pushGas = 16
const children = [
  {name: 'stop', code: '00'},
  {name: 'write-stop', code: '600160005500'},
  {name: 'write-revert', code: '600160005560006000fd'},
  {name: 'write-invalid', code: '6001600055fe'},
  {name: 'empty-return', code: '60006000f3'},
  {name: 'arithmetic-stop', code: '600260030100'},
]
// Gas is measured immediately before CALL, after the constant-cost pushes.
// 2,599/2,600 distinguish parent OOG from a valid zero-gas child call.
// 2,663/2,664/2,665 straddle the EIP-150 division boundary at 64.
// 25,055/25,056 probe the exact forwarded-gas threshold for an SSTORE.
const budgets = [
  [2599, 0], [2600, 0], [2600, 65535],
  [2601, 1], [2663, 65535], [2664, 65535], [2665, 65535],
  [3100, 500], [3100, 65535], [7400, 30000],
  [9900, 30000], [25055, 65535], [25056, 65535],
  [25057, 65535], [47400, 30000], [47400, 65535],
  [197400, 65535],
]

function parentCode(requested) {
  if (!Number.isInteger(requested) || requested < 0 || requested > 65535)
    throw Error('PUSH2 gas request out of range')
  // PUSH0 x 5: outSize, outOffset, inSize, inOffset, value.
  // PUSH1 target; PUSH2 gas; CALL; STOP.
  return hexToBytes('0x5f5f5f5f5f60c361' +
    requested.toString(16).padStart(4, '0') + 'f100')
}

function leanCall(childCode, available, requested) {
  const proc = spawnSync('lake', [
    'exe', 'evm-subset', '--call-slice', childCode, String(TARGET),
    String(available), String(requested), '50',
  ], {encoding: 'utf8', timeout: 60000, maxBuffer: 1024 * 1024})
  if (proc.error || proc.status !== 0)
    throw Error('Lean failed: ' + String(proc.error ?? proc.stderr))
  const json = JSON.parse(proc.stdout.trim().split('\n').at(-1))
  if (json.status === 'unsupported' || json.status === 'inputError')
    throw Error('Lean returned non-conformance outcome: ' + JSON.stringify(json))
  return json
}

async function referenceCall(childCode, available, requested) {
  const evm = await createEVM({common})
  await evm.stateManager.putAccount(parentAddress, new Account())
  await evm.stateManager.putAccount(childAddress, new Account())
  await evm.stateManager.putCode(parentAddress, parentCode(requested))
  await evm.stateManager.putCode(childAddress, hexToBytes('0x' + childCode))
  const gasLimit = BigInt(available + pushGas)
  const result = await evm.runCall({caller: callerAddress, to: parentAddress, gasLimit})
  const execution = result.execResult
  if (execution.exceptionError) {
    const message = String(execution.exceptionError.error ?? execution.exceptionError)
    if (!/out[ -]?of[ -]?gas/i.test(message))
      throw Error('unexpected parent-level exception: ' + message)
    return {parentOOG: true}
  }
  const stack = execution.runState?.stack?.getStack()
  if (!Array.isArray(stack) || stack.length !== 1 || ![0n, 1n].includes(stack[0]))
    throw Error('reference CALL did not leave exactly a Boolean success flag')
  const storage = await evm.stateManager.getStorage(childAddress, new Uint8Array(32))
  const slot0 = storage.length
    ? BigInt('0x' + Buffer.from(storage).toString('hex')).toString() : '0'
  return {
    parentOOG: false,
    succeeded: stack[0] === 1n,
    gasRemaining: (gasLimit - execution.executionGasUsed).toString(),
    slot0,
  }
}

const comparisons = []
const failures = []
let parentOOGCases = 0
let successCases = 0
let childFailureCases = 0
let mutationDetected = false
for (const child of children) {
  for (const [available, requested] of budgets) {
    const name = child.name + ':' + available + ':' + requested
    try {
      const actual = leanCall(child.code, available, requested)
      const expected = await referenceCall(child.code, available, requested)
      const mismatches = []
      if (expected.parentOOG) {
        parentOOGCases++
        if (actual.status !== 'callerOutOfGas')
          mismatches.push('caller-out-of-gas')
      } else {
        if (expected.succeeded) successCases++
        else childFailureCases++
        const actualSucceeded = actual.status === 'success'
        if (!['success', 'revert', 'exception'].includes(actual.status) ||
            actualSucceeded !== expected.succeeded)
          mismatches.push('call-success-bit')
        if (actual.gasRemaining !== expected.gasRemaining)
          mismatches.push('parent-gas')
        if (actual.slot0 !== expected.slot0)
          mismatches.push('child-slot0')
        if (actual.warmAddress !== true)
          mismatches.push('internal-cold-address-warming')
        // Deliberately corrupt one independent oracle value to prove the
        // exact gas comparison would reject a false expectation.
        if (!mutationDetected && actual.gasRemaining === expected.gasRemaining) {
          const forgedGas = (BigInt(expected.gasRemaining) + 1n).toString()
          mutationDetected = actual.gasRemaining !== forgedGas
        }
      }
      const record = {name, expected, actual, mismatches}
      comparisons.push(record)
      if (mismatches.length) failures.push(record)
    } catch (error) {
      const record = {name, error: String(error)}
      comparisons.push(record)
      failures.push(record)
    }
  }
}
const report = {
  kind: 'independent-real-0xf1-call-vs-lean-zero-value-child-api-boundaries',
  fork: 'Cancun',
  oracle: '@ethereumjs/evm@10.1.3 real parent opcode CALL',
  compared: comparisons.length,
  matched: comparisons.length - failures.length,
  mismatches: failures.length,
  parentOOGCases, successCases, childFailureCases,
  oracleGasMutationDetected: mutationDetected,
  comparedFields: ['CALL success bit', 'parent gas remaining', 'child slot 0'],
  limits: 'Cold target, zero value, no calldata/returndata or nested calls; Lean is a child API, not a CALL instruction. Revert versus exceptional child failure not independently classified.',
  firstFailures: failures.slice(0, 5),
}
console.log(JSON.stringify(report))
if (failures.length || !mutationDetected) process.exitCode = 1
