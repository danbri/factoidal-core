import { execFile } from 'node:child_process'
import { promisify } from 'node:util'
import { hexData, object, parseUniqueJson } from './rpc-client.mjs'

const execute = promisify(execFile)
export const MAX_INPUT_BYTES = 48 * 1024 // Also bounds each process argument.
const MAX_OUTPUT_BYTES = 4096 // The Lean frame return/revert observation limit.
const FRAME_FLAG = '--pure-frame-call'
const COMPARISON_CONTEXT = 'zero-value-context-free-v1'

function admission(code, address) {
  if (code === '0x') return 'empty-runtime-code'
  if (BigInt(address) <= 0xffffn) return 'address-in-low-precompile-range'
  if (code.length > 2 + MAX_INPUT_BYTES * 2) return 'runtime-code-exceeds-comparison-limit'
  return null
}

function frameOutcome(snapshot) {
  if (!object(snapshot) || snapshot.schemaVersion !== 1 || snapshot.memoryTruncated !== false ||
      snapshot.returnDataTruncated !== false || typeof snapshot.returnDataHex !== 'string') return null
  if (!['stopped', 'returned', 'reverted'].includes(snapshot.status)) return null
  const dataHex = `0x${snapshot.returnDataHex.toLowerCase()}`
  if (!hexData(dataHex) || dataHex.length > 2 + MAX_OUTPUT_BYTES * 2) return null
  if (snapshot.returnDataLength !== String((dataHex.length - 2) / 2)) return null
  if (snapshot.status === 'stopped' && dataHex !== '0x') return null
  return { kind: snapshot.status === 'reverted' ? 'revert' : 'return', dataHex }
}

export async function compareCall({ address, data, code, codeSource, remote, leanExe, gas, fuel, timeoutMs }) {
  if (!leanExe) return { status: 'not-requested' }
  const execution = { engine: `evm-subset ${FRAME_FLAG}`, codeSource, gas, fuel }
  const unavailable = reason => ({ status: 'unverified', reason, ...execution })
  if (remote.kind === 'rpc-error') return unavailable('provider-return-or-revert-bytes-unavailable')
  if (remote.dataHex.length > 2 + MAX_OUTPUT_BYTES * 2) return unavailable('provider-data-exceeds-comparison-limit')
  const refusal = admission(code, address)
  if (refusal) return unavailable(refusal)

  let snapshot
  try {
    const { stdout } = await execute(leanExe, [FRAME_FLAG, code, data, gas, fuel], {
      encoding: 'buffer', timeout: timeoutMs, maxBuffer: 32 * 1024, killSignal: 'SIGKILL',
    })
    snapshot = parseUniqueJson(stdout)
  } catch {
    return unavailable('frame-command-failed-or-malformed-output')
  }
  if (!object(snapshot) || snapshot.comparisonContext !== COMPARISON_CONTEXT) {
    return unavailable('frame-comparison-context-unrecognised')
  }
  execution.comparisonContext = snapshot.comparisonContext
  if (snapshot.status === 'unsupported') {
    return unavailable(snapshot.error === 'framePolicyViolation' ? 'frame-policy-violation' : 'frame-execution-unsupported')
  }
  if (snapshot.status === 'exceptional') return unavailable('frame-execution-exceptional')
  const local = frameOutcome(snapshot)
  if (!local) return unavailable('frame-output-incomplete-or-unrecognised')
  const matched = local.kind === remote.kind && local.dataHex === remote.dataHex.toLowerCase()
  return { status: matched ? 'match' : 'mismatch', ...execution, local }
}
