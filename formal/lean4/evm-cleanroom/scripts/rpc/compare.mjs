import { execFile } from 'node:child_process'
import { promisify } from 'node:util'
import { hexData, object } from './rpc-client.mjs'

const execute = promisify(execFile)
export const MAX_INPUT_BYTES = 48 * 1024 // Also bounds each process argument.
const MAX_OUTPUT_BYTES = 4096 // The --frame-call return/revert observation limit.

// This is a conservative admission scan; Lean performs the execution.
// Include only context-free opcodes implemented in the local frame slice.
const PURE_OPCODES = new Set([
  0x00, // STOP
  0x01, 0x02, 0x03, 0x04, // ADD, MUL, SUB, DIV
  0x10, 0x11, 0x14, 0x15, // LT, GT, EQ, ISZERO
  0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, // AND, OR, XOR, NOT, BYTE, SHL, SHR
  0x35, 0x36, // CALLDATALOAD, CALLDATASIZE
  0x50, 0x51, 0x52, 0x53, // POP, MLOAD, MSTORE, MSTORE8
  0x56, 0x57, 0x58, 0x59, 0x5b, // JUMP, JUMPI, PC, MSIZE, JUMPDEST
  0xf3, 0xfd, // RETURN, REVERT
])

function admission(code, address) {
  if (code === '0x') return 'empty-runtime-code'
  if (BigInt(address) <= 0xffffn) return 'address-in-low-precompile-range'
  if (code.length > 2 + MAX_INPUT_BYTES * 2) return 'runtime-code-exceeds-comparison-limit'
  const bytes = Buffer.from(code.slice(2), 'hex')
  for (let pc = 0; pc < bytes.length; pc++) {
    const opcode = bytes[pc]
    if (0x5f <= opcode && opcode <= 0x7f) {
      const immediateBytes = opcode - 0x5f
      if (pc + immediateBytes >= bytes.length) return 'incomplete-push-immediate'
      pc += immediateBytes
    } else if (!(0x80 <= opcode && opcode <= 0x9f) && !PURE_OPCODES.has(opcode)) {
      return 'opcode-outside-context-free-subset'
    }
  }
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
  const execution = { engine: 'evm-subset --frame-call', codeSource, gas, fuel }
  const unavailable = reason => ({ status: 'unverified', reason, ...execution })
  if (remote.kind === 'rpc-error') return unavailable('provider-return-or-revert-bytes-unavailable')
  if (remote.dataHex.length > 2 + MAX_OUTPUT_BYTES * 2) return unavailable('provider-data-exceeds-comparison-limit')
  const refusal = admission(code, address)
  if (refusal) return unavailable(refusal)

  let snapshot
  try {
    const { stdout } = await execute(leanExe, ['--frame-call', code, data, gas, fuel], {
      timeout: timeoutMs, maxBuffer: 32 * 1024, killSignal: 'SIGKILL',
    })
    snapshot = JSON.parse(stdout)
  } catch {
    return unavailable('frame-command-failed-or-malformed-output')
  }
  if (snapshot?.status === 'unsupported') return unavailable('frame-execution-unsupported')
  if (snapshot?.status === 'exceptional') return unavailable('frame-execution-exceptional')
  const local = frameOutcome(snapshot)
  if (!local) return unavailable('frame-output-incomplete-or-unrecognised')
  const matched = local.kind === remote.kind && local.dataHex === remote.dataHex.toLowerCase()
  return { status: matched ? 'match' : 'mismatch', ...execution, local }
}
