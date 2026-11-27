/**
 * Shared multi-account differential harness for the world-aware Lean dispatcher
 * (`evm-subset --world-batch`) against @ethereumjs/evm 10.1.3 used only as a
 * test oracle. Nothing here supplies a runtime answer to the Lean code.
 *
 * Semantic reference: ethereum/execution-specs, forks/cancun and forks/prague
 * vm/instructions/{environment,storage,memory,block,system}.py.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { mkdtempSync, readFileSync, writeFileSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { isDeepStrictEqual } from 'node:util'
import { fileURLToPath } from 'node:url'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createEVM } from '@ethereumjs/evm'
import { Account, bigIntToUnpaddedBytes, createAddressFromString, hexToBytes } from '@ethereumjs/util'

export const lockSha256 = 'cc95a62e125486d2de9a28cb5fc61c098b955aa22c2dd0b3dc0b19f2df770425'
assert.equal(createHash('sha256').update(readFileSync(new URL('./package-lock.json', import.meta.url)))
  .digest('hex'), lockSha256, 'EthereumJS dependency lock')

export const defaultExecutable = fileURLToPath(new URL('../../.lake/build/bin/evm-subset', import.meta.url))
export const CALLER = 0xc2
export const maxWord = (1n << 256n) - 1n
export const hex = data => Buffer.from(data).toString('hex')
export const word = n => BigInt(n).toString(16).padStart(64, '0')
export const addr = n => createAddressFromString('0x' + BigInt(n).toString(16).padStart(40, '0'))

/** Minimal PUSH encoder (PUSH0 for zero). */
export function push(n) {
  const value = BigInt(n)
  assert(value >= 0n && value <= maxWord)
  if (value === 0n) return '5f'
  const raw = value.toString(16)
  const even = raw.padStart(raw.length + raw.length % 2, '0')
  return (0x5f + even.length / 2).toString(16) + even
}
/** CALL-family invocation with all memory windows empty unless supplied. */
export function call(op, target, {value = 0, gas = 0xffff, inOff = 0, inSize = 0, outOff = 0, outSize = 0} = {}) {
  const ops = {call: 'f1', callcode: 'f2', delegatecall: 'f4', staticcall: 'fa'}
  const args = [outSize, outOff, inSize, inOff]
  if (op === 'call' || op === 'callcode') args.push(value)
  return [...args, target, gas].map(push).join('') + ops[op]
}
export const sstore = (slot, expr) => expr + push(slot) + '55'
/** Store the current top of stack in storage slot `slot`. */
export const keep = slot => push(slot) + '55'
export const ret = (offset, size) => push(size) + push(offset) + 'f3'
export const revert = (offset = 0, size = 0) => push(size) + push(offset) + 'fd'

const forks = {
  shanghaiPlus: Hardfork.Shanghai,
  cancunPlus: Hardfork.Cancun,
  osaka: Hardfork.Osaka,
}
const exceptionNames = new Map([
  ['out of gas', 'outOfGas'], ['invalid opcode', 'invalidOpcode'],
  ['static state change', 'writeProtection'], ['stack underflow', 'stackUnderflow'],
  ['stack overflow', 'stackOverflow'], ['invalid JUMP', 'invalidJump'],
  ['code store out of gas', 'outOfGas'], ['code size to deposit exceeds maximum code size', 'outOfGas'],
  ['invalid EOF format', 'invalidCode'], ['initcode exceeds max initcode size', 'outOfGas'],
  ['value overflow', 'valueOverflow'],
])

/** One compact line of `--world-batch` arguments. */
function leanLine(c) {
  const list = xs => xs.length ? xs.map(x => BigInt(x).toString(16)).join(',') : '-'
  const accounts = c.accounts.map(a => {
    const slots = Object.entries(a.storage ?? {}).map(([k, v]) => BigInt(k).toString(16) + '=' + BigInt(v).toString(16)).join(';')
    return [BigInt(a.address).toString(16), String(a.balance ?? 0), String(a.nonce ?? 0), a.code ?? '',
      a.hasStorage ? '1' : '0', slots || '-'].join(':')
  })
  return [c.profile, String(c.gas), String(c.fuel ?? 2000), c.readOnly ? '1' : '0', String(c.number ?? 0),
    (c.hashes ?? []).length ? c.hashes.map(h => h.replace(/^0x/, '')).join(',') : '-',
    BigInt(c.entry).toString(16), list(c.prewarm ?? []), list(c.observe), ...accounts].join(' ')
}

/** Run every case in one Lean process; returns parsed JSON per case. */
export function runLean(executable, cases, {keccak = true} = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'evm-world-'))
  try {
    const path = join(dir, 'cases.txt')
    writeFileSync(path, cases.map(leanLine).join('\n') + '\n')
    const args = [...(keccak ? ['--dangerously-enable-unverified-keccak'] : []), '--world-batch', path]
    const out = spawnSync(executable, args, {encoding: 'utf8', timeout: 600000, maxBuffer: 256 * 1024 * 1024})
    assert.equal(out.status, 0, 'Lean world batch exit: ' + out.stderr)
    const rows = out.stdout.trim().split('\n').map(line => JSON.parse(line))
    assert.equal(rows.length, cases.length, 'one Lean result per case')
    return rows
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}

/** Project a Lean row onto the fields the oracle can observe. */
export function projectLean(c, row) {
  if (row.status === 'indeterminate' || row.status === 'inputError') return {status: row.status, reason: row.reason}
  const out = {status: row.status, gasRemaining: row.gasRemaining, accounts: row.accounts.map(a => ({
    address: a.address, balance: a.balance, nonce: a.nonce, codeHex: a.codeHex, storage: a.storage,
    ...(c.observeWarm === false ? {} : {warm: a.warm}),
  }))}
  if (row.status === 'exceptional') out.reason = row.reason
  else {
    out.stack = row.stack
    out.returnBytesHex = row.returnBytesHex
    out.memoryHex = row.memoryHex
  }
  if (c.observeDestructs) out.selfDestructed = row.accounts.filter(a => a.selfDestructed).map(a => a.address)
  return out
}

/** Execute the same entry frame in EthereumJS and project the same fields. */
export async function runOracle(c) {
  const common = new Common({chain: Mainnet, hardfork: forks[c.profile]})
  const hashes = (c.hashes ?? []).map(h => BigInt('0x' + h.replace(/^0x/, '')))
  const number = BigInt(c.number ?? 0)
  const blockchain = {
    getBlock: async n => {
      const back = number - BigInt(n)
      assert(back >= 1n && back <= BigInt(hashes.length), 'oracle asked for an unsupplied block hash')
      return {hash: () => hexToBytes('0x' + word(hashes[hashes.length - Number(back)]))}
    },
    shallowCopy() { return this },
  }
  const evm = await createEVM({common, blockchain})
  for (const target of evm.precompiles.keys()) evm.journal.addAlwaysWarmAddress(target)
  for (const a of c.prewarm ?? []) evm.journal.addAlwaysWarmAddress(addr(a).toString())
  for (const a of c.accounts) {
    await evm.stateManager.putAccount(addr(a.address), new Account(BigInt(a.nonce ?? 0), BigInt(a.balance ?? 0)))
    if (a.code) await evm.stateManager.putCode(addr(a.address), hexToBytes('0x' + a.code))
    for (const [k, v] of Object.entries(a.storage ?? {}))
      await evm.stateManager.putStorage(addr(a.address), hexToBytes('0x' + word(k)), bigIntToUnpaddedBytes(BigInt(v)))
  }
  let lastOpcode
  evm.events.on('step', (step, resolve) => {
    if (step.depth === 0) lastOpcode = step.opcode.code
    resolve?.()
  })
  const block = {header: {number, coinbase: addr(0), timestamp: 0n, gasLimit: 30000000n, baseFeePerGas: 7n,
    prevRandao: new Uint8Array(32), getBlobGasPrice: () => 1n}}
  const gasLimit = BigInt(c.gas)
  const {execResult: ex} = await evm.runCall({
    caller: addr(CALLER), origin: addr(CALLER), to: addr(c.entry), gasLimit, isStatic: !!c.readOnly,
    skipNonceIncrement: true, block,
  })
  const error = ex.exceptionError?.error
  const status = error === 'revert' ? 'reverted' : error ? 'exceptional' :
    (lastOpcode === 0xf3 ? 'returned' : 'stopped')
  const out = {status, gasRemaining: String(gasLimit - ex.executionGasUsed), accounts: []}
  for (const a of c.observe) {
    const who = addr(a)
    const account = await evm.stateManager.getAccount(who)
    const code = await evm.stateManager.getCode(who)
    const storage = []
    for (let k = 0; k < 4; k++) {
      const v = await evm.stateManager.getStorage(who, hexToBytes('0x' + word(k)))
      storage.push(v.length ? BigInt('0x' + hex(v)).toString() : '0')
    }
    out.accounts.push({address: String(BigInt(a)), balance: String(account?.balance ?? 0n),
      nonce: String(account?.nonce ?? 0n), codeHex: hex(code), storage,
      ...(c.observeWarm === false ? {} : {warm: evm.journal.isWarmedAddress(who.bytes)})})
  }
  if (status === 'exceptional') {
    assert(exceptionNames.has(error), 'unmapped EthereumJS exception: ' + error)
    out.reason = exceptionNames.get(error)
  } else {
    const {memory, memoryWordCount, stack} = ex.runState
    out.stack = stack.peek(stack.length).map(String)
    out.returnBytesHex = hex(ex.returnValue)
    out.memoryHex = hex(memory.read(0, Number(32n * memoryWordCount))).slice(0, 8192)
  }
  if (c.observeDestructs) {
    const set = ex.selfdestruct ?? new Map()
    out.selfDestructed = c.observe.filter(a => [...set.keys()].some(k => BigInt(k) === BigInt(a))).map(a => String(BigInt(a)))
  }
  return out
}

/** Compare every case; returns a summary with first failures. */
export async function compareAll(executable, cases, extra = {}) {
  const leanRows = runLean(executable, cases)
  const failures = []
  let matched = 0
  for (const [i, c] of cases.entries()) {
    const expected = c.expectIndeterminate ? {status: 'indeterminate', reason: c.expectIndeterminate} : await runOracle(c)
    const actual = projectLean(c, leanRows[i])
    if (c.expect) for (const [k, v] of Object.entries(c.expect))
      assert(isDeepStrictEqual(expected[k], v), c.id + ' oracle self-check ' + k + ': ' + JSON.stringify(expected[k]))
    if (isDeepStrictEqual(expected, actual)) matched++
    else failures.push({id: c.id, expected, actual})
  }
  return {compared: cases.length, matched, mismatches: failures.length, firstFailures: failures.slice(0, 5), ...extra}
}
