#!/usr/bin/env node
/**
 * Independently compare executable Lean one-account storage execution against
 * pinned @ethereumjs/evm 10.1.3 (Prague), including signed refund counters.
 *
 * This is NOT an EELS state-root replay or a proof of all Ethereum semantics.
 * Run after npm ci --prefix scripts/differential and lake build.
 */
import { spawnSync } from 'node:child_process'
import { mkdtempSync, rmSync, readFileSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const hexByte = n => n.toString(16).padStart(2, '0')
const store = n => '60' + hexByte(n) + '600055'
const load = '600054'
const records = []
const seen = new Set()
function add(kind, code, original, gas = 150000) {
  const key = [code, original, gas].join(':')
  if (seen.has(key)) return
  seen.add(key)
  records.push({ kind, code, original, gas, fuel: 40, key: 0 })
}

// Exhaustive short "write history" shapes, plus warm reads.
const sequences = [
  [0], [1], [2], [3], [7],
  [0, 1], [1, 0], [1, 1], [1, 2], [2, 1], [7, 0],
  [0, 1, 0], [1, 2, 1], [2, 0, 2], [0, 0, 1],
  [1, 0, 1], [1, 0, 2], [2, 7, 0, 2],
  [0, 1, 2, 0], [7, 0, 7, 1], [1, 1, 0, 0]
]
for (const original of [0, 1, 7, 255]) {
  add('cold-load', load + '00', original)
  add('warm-load', load + load + '00', original)
  for (const seq of sequences) {
    const program = seq.map(store).join('')
    add('writes', program + '00', original)
    if (seq.length <= 2) add('read-after-writes', program + load + '00', original)
  }
}
if (records.length < 100) throw Error('insufficient distinct storage histories')

const temp = mkdtempSync(join(tmpdir(), 'lean-evm-storage-diff-'))
try {
  const inputFile = join(temp, 'cases.tsv')
  const data = records.map(r =>
    [r.code, r.gas, r.fuel, r.key, r.original].join('\t')).join('\n') + '\n'
  writeFileSync(inputFile, data)
  const lean = spawnSync('lake', ['exe', 'evm-subset', '--storage-batch', inputFile], {
    encoding: 'utf8', timeout: 300000, maxBuffer: 8 * 1024 * 1024
  })
  if (lean.error || lean.status !== 0) {
    throw Error('Lean CLI failed: ' + String(lean.error ?? lean.stderr).slice(-4000))
  }
  const outputs = lean.stdout.trimEnd().split('\n').map(line => JSON.parse(line))
  if (outputs.length !== records.length) {
    throw Error('Lean output count ' + outputs.length + ' differs from records ' + records.length)
  }

  const common = new Common({ chain: Mainnet, hardfork: Hardfork.Prague })
  const address = createAddressFromString('0x00000000000000000000000000000000000000c0')
  const keyBytes = new Uint8Array(32)
  const mismatches = []
  for (let i = 0; i < records.length; i++) {
    const c = records[i], actual = outputs[i]
    const evm = await createEVM({ common })
    await evm.stateManager.putAccount(address, new Account())
    if (c.original !== 0) {
      await evm.stateManager.putStorage(address, keyBytes, new Uint8Array([c.original]))
    }
    const result = await evm.runCode({
      to: address, code: hexToBytes('0x' + c.code),
      gasLimit: BigInt(c.gas)
    })
    const error = result.exceptionError
    if (error) {
      mismatches.push({ index: i, case: c, kind: 'oracle-exception',
        error: String(error.error ?? error), lean: actual })
      continue
    }
    const bytes = await evm.stateManager.getStorage(address, keyBytes)
    const value = bytes.length
      ? BigInt('0x' + Buffer.from(bytes).toString('hex')).toString() : '0'
    const expected = {
      status: 'ok',
      current: value,
      original: String(c.original),
      gasRemaining: (BigInt(c.gas) - result.executionGasUsed).toString(),
      refund: (result.gasRefund ?? 0n).toString()
    }
    const keys = Object.keys(expected)
    const different = keys.filter(k => actual[k] !== expected[k])
    if (different.length) {
      mismatches.push({index: i, case: c, kind: 'difference', different,
        expected, lean: actual})
    }
  }
  const summary = {
    kind: 'independent-one-account-storage-differential',
    oracle: '@ethereumjs/evm@10.1.3 Prague',
    compared: records.length,
    matched: records.length - mismatches.length,
    mismatches: mismatches.length,
    observedFields: ['current', 'original', 'gasRemaining', 'refund'],
    note: 'single account and slot, no nested calls or transaction settlement',
    firstMismatches: mismatches.slice(0, 8)
  }
  console.log(JSON.stringify(summary))
  if (mismatches.length) process.exitCode = 1
} finally {
  rmSync(temp, {recursive: true, force: true})
}
