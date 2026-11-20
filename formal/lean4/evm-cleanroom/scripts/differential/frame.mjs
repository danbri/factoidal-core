#!/usr/bin/env node
/**
 * Cross-implementation comparison of single-frame RETURN, REVERT and
 * exceptional rollback, using EthereumJS runCall (which creates a real
 * state-manager checkpoint and reverts it on exceptional outcomes).
 *
 * This is not an official EELS fixture or a full Ethereum transaction replay.
 */
import { spawnSync } from 'node:child_process'
import { createEVM } from '@ethereumjs/evm'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { Account, createAddressFromString, hexToBytes } from '@ethereumjs/util'

const address = createAddressFromString('0x00000000000000000000000000000000000000c0')
const caller = createAddressFromString('0x00000000000000000000000000000000000000c1')
const keyBytes = new Uint8Array(32)
const cases = [
  { id:'simple-stop', code:'00', kind:'stopped', original:0, gas:30000 },
  { id:'return-no-effects', code:'60006000f3', kind:'returned', original:0, gas:30000 },
  { id:'revert-no-effects', code:'60006000fd', kind:'reverted', original:0, gas:30000 },
  { id:'store-then-return', code:'600160005560006000f3', kind:'returned', original:0, gas:30000 },
  { id:'store-then-revert', code:'600160005560006000fd', kind:'reverted', original:0, gas:30000 },
  { id:'clear-then-return', code:'600060005560006000f3', kind:'returned', original:7, gas:30000 },
  { id:'clear-then-revert', code:'600060005560006000fd', kind:'reverted', original:7, gas:30000 },
  { id:'memory-return-byte', code:'602a60005360016000f3', kind:'returned', original:0, gas:30000 },
  { id:'memory-revert-byte', code:'602a60005360016000fd', kind:'reverted', original:0, gas:30000 },
  { id:'write-then-underflow', code:'600160005501', kind:'exceptional', original:0, gas:30000 },
  { id:'write-then-out-of-gas', code:'60016000556001600055', kind:'exceptional', original:0, gas:23000 },
  { id:'write-restore-revert', code:'6001600055600060005560006000fd', kind:'reverted', original:0, gas:50000 },
  { id:'write-restore-return', code:'6001600055600060005560006000f3', kind:'returned', original:0, gas:50000 }
]
const discrepancies = []
const common = new Common({ chain: Mainnet, hardfork: Hardfork.Prague })

for (const c of cases) {
  const lean = spawnSync('lake', ['exe', 'evm-subset', '--frame-storage',
    c.code, String(c.gas), '30', '0', String(c.original)], {
    encoding: 'utf8', timeout: 60000
  })
  if (lean.error || lean.status !== 0) {
    throw Error('Lean failed for ' + c.id + ': ' + String(lean.error ?? lean.stderr))
  }
  const actual = JSON.parse(lean.stdout.trim())
  const evm = await createEVM({ common })
  await evm.stateManager.putAccount(address, new Account())
  await evm.stateManager.putCode(address, hexToBytes('0x' + c.code))
  if (c.original !== 0) {
    await evm.stateManager.putStorage(address, keyBytes, new Uint8Array([c.original]))
  }
  const res = await evm.runCall({to:address,caller,gasLimit: BigInt(c.gas)})
  const exec = res.execResult
  const err = String(exec.exceptionError?.error ?? '').toLowerCase()
  const disposition = err.includes('revert') ? 'reverted' :
    err ? 'exceptional' : c.kind
  const storageBytes = await evm.stateManager.getStorage(address, keyBytes)
  const current = storageBytes.length
    ? BigInt('0x' + Buffer.from(storageBytes).toString('hex')).toString() : '0'
  const expected = {
    status: disposition,
    gasRemaining: (BigInt(c.gas) - exec.executionGasUsed).toString(),
    current,
    refund: (exec.gasRefund ?? 0n).toString()
  }
  if (disposition==='returned' || disposition==='reverted') {
    expected.returnDataHex = Buffer.from(exec.returnValue).toString('hex')
  }
  const keys=Object.keys(expected)
  const fields=keys.filter(k=>expected[k]!==actual[k])
  if(fields.length) discrepancies.push({case:c.id, fields, expected, actual, error:err})
}
const report={
  kind:'independent-frame-outcome-differential',
  oracle:'@ethereumjs/evm@10.1.3 Prague runCall',
  compared:cases.length, matched:cases.length-discrepancies.length,
  mismatches:discrepancies.length,
  fields:['status','gasRemaining','current','refund','returnDataHex'],
  firstDiscrepancies:discrepancies.slice(0,10),
  limitation:'one account, top-level frame, no nested calls or transaction settlement'
}
console.log(JSON.stringify(report))
if(discrepancies.length) process.exitCode=1
