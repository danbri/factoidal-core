#!/usr/bin/env node
/**
 * Differential matrix for BALANCE, EXTCODESIZE, EXTCODECOPY, EXTCODEHASH,
 * BLOCKHASH, TLOAD/TSTORE (EIP-1153) and MCOPY (EIP-5656) executed by the
 * actual world-aware Lean dispatcher, against @ethereumjs/evm 10.1.3 as an
 * oracle only. Normative reference: ethereum/execution-specs forks/cancun
 * vm/instructions/{environment,block,storage,memory}.py.
 *
 * Usage: node account-transient.mjs [path/to/evm-subset]
 */
import assert from 'node:assert/strict'
import { isDeepStrictEqual } from 'node:util'
import { CALLER, call, compareAll, defaultExecutable, keep, projectLean, push, ret, revert, runLean,
  runOracle, word } from './world-oracle.mjs'

const executable = process.argv[2] ?? defaultExecutable
const A = 0xc1, B = 0xc3, C = 0xc4, D = 0xc5, E = 0xc6, F = 0xc7
const highBits = (((1n << 256n) - 1n) ^ ((1n << 160n) - 1n)) | BigInt(B)
const cases = []
function add(id, code, {accounts = [], gas = 100000, profile = 'cancunPlus', observe = [A, B, C], ...rest} = {}) {
  cases.push({id, profile, gas, entry: A, prewarm: [A, CALLER], observe,
    accounts: [{address: A, balance: 1000, code}, ...accounts], ...rest})
}
const bCode = '6001600255' + '00'          // PUSH1 1 PUSH1 2 SSTORE STOP: 6 bytes
const others = [{address: B, balance: 77, nonce: 1, code: bCode}, {address: C, balance: 5},
  {address: E, balance: 1}, {address: F, nonce: 1}]

/** Add a pair at the exact gas the oracle uses for `code` and one gas less. */
const boundaries = []
function boundary(id, code, opts = {}) { boundaries.push([id, code, opts]) }

// Account reads, cold and warm, every relevant account class.
for (const [op, name] of [['31', 'balance'], ['3b', 'extcodesize'], ['3f', 'extcodehash']]) {
  for (const [label, target] of [['contract', B], ['funded', C], ['absent', D], ['balanceOnly', E],
    ['nonceOnly', F], ['self', A], ['caller', CALLER], ['precompile', 4], ['highBits', highBits]])
    add(`${name}:${label}`, push(target) + op + '00', {accounts: others})
  add(`${name}:cold-then-warm`, push(B) + op + push(B) + op + '00', {accounts: others})
  add(`${name}:prewarmed`, push(B) + op + '00', {accounts: others, prewarm: [A, CALLER, B]})
  add(`${name}:static`, push(B) + op + '00', {accounts: others, readOnly: true})
  boundary(`${name}:cold-gas`, push(B) + op, {accounts: others})
  add(`${name}:underflow`, op + '00', {accounts: others})
  // A reverted child's warm-up is discarded: the parent pays cold again.
  const child = push(C) + op + '50' + revert()
  add(`${name}:child-revert-discards-warmth`, call('call', B) + '50' + push(C) + op + '00',
    {accounts: [{address: B, code: child}, {address: C, balance: 5, code: '00'}]})
  const ok = push(C) + op + '50' + '00'
  add(`${name}:child-success-keeps-warmth`, call('call', B) + '50' + push(C) + op + '00',
    {accounts: [{address: B, code: ok}, {address: C, balance: 5, code: '00'}]})
}
// EXTCODECOPY windows, padding and expansion.
const xcopy = (target, mem, codeOff, size) => push(size) + push(codeOff) + push(mem) + push(target) + '3c'
for (const [label, target, mem, off, size] of [
  ['full', B, 0, 0, 32], ['inner', B, 5, 1, 3], ['past-end', B, 0, 100, 40], ['zero-huge-offset', B, (1n << 255n), 0, 0],
  ['zero-huge-code-offset', B, 0, (1n << 255n), 7], ['absent', D, 0, 0, 64], ['far', B, 1000, 2, 10],
  ['self', A, 0, 0, 40], ['two-words', B, 31, 0, 33]]) {
  add(`extcodecopy:${label}`, xcopy(target, mem, off, size) + '00', {accounts: others})
}
add('extcodecopy:warm-second', xcopy(B, 0, 0, 6) + xcopy(B, 32, 0, 6) + '00', {accounts: others})
boundary('extcodecopy:gas', xcopy(B, 0, 0, 32), {accounts: others})
boundary('extcodecopy:gas-expanding', xcopy(B, 100, 0, 70), {accounts: others})
add('extcodecopy:underflow', push(0) + push(B) + '3c00', {accounts: others})

// BLOCKHASH window: the 256 most recent complete blocks, newest last.
const hashes = Array.from({length: 256}, (_, i) => word(BigInt(i + 1) * 0x1000193n + 0xabcdefn))
for (const n of [299, 298, 200, 45, 44, 43, 300, 301, 0, (1n << 255n)])
  add(`blockhash:300:${n}`, push(n) + '4000', {number: 300, hashes, observe: [A]})
const few = hashes.slice(-5)
for (const n of [0, 1, 4, 5, 6]) add(`blockhash:5:${n}`, push(n) + '4000', {number: 5, hashes: few, observe: [A]})
boundary('blockhash:gas', push(299) + '40', {number: 300, hashes, observe: [A]})
add('blockhash:missing-history', push(200) + '4000',
  {number: 300, hashes: hashes.slice(-10), observe: [A], expectIndeterminate: 'missingBlockHash'})

// EIP-1153 transient storage.
const tstore = (key, value) => push(value) + push(key) + '5d'
const tload = key => push(key) + '5c'
add('transient:store-load', tstore(1, 42) + tload(1) + tload(2) + '00', {observe: [A]})
add('transient:overwrite', tstore(1, 42) + tstore(1, 0) + tstore(1, 9) + tload(1) + '00', {observe: [A]})
add('transient:static-load', tload(1) + '00', {readOnly: true, observe: [A]})
add('transient:static-store', tstore(1, 1) + '00', {readOnly: true, observe: [A]})
boundary('transient:store-gas', tstore(1, 1), {observe: [A]})
boundary('transient:load-gas', tload(1), {observe: [A]})
add('transient:underflow', push(1) + '5d00', {observe: [A]})
add('transient:not-storage', tstore(0, 5) + push(0) + '54' + tload(0) + '00', {observe: [A]})
add('transient:parent-revert', tstore(0, 5) + revert(), {observe: [A]})
// Child B: with empty calldata store 7 then halt (or revert); with calldata,
// copy its transient slot 0 into persistent slot 1.
function branchChild(endWith) {
  const write = tstore(0, 7) + endWith
  const read = tload(0) + keep(1) + '00'
  // CALLDATASIZE ISZERO PUSH1 dest JUMPI <read> JUMPDEST <write>
  const head = '3615' + '61' + '0000' + '57'
  const dest = (head.length + read.length) / 2
  return '3615' + '61' + dest.toString(16).padStart(4, '0') + '57' + read + '5b' + write
}
for (const [label, end, expectSlot] of [['halt', '00', '7'], ['revert', revert(), '0'], ['invalid', 'fe', '0']]) {
  const parent = call('call', B) + '50' + call('call', B, {inSize: 1}) + '50' + '00'
  add(`transient:child-${label}`, parent, {accounts: [{address: B, code: branchChild(end)}], observe: [A, B],
    gas: 300000})
}
// A grandchild failure rolls back only its own scope.
const grand = tstore(0, 3) + revert()
const middle = tstore(1, 4) + call('call', C) + '50' + tload(0) + keep(2) + tload(1) + keep(3) + '00'
add('transient:grandchild-revert', call('call', B) + '00',
  {accounts: [{address: B, code: middle}, {address: C, code: grand}], gas: 300000})
// Per-address isolation and DELEGATECALL using the caller's transient storage.
add('transient:isolation', tstore(0, 11) + call('call', B) + '50' + '00',
  {accounts: [{address: B, code: tload(0) + keep(0) + '00'}], observe: [A, B], gas: 200000})
add('transient:delegatecall', call('delegatecall', B) + '50' + tload(0) + keep(0) + '00',
  {accounts: [{address: B, code: tstore(0, 9) + '00'}], observe: [A, B], gas: 200000})
add('transient:staticcall-store-fails', call('staticcall', B) + keep(0) + '00',
  {accounts: [{address: B, code: tstore(0, 9) + '00'}], observe: [A, B], gas: 200000})
add('transient:staticcall-load', tstore(0, 13) + call('staticcall', A, {outSize: 32}) + '00',
  {accounts: [], observe: [A], gas: 200000})

// EIP-5656 MCOPY.
const mstore = (offset, value) => push(value) + push(offset) + '52'
const mcopy = (dest, src, len) => push(len) + push(src) + push(dest) + '5e'
const pattern = BigInt('0x' + Array.from({length: 32}, (_, i) => (i + 1).toString(16).padStart(2, '0')).join(''))
for (const [label, dest, src, len] of [
  ['forward-overlap', 1, 0, 32], ['backward-overlap', 0, 1, 31], ['disjoint', 32, 0, 32], ['same', 0, 0, 32],
  ['zero-huge', (1n << 255n), (1n << 255n), 0], ['source-expands', 0, 64, 1], ['dest-expands', 1000, 0, 10],
  ['both-expand', 200, 100, 64], ['one-byte', 31, 0, 1]])
  add(`mcopy:${label}`, mstore(0, pattern) + mcopy(dest, src, len) + '00', {observe: [A]})
boundary('mcopy:gas', mcopy(0, 32, 32), {observe: [A]})
boundary('mcopy:gas-large', mcopy(4000, 64, 3000), {observe: [A]})
add('mcopy:underflow', push(1) + push(1) + '5e00', {observe: [A]})

// Fork admission: shanghaiPlus spans the Cancun boundary, so the Lean
// dispatcher refuses (indeterminate) while the Shanghai oracle has no opcode.
const forkCases = [['tload', tload(0) + '00'], ['tstore', tstore(0, 1) + '00'], ['mcopy', mcopy(0, 0, 1) + '00']]
  .map(([name, code]) => ({id: 'fork:' + name, profile: 'shanghaiPlus', gas: 100000, entry: A,
    prewarm: [A, CALLER], observe: [A], accounts: [{address: A, code}]}))

for (const [id, code, opts] of boundaries) {
  add(id + ':probe', code, opts)
  const probe = cases.pop()
  const used = BigInt(probe.gas) - BigInt((await runOracle(probe)).gasRemaining)
  add(id + ':exact', code, {...opts, gas: Number(used)})
  add(id + ':one-short', code, {...opts, gas: Number(used - 1n)})
}
const summary = await compareAll(executable, cases)
if (process.env.PEEK) { const rows = runLean(executable, cases); for (const id of process.env.PEEK.split(",")) { const i = cases.findIndex(c => c.id === id); console.error(id, JSON.stringify({stack: rows[i].stack, status: rows[i].status, gas: rows[i].gasRemaining, st: rows[i].accounts.map(a => a.storage), tr: rows[i].accounts.map(a=>a.transient), mem: rows[i].memoryHex.slice(0,140)})) } }
// Independent gas expectations, computed from the EELS schedule by hand.
const expectGas = {
  'balance:contract': 100000 - 3 - 2600, 'balance:cold-then-warm': 100000 - 6 - 2600 - 100,
  'balance:prewarmed': 100000 - 3 - 100, 'extcodehash:absent': 100000 - 3 - 2600,
  'transient:store-load': 100000 - 6 - 100 - 3 - 100 - 3 - 100,
  'blockhash:300:299': 100000 - 3 - 20,
}
const leanRows = runLean(executable, cases)
const independent = Object.entries(expectGas).every(([id, gas]) => {
  const i = cases.findIndex(c => c.id === id)
  return leanRows[i].gasRemaining === String(gas)
})
// Negative control: a one-gas perturbation of a matched oracle answer is caught.
const probe = cases.find(c => c.id === 'balance:contract')
const oracle = await runOracle(probe)
const mutated = {...oracle, gasRemaining: String(BigInt(oracle.gasRemaining) + 1n)}
const leanProbe = projectLean(probe, leanRows[cases.indexOf(probe)])
const gasMutationCaught = isDeepStrictEqual(oracle, leanProbe) && !isDeepStrictEqual(mutated, leanProbe)
// Negative control: a wrong code byte in the target changes the oracle's EXTCODEHASH.
const hashProbe = cases.find(c => c.id === 'extcodehash:contract')
const altered = {...hashProbe, accounts: hashProbe.accounts.map(a => a.address === B ? {...a, code: '6001600355' + '00'} : a)}
const codeMutationCaught = !isDeepStrictEqual(await runOracle(altered), projectLean(hashProbe, leanRows[cases.indexOf(hashProbe)]))
// Fork guard.
const forkLean = runLean(executable, forkCases)
const forkOracle = await Promise.all(forkCases.map(runOracle))
const forkGuardHeld = forkLean.every(r => r.status === 'indeterminate' && r.reason === 'unsupportedFork') &&
  forkOracle.every(o => o.status === 'exceptional' && o.reason === 'invalidOpcode')

console.log(JSON.stringify({
  kind: 'world-aware account, block-hash, transient-storage and MCOPY differential',
  oracle: '@ethereumjs/evm 10.1.3 (Cancun), test oracle only',
  ...summary,
  categories: Object.fromEntries([...new Set(cases.map(c => c.id.split(':')[0]))].map(k => [k, cases.filter(c => c.id.startsWith(k + ':')).length])),
  gasBoundaryPairs: boundaries.length,
  independentGas: independent,
  negativeControls: {gasMutationCaught, codeMutationCaught, forkGuardHeld},
}))
