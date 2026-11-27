#!/usr/bin/env node
/**
 * Differential matrix for CREATE (0xf0) and CREATE2 (0xf5) executed by the
 * actual world-aware Lean dispatcher, against @ethereumjs/evm 10.1.3 as an
 * oracle only (Shanghai, Cancun and Osaka rules). Normative reference:
 * ethereum/execution-specs forks/{cancun,prague,osaka} vm/instructions/system.py
 * (create, create2, generic_create) and vm/interpreter.py (process_create_message).
 *
 * The expected addresses used to pick the observed accounts come from
 * EthereumJS (generateAddress, generateAddress2): test-side only.
 *
 * Usage: node create.mjs [path/to/evm-subset]
 */
import assert from 'node:assert/strict'
import { isDeepStrictEqual } from 'node:util'
import { generateAddress, generateAddress2, bigIntToBytes, hexToBytes, setLengthLeft } from '@ethereumjs/util'
import { CALLER, addr, call, compareAll, defaultExecutable, hex, keep, projectLean, push, ret, revert, runLean,
  runOracle } from './world-oracle.mjs'

const executable = process.argv[2] ?? defaultExecutable
const A = 0xc1, B = 0xc3
const big = bytes => BigInt('0x' + hex(bytes))
const createAddr = (from, nonce) => big(generateAddress(addr(from).bytes, bigIntToBytes(BigInt(nonce))))
const create2Addr = (from, salt, init) =>
  big(generateAddress2(addr(from).bytes, setLengthLeft(bigIntToBytes(BigInt(salt)), 32), hexToBytes('0x' + init)))

/** Write `code` (hex) into memory at `at` with MSTOREs. */
function store(code, at = 0) {
  let out = ''
  for (let i = 0; i < code.length; i += 64)
    out += push(BigInt('0x' + code.slice(i, i + 64).padEnd(64, '0'))) + push(at + i / 2) + '52'
  return out
}
const create = (value, offset, size) => push(size) + push(offset) + push(value) + 'f0'
const create2 = (value, offset, size, salt) => push(salt) + push(size) + push(offset) + push(value) + 'f5'
/** Store `init` at 0 and create from it. */
const deploy = (init, value = 0) => store(init) + create(value, 0, init.length / 2)
const deploy2 = (init, salt, value = 0) => store(init) + create2(value, 0, init.length / 2, salt)
/** Initcode returning `runtime` (hex, any length). */
const returning = runtime => store(runtime) + ret(0, runtime.length / 2)

const runtime = '6001600055' + '00'                  // PUSH1 1 PUSH1 0 SSTORE STOP
const init = {
  empty: '',
  stop: '00',
  runtime: returning(runtime),
  // ADDRESS, CALLER, CALLVALUE and own EXTCODESIZE+CODESIZE into slots 0..3.
  context: '30' + keep(0) + '33' + keep(1) + '34' + keep(2) + '303b38' + '01' + keep(3) + '00',
  revertData: store('deadbeef'.padEnd(64, '0')) + revert(0, 36),
  revertEmpty: revert(),
  invalid: 'fe',
  loop: '5b5f56',                                    // JUMPDEST PUSH0 JUMP
  ef: push(0xef) + '5f53' + ret(0, 1),               // MSTORE8(0, 0xef); RETURN(0,1)
  efSecond: push(0xef) + '600153' + ret(0, 2),       // 0x00ef is allowed
  zeros: n => ret(0, n),                             // RETURN a zero window of n bytes
  // Revert unless endowed; otherwise deploy the runtime.
  needsValue: '34' + push(6) + '57' + '5f5ffd' + '5b' + returning(runtime),
  callsThenReverts: call('call', B) + '50' + revert(),
  callsThenStops: call('call', B) + '50' + '00',
  storeAndReturn: push(7) + keep(1) + returning(runtime),
}
init.nested = deploy(init.runtime) + keep(0) + returning(runtime)
init.nestedThenRevert = deploy(init.runtime) + '50' + revert()
init.nestedInnerFails = deploy(init.invalid) + keep(0) + push(9) + keep(1) + '00'

const cases = []
const profiles = ['cancunPlus', 'osaka']
function add(id, code, {accounts = [], gas = 400000, observe = [], nonce = 1, balance = 1000, only, ...rest} = {}) {
  for (const profile of only ?? profiles)
    cases.push({id: `${id}@${profile}`, profile, gas, fuel: 200000, entry: A, prewarm: [A, CALLER],
      observe: [A, ...observe], accounts: [{address: A, balance, nonce, code}, ...accounts], ...rest})
}
const bCode = push(5) + keep(2) + '00'
const withB = [{address: B, code: bCode}]
const first = createAddr(A, 1), second = createAddr(A, 2), third = createAddr(A, 3)

// --- CREATE successes, contexts and nonce progression.
for (const [name, code] of [['empty', init.empty], ['stop', init.stop], ['runtime', init.runtime],
  ['context', init.context], ['store-and-return', init.storeAndReturn], ['ef-second-byte', init.efSecond]]) {
  add(`create:${name}`, deploy(code) + '00', {observe: [first]})
  add(`create:${name}-value`, deploy(code, 7) + '00', {observe: [first]})
  add(`create2:${name}`, deploy2(code, 0x1234) + '00', {observe: [create2Addr(A, 0x1234, code)]})
  add(`create2:${name}-value`, deploy2(code, 0x1234, 7) + '00', {observe: [create2Addr(A, 0x1234, code)]})
}
add('create:three', deploy(init.runtime) + deploy(init.context, 1) + deploy(init.stop) + '00',
  {observe: [first, second, third]})
add('create:then-call', deploy(init.runtime) + '80' + push(100) + '52' + call('call', first, {gas: 50000}) + '00',
  {observe: [first]})
add('create:offset-window', store(init.runtime, 64) + create(0, 64, init.runtime.length / 2) + '00', {observe: [first]})
add('create:window-past-memory', store(init.runtime) + create(0, 0, 200) + '00', {observe: [first]})
add('create:window-prefix', store(init.runtime) + create(0, 0, 3) + '00', {observe: [first]})
add('create:shanghai', deploy(init.runtime, 3) + '00', {observe: [first], only: ['shanghaiPlus']})
add('create2:shanghai', deploy2(init.runtime, 9, 3) + '00', {observe: [create2Addr(A, 9, init.runtime)], only: ['shanghaiPlus']})
for (const nonce of [0n, 1n, 0x7fn, 0x80n, 0xffn, 0x100n, 0xffffn, 0x10000n, (1n << 32n), (1n << 56n) - 1n, (1n << 56n), (1n << 64n) - 3n])
  add(`create:nonce-${nonce.toString(16)}`, deploy(init.context) + '00', {nonce, observe: [createAddr(A, nonce)], only: ['cancunPlus']})
// The last usable nonce: one creation succeeds, the next is a soft failure.
add('create:nonce-limit', deploy(init.stop) + deploy(init.stop) + '00',
  {nonce: (1n << 64n) - 2n, observe: [createAddr(A, (1n << 64n) - 2n), createAddr(A, (1n << 64n) - 1n)]})
add('create:nonce-max', deploy(init.stop) + '3d00', {nonce: (1n << 64n) - 1n, observe: [createAddr(A, (1n << 64n) - 1n)]})
add('create2:nonce-max', deploy2(init.stop, 1) + '3d00', {nonce: (1n << 64n) - 1n, observe: [create2Addr(A, 1, init.stop)]})
for (const salt of [0n, 1n, (1n << 255n), (1n << 256n) - 1n])
  add(`create2:salt-${salt.toString(16).slice(0, 8)}-${salt.toString(16).length}`, deploy2(init.context, salt, 2) + '00',
    {observe: [create2Addr(A, salt, init.context)], only: ['cancunPlus']})

// --- Failing initcode: return data, gas, rollback, warmth.
for (const [op, mk, target] of [['create', c => deploy(c), () => first], ['create2', c => deploy2(c, 5), c => create2Addr(A, 5, c)]]) {
  const rds = '3d'                                   // RETURNDATASIZE
  const copyOut = '3d5f' + push(0x100) + '3e'        // RETURNDATACOPY(0x100, 0, RETURNDATASIZE)
  add(`${op}:revert-data`, mk(init.revertData) + rds + copyOut + '00', {observe: [target(init.revertData)]})
  add(`${op}:revert-empty`, mk(init.revertEmpty) + rds + '00', {observe: [target(init.revertEmpty)]})
  add(`${op}:invalid`, mk(init.invalid) + rds + '00', {observe: [target(init.invalid)]})
  add(`${op}:loop-out-of-gas`, mk(init.loop) + rds + '00', {observe: [target(init.loop)], gas: 100000})
  add(`${op}:success-clears-returndata`, call('call', B) + '50' + mk(init.runtime) + rds + '00',
    {observe: [target(init.runtime)], accounts: [{address: B, code: store('11'.repeat(32)) + ret(0, 32)}]})
  add(`${op}:deposit-ef`, mk(init.ef) + rds + '00', {observe: [target(init.ef)]})
  add(`${op}:child-effects-rolled-back`, mk(init.callsThenReverts) + '00',
    {observe: [target(init.callsThenReverts), B], accounts: withB})
  add(`${op}:child-effects-kept`, mk(init.callsThenStops) + '00', {observe: [target(init.callsThenStops), B], accounts: withB})
  // Warmth of the new address afterwards: BALANCE is 100 gas in each case.
  for (const [name, code] of [['success', init.runtime], ['revert', init.revertEmpty], ['invalid', init.invalid]])
    add(`${op}:warm-after-${name}`, mk(code) + '50' + push(target(code)) + '3100', {observe: [target(code)]})
  // Static frame: write protection whatever the value.
  add(`${op}:static`, mk(init.stop) + '00', {readOnly: true, observe: [target(init.stop)]})
  // Depth: an entry frame at depth 1024 cannot create; at 1023 it can.
  add(`${op}:depth-1024`, mk(init.runtime) + rds + '00', {depth: 1024, observe: [target(init.runtime)]})
  add(`${op}:depth-1023`, mk(init.runtime) + rds + '00', {depth: 1023, observe: [target(init.runtime)]})
  // Funds: exactly the balance succeeds, one more is a soft failure (address stays cold).
  const mkv = (c, v) => op === 'create' ? deploy(c, v) : deploy2(c, 5, v)
  add(`${op}:value-all`, mkv(init.context, 1000) + '00', {observe: [target(init.context)]})
  add(`${op}:value-too-much`, mkv(init.context, 1001) + rds + push(target(init.context)) + '3100', {observe: [target(init.context)]})
  // Collisions: code, nonce, storage. A balance alone is not a collision.
  for (const [name, account] of [['code', {code: '00'}], ['nonce', {nonce: 1}], ['storage', {storage: {1: 5}, hasStorage: true}], ['storage-flag-only', {hasStorage: true}],
    ['balance-only', {balance: 9}]])
    add(`${op}:collision-${name}`, mk(init.runtime) + rds + push(target(init.runtime)) + '3100',
      {observe: [target(init.runtime)], accounts: [{address: target(init.runtime), ...account}]})
  // EIP-3860 initcode limit and EIP-170 code limit (zero windows: all-zero initcode is STOP).
  const window = (size, salt) => op === 'create' ? create(0, 0, size) : create2(0, 0, size, salt)
  const zeroInit = n => op === 'create' ? first : create2Addr(A, 5, '00'.repeat(n))
  for (const size of [49152, 49153, 32, 33])
    add(`${op}:initcode-${size}`, window(size, 5) + '00', {observe: [zeroInit(size)], gas: 2000000})
  for (const size of [24576, 24577, 1, 0])
    add(`${op}:deposit-${size}`, mk(init.zeros(size)) + rds + '00', {observe: [target(init.zeros(size))], gas: 10000000})
  add(`${op}:underflow`, (op === 'create' ? push(0) + push(0) : push(0) + push(0) + push(0)) + (op === 'create' ? 'f0' : 'f5') + '00')
  add(`${op}:huge-offset-zero-size`, (op === 'create' ? '' : push(1)) + push(0) + push(1n << 255n) + push(0) + (op === 'create' ? 'f0' : 'f5') + '00',
    {observe: [op === 'create' ? first : create2Addr(A, 1, '')]})
  add(`${op}:huge-size`, (op === 'create' ? '' : push(1)) + push(1n << 200n) + push(0) + push(0) + (op === 'create' ? 'f0' : 'f5') + '00')
}
// Nested creations.
const inner = createAddr(first, 1)
add('nested:success', deploy(init.nested) + '00', {observe: [first, inner], gas: 1000000})
add('nested:outer-reverts', deploy(init.nestedThenRevert) + '00', {observe: [first, inner], gas: 1000000})
add('nested:inner-fails', deploy(init.nestedInnerFails) + '00', {observe: [first, inner], gas: 1000000})
// CREATE2 with the same salt twice: the second collides and consumes its gas.
const same = create2Addr(A, 7, init.runtime)
add('create2:same-salt-twice', deploy2(init.runtime, 7) + deploy2(init.runtime, 7) + '3d00', {observe: [same], gas: 1000000})
// A reverted CREATE2 does not burn the address: the retry with value succeeds.
const retry = create2Addr(A, 7, init.needsValue)
add('create2:retry-after-revert', deploy2(init.needsValue, 7) + deploy2(init.needsValue, 7, 1) + '00', {observe: [retry], gas: 1000000})
// A reverting caller frame undoes a successful creation, including the nonce.
add('create:parent-reverts', deploy(init.runtime) + revert(), {observe: [first]})
// A child of the entry frame creates; the child then reverts or succeeds.
for (const [name, tail] of [['reverts', revert()], ['succeeds', '00']])
  add(`create:in-child-that-${name}`, call('call', B, {gas: 200000}) + '00',
    {observe: [B, createAddr(B, 1)], accounts: [{address: B, nonce: 1, code: deploy(init.runtime) + keep(0) + tail}]})
// DELEGATECALL: the creator is the executing account (A), not the code's owner.
add('create:via-delegatecall', call('delegatecall', B, {gas: 200000}) + '00',
  {observe: [first, createAddr(B, 1), B], accounts: [{address: B, nonce: 1, code: deploy(init.context, 2) + '00'}]})

// --- Gas boundaries: the least gas at which the oracle's outcome flips, and one less.
const sweeps = [
  ['create:gas-empty', deploy(init.empty), {}],
  ['create2:gas-empty', deploy2(init.empty, 1), {}],
  ['create:gas-stop', deploy(init.stop), {}],
  ['create:gas-deposit', deploy(init.runtime), {}],
  ['create2:gas-deposit', deploy2(init.runtime, 1), {}],
  ['create:gas-deposit-large', deploy(init.zeros(1000)), {}],
  ['create:gas-initcode-words', create(0, 0, 1000), {}],
  ['create2:gas-initcode-words', create2(0, 0, 1000, 1), {}],
]
let boundaryPairs = 0
for (const [id, code, opts] of sweeps) {
  for (const profile of profiles) {
    const mk = gas => ({id: `${id}:${gas}@${profile}`, profile, gas, fuel: 200000, entry: A, prewarm: [A, CALLER],
      observe: [A, first], accounts: [{address: A, balance: 1000, nonce: 1, code: code + '00'}], ...opts})
    // Least gas for the creator frame to finish at all (charge boundary).
    const frameOk = async gas => (await runOracle(mk(gas))).status === 'stopped'
    // Least gas for the creation itself to succeed (deposit boundary).
    const created = async gas => { const o = await runOracle(mk(gas)); return o.status === 'stopped' && o.stack[0] !== '0' }
    for (const pred of [frameOk, created]) {
      let lo = 0, hi = 400000
      assert(await pred(hi) && !(await pred(lo)), id + ' sweep bracket')
      while (hi - lo > 1) { const mid = (lo + hi) >> 1; if (await pred(mid)) hi = mid; else lo = mid }
      cases.push(mk(hi), mk(lo))
      boundaryPairs++
    }
  }
}

const summary = await compareAll(executable, cases)
const leanRows = runLean(executable, cases)
const row = id => leanRows[cases.findIndex(c => c.id === id)]
if (process.env.PEEK) for (const id of process.env.PEEK.split(',')) console.error(id, JSON.stringify(row(id)).slice(0, 1500))

// Independent gas expectations from the EELS schedule, computed by hand.
// Pushes: PUSH0 2 gas, PUSHn 3 gas. Empty initcode: the child uses nothing.
const expectGas = {
  'create:empty@cancunPlus': 400000 - 3 * 2 - 32000,
  'create2:empty@cancunPlus': 400000 - (3 + 2 + 2 + 2) - 32000,
  // 49152 zero bytes: 1536 words of memory (3*1536 + 1536^2/512) and 2 gas per
  // initcode word; the child executes STOP at no cost.
  'create:initcode-49152@cancunPlus': 2000000 - (3 + 2 + 2) - 32000 - (4608 + 4608) - 2 * 1536,
  'create2:initcode-49152@cancunPlus': 2000000 - (3 + 3 + 2 + 2) - 32000 - (4608 + 4608) - (2 + 6) * 1536,
}
const independentGas = Object.entries(expectGas).every(([id, gas]) => row(id).gasRemaining === String(gas))
// Lean-only observations the oracle does not expose: the EIP-6780 created mark.
const mark = (id, address) => row(id).accounts.find(a => a.address === String(address)).created
const createdMarks = mark('create:runtime@cancunPlus', first) === true && mark('create:revert-empty@cancunPlus', first) === false &&
  mark('create:collision-code@cancunPlus', first) === false && mark('create:value-too-much@cancunPlus', createAddr(A, 1)) === false &&
  mark('nested:success@cancunPlus', inner) === true && mark('nested:outer-reverts@cancunPlus', inner) === false
// Stack results the matrix relies on (so a matched pair of wrong answers cannot hide).
const pushed = id => row(id).stack?.[row(id).stack.length - 1]
const outcomes = pushed('create:runtime@cancunPlus') === String(first) && pushed('create:collision-code@cancunPlus') !== String(first) &&
  row('create:static@cancunPlus').status === 'exceptional' && row('create:initcode-49153@cancunPlus').status === 'exceptional' &&
  row('create:deposit-24576@cancunPlus').accounts[1].codeSize === '24576' && row('create:deposit-24577@cancunPlus').accounts[1].codeSize === '0'

// Negative controls.
const probe = cases.find(c => c.id === 'create:runtime@cancunPlus')
const oracle = await runOracle(probe)
const leanProbe = projectLean(probe, row(probe.id))
const gasMutationCaught = isDeepStrictEqual(oracle, leanProbe) &&
  !isDeepStrictEqual({...oracle, gasRemaining: String(BigInt(oracle.gasRemaining) + 1n)}, leanProbe)
const addressMutationCaught = !isDeepStrictEqual({...oracle, stack: [String(BigInt(oracle.stack[0]) ^ 1n)]}, leanProbe)
// A different initcode byte in the oracle's creator changes the deployed code.
const altered = {...probe, accounts: probe.accounts.map(a => a.address === A
  ? {...a, code: deploy(returning('6002600055' + '00')) + '00'} : a)}
const codeMutationCaught = !isDeepStrictEqual(await runOracle(altered), leanProbe)
// A different salt in the oracle changes the CREATE2 address.
const probe2 = cases.find(c => c.id === 'create2:runtime@cancunPlus')
const altered2 = {...probe2, accounts: probe2.accounts.map(a => a.address === A
  ? {...a, code: deploy2(init.runtime, 0x1235) + '00'} : a)}
const saltMutationCaught = isDeepStrictEqual(await runOracle(probe2), projectLean(probe2, row(probe2.id))) &&
  !isDeepStrictEqual(await runOracle(altered2), projectLean(probe2, row(probe2.id)))
// Without the Keccak opt-in an entered creation refuses; a soft failure needs no hash.
const noHash = runLean(executable, [probe, cases.find(c => c.id === 'create:value-too-much@cancunPlus')], {keccak: false})
const keccakGuardHeld = noHash[0].status === 'indeterminate' && noHash[0].reason === 'unsupportedFork' && noHash[1].status === 'stopped'

console.log(JSON.stringify({
  kind: 'world-aware CREATE and CREATE2 differential',
  oracle: '@ethereumjs/evm 10.1.3 (Shanghai, Cancun, Osaka), test oracle only',
  ...summary,
  categories: Object.fromEntries([...new Set(cases.map(c => c.id.split(':')[0]))].map(k => [k, cases.filter(c => c.id.startsWith(k + ':')).length])),
  profiles: Object.fromEntries(['shanghaiPlus', ...profiles].map(p => [p, cases.filter(c => c.profile === p).length])),
  gasBoundaryPairs: boundaryPairs,
  independentGas,
  leanOnly: {createdMarks, outcomes},
  negativeControls: {gasMutationCaught, addressMutationCaught, codeMutationCaught, saltMutationCaught, keccakGuardHeld},
}))
