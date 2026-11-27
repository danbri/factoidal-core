#!/usr/bin/env node
/**
 * Differential matrix for SELFDESTRUCT (0xff) under EIP-6780 and the
 * transaction-end deletion, executed by the actual world-aware Lean
 * dispatcher, against @ethereumjs/evm 10.1.3 as an oracle only. Normative
 * reference: ethereum/execution-specs forks/cancun and forks/prague
 * vm/instructions/system.py (selfdestruct) and fork.py (process_transaction).
 *
 * Most cases mark an account as created in this transaction by the test
 * adapter's account flag, and by `createdAddresses` in the oracle; the `e2e`
 * cases create the contract with CREATE or CREATE2 in the same frame (the
 * expected addresses, used only to pick observed accounts and call targets,
 * come from EthereumJS). `applyDeletion` asks both sides for the transaction end:
 * Lean applies `SelfDestruct.destroyRegistered` (the function
 * `CallTransaction.settleFrame` applies); the harness repeats for EthereumJS
 * what its VM does with `execResult.selfdestruct`.
 *
 * Usage: node selfdestruct.mjs [path/to/evm-subset]
 */
import assert from 'node:assert/strict'
import { isDeepStrictEqual } from 'node:util'
import { generateAddress, generateAddress2, bigIntToBytes, hexToBytes, setLengthLeft } from '@ethereumjs/util'
import { CALLER, addr, call, compareAll, defaultExecutable, hex, keep, projectLean, push, ret, revert, runLean,
  runOracle } from './world-oracle.mjs'

const executable = process.argv[2] ?? defaultExecutable
const A = 0xc1, B = 0xc3, C = 0xc4, D = 0xc5, E = 0xc6, F = 0xc7, G = 0xc8
const highBits = (((1n << 256n) - 1n) ^ ((1n << 160n) - 1n)) | BigInt(C)
const cases = []
function add(id, code, {accounts = [], gas = 300000, profile = 'cancunPlus', observe = [A, B, C, D, E, F],
  balance = 1000, created = false, ...rest} = {}) {
  cases.push({id, profile, gas, entry: A, prewarm: [A, CALLER], observe, observeDestructs: true,
    accounts: [{address: A, balance, nonce: 1, code, created, storage: {1: 5}}, ...accounts], ...rest})
}
const destruct = target => push(target) + 'ff'
const sink = [{address: C, balance: 5}, {address: E, balance: 1}, {address: F, nonce: 1},
  {address: G, balance: 3, nonce: 1, code: '00'}]
const boundaries = []
function boundary(id, code, opts = {}) { boundaries.push([id, code, opts]) }

// The entry account destroys itself: every beneficiary class, both balances,
// both originator classes, with and without the transaction end.
const beneficiaries = [['funded-cold', C, []], ['funded-warm', C, [C]], ['self', A, []], ['absent-cold', D, []],
  ['absent-warm', D, [D]], ['contract', G, []], ['balance-only', E, []], ['nonce-only', F, []],
  ['caller', CALLER, []], ['precompile', 4, []], ['high-bits', highBits, []]]
for (const created of [false, true]) for (const balance of [1000, 0]) for (const [label, target, warm] of beneficiaries)
  for (const applyDeletion of [false, true])
    add(`entry:${created ? 'created' : 'old'}:${balance ? 'funded' : 'empty'}:${label}${applyDeletion ? ':end' : ''}`,
      destruct(target), {accounts: sink, created, balance, applyDeletion, prewarm: [A, CALLER, ...warm],
        observe: [A, C, D, E, F, G, CALLER, 4]})
// The four price combinations and the zero-balance exemption, at exact gas and one short.
boundary('gas:warm-alive', destruct(C), {accounts: sink, prewarm: [A, CALLER, C]})
boundary('gas:cold-alive', destruct(C), {accounts: sink})
boundary('gas:warm-new-account', destruct(D), {accounts: sink, prewarm: [A, CALLER, D]})
boundary('gas:cold-new-account', destruct(D), {accounts: sink})
boundary('gas:cold-absent-zero-balance', destruct(D), {accounts: sink, balance: 0})
boundary('gas:self', destruct(A), {accounts: sink})
boundary('gas:created-cold-new-account', destruct(D), {accounts: sink, created: true, applyDeletion: true})
add('entry:underflow', 'ff', {accounts: sink})
add('entry:static', destruct(C), {accounts: sink, readOnly: true})
add('entry:static-created', destruct(C), {accounts: sink, readOnly: true, created: true, applyDeletion: true})
add('entry:storage-then-destruct', push(9) + keep(2) + destruct(C), {accounts: sink})
add('entry:storage-then-destruct:created:end', push(9) + keep(2) + destruct(C),
  {accounts: sink, created: true, applyDeletion: true})

// A child destroys itself and the parent continues, records the status and
// reads the beneficiary (warm after a successful child).
const balanceOf = target => push(target) + '31'
for (const created of [false, true]) for (const applyDeletion of [false, true]) {
  const tag = (created ? 'created' : 'old') + (applyDeletion ? ':end' : '')
  const child = who => ({address: B, balance: 50, nonce: 1, code: destruct(who), created, storage: {0: 3, 2: 4}})
  for (const [label, target] of [['to-third', C], ['to-absent', D], ['to-parent', A], ['to-self', B]])
    add(`child:${label}:${tag}`, call('call', B) + keep(0) + balanceOf(target) + keep(2) + '00',
      {accounts: [child(target), ...sink], applyDeletion})
  // The same child twice: the second run moves the value it was just sent.
  add(`child:twice:${tag}`, call('call', B) + keep(0) + call('call', B, {value: 7}) + keep(2) + '00',
    {accounts: [child(C), ...sink], applyDeletion})
  // Re-entry in the same transaction: the code is present until the end.
  // With calldata the child stores 7 in slot 1; without, it destroys itself.
  const branching = '3615' + '60' + '0b' + '57' + push(7) + keep(1) + '00' + '5b' + destruct(C)
  assert.equal(branching.indexOf('5b') / 2, 0x0b, 'jump destination')
  add(`child:reentry:${tag}`, call('call', B) + keep(0) + call('call', B, {inSize: 1}) + keep(2) +
    push(B) + '3b' + keep(3) + '00', {accounts: [{...child(C), code: branching}, ...sink], applyDeletion})
  add(`child:value-after-destruct:${tag}`, call('call', B) + keep(0) + call('call', B, {inSize: 1, value: 9}) + keep(2) + '00',
    {accounts: [{...child(C), code: branching}, ...sink], applyDeletion})
  // A grandchild destroys itself and the middle frame then reverts or fails.
  for (const [label, end] of [['revert', revert()], ['invalid', 'fe'], ['stop', '00']])
    add(`grandchild:middle-${label}:${tag}`, call('call', G) + keep(0) + balanceOf(D) + keep(2) + '00',
      {accounts: [child(D), {address: G, balance: 3, nonce: 1, code: call('call', B) + '50' + end}, sink[0]],
        applyDeletion})
  // The entry frame fails after the child succeeded: nothing is registered.
  add(`parent:revert:${tag}`, call('call', B) + '50' + revert(), {accounts: [child(C), ...sink], applyDeletion})
  add(`parent:invalid:${tag}`, call('call', B) + '50' + 'fe', {accounts: [child(C), ...sink], applyDeletion})
  add(`parent:out-of-gas:${tag}`, call('call', B) + '50' + push(1) + keep(3) + '00',
    {accounts: [child(C), ...sink], applyDeletion, gas: 30000})
  // The child runs in a static frame: write protection, the parent continues.
  add(`child:staticcall:${tag}`, call('staticcall', B) + keep(0) + balanceOf(C) + keep(2) + '00',
    {accounts: [child(C), ...sink], applyDeletion})
  // DELEGATECALL and CALLCODE: the executing (entry) account is the originator.
  for (const op of ['delegatecall', 'callcode'])
    add(`${op}:library-destructs:${tag}`, call(op, B) + keep(0) + '00',
      {accounts: [{...child(C), created: false}, ...sink], created, applyDeletion})
  // Too little gas forwarded for the new-account surcharge: the child fails.
  add(`child:underfunded:${tag}`, call('call', B, {gas: 30000}) + keep(0) + '00',
    {accounts: [child(D), ...sink], applyDeletion})
  add(`child:just-funded:${tag}`, call('call', B, {gas: 32603}) + keep(0) + '00',
    {accounts: [child(D), ...sink], applyDeletion})
}
// The same instruction under the Osaka profile.
for (const created of [false, true]) for (const [label, target] of [['funded-cold', C], ['self', A], ['absent-cold', D]])
  add(`osaka:${created ? 'created' : 'old'}:${label}`, destruct(target),
    {accounts: sink, created, applyDeletion: true, profile: 'osaka'})
add('osaka:child', call('call', B) + keep(0) + '00', {profile: 'osaka', applyDeletion: true,
  accounts: [{address: B, balance: 50, nonce: 1, code: destruct(C), created: true}, ...sink]})

// End to end with CREATE/CREATE2 in the same transaction (needs the Keccak opt-in).
const big = bytes => BigInt('0x' + hex(bytes))
const store = (code, at = 0) => {
  let out = ''
  for (let i = 0; i < code.length; i += 64)
    out += push(BigInt('0x' + code.slice(i, i + 64).padEnd(64, '0'))) + push(at + i / 2) + '52'
  return out
}
const returning = runtime => store(runtime) + ret(0, runtime.length / 2)
const deploy = (init, value) => store(init) + push(init.length / 2) + push(0) + push(value) + 'f0'
const deploy2 = (init, value, salt) => store(init) + push(salt) + push(init.length / 2) + push(0) + push(value) + 'f5'
const N = big(generateAddress(addr(A).bytes, bigIntToBytes(1n)))
const N2 = init => big(generateAddress2(addr(A).bytes, setLengthLeft(bigIntToBytes(7n), 32), hexToBytes('0x' + init)))
const old = {address: B, balance: 50, nonce: 1, code: destruct(C), storage: {0: 3}}
for (const profile of ['cancunPlus', 'osaka']) for (const applyDeletion of [false, true]) {
  const e2e = (id, code, target, extra = {}) => add(`e2e:${id}:${profile}${applyDeletion ? ':end' : ''}`, code,
    {accounts: [old, sink[0], sink[3]], observe: [A, B, C, G, target], profile, applyDeletion, fuel: 20000,
      gas: 600000, ...extra})
  const toThird = returning(destruct(C)), toSelf = returning(destruct(N))
  // The new contract is created with 40 wei, then called: it destroys itself.
  e2e('create-then-destruct', deploy(toThird, 40) + keep(0) + call('call', N) + keep(2) + '00', N)
  e2e('create-then-burn', deploy(toSelf, 40) + keep(0) + call('call', N) + keep(2) + '00', N)
  e2e('create2-then-destruct', deploy2(toThird, 40, 7) + keep(0) + call('call', N2(toThird)) + keep(2) + '00', N2(toThird))
  // The initcode itself ends in SELFDESTRUCT: empty code is deposited and the account is registered.
  e2e('initcode-destructs', deploy(destruct(C), 40) + keep(0) + '00', N)
  e2e('initcode-burns', deploy(destruct(N), 40) + keep(0) + '00', N)
  // A pre-existing contract destroys itself in the same transaction: it is kept.
  e2e('old-contract-kept', deploy(toThird, 40) + keep(0) + call('call', B) + keep(2) + call('call', N) + keep(3) + '00', N)
  e2e('old-only', deploy(returning('00'), 40) + keep(0) + call('call', B) + keep(2) + '00', N)
  // The destruction is in a middle frame that reverts, or the entry frame fails afterwards.
  e2e('middle-reverts', deploy(toThird, 40) + keep(0) + call('call', G) + keep(2) + '00', N,
    {accounts: [old, sink[0], {address: G, balance: 3, nonce: 1, code: call('call', N) + '50' + revert()}]})
  e2e('entry-reverts', deploy(toThird, 40) + '50' + call('call', N) + '50' + revert(), N)
  // Code is present until the transaction end, so the same CREATE2 collides.
  e2e('recreate-collides', deploy2(toThird, 40, 7) + keep(0) + call('call', N2(toThird)) + keep(2) +
    deploy2(toThird, 1, 7) + keep(3) + '00', N2(toThird))
  // Value sent to the destroyed new contract is destroyed with it.
  e2e('value-after-destruct', deploy(returning('3615600b57' + '00'.repeat(6) + '5b' + destruct(C)), 40) + keep(0) +
    call('call', N) + keep(2) + call('call', N, {value: 9, inSize: 1}) + keep(3) + '00', N)
}

for (const [id, code, opts] of boundaries) {
  add(id + ':probe', code, opts)
  const probe = cases.pop()
  const used = BigInt(probe.gas) - BigInt((await runOracle(probe)).gasRemaining)
  add(id + ':exact', code, {...opts, gas: Number(used)})
  add(id + ':one-short', code, {...opts, gas: Number(used - 1n)})
}
const summary = await compareAll(executable, cases)
const leanRows = runLean(executable, cases)
const row = id => { const i = cases.findIndex(c => c.id === id); assert(i >= 0, id); return leanRows[i] }
const account = (id, address) => row(id).accounts.find(a => a.address === String(address))

// Independent expectations, computed from the EELS rules by hand (not from the oracle).
const independent = [
  // PUSH1 (3) + 5000 + 2600 cold; + 25000 for a new account receiving value.
  row('entry:old:funded:funded-cold').gasRemaining === String(300000 - 3 - 7600),
  row('entry:old:funded:funded-warm').gasRemaining === String(300000 - 3 - 5000),
  row('entry:old:funded:absent-cold').gasRemaining === String(300000 - 3 - 32600),
  row('entry:old:funded:absent-warm').gasRemaining === String(300000 - 3 - 30000),
  row('entry:old:empty:absent-cold').gasRemaining === String(300000 - 3 - 7600),
  row('entry:old:funded:self').gasRemaining === String(300000 - 3 - 5000),
  // A pre-existing account: balance moved, code, nonce and storage kept, not registered.
  isDeepStrictEqual([account('entry:old:funded:funded-cold:end', A), account('entry:old:funded:funded-cold:end', C)]
    .map(a => [a.balance, a.nonce, a.codeHex.length > 0, a.storage[1], a.selfDestructed]),
    [['0', '1', true, '5', false], ['1005', '0', false, '0', false]]),
  // Self-beneficiary: unchanged if pre-existing, burnt if created.
  account('entry:old:funded:self', A).balance === '1000',
  account('entry:created:funded:self', A).balance === '0' && account('entry:created:funded:self', A).selfDestructed,
  // A created account: registered, and absent after the transaction end.
  isDeepStrictEqual((a => [a.balance, a.nonce, a.codeHex, a.storage[1], a.selfDestructed])(
    account('entry:created:funded:funded-cold:end', A)), ['0', '0', '', '0', true]),
  account('entry:created:funded:funded-cold', A).codeHex !== '' && account('entry:created:funded:funded-cold', A).nonce === '1',
  // Re-entry: the code ran again after SELFDESTRUCT (slot 1 = 7) until the end removed it.
  account('child:reentry:created', B).storage[1] === '7' && account('child:reentry:created:end', B).storage[1] === '0',
  // Value sent after SELFDESTRUCT is destroyed with the account.
  account('child:value-after-destruct:created', B).balance === '9' &&
    account('child:value-after-destruct:created:end', B).balance === '0',
  // A reverted middle frame discards the registration and restores the balance.
  account('grandchild:middle-revert:created:end', B).balance === '50' &&
    !account('grandchild:middle-revert:created:end', B).selfDestructed &&
    account('grandchild:middle-stop:created:end', B).selfDestructed,
  account('parent:revert:created:end', B).balance === '50' && !account('parent:revert:created:end', B).selfDestructed,
  row('parent:out-of-gas:created:end').status === 'exceptional' && account('parent:out-of-gas:created:end', B).balance === '50',
  // 30000 forwarded gas is short of PUSH1 + 32600; 32603 is exact.
  account('child:underfunded:old', A).storage[0] === '0' && account('child:just-funded:old', A).storage[0] === '1',
  // CREATE then SELFDESTRUCT in one transaction: 40 wei moved, the contract absent after the end.
  isDeepStrictEqual((a => [a.balance, a.nonce, a.codeHex, a.selfDestructed])(account('e2e:create-then-destruct:cancunPlus:end', N)),
    ['0', '0', '', true]) && account('e2e:create-then-destruct:cancunPlus:end', C).balance === '45' &&
    account('e2e:create-then-destruct:cancunPlus', N).codeHex === '60c4ff' && account('e2e:create-then-destruct:cancunPlus', N).nonce === '1',
  // Self-beneficiary of a new contract burns: nobody receives the 40 wei.
  account('e2e:create-then-burn:cancunPlus:end', C).balance === '5' && account('e2e:create-then-burn:cancunPlus', N).balance === '0' &&
    account('e2e:create-then-burn:cancunPlus', A).balance === '960',
  // SELFDESTRUCT in initcode: registered, deleted at the end.
  account('e2e:initcode-destructs:cancunPlus', N).selfDestructed && account('e2e:initcode-destructs:cancunPlus', N).nonce === '1' &&
    account('e2e:initcode-destructs:cancunPlus:end', N).nonce === '0' && account('e2e:initcode-destructs:cancunPlus:end', C).balance === '45',
  // The pre-existing contract keeps code, nonce and storage; the new one is deleted.
  isDeepStrictEqual((a => [a.balance, a.nonce, a.codeHex, a.storage[0], a.selfDestructed])(account('e2e:old-contract-kept:osaka:end', B)),
    ['0', '1', '60c4ff', '3', false]) && account('e2e:old-contract-kept:osaka:end', N).codeHex === '',
  // A reverted middle frame leaves the new contract alive with its balance.
  account('e2e:middle-reverts:cancunPlus:end', N).balance === '40' && account('e2e:middle-reverts:cancunPlus:end', N).codeHex === '60c4ff',
  // The second CREATE2 at the same address collides (0 pushed) because the code is still there.
  account('e2e:recreate-collides:cancunPlus', A).storage[3] === '0' && account('e2e:recreate-collides:cancunPlus', A).storage[2] === '1',
  // DELEGATECALL: the entry account is the originator.
  account('delegatecall:library-destructs:created', A).selfDestructed &&
    !account('delegatecall:library-destructs:created', B).selfDestructed,
]

// Negative controls: each perturbation of a matched answer must be caught.
const probeCase = cases.find(c => c.id === 'entry:created:funded:funded-cold:end')
const lean = projectLean(probeCase, row(probeCase.id))
const oracle = await runOracle(probeCase)
const matched = isDeepStrictEqual(oracle, lean)
const gasMutationCaught = matched &&
  !isDeepStrictEqual({...oracle, gasRemaining: String(BigInt(oracle.gasRemaining) + 1n)}, lean)
const balanceMutationCaught = matched && !isDeepStrictEqual({...oracle, accounts: oracle.accounts.map(a =>
  a.address === String(C) ? {...a, balance: String(BigInt(a.balance) + 1n)} : a)}, lean)
// The oracle without the created flag keeps the account: the registration matters.
const registrationMutationCaught = matched && !isDeepStrictEqual(await runOracle({...probeCase,
  accounts: probeCase.accounts.map(a => ({...a, created: false}))}), lean)
// The oracle without the transaction end still holds code and nonce.
const deletionMutationCaught = matched && !isDeepStrictEqual(await runOracle({...probeCase, applyDeletion: false}), lean)
// A reverted child's oracle answer with a forged registration is caught.
const revertCase = cases.find(c => c.id === 'grandchild:middle-revert:created')
const revertOracle = await runOracle(revertCase)
const forgedRegistrationCaught = isDeepStrictEqual(revertOracle, projectLean(revertCase, row(revertCase.id))) &&
  !isDeepStrictEqual({...revertOracle, selfDestructed: [String(B)]}, projectLean(revertCase, row(revertCase.id)))

// Fork guard: shanghaiPlus spans the Cancun boundary, so Lean refuses; the
// Shanghai oracle executes the pre-Cancun instruction.
const forkCases = [['entry', destruct(C), []], ['child', call('call', B) + '50' + '00',
  [{address: B, balance: 1, code: destruct(C)}]]].map(([name, code, accounts]) => ({id: 'fork:' + name,
  profile: 'shanghaiPlus', gas: 100000, entry: A, prewarm: [A, CALLER], observe: [A],
  accounts: [{address: A, balance: 10, code}, ...accounts]}))
const forkLean = runLean(executable, forkCases)
const forkOracle = await Promise.all(forkCases.map(runOracle))
const forkGuardHeld = forkLean.every(r => r.status === 'indeterminate' && r.reason === 'unsupportedFork') &&
  forkOracle.every(o => o.status === 'stopped')

// Ordering difference from the oracle, checked against EELS by hand: EELS
// charges gas before the static check, EthereumJS traps the static frame
// first. Both halt exceptionally with no gas left; only the reason differs.
const orderCase = {id: 'order:static-underfunded', profile: 'cancunPlus', gas: 5000, entry: A, readOnly: true,
  prewarm: [A, CALLER], observe: [A, C], accounts: [{address: A, balance: 10, code: destruct(C)}, sink[0]]}
const [orderLean] = runLean(executable, [orderCase])
const orderOracle = await runOracle(orderCase)
const staticOrder = orderLean.status === 'exceptional' && orderLean.reason === 'outOfGas' &&
  orderLean.gasRemaining === '0' && orderOracle.status === 'exceptional' &&
  orderOracle.reason === 'writeProtection' && orderOracle.gasRemaining === '0' &&
  isDeepStrictEqual(orderOracle.accounts, projectLean(orderCase, orderLean).accounts)

console.log(JSON.stringify({
  kind: 'world-aware SELFDESTRUCT (EIP-6780) and transaction-end deletion differential',
  oracle: '@ethereumjs/evm 10.1.3 (Cancun and Osaka), test oracle only',
  ...summary,
  categories: Object.fromEntries([...new Set(cases.map(c => c.id.split(':')[0]))].map(k => [k, cases.filter(c => c.id.startsWith(k + ':')).length])),
  gasBoundaryPairs: boundaries.length,
  independentChecks: independent.length,
  independentHeld: independent.every(Boolean),
  eelsOrderChecks: {staticChargedBeforeWriteProtection: staticOrder},
  negativeControls: {gasMutationCaught, balanceMutationCaught, registrationMutationCaught, deletionMutationCaught,
    forgedRegistrationCaught, forkGuardHeld},
}))
if (!independent.every(Boolean)) console.error('independent checks: ' + JSON.stringify(independent))
