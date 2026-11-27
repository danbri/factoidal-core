#!/usr/bin/env node
/**
 * Reuse all 36 retained signed-list fixtures through the actual authenticated
 * CLI. EthereumJS builds state proofs independently. The stored Geth/EthereumJS
 * results remain dated evidence; this script never claims those clients reran.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { performance } from 'node:perf_hooks'
import { RLP, bytes, hex, nat, fixed, keccak, bytesToBigInt, ecrecover, publicToAddress,
  MerklePatriciaTrie, clone, digest, buildStateWitness, checkStateWitness } from './oracle.mjs'

const snapshotPath = new URL('../../evidence/2026-11-24-transaction-list/list-execution.json', import.meta.url)
const sourcePath = new URL('../differential/transaction-list.mjs', import.meta.url)
const snapshotBytes = readFileSync(snapshotPath)
assert.equal(digest(snapshotBytes), 'ff3e56deaec8c8ff4cb99725f8d8283565a0e0fcf1c4fed175596faba5a3f484', 'dated reference evidence pin')
assert.equal(digest(readFileSync(sourcePath)), 'e0b16b7754b89be10f680da23f59b287b0e0bc7c9ce8007a5b93585700c0e768', 'fixture preparation source pin')
const snapshot = JSON.parse(snapshotBytes)
assert.equal(snapshot.rows.length, 36); assert.equal(snapshot.failed, 0)
const scalar = value => bytesToBigInt(value), decimal = value => BigInt(value).toString()
const unit = 131072n, parent = 193n, child = 194n, beneficiary = 196n, reverter = 197n, invalid = 198n, unsupported = 199n
const senders = [BigInt('0x7e5f4552091a69125d5dfcb7b8c2659029395bdf'), BigInt('0x2b5ad5c4795c026514f8317c7a215e218dccd6cf')]

// Decode the already retained signed bytes using the independent RLP and curve
// libraries. Sender recovery is deliberately a test oracle, not a Lean claim.
function decodeEnvelope(rawHex) {
  const raw = bytes(rawHex), typed = raw[0] < 0x80, type = typed ? raw[0] : 0
  assert([0, 1, 2, 3].includes(type))
  const fields = RLP.decode(typed ? raw.slice(1) : raw)
  assert.equal(hex(RLP.encode(fields)), hex(typed ? raw.slice(1) : raw), 'retained canonical signed encoding')
  const last = fields.length - 3, signature = fields.slice(last)
  const chainId = type === 0 ? (scalar(signature[0]) >= 35n ? (scalar(signature[0]) - 35n) / 2n : null) : scalar(fields[0])
  const signed = type === 0 ? (chainId === null ? fields.slice(0, 6) :
    [...fields.slice(0, 6), nat(chainId), bytes(''), bytes('')]) : fields.slice(0, last)
  const signingBytes = type === 0 ? RLP.encode(signed) : Uint8Array.from([type, ...RLP.encode(signed)])
  const recovery = type === 0 ? (chainId === null ? scalar(signature[0]) : scalar(signature[0]) - chainId * 2n - 8n)
    : scalar(signature[0]) + 27n
  const sender = bytesToBigInt(publicToAddress(ecrecover(keccak(signingBytes), recovery,
    fixed(scalar(signature[1]), 32), fixed(scalar(signature[2]), 32))))
  assert(senders.includes(sender), 'retained synthetic signer')
  const gasIndex = type === 0 ? 2 : type === 1 ? 3 : 4, toIndex = gasIndex + 1
  const access = type === 0 ? [] : fields[toIndex + 3]
  const transaction = { type, chainId: chainId === null ? null : decimal(chainId), sender: decimal(sender),
    to: decimal(scalar(fields[toIndex])), nonce: decimal(scalar(fields[type === 0 ? 0 : 1])),
    value: decimal(scalar(fields[toIndex + 1])), gasLimit: decimal(scalar(fields[gasIndex])),
    gasPriceCap: decimal(scalar(fields[type === 0 ? 1 : type === 1 ? 2 : 3])),
    priorityFeeCap: decimal(type >= 2 ? scalar(fields[2]) : 0), dataHex: hex(fields[toIndex + 2]),
    accessList: access.map(([address, keys]) => ({ address: decimal(scalar(address)), storageKeys: keys.map(key => decimal(scalar(key))) })) }
  return { transaction, ...(type === 3 ? { blobVersionedHashes: fields[10].map(hex), maxFeePerBlobGas: decimal(scalar(fields[9])) } : {}) }
}

const push = value => {
  const encoded = hex(nat(value))
  return encoded ? (0x5f + encoded.length / 2).toString(16) + encoded : '5f'
}
const effects = ending => '5f49805f555f52610abc60205fa160205f' + (ending ?? 'f3')
const hashReturn = '5f495f5260205ff3', slots = [['0', '7'], ['1', '9'], ['2', '0'], ['3', '0']]
function fixtureOptions(id) {
  const out = { code: '00', coinbase: beneficiary, secondBalance: 10n ** 15n, blockGas: 30_000_000n, excess: 0n }
  if (['single-blobhash', 'hash-context-reset', 'revert-middle-keeps-blob-burn', 'exception-middle-keeps-blob-burn',
    'sender-is-beneficiary', 'recipient-is-beneficiary', 'six-blob-aggregate', 'failed-receipt-still-counts-three-blobs',
    'nonzero-blob-price-across-failures'].includes(id)) out.code = effects()
  if (id === 'original-storage-reset') { out.code = '5f355f555f545f5260205ff3'; out.initialSlot = '0' }
  if (['warm-storage-reset', 'access-list-reset'].includes(id)) out.code = '5f545f54505f5260205ff3'
  if (['refund-reset', 'refund-restores-block-gas-pool'].includes(id)) out.code = '5f5f5500'
  if (id === 'receipt-log-reset') out.code = '5f355f52610abc60205fa160205ff3'
  if (['dependent-recipient-funding', 'beneficiary-tip-funds-next-sender', 'invalid-middle-balance'].includes(id)) out.secondBalance = 0n
  if (id === 'beneficiary-tip-funds-next-sender') out.coinbase = senders[1]
  if (['sender-is-beneficiary', 'sender-recipient-beneficiary-alias'].includes(id)) out.coinbase = senders[0]
  if (id === 'recipient-is-beneficiary') out.coinbase = parent
  if (['refund-restores-block-gas-pool', 'gas-limit-sum-exceeds-block-but-sequentially-fits',
    'invalid-middle-block-gas-reservation'].includes(id)) out.blockGas = 100_000n
  if (id === 'nonzero-blob-price-across-failures') out.excess = 80n * unit
  if (id.startsWith('nested-')) {
    const op = id.slice(7, -14), operands = [32n, 0n, 0n, 0n]
    assert(['call', 'callcode', 'delegatecall', 'staticcall'].includes(op), id)
    if (op === 'call' || op === 'callcode') operands.push(0n)
    out.code = [...operands, child, 30_000n].map(push).join('') +
      { call: 'f1', callcode: 'f2', delegatecall: 'f4', staticcall: 'fa' }[op] + '6020525f4960405260605ff3'
    out.childCode = hashReturn
  }
  return out
}
function initialAccounts(options) {
  const rows = new Map()
  const record = (address, { balance = 0n, nonce = 1n, code = '', storage = [] } = {}) => {
    const row = { address: decimal(address), exists: true, balance: decimal(balance), nonce: decimal(nonce), codeHex: code,
      storage: storage.map(([key, value]) => ({ key: decimal(key), value: decimal(value) })) }
    rows.set(row.address, row)
  }
  record(senders[0], { balance: 10n ** 15n, nonce: 7n })
  record(senders[1], { balance: options.secondBalance, nonce: 9n })
  record(parent, { balance: 5000n, code: options.code, storage: [['0', options.initialSlot ?? '7'], ...slots.slice(1)] })
  record(child, { balance: 100n, code: options.childCode ?? '', storage: slots })
  record(reverter, { balance: 100n, code: effects('fd'), storage: slots })
  record(invalid, { balance: 100n, code: effects('fe'), storage: slots })
  record(unsupported, { balance: 100n, code: '5f0c00', storage: slots })
  if (!rows.has(decimal(options.coinbase))) record(options.coinbase, { balance: 11n })
  return [...rows.values()]
}
function headers(options, gasUsed, blobGasUsed) {
  const make = (number, timestamp, gas, blobs) => [fixed(0, 32), fixed(0, 32), fixed(options.coinbase, 20),
    fixed(0, 32), fixed(0, 32), fixed(0, 32), fixed(0, 256), nat(0), nat(number), nat(options.blockGas), nat(gas),
    nat(timestamp), bytes(''), fixed(9, 32), fixed(0, 8), nat(2), fixed(0, 32), nat(blobs), nat(options.excess), fixed(0, 32)]
  const parentHeader = make(19_500_000, 1_710_338_235, options.blockGas / 2n, 3n * unit)
  const childHeader = make(19_500_001, 1_710_338_236, gasUsed, blobGasUsed)
  childHeader[0] = keccak(RLP.encode(parentHeader))
  return { parentHeader: parentHeader.map(hex), childHeader: childHeader.map(hex) }
}
const anchor = (request, root) => {
  request.parentHeader[3] = root
  request.childHeader[0] = hex(keccak(RLP.encode(request.parentHeader.map(bytes))))
}

export async function buildTransactionLists() {
  const cases = []
  for (const row of snapshot.rows) {
    const options = fixtureOptions(row.id), accounts = initialAccounts(options)
    const transactions = row.txBytes.map(raw => ({
      fuel: row.id === 'maximum-256-entries' ? '10' : row.id === 'maximum-reserved-fuel' ? '500000' : '1000',
      ...decodeEnvelope(raw),
    }))
    const declaredBlobs = row.id === 'invalid-seven-blob-aggregate' ? 6n * unit :
      transactions.reduce((sum, entry) => sum + BigInt(entry.blobVersionedHashes?.length ?? 0) * unit, 0n)
    const decoded = { schemaVersion: 1, accounts, transactions,
      ...headers(options, BigInt(row.gasUsed ?? options.blockGas), BigInt(row.blobGasUsed ?? declaredBlobs)) }
    // All 30 complete-execution requests reconstruct byte-for-byte. Rejected
    // lists stop before final totals, whose full values were not retained.
    // A permissive in-range declared execution total preserves the original
    // rejection instead of introducing an earlier prefix-gas failure.
    const reconstructedSha256 = digest(JSON.stringify(decoded))
    if (row.category === 'execution') assert.equal(reconstructedSha256, row.requestSha256, row.id + ': original input binding')
    const witnesses = await buildStateWitness(accounts)
    await checkStateWitness(witnesses, accounts)
    const request = { schemaVersion: 2, parentHeader: clone(decoded.parentHeader), childHeader: clone(decoded.childHeader),
      accounts: witnesses.accounts, transactions: clone(transactions) }
    anchor(request, witnesses.stateRoot)
    const baseline = { ...decoded, parentHeader: clone(request.parentHeader), childHeader: clone(request.childHeader) }
    cases.push({ id: row.id, category: row.category, transactions: transactions.length, request, baseline, expected: row,
      originalRequestSha256: row.requestSha256, reconstructedSha256,
      exactOriginalRequest: row.category === 'execution', stateRoot: witnesses.stateRoot })
  }
  assert.equal(cases.length, 36)
  assert.equal(cases.filter(test => test.exactOriginalRequest).length, 30)
  assert.equal(cases.reduce((sum, test) => sum + test.transactions, 0), 344)
  return cases
}

async function compareRetained(test, actual) {
  assert.equal(actual.status, test.expected.status, test.id + ': retained verdict')
  if (test.category !== 'execution') {
    assert.equal(actual.index, test.expected.index, test.id + ': retained first rejected index')
    assert.equal(actual.reason, test.expected.reason, test.id + ': retained rejection/boundary reason')
    assert(!('accounts' in actual) && !('receipts' in actual), 'no accepted partial state')
    return
  }
  assert.equal(actual.gasUsed, test.expected.gasUsed)
  assert.equal(actual.blobGasUsed, test.expected.blobGasUsed)
  assert.deepEqual(actual.receipts, test.expected.receipts, test.id + ': all retained receipt fields')
  const final = await buildStateWitness(actual.accounts)
  assert.equal('0x' + final.stateRoot, test.expected.stateRoot, test.id + ': complete independent final state commitment')
  const trie = new MerklePatriciaTrie({ useKeyHashing: false })
  for (const [index, raw] of test.expected.txBytes.entries()) await trie.put(RLP.encode(nat(index)), bytes(raw))
  assert.equal('0x' + hex(trie.root()), test.expected.transactionRoot, test.id + ': unchanged signed-byte commitment')
}

async function main() {
  const options = { oracleOnly: false }, args = process.argv.slice(2)
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--oracle-only') options.oracleOnly = true
    else if (['--list-bin', '--baseline-bin', '--output', '--fixtures'].includes(args[i])) {
      assert(args[i + 1]); options[args[i].slice(2)] = resolve(args[++i])
    } else throw Error('unknown argument: ' + args[i])
  }
  const executable = options['list-bin'] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-transaction-list', import.meta.url))
  const started = performance.now(), cases = await buildTransactionLists(), rows = [], failures = [], controls = []
  if (options.fixtures) writeFileSync(options.fixtures, JSON.stringify({ schemaVersion: 1,
    kind: 'authenticated-list-test-fixtures-not-results', cases }, null, 2) + '\n')
  const directory = mkdtempSync(join(tmpdir(), 'lean-authenticated-lists-'))
  let nativeInvocations = 0
  const run = (mode, request, binary = executable) => {
    const path = join(directory, 'request.json'); writeFileSync(path, JSON.stringify(request)); nativeInvocations++
    const result = spawnSync(binary, ['--dangerously-enable-unverified-keccak', mode, path],
      { encoding: 'utf8', timeout: 60_000, maxBuffer: 32 * 1024 * 1024 })
    if (result.error) throw result.error
    assert.equal(result.status, 0, result.stdout + '\n' + result.stderr)
    assert.equal(result.stderr, '')
    return JSON.parse(result.stdout)
  }
  try {
    if (!options.oracleOnly) for (const test of cases) {
      const before = performance.now()
      try {
        const baseline = run('--transaction-list', test.baseline), actual = run('--authenticated-transaction-list', test.request)
        assert.equal(baseline.schemaVersion, 1); assert.equal(actual.schemaVersion, 2)
        assert.deepEqual({ ...actual, schemaVersion: 1 }, baseline, test.id + ': complete decoded/authenticated output equality')
        if (options['baseline-bin']) {
          const previous = run('--transaction-list', test.baseline, options['baseline-bin'])
          assert.deepEqual(baseline, previous, test.id + ': complete prior/current decoded regression comparison')
        }
        await compareRetained(test, actual)
        rows.push({ id: test.id, category: test.category, transactions: test.transactions, status: actual.status,
          exactOriginalRequest: test.exactOriginalRequest, requestSha256: digest(JSON.stringify(test.request)),
          outcomeSha256: digest(JSON.stringify(actual)), milliseconds: performance.now() - before,
          ...(actual.status === 'executed' ? { gasUsed: actual.gasUsed, blobGasUsed: actual.blobGasUsed,
            receipts: actual.receipts.length, finalStateRoot: test.expected.stateRoot } : { index: actual.index, reason: actual.reason }) })
      } catch (error) { failures.push({ id: test.id, message: String(error).slice(0, 6000) }) }
    }
    if (!options.oracleOnly && !failures.length) {
      const first = cases.find(test => test.id === 'single-blobhash')
      for (const [id, mutate] of [
        ['code-byte-tamper', request => { request.accounts.find(row => row.address === decimal(parent)).codeHex += '00' }],
        ['missing-account-proof', request => { request.accounts[0].accountProof = [] }],
        ['changed-used-proof-bytes', request => { request.accounts[0].accountProof[0] += '80' }],
        ['wrong-parent-state-root', request => { anchor(request, 'ff'.repeat(32)) }],
        ['swapped-storage-root-proof', request => {
          const contract = request.accounts.find(row => row.address === decimal(parent))
          contract.storage[0].proof = []
        }],
      ]) {
        const request = clone(first.request); mutate(request)
        // If the runner executes any transaction, its zero fuel gives a different
        // indexed outcome. Refusal must happen before execution begins.
        request.transactions[0].fuel = '0'
        const actual = run('--authenticated-transaction-list', request)
        assert.equal(actual.status, 'indeterminate', id); assert.equal(actual.index, null, id)
        assert(actual.reason.startsWith('state-witness:'), id + ': admission before execution')
        assert(!('accounts' in actual) && !('receipts' in actual) && !('gasUsed' in actual), id + ': no partial result')
        controls.push({ id, status: actual.status, reason: actual.reason })
      }
      const empty = cases.find(test => test.id === 'empty-list'), records = clone(empty.baseline.accounts)
      records.push({ address: '224', exists: true, balance: '0', nonce: '0', codeHex: '', storage: [] })
      const witnessed = await buildStateWitness(records), request = clone(empty.request)
      request.accounts = witnessed.accounts; anchor(request, witnessed.stateRoot)
      const actual = run('--authenticated-transaction-list', request)
      assert.equal(actual.status, 'indeterminate'); assert.equal(actual.index, null)
      assert.equal(actual.reason, 'authenticated-empty-account-profile')
      controls.push({ id: 'present-empty-account-profile', status: actual.status, reason: actual.reason })
      assert.equal(controls.length, 6)

      // Falsify the join to the dated evidence, including rejected fixture index.
      const accepted = cases.find(test => test.id === 'single-blobhash'), rejected = cases.find(test => test.id === 'invalid-middle-nonce')
      await assert.rejects(() => compareRetained(rejected, { status: 'rejected', index: rejected.expected.index + 1, reason: rejected.expected.reason }))
      await assert.rejects(() => compareRetained(accepted, { status: 'rejected', index: 0, reason: 'invalid-sender-nonce' }))
      controls.push({ id: 'retained-evidence-index-and-category-falsification', passed: true })
    }
  } catch (error) { failures.push({ id: 'admission-controls', message: String(error).slice(0, 6000) }) }
  finally { rmSync(directory, { recursive: true, force: true }) }
  const report = { schemaVersion: 1, kind: 'authenticated-ordered-transaction-list-integration',
    mode: options.oracleOnly ? 'fixture-and-oracle-only' : 'native-cli', generatedLists: cases.length,
    exactOriginalExecutionRequests: cases.filter(test => test.exactOriginalRequest).length,
    allListTransactions: cases.reduce((sum, test) => sum + test.transactions, 0), nativeInvocations,
    passed: rows.length, failed: failures.length, controls, rows, failures, milliseconds: performance.now() - started,
    nativeSha256: options.oracleOnly ? null : digest(readFileSync(executable)),
    priorBaselineSha256: options.oracleOnly || !options['baseline-bin'] ? null : digest(readFileSync(options['baseline-bin'])),
    retainedEvidenceSha256: digest(snapshotBytes),
    referenceBoundary: 'The 2026-11-24 EthereumJS/Geth outputs are pinned recorded evidence. This run reconstructs all 30 executed requests byte-for-byte, reuses all 344 retained signed transaction occurrences, recovers their senders through the independent test library, builds authenticated prestate independently, runs both current native CLI modes, and compares complete output plus retained receipts and final state commitments. The six refusal/boundary fixtures reuse signed transactions and prestate but declare the valid block-gas limit as final execution gas because the original unobserved total was not retained; this preserves the tested first rejection. An optional separately built prior binary supplies a third full-output regression comparison. It does not rerun Geth or EthereumJS execution.',
    scope: 'Initial state proof admission only; decoded sender/signature, system-operation coverage, canonical header chain, transaction/receipt/poststate commitments and cryptographic refinement remain separate obligations.' }
  if (options.output) writeFileSync(options.output, JSON.stringify(report, null, 2) + '\n')
  console.log(JSON.stringify(options.output ? { ...report, rows: undefined } : report))
  if (failures.length || (!options.oracleOnly && (rows.length !== 36 || controls.length !== 7))) process.exitCode = 1
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) await main()
