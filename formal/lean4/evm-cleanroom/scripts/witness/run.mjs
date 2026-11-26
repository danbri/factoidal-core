#!/usr/bin/env node
/** Run actual Lean CLIs; external packages only construct/check test expectations. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { performance } from 'node:perf_hooks'
import { buildCorpus } from './corpus.mjs'
import { clone, digest, sourcePins } from './oracle.mjs'

export function compareCase(test, actual) {
  assert.equal(actual.status, test.expect.status, test.id + ': status')
  assert.equal(actual.schemaVersion, 1, test.id + ': schema version')
  assert.equal(actual.keccakOptIn, test.optIn !== false, test.id + ': explicit Keccak acceptance')
  for (const [field, value] of Object.entries(test.expect))
    assert.deepEqual(actual[field], value, test.id + '/' + field)
  const metadata = ['schemaVersion', 'keccakOptIn']
  if (actual.status === 'refused' || actual.status === 'inputError') {
    assert.equal(typeof actual.reason, 'string', test.id + ': refusal reason')
    assert(actual.reason.length > 0)
    if (test.reasonIncludes) assert(actual.reason.includes(test.reasonIncludes), test.id + ': classified refusal reason')
    assert(Object.keys(actual).every(field => [...metadata, 'status', 'classification', 'reason'].includes(field)),
      test.id + ': refusal must not expose an accepted partial result')
  } else {
    assert(Object.keys(actual).every(field => [...metadata, ...Object.keys(test.expect)].includes(field)),
      test.id + ': unexpected result field')
  }
}

const requestText = test => test.rawRequest ?? JSON.stringify(test.request)
const expectedResponse = test => ({ schemaVersion: 1, keccakOptIn: test.optIn !== false,
  ...(['refused', 'inputError'].includes(test.expect.status) ? { reason: test.reasonIncludes ?? 'synthetic comparator refusal' } : {}),
  ...clone(test.expect) })

function compareInventory(cases, rows) {
  assert.equal(rows.length, cases.length, 'complete native inventory')
  assert.equal(new Set(rows.map(row => row.id)).size, rows.length, 'unique native fixture ids')
  const byId = new Map(rows.map(row => [row.id, row]))
  for (const test of cases) {
    const row = byId.get(test.id); assert(row, 'missing fixture: ' + test.id)
    assert.equal(row.requestSha256, digest(requestText(test)), test.id + ': request binding')
    compareCase(test, row.actual)
  }
}

function comparatorControls(cases) {
  const controls = []
  const get = id => { const test = cases.find(row => row.id === id); assert(test, id); return test }
  const rejectMutation = (name, id, mutate) => {
    const test = get(id), wrong = expectedResponse(test)
    mutate(wrong)
    assert.throws(() => compareCase(test, wrong), undefined, name)
    controls.push(name)
  }
  rejectMutation('changed-membership-value', 'mpt/inline-empty-suffix-leaf', out => { out.valueHex = 'ff' })
  rejectMutation('present-replaced-with-absence', 'mpt/inline-empty-suffix-leaf', out => { out.status = 'absent'; delete out.valueHex })
  rejectMutation('absence-replaced-with-refusal', 'mpt/empty-trie', out => { out.status = 'refused'; out.reason = 'missing proof' })
  rejectMutation('missing-proof-replaced-with-absence', 'mpt/missing-hashed-child', out => { out.status = 'absent'; delete out.reason })
  rejectMutation('resource-replaced-with-invalid', 'mpt/proof-nodes-one-over', out => { out.classification = 'invalid' })
  rejectMutation('refusal-leaks-value', 'mpt/missing-hashed-child', out => { out.valueHex = '01' })
  rejectMutation('wrong-rlp-payload', 'official-rlp/shortstring', out => { out.payloadHex = '01' })
  rejectMutation('missing-rlp-child', 'official-rlp/stringlist', out => { out.children.pop() })
  rejectMutation('wrong-scalar', 'rlp-scalar/one', out => { out.integer = '2' })
  rejectMutation('missing-schema-version', 'rlp-scalar/one', out => { delete out.schemaVersion })
  for (const field of ['balance', 'nonce', 'codeHex'])
    rejectMutation('changed-derived-' + field, 'state/multiple-accounts-storage', out => { out.accounts[0][field] = '0' })
  rejectMutation('changed-derived-storage', 'state/multiple-accounts-storage', out => { out.accounts[0].storage[0].value = '0' })
  rejectMutation('omitted-derived-account', 'state/multiple-accounts-storage', out => { out.accounts.pop() })
  rejectMutation('present-empty-coerced-to-absence', 'state/present-empty-account', out => { out.accounts[0].exists = false })
  const rows = cases.map(test => ({ id: test.id, requestSha256: digest(requestText(test)), actual: expectedResponse(test) }))
  compareInventory(cases, rows)
  for (const [name, mutate] of [
    ['dropped-fixture', rows => { rows.pop() }],
    ['duplicate-fixture', rows => { rows[1] = clone(rows[0]) }],
    ['renamed-fixture', rows => { rows[0].id = 'not-in-corpus' }],
    ['changed-request-binding', rows => { rows[0].requestSha256 = '0'.repeat(64) }],
  ]) {
    const wrong = clone(rows); mutate(wrong)
    assert.throws(() => compareInventory(cases, wrong), undefined, name); controls.push(name)
  }
  assert.equal(controls.length, 20, 'fixed falsification inventory')
  return controls
}

async function main() {
  const args = process.argv.slice(2), options = { oracleOnly: false }
  for (let index = 0; index < args.length; index++) {
    const arg = args[index]
    if (arg === '--oracle-only') options.oracleOnly = true
    else if (['--proof-bin', '--list-bin', '--output', '--fixtures'].includes(arg)) {
      assert(args[index + 1], arg + ' needs a path'); options[arg.slice(2)] = resolve(args[++index])
    } else throw Error('unknown argument: ' + arg)
  }
  const proofBin = options['proof-bin'] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-witness-proof', import.meta.url))
  const listBin = options['list-bin'] ?? fileURLToPath(new URL('../../.lake/build/bin/evm-transaction-list', import.meta.url))
  const started = performance.now(), corpus = await buildCorpus(), { cases, oracleCounts } = corpus
  assert.equal(cases.length, 189, 'fixed complete corpus')
  const controls = comparatorControls(cases)
  if (options.fixtures) writeFileSync(options.fixtures, JSON.stringify({ schemaVersion: 1,
    kind: 'test-fixtures-not-native-results', sources: sourcePins, cases }, null, 2) + '\n')
  const rows = [], failures = [], directory = mkdtempSync(join(tmpdir(), 'lean-mpt-witness-'))
  try {
    if (!options.oracleOnly) for (const test of cases) {
      const requestPath = join(directory, 'request.json'), requestBytes = requestText(test)
      writeFileSync(requestPath, requestBytes)
      const binary = test.mode === '--state-witness' ? listBin : proofBin, before = performance.now()
      try {
        const result = spawnSync(binary, [...(test.optIn === false ? [] : ['--dangerously-enable-unverified-keccak']), test.mode, requestPath],
          { encoding: 'utf8', timeout: 60_000, maxBuffer: 4 * 1024 * 1024 })
        if (result.error) throw result.error
        assert.equal(result.status, test.exitCode ?? 0, test.id + ': process exit\n' + result.stdout.slice(0, 2000) + '\n' + result.stderr)
        assert.equal(result.stderr, '', test.id + ': no unstructured diagnostics')
        const actual = JSON.parse(result.stdout)
        compareCase(test, actual)
        rows.push({ id: test.id, family: test.family, requestSha256: digest(requestBytes),
          responseSha256: digest(result.stdout), exitCode: result.status, milliseconds: performance.now() - before, actual })
      } catch (error) { failures.push({ id: test.id, family: test.family, message: String(error).slice(0, 5000) }) }
    }
    if (!options.oracleOnly && !failures.length) compareInventory(cases, rows)
  } finally { rmSync(directory, { recursive: true, force: true }) }
  const groups = Object.fromEntries([...new Set(cases.map(test => test.family))].map(family => [family, {
    cases: cases.filter(test => test.family === family).length,
    nativePassed: rows.filter(row => row.family === family).length,
    nativeFailed: failures.filter(row => row.family === family).length,
  }]))
  const report = { schemaVersion: 1, kind: 'pure-lean-state-witness-tests',
    mode: options.oracleOnly ? 'oracle-and-comparator-only' : 'native-cli',
    generatedCases: cases.length, nativeInvocations: options.oracleOnly ? 0 : cases.length,
    nativePassed: rows.length, nativeFailed: failures.length, oracleCounts, comparatorControls: controls,
    milliseconds: performance.now() - started, groups,
    binaries: options.oracleOnly ? null : { proof: { path: proofBin, sha256: digest(readFileSync(proofBin)) },
      transactionList: { path: listBin, sha256: digest(readFileSync(listBin)) } },
    sources: sourcePins, rows, failures,
    scope: 'Actual bounded RLP, proof and state-admission CLI checks under a declared root. No signed-envelope authentication, canonical-chain proof, complete global trie canonicality, post-state-root construction or cryptographic refinement proof is implied.' }
  if (options.output) writeFileSync(options.output, JSON.stringify(report, null, 2) + '\n')
  console.log(JSON.stringify(options.output ? { ...report, rows: undefined, sources: undefined } : report))
  if (failures.length || (!options.oracleOnly && rows.length !== cases.length)) process.exitCode = 1
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url))
  await main()
