import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { copyFileSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { basename, delimiter, dirname, join, resolve } from 'node:path'

const [subsetPath, companionPath] = process.argv.slice(2)
assert(subsetPath && companionPath, 'expected the evm-subset and evm-call-transaction paths')
const subset = resolve(subsetPath)
const companion = resolve(companionPath)
const optIn = '--dangerously-enable-unverified-keccak'
const cwd = mkdtempSync(join(tmpdir(), 'evm-call-transaction-routing-'))
const requestPath = 'call transaction request.json'
const malformedPath = 'malformed request.json'

const request = {
  schemaVersion: 1,
  fork: 'shanghai',
  fuel: '10',
  transaction: {
    type: 2, chainId: '1', sender: '256', to: '257', nonce: '0', value: '0', gasLimit: '40000',
    gasPriceCap: '10', priorityFeeCap: '2', dataHex: '', accessList: [],
  },
  block: {
    chainId: '1', coinbase: '258', number: '1', timestamp: '1', gasLimit: '30000000',
    gasUsedBefore: '0', baseFee: '7', prevRandao: '0', blobBaseFee: '0',
  },
  accounts: [
    { address: '256', exists: true, balance: '1000000', nonce: '0', codeHex: '', storage: [] },
    { address: '257', exists: true, balance: '0', nonce: '1', codeHex: '00', storage: [] },
    { address: '258', exists: false, balance: '0', nonce: '0', codeHex: '', storage: [] },
  ],
}

function run(executable, args, env = process.env) {
  const { error, status, stderr, stdout } = spawnSync(executable, args, { cwd, encoding: 'utf8', env })
  if (error) throw error
  return { status, stderr, stdout }
}

function expectRouted(args, exit, status, keccakOptIn) {
  const direct = run(companion, args)
  assert.deepEqual(run(subset, args), direct)
  assert.equal(direct.status, exit)
  assert.equal(direct.stderr, '')
  const output = JSON.parse(direct.stdout)
  assert.equal(output.status, status)
  assert.equal(output.keccakOptIn, keccakOptIn)
  return output
}

try {
  writeFileSync(join(cwd, requestPath), JSON.stringify(request))
  writeFileSync(join(cwd, malformedPath), '{"schemaVersion":1,')

  assert.equal(expectRouted(['--call-transaction', requestPath], 0, 'executed', false).gasUsed, '21000')
  assert.equal(expectRouted([optIn, '--observe-logs', '--call-transaction', requestPath],
    0, 'executed', true).receiptStatus, 1)
  assert.equal(typeof expectRouted([optIn, '--call-transaction', malformedPath],
    2, 'inputError', true).reason, 'string')

  const isolated = join(cwd, basename(subset))
  copyFileSync(subset, isolated)
  const env = { ...process.env, PATH: [dirname(companion), process.env.PATH].filter(Boolean).join(delimiter) }
  for (const enabled of [false, true]) {
    const args = [...(enabled ? [optIn] : []), '--call-transaction', requestPath]
    const { status, stderr, stdout } = run(isolated, args, env)
    assert.equal(status, 2)
    assert.equal(stderr, '')
    assert.deepEqual(JSON.parse(stdout), {
      keccakOptIn: enabled, reason: 'transactionCompanionUnavailable', schemaVersion: 1, status: 'inputError',
    })
  }

  const legacy = run(isolated, ['--observe-logs', '602a5f52600160205fa100', '2000', '20'], env)
  assert.equal(legacy.status, 0)
  assert.equal(legacy.stderr, '')
  assert.equal(JSON.parse(legacy.stdout).status, 'ok')
  assert(legacy.stdout.endsWith(`,"logs":[{"address":"0","dataHex":"${'00'.repeat(31)}2a","topics":["1"]}],"logsTruncated":false}\n`))
  console.log(JSON.stringify({ kind: 'call-transaction-cli-routing', routed: 3, missing: 2, legacy: 1 }))
} finally {
  rmSync(cwd, { recursive: true, force: true })
}
