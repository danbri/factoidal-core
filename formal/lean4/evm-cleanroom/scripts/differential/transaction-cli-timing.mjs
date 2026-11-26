#!/usr/bin/env node
/** Paired unchanged transaction-CLI timings; this is measurement, not an oracle. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { mkdtempSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs'
import { arch, cpus, platform, release, tmpdir } from 'node:os'
import { join } from 'node:path'

assert.equal(process.argv.length, 7,
  'usage: transaction-cli-timing.mjs BEFORE_BIN_DIR BEFORE_COMMIT AFTER_BIN_DIR AFTER_COMMIT BLOB_REQUEST')
const [beforeDir, beforeCommit, afterDir, afterCommit, fixturePath] = process.argv.slice(2)
for (const commit of [beforeCommit, afterCommit]) assert.match(commit, /^[a-f0-9]{40}$/)
const digest = bytes => createHash('sha256').update(bytes).digest('hex')
const identify = (directory, source, name) => {
  const executable = realpathSync(join(directory, name))
  return { executable, source, sha256: digest(readFileSync(executable)) }
}
const blob = JSON.parse(readFileSync(fixturePath, 'utf8'))
assert.equal(blob.transaction.type, 3)
const ordinary = structuredClone(blob)
ordinary.transaction.type = 2
for (const field of ['parentHeader', 'childHeader', 'blobVersionedHashes', 'maxFeePerBlobGas', 'priorBlobGas'])
  delete ordinary[field]
const temporary = mkdtempSync(join(tmpdir(), 'lean-transaction-timing-'))
const warmupPairs = 12, measuredPairs = 160
const summary = values => {
  const sorted = [...values].sort((a, b) => a - b)
  const rank = q => sorted[Math.ceil(q * sorted.length) - 1]
  return { p50: rank(0.5), p95: rank(0.95), p99: rank(0.99),
    min: sorted[0], max: sorted.at(-1), spread: sorted.at(-1) - sorted[0] }
}
function measure(engine, args) {
  const start = process.hrtime.bigint()
  const child = spawnSync(engine.executable, args, { encoding: 'utf8', timeout: 10_000, maxBuffer: 1024 * 1024 })
  const ns = Number(process.hrtime.bigint() - start)
  assert.ifError(child.error)
  assert.equal(child.status, 0, child.stderr)
  assert.equal(child.stderr, '')
  assert.equal(JSON.parse(child.stdout).status, 'executed')
  return { ns, output: child.stdout }
}
try {
  const paths = []
  for (const [name, file, input, mode] of [
    ['ordinary-cancun-call', 'evm-call-transaction', ordinary, '--call-transaction'],
    ['blob-cancun-call', 'evm-blob-call', blob, '--batch'],
  ]) {
    const inputFile = join(temporary, name + '.json')
    const encoded = JSON.stringify(input) + '\n'
    writeFileSync(inputFile, encoded)
    const args = ['--dangerously-enable-unverified-keccak', mode, inputFile]
    const before = identify(beforeDir, beforeCommit, file), after = identify(afterDir, afterCommit, file)
    const expected = measure(before, args).output, samples = []
    for (let i = -warmupPairs; i < measuredPairs; i++) {
      const order = i % 2 === 0 ? ['before', 'after'] : ['after', 'before']
      const pair = { first: order[0] }
      for (const lane of order) {
        const result = measure(lane === 'before' ? before : after, args)
        assert.equal(result.output, expected, name + ': byte-identical result')
        pair[lane] = result.ns
      }
      if (i >= 0) samples.push(pair)
    }
    paths.push({ name, before, after, requestSha256: digest(encoded), outputSha256: digest(expected),
      samples, beforeDistribution: summary(samples.map(x => x.before)),
      afterDistribution: summary(samples.map(x => x.after)),
      pairedAfterMinusBefore: summary(samples.map(x => x.after - x.before)) })
  }
  console.log(JSON.stringify({ kind: 'paired-unchanged-transaction-cli-timing', units: 'nanoseconds',
    quantiles: 'nearest rank', measured: 'process launch, file/JSON input, execution, JSON output and exit',
    date: new Date().toISOString(), warmupPairs, measuredPairs,
    system: { os: platform(), release: release(), arch: arch(), cpu: cpus()[0]?.model,
      logicalCpus: cpus().length, node: process.version },
    paths, limitation: 'Two synthetic process-inclusive paths; not whole-list throughput or a latency guarantee.' }))
} finally {
  rmSync(temporary, { recursive: true, force: true })
}
