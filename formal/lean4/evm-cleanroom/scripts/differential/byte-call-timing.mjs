#!/usr/bin/env node
/** Paired end-to-end execution timings for two existing CLI paths. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync, realpathSync } from 'node:fs'
import { cpus, platform, arch, release } from 'node:os'

if (process.argv.length !== 6) {
  throw Error('usage: node byte-call-timing.mjs BEFORE_EXE BEFORE_SOURCE AFTER_EXE AFTER_SOURCE')
}
const [beforePath, beforeSource, afterPath, afterSource] = process.argv.slice(2)
function identify(path, source) {
  assert.match(source, /^[0-9a-f]{40}$/)
  const executable = realpathSync(path)
  const sha256 = createHash('sha256').update(readFileSync(executable)).digest('hex')
  return {executable, source, sha256}
}
const before = identify(beforePath, beforeSource)
const after = identify(afterPath, afterSource)
assert.notEqual(before.sha256, after.sha256)
assert.notEqual(before.source, after.source)

const warmupPairs = 12
const measuredPairs = 160
const paths = [
  {name: 'legacy-frame-call-abi', args: ['--frame-call', '6004356024359010155f5260205ff3',
    '11223344' + '0'.repeat(63) + '8' + '0'.repeat(63) + '1', '50000', '100']},
  {name: 'legacy-zero-window-call-with-storage', args: ['--call-opcode',
    '5f5f5f5f5f60c3617530f100', '600160005500', '50000', '100']},
]
function measure(engine, args) {
  const start = process.hrtime.bigint()
  const child = spawnSync(engine.executable, args, {encoding:'utf8', timeout:10000})
  const ns = Number(process.hrtime.bigint() - start)
  if (child.error || child.status !== 0) throw Error(String(child.error ?? child.stderr))
  const json = JSON.parse(child.stdout)
  assert(Number.isSafeInteger(ns) && ns > 0)
  return {ns, json}
}
function summary(samples) {
  const sorted = [...samples].sort((a,b) => a-b)
  const rank = q => sorted[Math.ceil(q * sorted.length) - 1]
  return {
    p50: rank(0.5), p95: rank(0.95), p99: rank(0.99),
    max: sorted.at(-1), min: sorted[0], spread: sorted.at(-1) - sorted[0]
  }
}

function paired(path) {
  const {name,args} = path
  const reference = measure(before, args).json
  const expected = name === 'legacy-frame-call-abi' ? 'returned' : 'stopped'
  assert.equal(reference.status, expected)
  const fields = Object.keys(reference)
  const projection = obj => Object.fromEntries(fields.map(field => [field, obj[field]]))
  const samples = []
  for (let i = -warmupPairs; i < measuredPairs; i++) {
    const order = i % 2 === 0 ? ['before', 'after'] : ['after', 'before']
    const pair = {first: order[0]}
    for (const lane of order) {
      const reading = measure(lane === 'before' ? before : after, args)
      assert.deepEqual(projection(reading.json), reference, name + ' ' + lane + ' CLI result')
      pair[lane] = reading.ns
    }
    if (i >= 0) samples.push(pair)
  }
  return {
    name, args, comparedLegacyFields: fields, samples,
    before: summary(samples.map(s => s.before)),
    after: summary(samples.map(s => s.after)),
    pairedAfterMinusBefore: summary(samples.map(s => s.after - s.before))
  }
}
console.log(JSON.stringify({
  kind: 'paired-native-evm-cli-timing', units: 'nanoseconds', quantiles: 'nearest rank',
  measured: 'child process launch, native interpretation, JSON serialization and process exit',
  date: new Date().toISOString(), system: {
    os: platform(), release: release(), arch: arch(), cpu: cpus()[0]?.model, logicalCpus: cpus().length,
    node: process.version
  },
  warmupPairs, measuredPairs, before, after, paths: paths.map(paired)
}))
