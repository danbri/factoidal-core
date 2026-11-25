#!/usr/bin/env node
/**
 * Optional process-inclusive observations for two authenticated-list fixtures.
 * Two separately built native programs expose three measured modes. External
 * libraries prepare proofs outside timing; no reference client executes here.
 * The automatic flock wrapper excludes cooperating Lean builds while sampling.
 */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { chmodSync, copyFileSync, existsSync, mkdtempSync, readFileSync, rmSync, statSync, writeFileSync } from 'node:fs'
import { availableParallelism, arch, cpus, loadavg, platform, release, tmpdir, totalmem } from 'node:os'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import { performance } from 'node:perf_hooks'
import { buildTransactionLists } from './transaction-lists.mjs'
import { digest } from './oracle.mjs'

const script = fileURLToPath(import.meta.url)
const project = resolve(dirname(script), '../..')
const repository = resolve(project, '../../..')
const baselineRevision = '40c3f0335501677d782df566ef7fd1e8a5cc4ad5'
const modeNames = ['baselineDecoded', 'currentDecoded', 'currentAuthenticated']
const orders = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
const laneNames = ['single-blobhash', 'maximum-256-entries']

function command(binary, args, options = {}) {
  const result = spawnSync(binary, args, { encoding: 'utf8', timeout: 30_000,
    maxBuffer: 32 * 1024 * 1024, ...options })
  if (result.error) throw result.error
  assert.equal(result.status, 0, [binary, ...args].join(' ') + ': ' + result.stderr)
  return result.stdout
}
const fileHash = path => digest(readFileSync(path))
const maybeText = path => existsSync(path) ? readFileSync(path, 'utf8').trim() : null
const canonical = value => Array.isArray(value) ? value.map(canonical) :
  value !== null && typeof value === 'object' ? Object.fromEntries(Object.keys(value).sort().map(key => [key, canonical(value[key])])) : value
const canonicalHash = value => digest(JSON.stringify(canonical(value)))

function distribution(values) {
  assert(values.length > 0 && values.every(Number.isFinite))
  const sorted = [...values].sort((a, b) => a - b)
  const quantile = fraction => {
    const pos = (sorted.length - 1) * fraction, low = Math.floor(pos), high = Math.ceil(pos)
    return sorted[low] + (sorted[high] - sorted[low]) * (pos - low)
  }
  const mean = values.reduce((a, b) => a + b, 0) / values.length
  const standardDeviation = Math.sqrt(values.reduce((sum, value) => sum + (value - mean) ** 2, 0) / values.length)
  return { count: values.length, min: sorted[0], p10: quantile(0.1), p25: quantile(0.25),
    median: quantile(0.5), p75: quantile(0.75), p90: quantile(0.9), p95: quantile(0.95),
    max: sorted.at(-1), mean, standardDeviation }
}

function sourceClosure(root) {
  const seen = new Map(), coreImports = new Set()
  function visit(module) {
    if (seen.has(module)) return
    const path = module.replaceAll('.', '/') + '.lean', raw = readFileSync(join(root, path))
    const entry = { module, path, bytes: raw.length, sha256: digest(raw) }
    seen.set(module, entry)
    for (const match of raw.toString('utf8').matchAll(/^import\s+([^\n]+)/gm)) {
      for (const dependency of match[1].split('--')[0].trim().split(/\s+/)) {
        if (dependency.startsWith('EVMCleanroom.')) visit(dependency)
        else coreImports.add(dependency)
      }
    }
  }
  visit('EVMCleanroom.TransactionListCLI')
  const files = [...seen.values()].sort((a, b) => a.path < b.path ? -1 : a.path > b.path ? 1 : 0)
  return { root, files, sha256: canonicalHash(files), standardLibraryImports: [...coreImports].sort() }
}

function programIdentity(root, executable, buildConfig) {
  const source = sourceClosure(root)
  const artifacts = [buildConfig, 'lean-toolchain', '.lake/build/bin/evm-transaction-list.trace',
    '.lake/build/bin/evm-transaction-list.rsp', '.lake/build/ir/EVMCleanroom/TransactionListCLI.c.o.export.trace']
  const build = artifacts.map(path => ({ path, sha256: fileHash(join(root, path)),
    text: readFileSync(join(root, path), 'utf8') }))
  return { executable, bytes: statSync(executable).size, sha256: fileHash(executable), source, build }
}

function toolchainIdentity(bin) {
  const tools = {}
  for (const name of ['lean', 'lake', 'leanc', 'clang']) {
    const path = join(bin, name)
    tools[name] = { path, sha256: fileHash(path), version: command(path, ['--version']).trim() }
  }
  return tools
}

function optionsFromArgs(args) {
  const options = { warmups: 6, rounds: 30, lock: '/tmp/ethereum-mpt-lean.lock', underLock: false,
    currentRoot: project, output: join(project, 'evidence/mpt-benchmark.json'),
    baselineBuildConfig: 'lakefile-mpt-local.toml', currentBuildConfig: 'lakefile-mpt-primitives-local.toml' }
  const names = { '--baseline-root': 'baselineRoot', '--current-root': 'currentRoot',
    '--baseline-bin': 'baselineBin', '--current-bin': 'currentBin', '--toolchain-bin': 'toolchainBin',
    '--baseline-build-config': 'baselineBuildConfig', '--current-build-config': 'currentBuildConfig',
    '--output': 'output', '--lock': 'lock', '--warmups': 'warmups', '--rounds': 'rounds' }
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--under-lock') { options.underLock = true; continue }
    const name = names[args[i]]; assert(name && args[i + 1], 'unknown/incomplete argument: ' + args[i])
    options[name] = ['warmups', 'rounds'].includes(name) ? Number(args[++i]) : args[++i]
  }
  assert(options.baselineRoot && options.toolchainBin, '--baseline-root and --toolchain-bin are required')
  for (const name of ['baselineRoot', 'currentRoot', 'toolchainBin', 'output', 'lock']) options[name] = resolve(options[name])
  for (const name of ['warmups', 'rounds']) assert(Number.isSafeInteger(options[name]) && options[name] % 6 === 0)
  assert(options.warmups >= 6 && options.rounds >= 30, 'at least six warmups and thirty measurements per mode/lane')
  options.baselineBin = resolve(options.baselineBin ?? join(options.baselineRoot, '.lake/build/bin/evm-transaction-list'))
  options.currentBin = resolve(options.currentBin ?? join(options.currentRoot, '.lake/build/bin/evm-transaction-list'))
  return options
}

async function main() {
  const rawArgs = process.argv.slice(2), options = optionsFromArgs(rawArgs)
  if (!options.underLock) {
    // -F replaces flock with the measured harness, retaining the lock descriptor.
    const result = spawnSync('flock', ['-F', '-w', '60', options.lock, process.execPath, script,
      ...rawArgs, '--under-lock'], { stdio: 'inherit', timeout: 600_000 })
    if (result.error) throw result.error
    assert.equal(result.status, 0, 'benchmark child failed or lock wait timed out')
    return
  }
  const probe = spawnSync('flock', ['-n', options.lock, 'true'])
  assert.equal(probe.status, 1, 'the cooperative compiler/timing lock must already be held')
  const started = performance.now(), generatedAt = new Date().toISOString()
  const baseline = programIdentity(options.baselineRoot, options.baselineBin, options.baselineBuildConfig)
  const current = programIdentity(options.currentRoot, options.currentBin, options.currentBuildConfig)
  for (const file of baseline.source.files) {
    const committed = spawnSync('git', ['-C', repository, 'show', baselineRevision + ':formal/lean4/evm-cleanroom/' + file.path],
      { maxBuffer: 16 * 1024 * 1024, timeout: 30_000 })
    assert.equal(committed.status, 0, 'missing baseline source object: ' + file.path)
    assert.equal(digest(committed.stdout), file.sha256, 'baseline source differs from pinned revision: ' + file.path)
  }
  baseline.source.verifiedRevision = baselineRevision
  current.source.repositoryHead = command('git', ['-C', repository, 'rev-parse', 'HEAD']).trim()
  current.source.workingTreeIdentity = 'The complete transitive project source manifest, not repository HEAD, identifies this uncommitted candidate.'
  const supportPaths = ['scripts/witness/bench.mjs', 'scripts/witness/transaction-lists.mjs',
    'scripts/witness/oracle.mjs', 'scripts/differential/transaction-list.mjs',
    'scripts/differential/package.json', 'scripts/differential/package-lock.json',
    'evidence/2026-11-24-transaction-list/list-execution.json']
  const support = supportPaths.map(path => ({ path, sha256: fileHash(join(project, path)) }))
  const tools = toolchainIdentity(options.toolchainBin)
  const environment = { LEAN_NUM_THREADS: '1', LEAN_STACK_SIZE_KB: '32768', MIMALLOC_ARENA_RESERVE: '64M' }
  const report = { schemaVersion: 1, kind: 'optional-authenticated-witness-process-benchmark', status: 'running', generatedAt,
    methodology: { lanes: laneNames, warmupRoundsPerModeAndLane: options.warmups, measuredRoundsPerModeAndLane: options.rounds,
      order: 'All six permutations of the three modes repeat equally; lane order reverses on alternate rounds.',
      permutations: orders.map(order => order.map(index => modeNames[index])),
      timer: 'performance.now around spawnSync, in milliseconds; includes fresh process startup, native file read, parsing, execution, full JSON serialization and stdout capture. Fixture preparation, file writing and JS comparison are outside timing.',
      processModel: 'Every sample is a fresh process. Warmups warm OS caches; no persistent native process/state and no cache eviction.',
      comparison: 'Every invocation is checked against all three full outputs in its round and the first baseline output, after changing only schemaVersion 2 to 1; retained status, gas, blob gas and every receipt are also checked.',
      quantiles: 'Linear interpolation at (n-1)*p; standard deviation is population standard deviation.',
      lock: options.lock, lockMethod: 'Automatic flock -F wrapper, shared with cooperating Lean builds; does not isolate unrelated host activity.',
      runtimeEnvironment: environment, perProcessTimeoutMs: 30_000, outerHarnessTimeoutMs: 600_000,
      exclusions: 'Warmups are retained in raw rows and excluded from distributions. No measured outliers are discarded.' },
    host: { platform: platform(), release: release(), architecture: arch(), logicalCPUs: cpus().length,
      availableParallelism: availableParallelism(), cpuModel: cpus()[0]?.model, totalMemoryBytes: totalmem(),
      cpuMax: maybeText('/sys/fs/cgroup/cpu.max'), cpuset: maybeText('/sys/fs/cgroup/cpuset.cpus.effective'),
      memoryMax: maybeText('/sys/fs/cgroup/memory.max'), loadAverageStart: loadavg(), node: process.version },
    toolchain: tools, programs: { baseline, current }, supportSources: support, lanes: [], rows: [],
    scope: 'Two small synthetic fixtures from the pinned retained list corpus, on one shared host. These are process-inclusive observations of an experimental executor, not client throughput, execution-component timings, scalability, cryptographic refinement or a consensus-performance guarantee. No Geth/EthereumJS execution is rerun; independent libraries only prepare/check fixture proofs outside timing.' }
  const directory = mkdtempSync(join(tmpdir(), 'lean-witness-bench-'))
  const originals = [options.baselineBin, options.currentBin]
  const frozen = originals.map((path, index) => {
    const copy = join(directory, index === 0 ? 'baseline-transaction-list' : 'current-transaction-list')
    copyFileSync(path, copy); chmodSync(copy, 0o755)
    assert.equal(fileHash(copy), index === 0 ? baseline.sha256 : current.sha256)
    return copy
  })
  let failure
  try {
    const all = await buildTransactionLists()
    const lanes = laneNames.map(id => {
      const test = all.find(row => row.id === id); assert(test && test.category === 'execution' && test.exactOriginalRequest)
      assert.deepEqual(test.baseline.parentHeader, test.request.parentHeader)
      assert.deepEqual(test.baseline.childHeader, test.request.childHeader)
      assert.deepEqual(test.baseline.transactions, test.request.transactions)
      const decodedText = JSON.stringify(test.baseline), authenticatedText = JSON.stringify(test.request)
      const paths = [join(directory, id + '-decoded.json'), join(directory, id + '-authenticated.json')]
      writeFileSync(paths[0], decodedText); writeFileSync(paths[1], authenticatedText)
      const description = { id, transactions: test.transactions, stateRoot: test.stateRoot,
        decodedInput: { bytes: Buffer.byteLength(decodedText), sha256: digest(decodedText) },
        authenticatedInput: { bytes: Buffer.byteLength(authenticatedText), sha256: digest(authenticatedText) },
        originalUnanchoredRequestSha256: test.originalRequestSha256, gasUsed: test.expected.gasUsed,
        blobGasUsed: test.expected.blobGasUsed, referenceOutcome: null }
      report.lanes.push(description)
      return { test, paths, description }
    })
    for (const [phase, count] of [['warmup', options.warmups], ['measured', options.rounds]]) {
      for (let round = 0; round < count; round++) {
        const laneOrder = round % 2 ? [1, 0] : [0, 1]
        for (const laneIndex of laneOrder) {
          const lane = lanes[laneIndex], outputs = new Map(), rows = []
          const order = orders[(round + laneIndex * 3) % orders.length]
          for (const [position, mode] of order.entries()) {
            const args = ['--dangerously-enable-unverified-keccak', mode === 2 ? '--authenticated-transaction-list' : '--transaction-list', lane.paths[mode === 2 ? 1 : 0]]
            const load = loadavg(), before = performance.now()
            const result = spawnSync(frozen[mode === 0 ? 0 : 1], args, { encoding: 'utf8',
              env: { ...process.env, ...environment }, timeout: 30_000, maxBuffer: 32 * 1024 * 1024 })
            const milliseconds = performance.now() - before
            if (result.error) throw result.error
            assert.equal(result.status, 0, lane.test.id + ': ' + result.stdout + result.stderr)
            assert.equal(result.stderr, '', lane.test.id + ': unexpected diagnostic')
            const actual = JSON.parse(result.stdout)
            assert.equal(actual.schemaVersion, mode === 2 ? 2 : 1)
            assert.equal(actual.keccakOptIn, true); assert.equal(actual.status, 'executed')
            assert.equal(actual.gasUsed, lane.test.expected.gasUsed)
            assert.equal(actual.blobGasUsed, lane.test.expected.blobGasUsed)
            assert.deepEqual(actual.receipts, lane.test.expected.receipts, lane.test.id + ': complete retained receipt comparison')
            const normalized = { ...actual, schemaVersion: 1 }
            outputs.set(mode, normalized)
            rows.push({ lane: lane.test.id, phase, round, orderPosition: position, mode: modeNames[mode],
              milliseconds, loadAverageBefore: load, stdoutBytes: Buffer.byteLength(result.stdout),
              stdoutSha256: digest(result.stdout), normalizedOutputSha256: canonicalHash(normalized), completeOutputEqual: false })
          }
          const previous = outputs.get(0)
          if (lane.description.referenceOutcome === null) lane.description.referenceOutcome = previous
          for (const mode of [0, 1, 2]) {
            assert.deepEqual(outputs.get(mode), previous, lane.test.id + ': complete three-mode equality')
            assert.deepEqual(outputs.get(mode), lane.description.referenceOutcome, lane.test.id + ': complete repeated-output equality')
          }
          rows.forEach(row => { row.completeOutputEqual = true })
          report.rows.push(...rows)
        }
        if (round === count - 1 || (round + 1) % 6 === 0)
          console.error(JSON.stringify({ phase, roundsCompleted: round + 1, lanes: laneNames, checkedInvocations: report.rows.length }))
      }
    }
    for (const lane of report.lanes) {
      lane.normalizedOutputSha256 = canonicalHash(lane.referenceOutcome)
      lane.milliseconds = Object.fromEntries(modeNames.map(mode => [mode, distribution(report.rows
        .filter(row => row.phase === 'measured' && row.lane === lane.id && row.mode === mode).map(row => row.milliseconds))]))
      const pairs = [['currentDecoded', 'baselineDecoded'], ['currentAuthenticated', 'currentDecoded'], ['currentAuthenticated', 'baselineDecoded']]
      lane.pairedComparisons = pairs.map(([numerator, denominator]) => {
        const differences = [], ratios = []
        for (let round = 0; round < options.rounds; round++) {
          const rows = report.rows.filter(row => row.phase === 'measured' && row.lane === lane.id && row.round === round)
          const a = rows.find(row => row.mode === numerator).milliseconds, b = rows.find(row => row.mode === denominator).milliseconds
          differences.push(a - b); ratios.push(a / b)
        }
        return { numerator, denominator, differenceMilliseconds: distribution(differences), ratio: distribution(ratios) }
      })
    }
    assert.equal(report.rows.length, laneNames.length * modeNames.length * (options.warmups + options.rounds))
    for (const [index, original] of originals.entries()) {
      assert.equal(fileHash(original), index === 0 ? baseline.sha256 : current.sha256, 'original executable changed during timing')
      assert.equal(fileHash(frozen[index]), index === 0 ? baseline.sha256 : current.sha256, 'frozen executable changed during timing')
    }
    assert.equal(sourceClosure(options.baselineRoot).sha256, baseline.source.sha256)
    assert.equal(sourceClosure(options.currentRoot).sha256, current.source.sha256)
    for (const entry of support) assert.equal(fileHash(join(project, entry.path)), entry.sha256, 'support source changed during timing')
    report.status = 'passed'
  } catch (error) {
    failure = error; report.status = 'failed'; report.failure = String(error.stack ?? error)
  } finally {
    report.host.loadAverageEnd = loadavg()
    report.completedAt = new Date().toISOString(); report.harnessMilliseconds = performance.now() - started
    report.checkedInvocations = report.rows.filter(row => row.completeOutputEqual).length
    writeFileSync(options.output, JSON.stringify(report, null, 2) + '\n')
    rmSync(directory, { recursive: true, force: true })
  }
  console.log(JSON.stringify({ status: report.status, output: options.output, checkedInvocations: report.checkedInvocations,
    binarySha256: { baseline: baseline.sha256, current: current.sha256 },
    mediansMilliseconds: report.lanes.map(lane => ({ id: lane.id,
      ...Object.fromEntries(Object.entries(lane.milliseconds ?? {}).map(([mode, stats]) => [mode, stats.median])) })) }))
  if (failure) throw failure
}

await main()
