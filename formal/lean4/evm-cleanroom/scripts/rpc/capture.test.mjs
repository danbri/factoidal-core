import assert from 'node:assert/strict'
import { execFile } from 'node:child_process'
import { createHash } from 'node:crypto'
import { once } from 'node:events'
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises'
import http from 'node:http'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { test } from 'node:test'
import { fileURLToPath } from 'node:url'
import { promisify } from 'node:util'
import { capture, parseCli } from './capture.mjs'
import { createRpc } from './rpc-client.mjs'

const invoke = promisify(execFile)
const FIXTURE = JSON.parse(await readFile(new URL('./mock-fixture.json', import.meta.url), 'utf8'))
const CLI = fileURLToPath(new URL('./capture.mjs', import.meta.url))

function defaultResult(request) {
  switch (request.method) {
    case 'eth_chainId': return FIXTURE.chainId
    case 'eth_getBlockByNumber': return FIXTURE.block
    case 'eth_getBlockByHash': return request.params[0] === FIXTURE.block.hash ? FIXTURE.block : FIXTURE.parent
    case 'eth_getCode': return FIXTURE.code
    case 'eth_call': return FIXTURE.returnData
    case 'eth_getTransactionByHash': return FIXTURE.transaction
    case 'eth_getTransactionReceipt': return FIXTURE.receipt
    default: throw new Error('unexpected mock RPC request')
  }
}

async function mock(t, override = () => undefined) {
  const requests = []
  const server = http.createServer(async (incoming, response) => {
    const chunks = []
    for await (const chunk of incoming) chunks.push(chunk)
    const request = JSON.parse(Buffer.concat(chunks))
    requests.push(request)
    const envelope = override(request, response, requests)
    if (envelope === false) return
    response.setHeader('Content-Type', 'application/json')
    response.end(JSON.stringify(envelope ?? { jsonrpc: '2.0', id: request.id, result: defaultResult(request) }))
  })
  server.listen(0, '127.0.0.1')
  await once(server, 'listening')
  t.after(() => {
    server.closeAllConnections()
    return new Promise((resolve, reject) => server.close(error => error ? reject(error) : resolve()))
  })
  return { url: `http://127.0.0.1:${server.address().port}`, requests }
}

function args(rpc, extras = []) {
  return ['--network', FIXTURE.network, '--rpc', rpc, '--address', FIXTURE.address,
    '--data', FIXTURE.data, '--out', 'fixture.json', ...extras]
}

const options = (url, extras) => parseCli(args(url, extras))
const rpcResult = (request, result) => ({ jsonrpc: '2.0', id: request.id, result })
const rpcError = (request, error) => ({ jsonrpc: '2.0', id: request.id, error })
const BLOCK_SELECTOR = { blockHash: FIXTURE.block.hash, requireCanonical: true }
const outcome = (status, dataHex = FIXTURE.returnData.slice(2)) => ({
  schemaVersion: 1, status, returnDataHex: dataHex, returnDataLength: String(dataHex.length / 2),
  returnDataTruncated: false, memoryTruncated: false,
})

async function scratch(t) {
  const directory = await mkdtemp(join(tmpdir(), 'evm-rpc-test-'))
  t.after(() => rm(directory, { recursive: true, force: true }))
  return directory
}

async function stub(t, snapshot, code = FIXTURE.code) {
  const executable = join(await scratch(t), 'evm-subset')
  const expected = ['--frame-call', code, FIXTURE.data, '1000000', '10000']
  await writeFile(executable, `#!${process.execPath}\nif (JSON.stringify(process.argv.slice(2)) !== ${JSON.stringify(JSON.stringify(expected))}) process.exit(9)\nconsole.log(${JSON.stringify(JSON.stringify(snapshot))})\n`, { mode: 0o700 })
  return executable
}

test('captures a deterministic call and keeps raw chain-specific fields', async t => {
  const { url, requests } = await mock(t)
  const executable = await stub(t, outcome('returned'))
  const observed = await capture(options(url, ['--tx', FIXTURE.transaction.hash, '--lean-exe', executable]))
  assert.equal(observed.captureStatus, 'captured')
  assert.equal(observed.expectedProfile.chainType, 'op-stack-rollup')
  assert.equal(observed.provider.chainId, FIXTURE.chainId)
  assert.deepEqual(observed.providerAssertions.block, FIXTURE.block)
  assert.deepEqual(observed.providerAssertions.parentBlock, FIXTURE.parent)
  assert.deepEqual(observed.providerAssertions.transaction, FIXTURE.transaction)
  assert.deepEqual(observed.providerAssertions.receipt, FIXTURE.receipt)
  assert.equal(observed.verification.stateRoot, 'unverified')
  assert.equal(observed.verification.consensus, 'unverified')
  assert.deepEqual(observed.verification.localComparison, {
    status: 'match', engine: 'evm-subset --frame-call', codeSource: 'provider-chain-code',
    gas: '1000000', fuel: '10000', local: { kind: 'return', dataHex: FIXTURE.returnData },
  })
  assert.deepEqual(requests.map(({ method, params }) => [method, params]), [
    ['eth_chainId', []], ['eth_getBlockByNumber', ['latest', false]],
    ['eth_getBlockByNumber', [FIXTURE.block.number, false]],
    ['eth_getBlockByHash', [FIXTURE.parent.hash, false]],
    ['eth_getCode', [FIXTURE.address, BLOCK_SELECTOR]],
    ['eth_call', [{ to: FIXTURE.address, data: FIXTURE.data }, BLOCK_SELECTOR]],
    ['eth_getTransactionByHash', [FIXTURE.transaction.hash]],
    ['eth_getTransactionReceipt', [FIXTURE.transaction.hash]],
    ['eth_getBlockByNumber', [FIXTURE.block.number, false]],
  ])
  assert.deepEqual(observed.acquisition.before, observed.acquisition.after)
  for (const [i, request] of observed.acquisition.requests.entries()) {
    assert.equal(request.id, i + 1)
    assert.match(request.responseBodySha256, /^[0-9a-f]{64}$/)
    assert.ok(request.bytes > 0)
    assert.ok(Number.isFinite(Date.parse(request.startedAt)))
  }
})

test('resolves explicit hashes and confirms their canonical height before reading state', async t => {
  const { url, requests } = await mock(t)
  const observed = await capture(options(url, ['--block', FIXTURE.block.hash]))
  assert.equal(observed.verification.localComparison.status, 'not-requested')
  assert.deepEqual(requests.slice(1, 3).map(({ method, params }) => [method, params]), [
    ['eth_getBlockByHash', [FIXTURE.block.hash, false]],
    ['eth_getBlockByNumber', [FIXTURE.block.number, false]],
  ])
})

test('passes synthetic runtime to both processes and skips PUSH immediates in the admission scan', async t => {
  const code = '0x605460005260206000f3' // 0x54 as data, rather than executing SLOAD.
  const data = `0x${'54'.padStart(64, '0')}`
  const { url, requests } = await mock(t, request =>
    request.method === 'eth_call' ? rpcResult(request, data) : undefined)
  const executable = await stub(t, outcome('returned', data.slice(2)), code)
  const observed = await capture(options(url, ['--code-override', code, '--lean-exe', executable]))
  assert.deepEqual(requests.find(request => request.method === 'eth_call').params[2], {
    [FIXTURE.address]: { code },
  })
  assert.equal(observed.providerAssertions.call.chainCodeHex, FIXTURE.code)
  assert.deepEqual(observed.providerAssertions.call.executionCode, { source: 'synthetic-state-override', dataHex: code })
  assert.equal(observed.verification.localComparison.status, 'match')
})

test('compares exact revert bytes from a recognised JSON-RPC error', async t => {
  const code = FIXTURE.code.replace(/f3$/, 'fd')
  const { url } = await mock(t, request => {
    if (request.method === 'eth_getCode') return rpcResult(request, code)
    if (request.method === 'eth_call') {
      return rpcError(request, { code: -32000, message: 'execution reverted', data: FIXTURE.returnData })
    }
  })
  const executable = await stub(t, outcome('reverted'), code)
  const observed = await capture(options(url, ['--lean-exe', executable]))
  assert.deepEqual(observed.providerAssertions.call.outcome, {
    kind: 'revert', dataHex: FIXTURE.returnData, rpcErrorCode: -32000,
  })
  assert.equal(observed.captureStatus, 'captured')
  assert.equal(observed.verification.localComparison.status, 'match')
})

test('does not report equal bytes with a different halt kind as a match', async t => {
  const { url } = await mock(t)
  const executable = await stub(t, outcome('reverted'))
  const observed = await capture(options(url, ['--lean-exe', executable]))
  assert.equal(observed.verification.localComparison.status, 'mismatch')
})

test('detects a false expected eth_call and saves the evidence with exit 2', async t => {
  const { url } = await mock(t, request =>
    request.method === 'eth_call' ? rpcResult(request, '0xdeadbeef') : undefined)
  const executable = await stub(t, outcome('returned'))
  const directory = await scratch(t)
  await assert.rejects(invoke(process.execPath, [CLI, ...args(url, ['--lean-exe', executable])], { cwd: directory }),
    { code: 2 })
  const file = join(directory, 'fixture.json')
  const saved = await readFile(file, 'utf8')
  assert.equal(JSON.parse(saved).verification.localComparison.status, 'mismatch')
  await assert.rejects(invoke(process.execPath, [CLI, ...args(url)], { cwd: directory }),
    error => error.code === 1 && error.stderr.includes('Evidence file already exists'))
  assert.equal(await readFile(file, 'utf8'), saved)
})

test('refuses captured runtime that needs contract context', async t => {
  const { url } = await mock(t, request =>
    request.method === 'eth_getCode' ? rpcResult(request, '0x60005460005260206000f3') : undefined)
  const observed = await capture(options(url, ['--lean-exe', '/not-run']))
  assert.equal(observed.captureStatus, 'captured')
  assert.equal(observed.verification.localComparison.reason, 'opcode-outside-context-free-subset')
})

test('rejects malformed, unsupported, exceptional or truncated Lean observations', async t => {
  const { url } = await mock(t)
  const cases = [
    [{ ...outcome('returned'), returnDataTruncated: true }, 'frame-output-incomplete-or-unrecognised'],
    [{ ...outcome('returned'), memoryTruncated: true }, 'frame-output-incomplete-or-unrecognised'],
    [{ ...outcome('returned'), returnDataTruncated: undefined }, 'frame-output-incomplete-or-unrecognised'],
    [{ ...outcome('returned'), returnDataLength: '33' }, 'frame-output-incomplete-or-unrecognised'],
    [outcome('returned', '123'), 'frame-output-incomplete-or-unrecognised'],
    [{ ...outcome('returned'), schemaVersion: 2 }, 'frame-output-incomplete-or-unrecognised'],
    [{ status: 'unsupported' }, 'frame-execution-unsupported'],
    [{ status: 'exceptional' }, 'frame-execution-exceptional'],
  ]
  for (const [snapshot, reason] of cases) {
    const executable = await stub(t, snapshot)
    const observed = await capture(options(url, ['--lean-exe', executable]))
    assert.equal(observed.verification.localComparison.status, 'unverified')
    assert.equal(observed.verification.localComparison.reason, reason)
  }
})

test('compares a fully observed STOP as empty successful return data', async t => {
  const { url } = await mock(t, request => {
    if (request.method === 'eth_getCode') return rpcResult(request, '0x00')
    if (request.method === 'eth_call') return rpcResult(request, '0x')
  })
  const executable = await stub(t, outcome('stopped', ''), '0x00')
  const observed = await capture(options(url, ['--lean-exe', executable]))
  assert.equal(observed.verification.localComparison.status, 'match')
})

test('refuses a comparison over the exact observation bound', async t => {
  const { url } = await mock(t, request =>
    request.method === 'eth_call' ? rpcResult(request, `0x${'ff'.repeat(4097)}`) : undefined)
  const observed = await capture(options(url, ['--lean-exe', '/not-run']))
  assert.equal(observed.captureStatus, 'captured')
  assert.equal(observed.verification.localComparison.reason, 'provider-data-exceeds-comparison-limit')
})

test('checks the expected chain ID before making any state read', async t => {
  const { url, requests } = await mock(t, request =>
    request.method === 'eth_chainId' ? rpcResult(request, '0x1') : undefined)
  await assert.rejects(capture(options(url)), /expected 11155420, received 1/)
  assert.deepEqual(requests.map(request => request.method), ['eth_chainId'])
})

test('rejects response ids with the wrong value or type', async t => {
  for (const wrongId of [id => id + 1, id => String(id)]) {
    const { url } = await mock(t, request => ({ ...rpcResult(request, FIXTURE.chainId), id: wrongId(request.id) }))
    await assert.rejects(capture(options(url)), /mismatched id/)
  }
})

test('rejects JSON-RPC responses containing both result and error', async t => {
  const { url } = await mock(t, request => ({ ...rpcResult(request, FIXTURE.chainId), error: {} }))
  await assert.rejects(capture(options(url)), /response envelope/)
})

test('rejects duplicate JSON member names, including names encoded with escapes', async t => {
  for (const result of [String.raw`"result":"0x1","res\u0075lt":"0xaa37dc"`,
    String.raw`"result":{"extra":{"x":3,"\u0078":4}}`]) {
    const { url } = await mock(t, (request, response) => {
      response.end(`{"jsonrpc":"2.0","id":${request.id},${result}}`)
      return false
    })
    await assert.rejects(capture(options(url)), /Duplicate member name in RPC JSON/)
  }
})

test('refuses excess JSON nesting before parsing the application response', async t => {
  const { url } = await mock(t, (request, response) => {
    response.end(`{"jsonrpc":"2.0","id":${request.id},"result":${'['.repeat(10000)}0${']'.repeat(10000)}}`)
    return false
  })
  await assert.rejects(capture(options(url)), /RPC JSON nesting limit exceeded/)
})

test('keeps validated RPC codes and discards untrusted error text, data and URL credentials', async t => {
  const providerSecret = 'rpcApiSecretValue'
  const pathSecret = 'rpcPathSecretValue'
  const { url } = await mock(t, request => {
    if (request.method === 'eth_call') {
      return rpcError(request, { code: -32001, message: `\u001b[31m ${pathSecret}`, data: { providerSecret } })
    }
  })
  const observed = await capture(options(`${url}/${pathSecret}?api_key=${providerSecret}`, ['--lean-exe', '/not-run']))
  assert.equal(observed.provider.origin, url)
  assert.equal(observed.captureStatus, 'call-error')
  assert.deepEqual(observed.providerAssertions.call.outcome, { kind: 'rpc-error', rpcErrorCode: -32001 })
  assert.deepEqual(observed.acquisition.requests.find(request => request.method === 'eth_call').error, { code: -32001 })
  assert.equal(observed.verification.localComparison.status, 'unverified')
  assert.doesNotMatch(JSON.stringify(observed), new RegExp(`${providerSecret}|${pathSecret}|api_key|\\u001b`, 'i'))
})

test('rejects malformed errors without echoing strings from the provider', async t => {
  const { url } = await mock(t, request => rpcError(request, { code: 'hidden-secret', message: 'hidden-secret' }))
  await assert.rejects(capture(options(url)), error =>
    error.message.includes('Malformed JSON-RPC error') && !error.message.includes('hidden-secret'))
})

test('refuses a provider result that reflects a URL query token', async t => {
  for (const [secret, reflected] of [
    ['reflected-secret', 'reflected-secret'], ['123456789', 123456789],
    ['12345678976234567890987654', JSON.rawJSON('12345678976234567890987654')],
  ]) {
    const { url } = await mock(t, request => request.method === 'eth_getBlockByNumber'
      ? rpcResult(request, { ...FIXTURE.block, extra: reflected }) : undefined)
    await assert.rejects(capture(options(`${url}/?token=${secret}`)), error =>
      error.message.includes('credential or endpoint data') && !error.message.includes(secret))
  }
})

test('preserves integers in provider-specific fields beyond JavaScript safe precision', async t => {
  const { url } = await mock(t, request => request.method === 'eth_getBlockByNumber'
    ? rpcResult(request, { ...FIXTURE.block, extra: JSON.rawJSON('9007199254740993') }) : undefined)
  const observed = await capture(options(url))
  assert.match(JSON.stringify(observed.providerAssertions.block), /"extra":9007199254740993/)
})

test('validates CLI data and code and refuses malformed provider bytes', async t => {
  const { url } = await mock(t, request =>
    request.method === 'eth_getCode' ? rpcResult(request, '0xabc') : undefined)
  assert.throws(() => options(url, ['--code-override', '0x123']), /Invalid --code-override/)
  assert.throws(() => options(url, ['--lean-exe', 'relative']), /absolute path/)
  assert.throws(() => parseCli(args(url).map(arg => arg === FIXTURE.data ? '0xg0' : arg)), /Invalid --data/)
  await assert.rejects(capture(options(url)), /malformed runtime bytecode/)
})

test('validates eth_call result data', async t => {
  const { url } = await mock(t, request =>
    request.method === 'eth_call' ? rpcResult(request, '0xhello') : undefined)
  await assert.rejects(capture(options(url)), /malformed return data/)
})

test('rejects a missing block', async t => {
  const { url } = await mock(t, request =>
    request.method === 'eth_getBlockByNumber' ? rpcResult(request, null) : undefined)
  await assert.rejects(capture(options(url)), /requested block is missing/)
})

test('fails closed when the provider refuses a block-hash selector', async t => {
  const { url, requests } = await mock(t, request => request.method === 'eth_getCode'
    ? rpcError(request, { code: -32602, message: 'selector not supported' }) : undefined)
  await assert.rejects(capture(options(url)), /eth_getCode: RPC error code -32602/)
  assert.deepEqual(requests.filter(request => request.method === 'eth_getCode').map(request => request.params), [
    [FIXTURE.address, BLOCK_SELECTOR],
  ])
})

test('checks a block hash changed after the call and detects reorg races', async t => {
  const { url, requests } = await mock(t, (request, _response, seen) =>
    request.method === 'eth_getBlockByNumber' && seen.some(entry => entry.method === 'eth_call')
      ? rpcResult(request, { ...FIXTURE.block, hash: FIXTURE.parent.hash }) : undefined)
  await assert.rejects(capture(options(url)), /Block hash changed at the pinned number/)
  assert.equal(requests.filter(request => request.params[0] === 'latest').length, 1)
})

test('rejects contradictory block data even when a provider claims the same hash', async t => {
  const { url } = await mock(t, (request, _response, seen) =>
    request.method === 'eth_getBlockByNumber' && seen.some(entry => entry.method === 'eth_call')
      ? rpcResult(request, { ...FIXTURE.block, transactions: [] }) : undefined)
  await assert.rejects(capture(options(url)), /conflicting block data/)
})

test('checks parent height and receipt identity before saving evidence', async t => {
  const badParent = await mock(t, request => request.method === 'eth_getBlockByHash'
    ? rpcResult(request, { ...FIXTURE.parent, number: '0x120' }) : undefined)
  await assert.rejects(capture(options(badParent.url)), /Parent block number does not match/)
  const badReceipt = await mock(t, request => request.method === 'eth_getTransactionReceipt'
    ? rpcResult(request, { ...FIXTURE.receipt, transactionIndex: '0x1' }) : undefined)
  await assert.rejects(capture(options(badReceipt.url, ['--tx', FIXTURE.transaction.hash])), /receipt does not match/)
})

test('bounds a chunked response that lacks a content-length header', async t => {
  const { url } = await mock(t, (_request, response) => {
    for (let i = 0; i < 5; i++) response.write(Buffer.alloc(1024 * 1024, 'x'))
    response.end()
    return false
  })
  await assert.rejects(capture(options(url)), /RPC response byte limit exceeded/)
})

test('rejects an excessive stated content length before reading the body', async t => {
  const { url } = await mock(t, (_request, response) => {
    response.writeHead(200, { 'Content-Length': 4 * 1024 * 1024 + 1 }).flushHeaders()
    return false
  })
  await assert.rejects(capture(options(url)), /RPC response byte limit exceeded/)
})

test('enforces a deadline even when response headers and a partial body arrive', async t => {
  const { url } = await mock(t, (_request, response) => {
    response.write('{')
    return false
  })
  await assert.rejects(capture(options(url, ['--timeout-ms', '100'])), /RPC request timed out/)
})

test('rejects redirects before following them and fails promptly on a severed body', async t => {
  const redirect = await mock(t, (_request, response) => {
    response.writeHead(307, { Location: 'http://127.0.0.1:9/should-not-connect' }).end()
    return false
  })
  await assert.rejects(capture(options(redirect.url)), /HTTP status 307/)
  assert.equal(redirect.requests.length, 1)
  const severed = await mock(t, (_request, response) => {
    response.write('[')
    response.destroy()
    return false
  })
  await assert.rejects(capture(options(severed.url)), /connection closed|Transport error ECONNRESET/)
})

test('refuses methods outside the read-only allowlist before sending requests', async t => {
  const { url, requests } = await mock(t)
  await assert.rejects(createRpc(url, 1000).read('eth_sendRawTransaction', ['0x']), /outside the read-only allowlist/)
  assert.deepEqual(requests, [])
})

test('compares the deterministic calldata fixture with the Lean executable', {
  skip: process.env.EVM_RPC_TEST_LEAN_EXE ? false : 'set EVM_RPC_TEST_LEAN_EXE to exercise --frame-call',
}, async t => {
  const { url } = await mock(t)
  const observed = await capture(options(url, ['--lean-exe', process.env.EVM_RPC_TEST_LEAN_EXE]))
  assert.deepEqual(observed.verification.localComparison.local, { kind: 'return', dataHex: FIXTURE.returnData })
  assert.equal(observed.verification.localComparison.status, 'match')
})

const SAVED_CAPTURES = [
  ['op-sepolia-51770430.json', '43c1c9702ed4fa11478781955099c7f170a55bdc13408e3eb4edd44b5f7e2557'],
  ['polygon-97758671.json', '9afb228dcd84b4b4e361bd8b1adf4a86479672ab1c0ef2ea46012cc15c3b9322'],
]

for (const [file, sha256] of SAVED_CAPTURES) {
  test(`replays the recorded provider assertions in ${file} through the capture host`, async t => {
    const raw = await readFile(new URL(`./evidence/${file}`, import.meta.url))
    assert.equal(createHash('sha256').update(raw).digest('hex'), sha256)
    const saved = JSON.parse(raw)
    const { provider, providerAssertions: chain, acquisition } = saved
    const { address, dataHex, executionCode } = chain.call
    assert.equal(executionCode.source, 'synthetic-state-override')
    assert.equal(chain.call.chainCodeHex, '0x')
    const { url, requests } = await mock(t, request => {
      const snapshots = {
        eth_chainId: provider.chainId, eth_getBlockByNumber: chain.block,
        eth_getBlockByHash: request.params[0] === chain.block.hash ? chain.block : chain.parentBlock,
        eth_getCode: chain.call.chainCodeHex, eth_call: chain.call.outcome.dataHex,
        eth_getTransactionByHash: chain.transaction, eth_getTransactionReceipt: chain.receipt,
      }
      return rpcResult(request, snapshots[request.method])
    })
    const executable = process.env.EVM_RPC_TEST_LEAN_EXE ?? await stub(t, outcome('returned'))
    const options = parseCli([
      '--network', saved.expectedProfile.id, '--rpc', url, '--address', address, '--data', dataHex,
      '--out', 'fixture.json', '--block', acquisition.blockSelector, '--code-override', executionCode.dataHex,
      '--lean-exe', executable, ...(chain.transaction ? ['--tx', chain.transaction.hash] : []),
    ])
    const replayed = await capture(options)
    assert.deepEqual(replayed.expectedProfile, saved.expectedProfile)
    assert.deepEqual(replayed.providerAssertions, chain)
    assert.deepEqual(replayed.acquisition.before, acquisition.before)
    assert.deepEqual(replayed.acquisition.after, acquisition.after)
    assert.deepEqual(requests.map(({ id, method, params }) => ({ id, method, params })),
      acquisition.requests.map(({ id, method, params }) => ({ id, method, params })))
    assert.equal(replayed.verification.localComparison.status, 'match')
    assert.deepEqual(replayed.verification, saved.verification)
  })
}
