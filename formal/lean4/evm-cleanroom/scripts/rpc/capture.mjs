import { link, mkdtemp, rm, writeFile } from 'node:fs/promises'
import { dirname, isAbsolute, join } from 'node:path'
import { pathToFileURL } from 'node:url'
import { isDeepStrictEqual, parseArgs } from 'node:util'
import { compareCall, MAX_INPUT_BYTES } from './compare.mjs'
import { CaptureError, createRpc, hexData, object } from './rpc-client.mjs'

const POLYGON_DOCS = 'https://docs.polygon.technology/pos/reference/rpc-endpoints'
const PROFILES = new Map([
  ['amoy', {
    name: 'Polygon PoS Amoy', chainId: 80002, chainType: 'polygon-pos-sidechain',
    defaultRpc: 'https://polygon-amoy.drpc.org', source: POLYGON_DOCS,
  }],
  ['polygon', {
    name: 'Polygon PoS mainnet', chainId: 137, chainType: 'polygon-pos-sidechain',
    defaultRpc: 'https://polygon.drpc.org', source: POLYGON_DOCS,
  }],
  ['op-sepolia', {
    name: 'OP Sepolia', chainId: 11155420, chainType: 'op-stack-rollup',
    defaultRpc: 'https://sepolia.optimism.io',
    source: 'https://github.com/ethereum-optimism/superchain-registry/blob/main/chainList.json',
  }],
])

const USAGE = `Usage: node capture.mjs --network amoy|polygon|op-sepolia --address 0xADDRESS --data 0xBYTES --out FILE
  [--rpc URL] [--block latest|NUMBER|0xNUMBER|0xHASH] [--tx 0xHASH]
  [--code-override 0xBYTES] [--lean-exe /absolute/path --gas N --fuel N] [--timeout-ms N]

Creates a new JSON file with a read-only capture at a resolved block.
Default request timeout is 10000 ms. Default local gas and fuel are 1000000 and 10000.
Exit 0 for a successful capture or a requested comparison that matches,
1 for a capture, call or file error, and 2 for a saved capture with an unverified or mismatching comparison.`

const quantity = value => typeof value === 'string' && /^0x(?:0|[1-9a-f][0-9a-f]{0,63})$/i.test(value) && value.startsWith('0x')
const hash = value => typeof value === 'string' && value.length === 66 && hexData(value)
const address = value => typeof value === 'string' && value.length === 42 && hexData(value)
const sameHex = (left, right) => left.toLowerCase() === right.toLowerCase()

function blockSelector(input) {
  if (input === 'latest') return { method: 'eth_getBlockByNumber', value: input }
  if (hash(input)) return { method: 'eth_getBlockByHash', value: input.toLowerCase() }
  if (quantity(input)) return { method: 'eth_getBlockByNumber', value: input.toLowerCase() }
  if (/^(0|[1-9][0-9]{0,76})$/.test(input)) {
    return { method: 'eth_getBlockByNumber', value: `0x${BigInt(input).toString(16)}` }
  }
  throw new CaptureError('Invalid --block. Use latest, a block number or a 32-byte hash.')
}

function bytes(input, label) {
  if (!hexData(input) || input.length > 2 + 2 * MAX_INPUT_BYTES) {
    throw new CaptureError(`Invalid ${label}. Use even-length 0x-prefixed hex up to 48 KiB.`)
  }
  return input.toLowerCase()
}

function decimal(input, maximum, label) {
  if (!/^[1-9][0-9]{0,8}$/.test(input) || Number(input) > maximum) {
    throw new CaptureError(`Invalid ${label}. Use a decimal integer from 1 to ${maximum}.`)
  }
  return input
}

export function parseCli(args) {
  const options = Object.fromEntries([
    'network', 'rpc', 'address', 'data', 'block', 'tx', 'out', 'code-override',
    'lean-exe', 'gas', 'fuel', 'timeout-ms',
  ].map(name => [name, { type: 'string', multiple: true }]))
  let parsed
  try {
    parsed = parseArgs({ args, options: { ...options, help: { type: 'boolean' } } }).values
  } catch {
    throw new CaptureError('Invalid arguments. Run with --help for usage.')
  }
  if (parsed.help) return null
  if (Object.values(parsed).some(values => values.length !== 1)) {
    throw new CaptureError('Specify each option at most once.')
  }
  const values = Object.fromEntries(Object.entries(parsed).map(([key, [value]]) => [key, value]))
  const profile = PROFILES.get(values.network)
  if (!profile) throw new CaptureError('Use --network amoy, polygon or op-sepolia.')
  if (!address(values.address)) throw new CaptureError('Use --address with a 20-byte hexadecimal address.')
  if (values.tx !== undefined && !hash(values.tx)) throw new CaptureError('Use --tx with a 32-byte hexadecimal hash.')
  if (!values.out) throw new CaptureError('Use --out to name a new evidence file.')
  if (values['lean-exe'] !== undefined && !isAbsolute(values['lean-exe'])) {
    throw new CaptureError('Use an absolute path for --lean-exe.')
  }
  if (!values['lean-exe'] && (values.gas !== undefined || values.fuel !== undefined)) {
    throw new CaptureError('--gas and --fuel require --lean-exe.')
  }
  return {
    network: values.network, profile, rpc: values.rpc ?? profile.defaultRpc,
    customRpc: values.rpc !== undefined, address: values.address.toLowerCase(),
    data: bytes(values.data, '--data'), block: blockSelector(values.block ?? 'latest'),
    tx: values.tx?.toLowerCase(), out: values.out,
    codeOverride: values['code-override'] === undefined ? undefined : bytes(values['code-override'], '--code-override'),
    leanExe: values['lean-exe'], gas: decimal(values.gas ?? '1000000', 50000000, '--gas'),
    fuel: decimal(values.fuel ?? '10000', 1000000, '--fuel'),
    timeoutMs: Number(decimal(values['timeout-ms'] ?? '10000', 60000, '--timeout-ms')),
  }
}

async function result(rpc, method, params) {
  const reply = await rpc.read(method, params)
  if (reply.error) throw new CaptureError(`${method}: RPC error code ${reply.error.code}`)
  return reply.result
}

async function block(rpc, method, selector) {
  const entry = await result(rpc, method, [selector, false])
  if (entry === null) throw new CaptureError(`${method}: requested block is missing`)
  if (!object(entry) || !quantity(entry.number) || !hash(entry.hash) || !hash(entry.parentHash) ||
      !hash(entry.stateRoot) || !Array.isArray(entry.transactions) || !entry.transactions.every(hash)) {
    throw new CaptureError(`${method}: malformed block header or transaction hashes`)
  }
  const actual = method === 'eth_getBlockByHash' ? entry.hash : entry.number
  if (selector !== 'latest' && !sameHex(actual, selector)) {
    throw new CaptureError(`${method}: block identity does not match the request`)
  }
  return entry
}

async function parentBlock(rpc, child) {
  const number = BigInt(child.number)
  if (number === 0n) {
    if (BigInt(child.parentHash) !== 0n) throw new CaptureError('Genesis block has a nonzero parent hash')
    return null
  }
  const parent = await block(rpc, 'eth_getBlockByHash', child.parentHash)
  if (BigInt(parent.number) !== number - 1n) throw new CaptureError('Parent block number does not match the child')
  return parent
}

function sameBlock(resolved, observed) {
  if (!sameHex(resolved.hash, observed.hash)) throw new CaptureError('Block hash changed at the pinned number')
  if (!isDeepStrictEqual(resolved, observed)) {
    throw new CaptureError('Provider reported conflicting block data for one block hash')
  }
}

async function chosenTransaction(rpc, captured, txHash) {
  if (!txHash) return null
  const index = captured.transactions.findIndex(value => sameHex(value, txHash))
  if (index < 0) throw new CaptureError('Selected transaction is absent from the captured block')
  const transaction = await result(rpc, 'eth_getTransactionByHash', [txHash])
  const receipt = await result(rpc, 'eth_getTransactionReceipt', [txHash])
  for (const [label, raw, hashField] of [
    ['transaction', transaction, 'hash'], ['receipt', receipt, 'transactionHash'],
  ]) {
    if (!object(raw) || !hash(raw[hashField]) || !sameHex(raw[hashField], txHash) ||
        !hash(raw.blockHash) || !sameHex(raw.blockHash, captured.hash) ||
        !quantity(raw.blockNumber) || !sameHex(raw.blockNumber, captured.number) ||
        !quantity(raw.transactionIndex) || BigInt(raw.transactionIndex) !== BigInt(index)) {
      throw new CaptureError(`Selected ${label} does not match the captured block and transaction`)
    }
  }
  return { transaction, receipt }
}

async function call(rpc, snapshot, options) {
  const selector = { blockHash: snapshot.hash, requireCanonical: true }
  const code = await result(rpc, 'eth_getCode', [options.address, selector])
  if (!hexData(code)) throw new CaptureError('eth_getCode: malformed runtime bytecode')
  const transaction = { to: options.address, data: options.data, value: '0x0' }
  const params = [transaction, selector]
  if (options.codeOverride !== undefined) params.push({ [options.address]: { code: options.codeOverride } })
  const response = await rpc.read('eth_call', params)
  const { result: returnData, error } = response
  let outcome
  if (error) {
    outcome = Object.hasOwn(error, 'revertDataHex')
      ? { kind: 'revert', dataHex: error.revertDataHex, rpcErrorCode: error.code }
      : { kind: 'rpc-error', rpcErrorCode: error.code }
  } else {
    if (!hexData(returnData)) throw new CaptureError('eth_call: malformed return data')
    outcome = { kind: 'return', dataHex: returnData }
  }
  return {
    address: options.address, dataHex: options.data, valueHex: transaction.value, chainCodeHex: code,
    executionCode: options.codeOverride === undefined
      ? { source: 'provider-chain-code', dataHex: code }
      : { source: 'synthetic-state-override', dataHex: options.codeOverride },
    outcome,
  }
}

export async function capture(options) {
  const rpc = createRpc(options.rpc, options.timeoutMs)
  const chainId = await result(rpc, 'eth_chainId', [])
  if (!quantity(chainId)) throw new CaptureError('eth_chainId: malformed chain ID')
  if (BigInt(chainId) !== BigInt(options.profile.chainId)) {
    throw new CaptureError(`eth_chainId: expected ${options.profile.chainId}, received ${BigInt(chainId)}`)
  }
  const selected = await block(rpc, options.block.method, options.block.value)
  const before = options.block.method === 'eth_getBlockByNumber' && options.block.value !== 'latest'
    ? selected : await block(rpc, 'eth_getBlockByNumber', selected.number)
  sameBlock(selected, before)
  const parent = await parentBlock(rpc, before)
  const observation = await call(rpc, before, options)
  const transaction = await chosenTransaction(rpc, before, options.tx)
  const after = await block(rpc, 'eth_getBlockByNumber', before.number)
  sameBlock(before, after)
  const localComparison = await compareCall({
    ...options, code: observation.executionCode.dataHex,
    codeSource: observation.executionCode.source, remote: observation.outcome,
  })
  return {
    schemaVersion: 1,
    captureStatus: observation.outcome.kind === 'rpc-error' ? 'call-error' : 'captured',
    expectedProfile: { id: options.network, ...options.profile },
    provider: { origin: rpc.origin, customEndpoint: options.customRpc, chainId },
    acquisition: {
      blockSelector: options.block.value, stateQuerySelector: 'canonical-block-hash',
      before: { number: before.number, hash: before.hash }, after: { number: after.number, hash: after.hash },
      requests: rpc.requests,
    },
    providerAssertions: { block: before, parentBlock: parent, ...transaction, call: observation },
    verification: {
      localComparison, stateRoot: 'unverified', transactionExecution: 'unverified',
      blockHash: 'unverified', consensus: 'unverified',
    },
  }
}

async function saveEvidence(path, evidence) {
  const directory = await mkdtemp(join(dirname(path), '.evm-rpc-'))
  const temporary = join(directory, 'capture.json')
  try {
    await writeFile(temporary, `${JSON.stringify(evidence, null, 2)}\n`, { mode: 0o600 })
    await link(temporary, path)
  } finally {
    await rm(directory, { recursive: true, force: true })
  }
}

async function main() {
  try {
    const options = parseCli(process.argv.slice(2))
    if (!options) {
      console.log(USAGE)
      return 0
    }
    const evidence = await capture(options)
    await saveEvidence(options.out, evidence)
    const comparison = evidence.verification.localComparison.status
    console.log(`RPC capture ${evidence.captureStatus}. Local comparison ${comparison}.`)
    if (evidence.captureStatus === 'call-error') return 1
    return comparison === 'not-requested' || comparison === 'match' ? 0 : 2
  } catch (error) {
    if (error instanceof CaptureError) console.error(error.message)
    else if (error?.code === 'EEXIST') console.error('Evidence file already exists')
    else console.error('Unable to write capture evidence or complete the request')
    return 1
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  process.exitCode = await main()
}
