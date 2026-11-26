/** Optional local oracle, required for the pinned Geth lane in EVM CI. */
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'

export const gethAddress = address => '0x' + address.toString(16).padStart(40, '0')
const receiver = gethAddress(0xc1)
const sender = gethAddress(0xc2)
const key = '0x' + '00'.repeat(32)
const shanghai = {
  chainId: 1, homesteadBlock: 0, eip150Block: 0, eip155Block: 0, eip158Block: 0,
  byzantiumBlock: 0, constantinopleBlock: 0, petersburgBlock: 0, istanbulBlock: 0,
  berlinBlock: 0, londonBlock: 0, mergeNetsplitBlock: 0, terminalTotalDifficulty: 0, shanghaiTime: 0
}
const asHexQuantity = n => '0x' + BigInt(n).toString(16)
const unprefix = hex => hex.replace(/^0x/, '')

export function openGeth() {
  const path = process.env.EVM_GETH_EXE
  if (!path) return null
  const proc = spawnSync(path, ['--version'], {encoding: 'utf8', timeout: 10000})
  if (proc.error || proc.status !== 0) throw Error('Geth version probe failed: ' + String(proc.error ?? proc.stderr))
  const version = proc.stdout.trim()
  assert.equal(version, 'evm version 1.17.10-stable-1df30b18')
  const sourceCommit = '1df30b18d9ed35ee9d28ffd4648442c2204554ad'
  const sha256 = createHash('sha256').update(readFileSync(path)).digest('hex')
  assert.equal(sha256, 'd8cfddad15a8c601e7b069bc5973ad073dbc2d632b8c5ab50e513ef27c53d6da')
  const dir = mkdtempSync(join(tmpdir(), 'evm-geth-shanghai-'))
  const prestate = join(dir, 'genesis.json')
  const close = () => rmSync(dir, {recursive:true, force:true})
  process.on('exit', close)

  function run({code, data = '', gas, accounts = []}) {
    assert(Number.isSafeInteger(gas) && gas > 0, 'Geth requires positive initial gas')
    const alloc = Object.fromEntries([[0xc1, code, 0, 0], ...accounts]
      .map(([address, bytecode, balance, nonce]) => [unprefix(gethAddress(address)), {
        balance: asHexQuantity(balance), nonce: asHexQuantity(nonce), code: '0x' + bytecode
      }]))
    // The Geth runner uses the supplied genesis gas limit for runtime.Call.
    writeFileSync(prestate, JSON.stringify({
      config: shanghai, difficulty: '0x0', gasLimit: asHexQuantity(gas), alloc
    }))
    const p = spawnSync(path, ['run', '--prestate', prestate, '--receiver', receiver, '--sender', sender,
      '--input', '0x' + data, '--dump', '--trace', '--trace.nomemory=false', '--trace.noreturndata=false', code],
    {encoding:'utf8', timeout:10000, maxBuffer:8 * 1024 * 1024})
    if (p.error || p.status !== 0) throw Error('Geth process failed: ' + String(p.error ?? p.stderr))
    const trace = p.stderr.split('\n').filter(line => line.startsWith('{')).map(line => JSON.parse(line))
    const terminal = trace.at(-1)
    const topSteps = trace.filter(event => event.depth === 1)
    const lastStep = topSteps.filter(event => event.error === undefined).at(-1)
    assert.equal(BigInt(topSteps[0].gas), BigInt(gas), 'Geth initial frame gas')
    assert.match(terminal.output, /^(?:[0-9a-f]{2})*$/, 'Geth terminal output')
    assert.match(terminal.gasUsed, /^0x[0-9a-f]+$/, 'Geth gas use')
    const status = terminal.error === 'execution reverted' ? 'reverted' : terminal.error ? 'exceptional' :
      lastStep.op === 0xf3 ? 'returned' : 'stopped'
    const post = JSON.parse(p.stdout)
    assert.match(post.root, /^[0-9a-f]{64}$/, 'Geth state dump root')
    assert(post.accounts && typeof post.accounts === 'object', 'Geth state dump accounts')
    const after = new Map(Object.entries(post.accounts).map(([address, account]) => [address.toLowerCase(), account]))
    function account(address) {
      const a = after.get(gethAddress(address))
      if (a) {
        assert.match(a.balance, /^(?:0|[1-9][0-9]*)$/, 'Geth account balance')
        assert(Number.isSafeInteger(a.nonce) && a.nonce >= 0, 'Geth account nonce')
      }
      const stored = a?.storage?.[key]
      if (stored !== undefined) assert.match(stored, /^[0-9a-f]{1,64}$/, 'Geth storage value')
      return {
        balance: a ? a.balance : '0',
        nonce: a ? String(a.nonce) : '0',
        slot0: stored === undefined ? '0' : BigInt('0x' + stored).toString()
      }
    }
    const result = {
      status, gasRemaining: String(BigInt(gas) - BigInt(terminal.gasUsed)),
      bytesHex: terminal.output, account,
    }
    if (status === 'stopped') {
      assert.equal(lastStep.op, 0, 'expected a top-level STOP')
      assert.equal(unprefix(lastStep.memory ?? '0x').length / 2, lastStep.memSize, 'complete Geth terminal memory')
      result.memoryHex = unprefix(lastStep.memory ?? '0x')
      result.memorySize = String(lastStep.memSize)
      result.stack = lastStep.stack.map(value => BigInt(value).toString()).reverse()
    }
    if (status !== 'exceptional') {
      result.returnDataHex = unprefix(lastStep.returnData ?? '0x')
    }
    if (status === 'stopped' || status === 'returned') {
      assert(Number.isSafeInteger(lastStep.refund), 'Geth refund counter')
      result.refund = String(lastStep.refund)
    }
    return result
  }
  return {version, sourceCommit, sha256, fork:'Shanghai', run}
}
