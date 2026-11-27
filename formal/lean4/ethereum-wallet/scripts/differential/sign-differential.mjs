// Differential test of eth-wallet-sign against EthereumJS, used as a test oracle only.
//
// For each case a key is made fresh from the system random source, a transaction is drawn at
// random, EthereumJS signs it, and eth-wallet-sign signs the same JSON. The raw bytes, the
// transaction hash and the sender must be identical. EIP-7702 authorizations are signed by
// both sides and compared tuple by tuple before they go into a kind 4 transaction.
// Negative controls: a changed field must change the bytes, another key must change the
// signature, and the tool must refuse to sign without its risk flag.
//
// Keys exist only in this process and on the child's command line; they are never printed
// and never touch a network. usage: node sign-differential.mjs <eth-wallet-sign> [cases per kind]
import { execFileSync, spawnSync } from 'node:child_process'
import { randomBytes, randomInt } from 'node:crypto'
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import {
  createAccessList2930Tx, createBlob4844Tx, createEOACode7702Tx, createFeeMarket1559Tx, createLegacyTx,
} from '@ethereumjs/tx'
import {
  bytesToHex, eoaCode7702AuthorizationListBytesItemToJSON, eoaCode7702SignAuthorization, hexToBytes,
} from '@ethereumjs/util'

const [binary, perKindArg] = process.argv.slice(2)
if (!binary) {
  console.error('usage: node sign-differential.mjs <eth-wallet-sign> [cases per kind]')
  process.exit(2)
}
const perKind = Number(perKindArg ?? 40)
const RISK = '--dangerously-enable-variable-time-signing'
const dir = mkdtempSync(join(tmpdir(), 'eth-wallet-sign-'))

const hex = (n) => '0x' + n.toString(16)
const randomHex = (bytes) => bytesToHex(randomBytes(bytes))
const randomBig = (maxBytes) => {
  const size = randomInt(0, maxBytes + 1)
  return size === 0 ? 0n : BigInt(bytesToHex(randomBytes(size)))
}
const pick = (list) => list[randomInt(0, list.length)]

function randomKey() {
  // A valid scalar with overwhelming probability; the oracle rejects the rest.
  return randomBytes(32)
}

function randomAccessList() {
  const entries = []
  for (let i = randomInt(0, 4); i > 0; i--) {
    const storageKeys = []
    for (let k = randomInt(0, 4); k > 0; k--) {
      storageKeys.push(pick([randomHex(32), '0x' + '00'.repeat(31) + '01', '0x' + '00'.repeat(32)]))
    }
    entries.push({ address: pick([randomHex(20), '0x' + '00'.repeat(19) + '07']), storageKeys })
  }
  return entries
}

function randomFields(kind) {
  const chainId = pick([1n, 1n, 10n, 137n, 11155111n, 0xfffffffffffn])
  const maxPriorityFeePerGas = randomBig(5)
  const fields = {
    type: hex(kind),
    chainId: hex(chainId),
    nonce: hex(pick([0n, 1n, 0x7fn, 0x80n, randomBig(7)])),
    gas: hex(21000n + randomBig(3)),
    to: pick([randomHex(20), randomHex(20), '0x' + '00'.repeat(20), '0x00000000000000000000000000000000000000ff']),
    value: hex(pick([0n, 1n, randomBig(12), randomBig(32)])),
    input: pick(['0x', '0x00', '0x7f', '0x80', randomHex(randomInt(1, 80)), randomHex(randomInt(56, 300))]),
  }
  if (kind <= 2 && randomInt(0, 4) === 0) fields.to = null
  if (kind < 2) {
    fields.gasPrice = hex(randomBig(6))
  } else {
    fields.maxPriorityFeePerGas = hex(maxPriorityFeePerGas)
    fields.maxFeePerGas = hex(maxPriorityFeePerGas + randomBig(6))
  }
  if (kind === 0 && randomInt(0, 4) === 0) fields.chainId = null
  if (kind >= 1) fields.accessList = randomAccessList()
  if (kind === 3) {
    fields.maxFeePerBlobGas = hex(1n + randomBig(4))
    fields.blobVersionedHashes = []
    for (let i = randomInt(1, 4); i > 0; i--) fields.blobVersionedHashes.push('0x01' + randomHex(31).slice(2))
  }
  return fields
}

function oracleSign(fields, key) {
  const kind = Number(fields.type)
  const data = {
    nonce: fields.nonce, gasLimit: fields.gas, to: fields.to ?? undefined, value: fields.value,
    data: fields.input,
  }
  let tx
  if (kind === 0) {
    data.gasPrice = fields.gasPrice
    // Without a chain id EthereumJS signs the pre-EIP-155 form when the hardfork predates it.
    tx = fields.chainId === null
      ? createLegacyTx(data, { common: new Common({ chain: Mainnet, hardfork: Hardfork.TangerineWhistle }) })
      : createLegacyTx(data, { common: commonFor(fields.chainId) })
  } else {
    data.chainId = fields.chainId
    data.accessList = fields.accessList
    if (kind === 1) {
      data.gasPrice = fields.gasPrice
      tx = createAccessList2930Tx(data, { common: commonFor(fields.chainId) })
    } else {
      data.maxFeePerGas = fields.maxFeePerGas
      data.maxPriorityFeePerGas = fields.maxPriorityFeePerGas
      if (kind === 2) tx = createFeeMarket1559Tx(data, { common: commonFor(fields.chainId) })
      else if (kind === 3) {
        data.maxFeePerBlobGas = fields.maxFeePerBlobGas
        data.blobVersionedHashes = fields.blobVersionedHashes
        tx = createBlob4844Tx(data, { common: commonFor(fields.chainId) })
      } else {
        data.authorizationList = fields.authorizationList
        tx = createEOACode7702Tx(data, { common: commonFor(fields.chainId) })
      }
    }
  }
  const signed = tx.sign(key)
  return {
    raw: bytesToHex(signed.serialize()),
    hash: bytesToHex(signed.hash()),
    from: signed.getSenderAddress().toString().toLowerCase(),
  }
}

// Blob transactions here carry versioned hashes only, so no KZG operation is ever needed;
// the oracle still wants the slot filled.
const noKzg = new Proxy({}, { get: () => () => { throw new Error('KZG is not used in this test') } })

function commonFor(chainIdHex) {
  // The oracle checks the transaction's chain id against its Common; give it the same id.
  return new Common({
    chain: { ...Mainnet, chainId: Number(BigInt(chainIdHex)) },
    hardfork: Hardfork.Prague,
    customCrypto: { kzg: noKzg },
  })
}

function wallet(command, key, document) {
  const path = join(dir, 'input.json')
  writeFileSync(path, JSON.stringify(document))
  const out = execFileSync(binary, [command, RISK, '--test-key-hex', bytesToHex(key).slice(2), path],
    { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] })
  return JSON.parse(out)
}

const quantity = (text) => BigInt(text === '0x' ? '0x0' : text)

function authorizations(count) {
  const list = []
  for (let i = 0; i < count; i++) {
    const authorityKey = randomKey()
    const unsigned = {
      chainId: pick(['0x0', '0x1', hex(137n)]),
      address: randomHex(20),
      nonce: hex(pick([0n, 1n, randomBig(7)])),
    }
    const oracle = eoaCode7702AuthorizationListBytesItemToJSON(eoaCode7702SignAuthorization(unsigned, authorityKey))
    const mine = wallet('sign-authorization', authorityKey, unsigned)
    for (const name of ['chainId', 'nonce', 'yParity', 'r', 's']) {
      if (quantity(oracle[name]) !== quantity(mine[name])) throw new Error(`authorization ${name} differs`)
    }
    if (oracle.address.toLowerCase() !== mine.address) throw new Error('authorization address differs')
    list.push({ chainId: mine.chainId, address: mine.address, nonce: mine.nonce, yParity: mine.yParity, r: mine.r, s: mine.s })
  }
  return list
}

const counts = { matched: {}, authorizationsMatched: 0, controls: 0 }
try {
  for (const kind of [0, 1, 2, 3, 4]) {
    counts.matched[kind] = 0
    for (let i = 0; i < perKind; i++) {
      const key = randomKey()
      const fields = randomFields(kind)
      if (kind === 4) {
        fields.authorizationList = authorizations(randomInt(1, 4))
        counts.authorizationsMatched += fields.authorizationList.length
      }
      const oracle = oracleSign(fields, key)
      const mine = wallet('sign', key, fields)
      if (mine.raw !== oracle.raw) throw new Error(`kind ${kind} case ${i}: raw bytes differ\n${JSON.stringify(fields)}`)
      if (mine.hash !== oracle.hash) throw new Error(`kind ${kind} case ${i}: hash differs`)
      if (mine.from !== oracle.from) throw new Error(`kind ${kind} case ${i}: sender differs`)
      counts.matched[kind] += 1
      if (i < 5) {
        // Controls: a changed nonce and another key must each change the bytes.
        const changed = wallet('sign', key, { ...fields, nonce: hex(BigInt(fields.nonce) + 1n) })
        const otherKey = wallet('sign', randomKey(), fields)
        if (changed.raw === oracle.raw || otherKey.raw === oracle.raw || otherKey.from === oracle.from) {
          throw new Error(`kind ${kind} case ${i}: a negative control matched`)
        }
        counts.controls += 2
      }
    }
  }
  // Control: no risk flag, no signature.
  const path = join(dir, 'input.json')
  const refused = spawnSync(binary, ['sign', '--test-key-hex', bytesToHex(randomKey()).slice(2), path], { encoding: 'utf8' })
  if (refused.status === 0 || refused.stdout.includes('"raw"')) throw new Error('signed without the risk flag')
  counts.controls += 1
  // Control: a zero key and the group order are refused.
  for (const bad of ['00'.repeat(32), 'fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141']) {
    const result = spawnSync(binary, ['sign', RISK, '--test-key-hex', bad, path], { encoding: 'utf8' })
    if (result.status === 0 || result.stdout.includes('"raw"')) throw new Error('signed with an invalid key')
    counts.controls += 1
  }
} finally {
  rmSync(dir, { recursive: true, force: true })
}
console.log(JSON.stringify({ oracle: '@ethereumjs/tx 10.1.3 (test oracle only)', casesPerKind: perKind, ...counts }))
