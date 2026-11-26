#!/usr/bin/env node
/**
 * First REAL historical Ethereum mainnet transaction, Frontier block 46147.
 *
 * 1. Decode and independently signature-check the exact historical signed
 *    RLP from a published transaction example (EthereumJS 10.1.3).
 * 2. Recompute tx hash, 1-entry canonical transaction MPT, pre-Byzantium
 *    receipt MPT (the receipt carries the *published* intermediate state
 *    root), and 15-field Frontier block-header hash.
 * 3. Feed the actual transaction value/gas/nonce into our executable Lean
 *    Frontier transfer model with explicitly ILLUSTRATIVE pre-balances,
 *    then verify gas and conditional conservation.
 *
 * No EthereumJS EVM runs this transaction. This is not verified replay
 * against actual authenticated pre-transaction state: the receipt's
 * intermediate state root is INPUT, not output of Lean or a state trie.
 * Fail closed on every mismatch. Do not describe this as end-to-end
 * mainnet state-root replay until issue #650's witness obligation is done.
 */
import { createHash } from 'node:crypto'
import { readFileSync, mkdirSync, writeFileSync } from 'node:fs'
import { dirname } from 'node:path'
import { spawnSync } from 'node:child_process'
import { createBlockHeaderFromRPC } from '@ethereumjs/block'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createMPT } from '@ethereumjs/mpt'
import { RLP } from '@ethereumjs/rlp'
import { createTxFromRLP } from '@ethereumjs/tx'
import { bigIntToUnpaddedBytes, bytesToHex, hexToBytes } from '@ethereumjs/util'

const EXPECTED = Object.freeze({
  blockNumber: 46147n,
  blockHash: '0x4e3a3754410177e6937ef1f84bba68ea139e8d1a2258c5f85db9f1cd715a1bdd',
  transactionHash: '0x5c504ed432cb51138bcf09aa5e8a410dd4a1e204ef84bfed1be16dfba1b22060',
  sender: '0xa1e4380a3b1f749673e270229993ee55f35663b4',
  receiver: '0x5df9b87991262f6ba471f09758cde1c0fc1de734',
  value: 31337n,
  gas: 21000n,
  gasPrice: 50000000000000n,
  fee: 1050000000000000000n,
  receiptsRoot: '0xfe2bf2a941abf41d72637e5b91750332a30283efd40c424dc522b77e6f0ed8c4',
  transactionsRoot: '0x4513310fcb9f6f616972a3b948dc5d547f280849a87ebb5af0191f98b87be598',
  receiptIntermediateRoot: '0x96a8e009d2b88b1483e6941e6812e32263b05683fac202abc622a3e31aed1957',
  finalBlockStateRoot: '0x0e0df2706b0a4fb8bd08c9246d472abbe850af446405d9eba1db41db18b4a169',
})

function require(ok, message) {
  if (!ok) throw Error(message)
}
function same(a,b) {
  return String(a).toLowerCase() === String(b).toLowerCase()
}
function bigInt(input, what) {
  require(typeof input === 'string' && /^(0x[0-9a-f]+|[0-9]+)$/i.test(input),
    'malformed '+what)
  return BigInt(input)
}
const zeroBloom='0x'+'00'.repeat(256)
const frontier=new Common({chain:Mainnet,hardfork:Hardfork.Chainstart})

async function check(record) {
  require(record.schemaVersion===1 && record.provenance?.executionFork?.includes('Frontier'),
    'wrong fixture schema/fork')
  const b=record.block, d=record.transaction, receipt=record.receipt
  require(b && d && receipt && b.zeroLogsBloom && receipt.zeroLogsBloom &&
    Array.isArray(b.uncles) && b.uncles.length===0 &&
    Array.isArray(receipt.logs) && receipt.logs.length===0,
  'nonempty logs or uncles not handled')
  require(bigInt(b.number,'block number')===EXPECTED.blockNumber &&
    same(b.hash,EXPECTED.blockHash) && same(d.hash,EXPECTED.transactionHash) &&
    bigInt(b.gasUsed,'block gas')===EXPECTED.gas &&
    bigInt(b.gasLimit,'block limit')===21003n,
  'historical block/tx identity changed')
  require(same(b.stateRoot,EXPECTED.finalBlockStateRoot) &&
    same(b.transactionsRoot,EXPECTED.transactionsRoot) &&
    same(b.receiptsRoot,EXPECTED.receiptsRoot) &&
    same(receipt.preByzantiumPostTransactionStateRoot,EXPECTED.receiptIntermediateRoot),
  'published historical root changed')

  const signedBytes=hexToBytes(d.raw)
  const tx=createTxFromRLP(signedBytes,{common:frontier})
  require(tx.type===0 && tx.v===28n &&
    tx.getSenderAddress().toString().toLowerCase()===EXPECTED.sender &&
    same(bytesToHex(tx.hash()),EXPECTED.transactionHash) &&
    same(bytesToHex(tx.serialize()),d.raw) &&
    same(d.from,EXPECTED.sender) &&
    same(d.to,EXPECTED.receiver) &&
    same(tx.to?.toString(),EXPECTED.receiver) &&
    tx.value===EXPECTED.value && bigInt(d.value,'value')===tx.value &&
    tx.gasPrice===EXPECTED.gasPrice && bigInt(d.gasPrice,'gas price')===tx.gasPrice &&
    tx.gasLimit===EXPECTED.gas && bigInt(d.gasLimit,'gas limit')===tx.gasLimit &&
    tx.nonce===0n && bigInt(d.nonce,'nonce')===tx.nonce &&
    tx.data.length===0 && d.data==='0x' && d.index===0,
    'signed historical Frontier transaction metadata/signature mismatch')

  const transactions=await createMPT()
  const leafKey=RLP.encode(0)
  await transactions.put(leafKey,signedBytes)
  const computedTransactionsRoot=bytesToHex(transactions.root())
  require(same(computedTransactionsRoot,b.transactionsRoot),
    'actual historical signed RLP does not reconstruct transactionsRoot')

  require(bigInt(receipt.gasUsed,'receipt gas')===EXPECTED.gas &&
    bigInt(receipt.cumulativeGasUsed,'cumulative gas')===EXPECTED.gas,
    'historical receipt gas mismatch')
  // Frontier receipts contain *post-transaction stateRoot* rather than
  // Byzantium+ status. That is a PUBLISHED input, not a Lean result.
  const receiptBytes=RLP.encode([
    hexToBytes(receipt.preByzantiumPostTransactionStateRoot),
    bigIntToUnpaddedBytes(bigInt(receipt.cumulativeGasUsed,'cumulative gas')),
    hexToBytes(zeroBloom), [],
  ])
  const receipts=await createMPT()
  await receipts.put(leafKey,receiptBytes)
  const computedReceiptsRoot=bytesToHex(receipts.root())
  require(same(computedReceiptsRoot,b.receiptsRoot),
    'pre-Byzantium receipt bytes do not reconstruct receiptsRoot')
  const rpcHeader={
    ...b, logsBloom:zeroBloom,
    transactions:[d.hash], uncles:[],
  }
  const header=createBlockHeaderFromRPC(rpcHeader,{common:frontier})
  const computedBlockHash=bytesToHex(header.hash())
  require(same(computedBlockHash,b.hash),
    'published Frontier block header RLP/hash mismatch')

  // NOT real prestate! We cannot yet authenticate historical account balances,
  // recipient code, or block 46146's world trie. These initial amounts are an
  // illustrative witness to challenge Lean's arithmetic, NOT chain facts.
  const illustrativeBalances={
    sender:2000000000000000000n,
    receiver:0n,miner:0n,
  }
  const inputs=[
    tx.gasLimit, bigInt(b.gasLimit,'block limit'), tx.gasPrice, tx.value,
    0n, 0n, illustrativeBalances.sender, illustrativeBalances.receiver,
    illustrativeBalances.miner, 0n, tx.nonce, 1n,
  ].map(String)
  const lean=spawnSync('lake',['exe','evm-subset','--frontier-transfer',...inputs],{
    encoding:'utf8',timeout:60000,maxBuffer:1024*1024
  })
  if(lean.error||lean.status!==0)
    throw Error('Lean Frontier transition failed: '+String(lean.error??lean.stderr).slice(-3500))
  const output=JSON.parse(lean.stdout.trim().split('\n').at(-1))
  require(output.status==='ok','Lean refused canonical Frontier tx under illustrative prestate')
  const chargedFee=bigInt(output.chargedFee,'charged fee')
  const sender=bigInt(output.senderAfterBalance,'sender output')
  const receiver=bigInt(output.receiverAfterBalance,'receiver output')
  const miner=bigInt(output.minerAfterBalance,'miner output')
  const used=bigInt(output.gasUsed,'gas used')
  require(chargedFee===EXPECTED.fee && used===EXPECTED.gas &&
    bigInt(output.gasRemaining,'gas remaining')===0n &&
    bigInt(output.valueTransferred,'transferred')===EXPECTED.value &&
    bigInt(output.senderAfterNonce,'nonce')===1n &&
    sender+receiver+miner ===
      illustrativeBalances.sender+illustrativeBalances.receiver+illustrativeBalances.miner &&
    sender+EXPECTED.value+chargedFee===illustrativeBalances.sender &&
    receiver===illustrativeBalances.receiver+EXPECTED.value &&
    miner===illustrativeBalances.miner+chargedFee,
    'Lean Frontier accounting failed independent conservation/fee checks')
  const preStateAuthenticated=false
  const leanDerivedIntermediateStateRoot=null
  const fullMainnetStateReplay=false
  return {
    status:'pass',kind:'historical-mainnet-frontier-signed-tx-commitments-and-conditional-lean-execution',
    network:'Ethereum mainnet',hardfork:'Frontier',block:EXPECTED.blockNumber.toString(),
    transactionHash:EXPECTED.transactionHash,blockHash:computedBlockHash,
    recoveredSender:EXPECTED.sender,valueWei:EXPECTED.value.toString(),
    chargedGas:used.toString(),chargedFeeWei:chargedFee.toString(),
    transactionRoot:computedTransactionsRoot,receiptsRoot:computedReceiptsRoot,
    receiptIntermediateStateRootFromPublishedEvidence:receipt.preByzantiumPostTransactionStateRoot,
    canonicalPostBlockStateRootFromPublishedEvidence:b.stateRoot,
    preStateAuthenticated,leanDerivedIntermediateStateRoot,fullMainnetStateReplay,
    checked: [
      'canonical signed raw transaction hash and recovered sender',
      'historical Frontier block header hash from 15 fields',
      'historical one-transaction MPT root from real signed raw RLP',
      'historical pre-Byzantium receipt MPT root from published intermediate state root',
      'Lean conditional transfer/fee/nonce transition (illustrative balances)',
    ],
    missing:[
      'authenticated account/storage/code witness from block 46146',
      'Lean-derived posttransaction world state root, independently checked against receipt root',
      '5 ETH Frontier block subsidy and any other account updates in complete post-block root',
      'PoW and chain canonicality proof, independent RLP/MPT/Keccak verification',
    ],
    proofBoundary:'Historical transaction and block commitments are real; receipt state root is an external input and Lean balances are illustrative, NOT actual historical state replay',
  }
}
async function falsification(record) {
  const mutations=[
    {name:'forged-raw-rlp',mutate:o=>{
      const s=o.transaction.raw;o.transaction.raw=s.slice(0,-1)+(s.at(-1)==='0'?'1':'0')
    }},
    {name:'wrong-receipts-root',mutate:o=>{o.block.receiptsRoot='0x'+'00'.repeat(32)}},
    {name:'wrong-intermediate-state-root',mutate:o=>{
      o.receipt.preByzantiumPostTransactionStateRoot='0x'+'11'.repeat(32)
    }},
    {name:'wrong-transactions-root',mutate:o=>{o.block.transactionsRoot='0x'+'00'.repeat(32)}},
    {name:'wrong-legacy-gas-price',mutate:o=>{o.transaction.gasPrice='0x1'}},
    {name:'wrong-header-nonce',mutate:o=>{o.block.nonce='0x123456789abcdef0'}},
  ]
  let caught=0
  for(const x of mutations) {
    const forged=structuredClone(record)
    x.mutate(forged)
    try {await check(forged)}catch{caught++}
  }
  require(caught===mutations.length,'one or more forged canonical record controls evaded the validator')
  return caught
}
const opts=process.argv.slice(2)
if(![2,4].includes(opts.length) ||
  opts[0]!=='--fixture' || (opts.length===4 && opts[2]!=='--out'))
  throw Error('usage: replay-first-mainnet.mjs --fixture JSON [--out RESULT_JSON]')
const bytes=readFileSync(opts[1])
const record=JSON.parse(bytes)
try {
  const report=await check(record)
  report.fixtureSha256=createHash('sha256').update(bytes).digest('hex')
  report.adversarialControlsRejected=await falsification(record)
  if(opts.length===4){
    mkdirSync(dirname(opts[3]),{recursive:true})
    writeFileSync(opts[3],JSON.stringify(report,null,2)+'\n')
  }
  console.log(JSON.stringify(report))
} catch(err) {
  console.error('first real mainnet transfer evidence gate failed:',String(err))
  process.exitCode=1
}
