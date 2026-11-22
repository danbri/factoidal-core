#!/usr/bin/env node
/**
 * Archive EIP-1186 witness verifier for REAL Frontier block 46,147.
 *
 * This is the bridge from transaction-level proof obligations to authenticated
 * mainnet execution. A candidate witness must contain:
 *  - Full block 46146 header, whose Keccak hash is the KNOWN parent hash.
 *  - eth_getProof account proofs for sender, recipient and miner at block 46146.
 *  - The three proof paths must hash to the header's actual stateRoot.
 *
 * The script verifies each account nonce, balance, storage root and code
 * hash against the proof's RLP value. It loads sparse trie nodes into a
 * mutable MPT, uses the *real Lean Frontier transaction settlement* to update
 * the three account records, and checks the new authenticated state trie
 * against block 46147's PRE-BYZANTIUM receipt intermediate root.
 *
 * Then it applies Frontier's separate 5 ETH block subsidy and checks the
 * FULL post-block state root from block 46147's header. No uncle blocks are
 * allowed in this published historical block.
 *
 * No proof node is simply trusted. The proofs, signature, header and both
 * roots must all verify or exit nonzero. KZG, EIP-1559, EIP-150 and
 * post-Byzantium receipt status rules do NOT apply to this block.
 *
 * --selftest uses synthetic state solely to challenge the proof machinery
 * and mutations. It never claims historical replay.
 */
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs'
import { dirname } from 'node:path'
import { spawnSync } from 'node:child_process'
import { createBlockHeaderFromRPC } from '@ethereumjs/block'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createMPT, createMerkleProof, updateMPTFromMerkleProof, verifyMerkleProof } from '@ethereumjs/mpt'
import { RLP } from '@ethereumjs/rlp'
import { createAccount, bytesToBigInt, bytesToHex, hexToBytes,
  KECCAK256_NULL, KECCAK256_RLP } from '@ethereumjs/util'

const frontier = new Common({chain:Mainnet,hardfork:Hardfork.Chainstart})
const EMPTY_CODE_HASH=bytesToHex(KECCAK256_NULL).toLowerCase()
const EMPTY_STORAGE_ROOT=bytesToHex(KECCAK256_RLP).toLowerCase()
const FIVE_ETH=5000000000000000000n
const MAX_BALANCE=1n<<256n
function require(ok,msg) {if(!ok)throw Error(msg)}
function same(a,b) {return String(a).toLowerCase()===String(b).toLowerCase()}
function num(s,label) {
  require(typeof s==='string' && /^(0x[0-9a-f]+|[0-9]+)$/i.test(s),'bad '+label)
  return BigInt(s)
}
function assertHex(s,bytes,what){
  require(typeof s==='string' &&
    new RegExp('^0x[0-9a-fA-F]{'+(2*bytes)+'}$').test(s),'bad '+what)
}
function address(s) {assertHex(s,20,'address');return s.toLowerCase()}
function decodeProvenAccount(serialized) {
  if(serialized===null)
    return {exists:false,nonce:0n,balance:0n,storageHash:EMPTY_STORAGE_ROOT,
      codeHash:EMPTY_CODE_HASH}
  const fields=RLP.decode(serialized)
  require(Array.isArray(fields) && fields.length===4 &&
    fields.every(f=>f instanceof Uint8Array),'invalid four-tuple RLP account')
  const [nonce,balance,storageRoot,codeHash]=fields
  require(storageRoot.length===32 && codeHash.length===32,'invalid account hash size')
  return {exists:true,nonce:bytesToBigInt(nonce),balance:bytesToBigInt(balance),
    storageHash:bytesToHex(storageRoot).toLowerCase(),
    codeHash:bytesToHex(codeHash).toLowerCase()}
}
async function authenticateAccounts(root, bundles, addresses) {
  assertHex(root,32,'parent state root')
  require(Array.isArray(bundles) && bundles.length===addresses.length,
    'missing or extra EIP-1186 account proof')
  const seen=new Set(), out=[]
  for(const addr of addresses) {
    const p=bundles.find(row=>same(row.address,addr))
    require(p && !seen.has(addr),'missing or duplicated required proof '+addr)
    seen.add(addr)
    require(Array.isArray(p.accountProof) && p.accountProof.length>0 &&
      (p.storageProof===undefined ||
       Array.isArray(p.storageProof) && p.storageProof.length===0),
      'missing EIP-1186 proof nodes or unexpected storage proof')
    const nodes=p.accountProof.map(node=>{
      require(typeof node==='string' && /^0x[0-9a-fA-F]+$/.test(node),
        'invalid proof node bytes')
      return hexToBytes(node)
    })
    const accountBytes=await verifyMerkleProof(hexToBytes(addr),nodes,{
      root:hexToBytes(root),useKeyHashing:true})
    const actual=decodeProvenAccount(accountBytes)
    for(const [name,field] of [
      ['balance',actual.balance],['nonce',actual.nonce],
    ])require(num(p[name],name)===field,'forged account proof '+name+' for '+addr)
    // EIP-1186 eth_getProof represents an ABSENT account by zeroed codeHash
    // and storageHash, whereas an EXISTING empty-code/empty-storage account
    // uses Keccak(empty bytes) and Keccak(RLP empty string). A verified MPT
    // nonmembership result is the sole authority for selecting the convention:
    // the RPC cannot *declare* an address absent to evade a real account.
    const rpcAbsentHash='0x'+'00'.repeat(32)
    const expectedCodeHash=actual.exists?actual.codeHash:rpcAbsentHash
    const expectedStorageHash=actual.exists?actual.storageHash:rpcAbsentHash
    require(same(p.codeHash,expectedCodeHash) &&
      same(p.storageHash,expectedStorageHash),
      'forged account code/storage hashes or nonmembership convention for '+addr)
    out.push({...actual,address:addr,proofNodes:nodes})
  }
  return out
}
function accountRlp(a) {
  require(a.nonce>=0n && a.nonce<(1n<<64n) &&
    a.balance>=0n && a.balance<MAX_BALANCE,'nonce/balance outside RLP account bounds')
  return createAccount({
    nonce:a.nonce,balance:a.balance,
    storageRoot:hexToBytes(a.storageHash),
    codeHash:hexToBytes(a.codeHash),
  }).serialize()
}
async function replayFromRoot(root, actual, newAccounts) {
  const trie=await createMPT({useKeyHashing:true,root:hexToBytes(root)})
  for(const account of actual){
    await updateMPTFromMerkleProof(trie,account.proofNodes,true)
    const oldBytes=await trie.get(hexToBytes(account.address),true)
    const old=decodeProvenAccount(oldBytes)
    require(old.balance===account.balance && old.nonce===account.nonce &&
      same(old.storageHash,account.storageHash) &&
      same(old.codeHash,account.codeHash),
      'sparse authenticated trie did not reproduce an account')
  }
  // Only three accounts can change in the explicitly scoped Frontier
  // no-contract-code transfer plus block-subsidy transition.
  for(const a of newAccounts) {
    require(actual.some(old=>same(old.address,a.address)),
      'attempted unauthenticated address update')
    await trie.put(hexToBytes(a.address),accountRlp(a))
  }
  return bytesToHex(trie.root())
}
function runLean(tx,b,accounts) {
  const input=[
    num(tx.gasLimit,'gas limit'), num(b.gasLimit,'block gas limit'),
    num(tx.gasPrice,'gas price'), num(tx.value,'value'), 0n,0n,
    accounts[0].balance,accounts[1].balance,accounts[2].balance,
    accounts[0].nonce,num(tx.nonce,'signed nonce'),1n,
  ].map(String)
  const p=spawnSync('lake',['exe','evm-subset','--frontier-transfer',...input],{
    encoding:'utf8',timeout:60000,maxBuffer:1024*1024})
  require(!p.error && p.status===0,'Lean Frontier transfer process error: '+String(p.error??p.stderr))
  const result=JSON.parse(p.stdout.trim().split('\n').at(-1))
  require(result.status==='ok','Lean rejected authenticated Frontier transaction: '+JSON.stringify(result))
  return result
}
async function verifyHistorical(bundle,historical) {
  const b=historical.block,tx=historical.transaction,receipt=historical.receipt
  const parent=bundle.parentHeader
  require(bundle.schemaVersion===1 && parent && Array.isArray(bundle.accounts),
    'bad historical witness-bundle shape')
  require(num(parent.number,'parent block number')===46146n,
    'witness must be anchored at block 46146, not block 46147')
  require(same(parent.hash,b.parentHash),'wrong block 46146 parent hash')
  const header=createBlockHeaderFromRPC({
    ...parent,logsBloom:parent.logsBloom ??
      (parent.zeroLogsBloom?'0x'+'00'.repeat(256):null)
  },{common:frontier})
  require(same(bytesToHex(header.hash()),b.parentHash),
    'claimed parent block hash fails 15-field Frontier header authentication')
  const sourceRoot=bytesToHex(header.stateRoot)
  assertHex(sourceRoot,32,'parent MPT root')
  const sender=address(tx.from),receiver=address(tx.to),miner=address(b.miner)
  require(new Set([sender,receiver,miner]).size===3,
    'three participant account addresses are not distinct')
  const actual=await authenticateAccounts(sourceRoot,bundle.accounts,
    [sender,receiver,miner])
  const [from,to,coinbase]=actual
  require(same(from.codeHash,EMPTY_CODE_HASH) &&
    same(to.codeHash,EMPTY_CODE_HASH),
    'signed sender or recipient has EVM code in authenticated prestate; this slice cannot execute it')
  require(from.nonce===0n,'historical first transaction has different prestate nonce')
  const transition=runLean(tx,b,actual)
  const intermediate=[
    {...from,nonce:num(transition.senderAfterNonce,'new sender nonce'),
      balance:num(transition.senderAfterBalance,'new sender balance')},
    {...to,balance:num(transition.receiverAfterBalance,'new receiver balance')},
    {...coinbase,balance:num(transition.minerAfterBalance,'new miner balance')},
  ]
  const intermediateRoot=await replayFromRoot(sourceRoot,actual,intermediate)
  require(same(intermediateRoot,receipt.preByzantiumPostTransactionStateRoot),
    'REAL MAINNET TRANSACTION STATE ROOT MISMATCH: '+intermediateRoot+
    ' expected '+receipt.preByzantiumPostTransactionStateRoot)
  // Once the single transaction is settled, Frontier adds its 5 ETH block
  // subsidy to the miner. This block has zero uncles and no ommers rewards.
  require(Array.isArray(b.uncles) && b.uncles.length===0,
    'Frontier uncle payouts not covered')
  const afterBlock=[
    intermediate[0],intermediate[1],
    {...intermediate[2],balance:intermediate[2].balance+FIVE_ETH},
  ]
  // Reconstruct using the original signed prestate proofs; this ensures
  // the authenticated root isn't merely overwritten with a published value.
  const finalRoot=await replayFromRoot(sourceRoot,actual,afterBlock)
  require(same(finalRoot,b.stateRoot),
    'REAL MAINNET BLOCK STATE ROOT MISMATCH: '+finalRoot+' expected '+b.stateRoot)
  return {
    status:'full-historical-three-account-root-replay-pass',
    block:'46147',from:sender,to:receiver,miner,
    validatedPrestateRoot:sourceRoot,
    derivedIntermediateStateRoot:intermediateRoot,
    derivedFinalBlockStateRoot:finalRoot,
    publishedIntermediateStateRoot:receipt.preByzantiumPostTransactionStateRoot,
    publishedFinalBlockStateRoot:b.stateRoot,
    transactionGasUsed:transition.gasUsed,
    transactionFeeWei:transition.chargedFee,
    genesisFrontierBlockSubsidyWei:FIVE_ETH.toString(),
    witnessedAccounts:actual.length,
    codeHashesValidated:true,signatureAndTxHeaderValidatedBySeparateGate:true,
    trust:'EthereumJS RLP/MPT/Keccak and published block header, Lean arithmetic; PoW chain canonicality not independently proved',
  }
}

async function syntheticSelftest(historical){
  const b=historical.block,tx=historical.transaction
  const roles=[address(tx.from),address(tx.to),address(b.miner)]
  const trials=[]
  for(const receiverExists of [true,false]){
    const accounts=[
      {address:roles[0],nonce:0n,balance:2000000000000000000n,
        storageHash:EMPTY_STORAGE_ROOT,codeHash:EMPTY_CODE_HASH,exists:true},
      {address:roles[1],nonce:0n,balance:0n,
        storageHash:EMPTY_STORAGE_ROOT,codeHash:EMPTY_CODE_HASH,exists:receiverExists},
      {address:roles[2],nonce:0n,balance:0n,
        storageHash:EMPTY_STORAGE_ROOT,codeHash:EMPTY_CODE_HASH,exists:true},
    ]
    const reference=await createMPT({useKeyHashing:true})
    for(const a of accounts)
      if(a.exists)await reference.put(hexToBytes(a.address),accountRlp(a))
    const root=bytesToHex(reference.root())
    const bundles=[]
    for(const a of accounts) {
      const proof=await createMerkleProof(reference,hexToBytes(a.address))
      bundles.push({address:a.address,accountProof:proof.map(bytesToHex),
        storageProof:[],balance:'0x'+a.balance.toString(16),
        nonce:'0x'+a.nonce.toString(16),
        codeHash:a.codeHash,storageHash:a.storageHash})
    }
    const proven=await authenticateAccounts(root,bundles,roles)
    require(proven[1].exists===receiverExists,
      'proof did not correctly classify recipient account existence')
    const transfer=runLean(tx,b,proven)
    const changed=[
      {...proven[0],balance:BigInt(transfer.senderAfterBalance),
        nonce:BigInt(transfer.senderAfterNonce)},
      {...proven[1],balance:BigInt(transfer.receiverAfterBalance)},
      {...proven[2],balance:BigInt(transfer.minerAfterBalance)},
    ]
    const proofRoot=await replayFromRoot(root,proven,changed)
    for(const a of changed) await reference.put(hexToBytes(a.address),accountRlp(a))
    const fullRoot=bytesToHex(reference.root())
    require(same(proofRoot,fullRoot),
      'sparse proof trie and complete independently-built trie diverged')
    const mutations=[
      x=>{x[0].balance='0x1'},
      x=>{x[0].accountProof[0]='0xdeadbeef'},
      x=>{x[1].codeHash='0x'+'11'.repeat(32)},
      x=>{x[2].address=roles[0]},
    ]
    let rejected=0
    for(const mutate of mutations) {
      const forged=structuredClone(bundles)
      mutate(forged)
      try {await authenticateAccounts(root,forged,roles)}
      catch {rejected++}
    }
    require(rejected===mutations.length,'one or more forged account proofs accepted')
    let wrongRootRejected=false
    try{await authenticateAccounts('0x'+'11'.repeat(32),bundles,roles)}
    catch{wrongRootRejected=true}
    require(wrongRootRejected,'forged parent trie root incorrectly accepted')
    trials.push({receiverExists,root,mutatedRoot:proofRoot,
      fullTrieMatched:true,forgeriesRejected:rejected+1})
  }
  return {status:'synthetic-archive-proof-mutation-tests-pass',
    syntheticOnly:true,
    syntheticScenarios:trials.length,
    testedPresentAndAbsentRecipient:true,
    completeTrieMatchesSparseProofTrie:trials.every(t=>t.fullTrieMatched),
    forgedProofsRejected:trials.reduce((n,t)=>n+t.forgeriesRejected,0),
    trials,
    historicalPrestateAvailable:false,
    actualMainnetStateRootReplayed:false}
}

const args=process.argv.slice(2)
function opt(flag){const i=args.indexOf(flag);return i>=0?args[i+1]:undefined}
const historicalFile=opt('--historical')
require(historicalFile,'usage: --historical evidence/frontier-mainnet-46147.json (--selftest | --witness BUNDLE.json) [--out FILE]')
const historical=JSON.parse(readFileSync(historicalFile,'utf8'))
try {
  let result
  if(args.includes('--selftest')) result=await syntheticSelftest(historical)
  else {
    const file=opt('--witness')
    require(file,'witness file required, never fabricate an actual historical proof')
    result=await verifyHistorical(JSON.parse(readFileSync(file,'utf8')),historical)
  }
  const output=opt('--out')
  if(output){
    mkdirSync(dirname(output),{recursive:true})
    writeFileSync(output,JSON.stringify(result,null,2)+'\n')
  }
  console.log(JSON.stringify(result))
} catch (e){
  console.error('Frontier authenticated prestate replay failed closed:',String(e))
  process.exitCode=1
}
