#!/usr/bin/env node
/**
 * Execute genuine EELS-generated Cancun PUSH0 contract state-test cases
 * through Lean's Frame.run / TxAccounting, reconstructing the *complete*
 * account-storage and world-state roots with a trusted EthereumJS MPT host.
 *
 * This is a deliberately bounded contract slice, not arbitrary Ethereum
 * execution. No EthereumJS runTx, runCall or runCode is used for the case
 * under test. All unsupported cases remain visible in the denominator.
 *
 * Usage: node scripts/eels/run-lean-contract-state-tests.mjs
 *          --fixture /path/test_push0_contracts.json --out /path/results.json
 */
import { createHash } from 'node:crypto'
import { readFileSync, mkdirSync, writeFileSync } from 'node:fs'
import { dirname } from 'node:path'
import { spawnSync } from 'node:child_process'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createTxFromRLP } from '@ethereumjs/tx'
import { bytesToHex, createAccount, createAddressFromString, hexToBytes } from '@ethereumjs/util'
import { createVM } from '@ethereumjs/vm'

const MIRROR_COMMIT = '3c4287ae3aea1f45af9288629834f0584fcde69a'
const SOURCE_PATH = 'stable/state_tests/shanghai/eip3855_push0/test_push0_contracts.json'
const SOURCE_URL = 'https://raw.githubusercontent.com/ethereumjs/execution-spec-tests-fixtures/' +
  MIRROR_COMMIT + '/' + SOURCE_PATH
const EMPTY_LOG_HASH = '0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347'
const SUPPORTED = new Set(['before_jumpdest', 'key_sstore', 'storage_overwrite', 'gas_cost', 'fill_stack', 'stack_overflow'])
const OPT = {}
for(let i=2;i<process.argv.length;i+=2){
  if(!process.argv[i]?.startsWith('--') || process.argv[i+1]===undefined)
    throw Error('expected --fixture FILE --out FILE')
  OPT[process.argv[i].slice(2)] = process.argv[i+1]
}
if(!OPT.fixture || !OPT.out) throw Error('usage: --fixture FILE --out FILE')
const bytes=readFileSync(OPT.fixture)
const sha256=createHash('sha256').update(bytes).digest('hex')
const fixture=JSON.parse(bytes)
if(!fixture || Array.isArray(fixture) || typeof fixture!=='object') throw Error('invalid fixture')
const IDs=Object.keys(fixture)
if(IDs.length!==24) throw Error('fixture inventory changed; fail closed')
const selected=IDs.filter(id=>id.includes('fork_Cancun-state_test'))
if(selected.length!==6) throw Error('expected exactly six Cancun fixture cases')
const common = new Common({chain:Mainnet,hardfork:Hardfork.Cancun})
const cases=[]
let passed=0,failed=0,unsupported=0
const parseHex=(s,name)=>{
  if(typeof s!=='string'||!/^0x[0-9a-fA-F]+$/.test(s)) throw Error(name+' is not a hex integer')
  return BigInt(s)
}
const canonicalAddress=(s,name)=>{
  if(typeof s!=='string'||!/^0x[0-9a-fA-F]{40}$/.test(s)) throw Error('bad '+name)
  return s.toLowerCase()
}
const valueAsBytes=(n)=>{
  if(n<0n || n>=1n<<256n) throw Error('invalid storage value')
  if(n===0n) return new Uint8Array(0)
  const h=n.toString(16).padStart(Math.ceil(n.toString(16).length/2)*2,'0')
  return hexToBytes('0x'+h)
}
const runLean=(args)=>{
  const p=spawnSync('lake',['exe','evm-subset',...args],{
    encoding:'utf8',timeout:60000,maxBuffer:2*1024*1024
  })
  if(p.error||p.status!==0) throw Error('Lean executable failed: '+String(p.error??p.stderr).slice(-4000))
  const output=JSON.parse(p.stdout.trim().split('\n').at(-1))
  if(output.status!=='ok'&&output.status!=='stopped'&&output.status!=='exceptional')
    throw Error('Lean refuses selected fixture: '+JSON.stringify(output))
  return output
}

for(const id of selected){
  const record=fixture[id]
  const suffix=id.match(/-([a-z_]+)\]$/)?.[1]
  if(!suffix) throw Error('unrecognized Cancun test id '+id)
  if(!SUPPORTED.has(suffix)){
    unsupported++
    cases.push({id,status:'unsupported',reason:'unimplemented-large-stack-or-exception-case'})
    continue
  }
  try {
    const pre=record.pre
    const env=record.env
    const tx=record.transaction
    const official=record.post?.Cancun?.[0]
    if(!pre||!env||!tx||!official||record.post.Cancun.length!==1)
      throw Error('incomplete Cancun state-test envelope')
    if(Object.keys(pre).length!==2||Object.keys(tx.data).length!==1||
      Object.keys(tx.value).length!==1||Object.keys(tx.gasLimit).length!==1)
      throw Error('not a restricted two-account single-transaction fixture')
    const sender=canonicalAddress(tx.sender,'sender')
    const destination=canonicalAddress(tx.to,'destination')
    const coinbase=canonicalAddress(env.currentCoinbase,'coinbase')
    if(new Set([sender,destination,coinbase]).size!==3 ||
        !pre[sender] || !pre[destination] || !official.state)
      throw Error('unexpected account addresses')
    const senderPre=pre[sender],contractPre=pre[destination]
    if(senderPre.code!=='0x' || Object.keys(senderPre.storage??{}).length!==0 ||
      Object.keys(contractPre.storage??{}).length!==0 ||
      parseHex(contractPre.balance,'contract balance')!==0n ||
      typeof contractPre.code!=='string'||!/^0x(?:[a-fA-F0-9]{2})+$/.test(contractPre.code))
      throw Error('unsupported prestate code, balance or storage')
    const rawTx=official.txbytes
    if(!/^0x[0-9a-fA-F]+$/.test(rawTx||''))throw Error('no signed tx bytes')
    const signed=createTxFromRLP(hexToBytes(rawTx),{common})
    if(signed.type!==0 || signed.getSenderAddress().toString().toLowerCase()!==sender ||
      signed.to?.toString().toLowerCase()!==destination ||
      signed.value!==0n || signed.data.length!==0 ||
      signed.nonce!==parseHex(tx.nonce,'nonce') ||
      signed.gasLimit!==parseHex(tx.gasLimit[0],'gasLimit') ||
      signed.gasPrice!==parseHex(tx.gasPrice,'gasPrice'))
      throw Error('signed transaction does not match restricted fixture')
    const startingNonce=parseHex(senderPre.nonce,'sender nonce')
    const balance=parseHex(senderPre.balance,'sender balance')
    const baseFee=parseHex(env.currentBaseFee,'base fee')
    if(signed.nonce!==startingNonce || signed.gasPrice<baseFee)
      throw Error('invalid envelope or nonce')
    const intrinsic=21000n // Empty calldata, no access list or creation (Cancun)
    if(signed.gasLimit<intrinsic) throw Error('below intrinsic gas')
    const available=signed.gasLimit-intrinsic

    // Lean actually executes the nonempty contract, including SSTORE, jumps,
    // gas and its implicit STOP beyond bytecode end.
    const state=runLean(['--frame-storage',contractPre.code,
       available.toString(),'4096','0','0'])
    const isExpectedException = suffix === 'stack_overflow'
    if((isExpectedException ?
        (state.status!=='exceptional' || state.error!=='stackOverflow' ||
         state.gasRemaining!=='0') : state.status!=='stopped') ||
       state.original!=='0' || state.refund!=='0')
      throw Error('Lean frame outcome/refund differs from expected successful or exceptional category')
    const remaining=BigInt(state.gasRemaining)
    const slot0=BigInt(state.current)
    if(remaining>available || slot0 >= (1n<<256n))
      throw Error('invalid Lean frame output')
    const used=available-remaining

    // Restricted empty-calldata settlement: Prague EIP-7623 floor is equal
    // to Cancun intrinsic here (21000), so the local Lean TxAccounting
    // branch computes the SAME amount, without applying a new fork price.
    const settlement=runLean(['--tx-fee','0','0','0','0',
      signed.gasLimit.toString(),signed.gasPrice.toString(),'0',
      baseFee.toString(),balance.toString(),startingNonce.toString(),
      used.toString(),'0'])
    const charged=BigInt(settlement.chargedGas)
    const senderAfter=BigInt(settlement.senderAfterBalance)
    const nonceAfter=BigInt(settlement.senderAfterNonce)
    const coinbaseReward=BigInt(settlement.minerReward)
    if(charged!==intrinsic+used || senderAfter+charged*signed.gasPrice!==balance ||
      nonceAfter!==startingNonce+1n ||
      coinbaseReward!==charged*(signed.gasPrice-baseFee))
      throw Error('Lean fee settlement violates restricted Cancun accounting')

    // Unverified host computes Ethereum code hash, storage trie RLP/Keccak
    // and account MPT from the independently Lean-calculated state changes.
    // Critically: no EthereumJS EVM or transaction executor is called.
    const vm=await createVM({common})
    const senderAddress=createAddressFromString(sender)
    const contractAddress=createAddressFromString(destination)
    const minerAddress=createAddressFromString(coinbase)
    await vm.stateManager.putAccount(senderAddress,
      createAccount({balance:senderAfter,nonce:nonceAfter}))
    await vm.stateManager.putAccount(contractAddress,
      createAccount({balance:parseHex(contractPre.balance,'contract balance'),
                     nonce:parseHex(contractPre.nonce,'contract nonce')}))
    await vm.stateManager.putCode(contractAddress,hexToBytes(contractPre.code))
    if(slot0!==0n){
      await vm.stateManager.putStorage(contractAddress,new Uint8Array(32),valueAsBytes(slot0))
    }
    if(coinbaseReward!==0n)
      await vm.stateManager.putAccount(minerAddress,
        createAccount({balance:coinbaseReward,nonce:0n}))
    const root=bytesToHex(await vm.stateManager.getStateRoot())

    // Compare all post-account fields, not just one root. This step is
    // valuable but not itself an independent code/trie implementation.
    const post=Object.fromEntries(Object.entries(official.state)
      .map(([k,v])=>[k.toLowerCase(),v]))
    const expectedSet=new Set([sender,destination,coinbase])
    if(new Set(Object.keys(post)).size!==expectedSet.size ||
      Object.keys(post).some(a=>!expectedSet.has(a)))
      throw Error('published post account inventory changed')
    if(parseHex(post[sender].balance,'post sender balance')!==senderAfter ||
      parseHex(post[sender].nonce,'post sender nonce')!==nonceAfter ||
      post[sender].code!=='0x' || Object.keys(post[sender].storage??{}).length!==0 ||
      parseHex(post[destination].balance,'post destination balance')!==0n ||
      parseHex(post[destination].nonce,'post destination nonce')!==
         parseHex(contractPre.nonce,'contract nonce') ||
      post[destination].code.toLowerCase()!==contractPre.code.toLowerCase() ||
      parseHex(post[coinbase].balance,'post coinbase reward')!==coinbaseReward ||
      parseHex(post[coinbase].nonce,'post coinbase nonce')!==0n ||
      post[coinbase].code!=='0x' || Object.keys(post[coinbase].storage??{}).length!==0)
      throw Error('published post account fields differ')
    const expectedStorage=post[destination].storage??{}
    if(Object.keys(expectedStorage).some(k=>parseHex(k,'post storage key')!==0n) ||
      (slot0===0n ? Object.keys(expectedStorage).length!==0 :
        Object.keys(expectedStorage).length!==1 ||
        parseHex(Object.values(expectedStorage)[0],'post storage value')!==slot0))
      throw Error('published post storage differs from Lean')
    if(root.toLowerCase()!==official.hash.toLowerCase() ||
      official.logs.toLowerCase()!==EMPTY_LOG_HASH)
      throw Error('published post state root/log hash differs: calculated '+root+
        ' expected '+official.hash)

    passed++
    cases.push({id,status:'pass',fork:'Cancun',
      contractCode:contractPre.code,
      outcome:state.status,
      exception:state.status==='exceptional'?state.error:null,
      slot0:slot0.toString(),
      intrinsicGas:intrinsic.toString(),leanExecutionGas:used.toString(),
      chargedGas:charged.toString(),
      senderAfterBalance:senderAfter.toString(),
      coinbaseReward:coinbaseReward.toString(),
      expectedStateRoot:official.hash,computedStateRoot:root,
      expectedStorage:{'0x00':slot0.toString()},
      logsComparison:'fixed-empty-logs-hash',
      proofBoundary:'Lean code execution, SSTORE and fee settlement; trusted EthereumJS signature decoding, account/storage MPT encoding and host field mapping'})
  } catch(e) {
    failed++
    cases.push({id,status:'fail',reason:String(e)})
  }
}
const totals={fixtureCases:IDs.length,forkCases:selected.length,
  passed,failed,unsupported,otherForkCases:IDs.length-selected.length}
const report={schemaVersion:1,kind:'EELS-Cancun-contract-state-root-replay',
 status:failed?'fail':passed?'pass':'unsupported-only',
 provenance:{fixtureUrl:SOURCE_URL,mirrorCommit:MIRROR_COMMIT,fixtureSha256:sha256,
   fork:'Cancun',fixturePath:SOURCE_PATH},
 totals,cases,
 limits:{
   scopedCases:[...SUPPORTED],
   codeExecution:'Lean Frame.run with implicit STOP; single-slot observation',
   settlement:'Lean TxAccounting, zero value/empty calldata/no refund/legacy transaction',
   trusted:['EthereumJS signed RLP decoding and signer recovery',
     'EthereumJS world/storage MPT, RLP and code hashing',
     'JavaScript fixture mapping, selection, verification and orchestration',
     'Lean compiler/runtime and underlying host'],
   notClaimed:['generic EELS conformance','nested CALL','CALLDATA','nonzero-value transfers',
    'full receipt/log execution','independent MPT implementation',
    'Ethereum semantic-refinement theorem','mainnet transaction replay']
 }}
mkdirSync(dirname(OPT.out),{recursive:true})
writeFileSync(OPT.out,JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({status:report.status,...totals,
  fixtureSha256:sha256,report:OPT.out,firstFailure:cases.find(c=>c.status==='fail')??null}))
if(failed||passed!==SUPPORTED.size||passed+unsupported!==6)process.exitCode=1
