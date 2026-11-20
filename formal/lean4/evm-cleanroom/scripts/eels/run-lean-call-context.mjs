#!/usr/bin/env node
/**
 * Genuine published Cancun EELS CALL-context state test:
 * child RETURN byte -> parent RETURNDATACOPY -> MLOAD -> SSTORE.
 *
 * Lean executes complete parent bytecode containing actual CALL, the child
 * bytecode, RETURN and the parent memory/storage transitions, and restricted
 * sender fee accounting. EthereumJS is used ONLY for signed-envelope
 * decoding/recovery, RLP/account/code/storage-trie/world MPT serialization.
 * No EthereumJS EVM/runCall/runTx execution substitutes for the Lean engine.
 *
 * This fixture has 16 cases: one supported Cancun CALL case, three other
 * Cancun call families not yet supported, twelve other-fork cases. Every
 * unexecuted case is reported in the denominator.
 */
import { createHash } from 'node:crypto'
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs'
import { dirname } from 'node:path'
import { spawnSync } from 'node:child_process'
import { Common, Hardfork, Mainnet } from '@ethereumjs/common'
import { createTxFromRLP } from '@ethereumjs/tx'
import { bytesToHex, createAccount, createAddressFromString, hexToBytes } from '@ethereumjs/util'
import { createVM } from '@ethereumjs/vm'

const opt={}
for(let i=2;i<process.argv.length;i+=2){
 if(!process.argv[i]?.startsWith('--')||process.argv[i+1]===undefined)throw Error('expected --fixture FILE --out FILE')
 opt[process.argv[i].slice(2)]=process.argv[i+1]
}
if(!opt.fixture||!opt.out)throw Error('usage: --fixture FILE --out FILE')
const raw=readFileSync(opt.fixture)
const sha256=createHash('sha256').update(raw).digest('hex')
const fixture=JSON.parse(raw)
const ids=Object.keys(fixture)
if(ids.length!==16)throw Error('unexpected total fixture inventory')
const selected=ids.filter(id=>id.includes('fork_Cancun-state_test'))
if(selected.length!==4)throw Error('unexpected Cancun fixture inventory')
const CASE_ID=selected.find(id=>id.endsWith('-call]'))
if(!CASE_ID)throw Error('no Cancun CALL fixture')
const cases=[]
for(const id of selected){
 if(id!==CASE_ID)cases.push({id,status:'unsupported',reason:'CALLCODE-DELEGATECALL-STATICCALL-not-implemented'})
}
const parseHex=(s,label)=>{
 if(typeof s!=='string'||!/^0x[0-9a-fA-F]+$/.test(s))throw Error('bad hex '+label)
 return BigInt(s)
}
const addr=(s,label)=>{
 if(typeof s!=='string'||!/^0x[0-9a-fA-F]{40}$/.test(s))throw Error('bad '+label)
 return s.toLowerCase()
}
const byteValue=n=>{
 if(n<0n || n>=1n<<256n)throw Error('bad 256-bit storage value')
 if(n===0n)return new Uint8Array(0)
 let h=n.toString(16)
 if(h.length%2)h='0'+h
 return hexToBytes('0x'+h)
}
const execLean=(args)=>{
 const p=spawnSync('lake',['exe','evm-subset',...args],{
  encoding:'utf8',maxBuffer:4*1024*1024,timeout:60000
 })
 if(p.error||p.status!==0)throw Error('Lean CLI process failed: '+String(p.error??p.stderr).slice(-3000))
 const out=JSON.parse(p.stdout.trim().split('\n').at(-1))
 if(!['ok','stopped'].includes(out.status))throw Error('Lean refused declared CALL test: '+JSON.stringify(out))
 return out
}
try {
 const rec=fixture[CASE_ID],post=rec.post?.Cancun?.[0]
 const pre=rec.pre,tx=rec.transaction,env=rec.env
 if(!post||rec.post.Cancun.length!==1||!pre||!tx||!env||Object.keys(pre).length!==3)
   throw Error('fixture is not the expected three-account state-test envelope')
 const sender=addr(tx.sender,'sender')
 const parentAddress=addr(tx.to,'parent contract')
 const childAddress=Object.keys(pre).map(a=>a.toLowerCase())
   .find(a=>a!==sender && a!==parentAddress)
 const miner=addr(env.currentCoinbase,'coinbase')
 if(!childAddress || new Set([sender,parentAddress,childAddress,miner]).size!==4)
   throw Error('account identities not distinct')
 const senderPre=pre[sender],parentPre=pre[parentAddress],childPre=pre[childAddress]
 if(!senderPre||!parentPre||!childPre||
   senderPre.code!=='0x'||
   Object.keys(senderPre.storage??{}).length!==0||
   Object.keys(parentPre.storage??{}).length!==0||
   Object.keys(childPre.storage??{}).length!==0||
   parseHex(parentPre.balance,'parent balance')!==0n||
   parseHex(childPre.balance,'child balance')!==0n)
   throw Error('unmodelled prestate accounts/storage/value')
 const common=new Common({chain:Mainnet,hardfork:Hardfork.Cancun})
 const signed=createTxFromRLP(hexToBytes(post.txbytes),{common})
 const gasLimit=parseHex(tx.gasLimit[0],'limit')
 const gasPrice=parseHex(tx.gasPrice,'price')
 const startBalance=parseHex(senderPre.balance,'balance')
 const startNonce=parseHex(senderPre.nonce,'sender nonce')
 const baseFee=parseHex(env.currentBaseFee,'base fee')
 if(signed.type!==0||
   signed.getSenderAddress().toString().toLowerCase()!==sender||
   signed.to?.toString().toLowerCase()!==parentAddress||
   signed.gasLimit!==gasLimit || signed.gasPrice!==gasPrice ||
   signed.nonce!==startNonce || signed.value!==0n ||
   signed.data.length!==0 || gasPrice<baseFee ||
   gasLimit<21000n || gasLimit>1000000n)
   throw Error('signed tx does not match supported fixed Cancun envelope')
 const initialGas=gasLimit-21000n
 const result=execLean(['--call-opcode-at',
   parentPre.code,childPre.code,BigInt(parentAddress).toString(),
   BigInt(childAddress).toString(),initialGas.toString(),'256','256'])
 if(result.status!=='stopped'||result.parentSlot0!=='1'||
   result.parentSlot1!=='255'||result.slot0!=='0'||
   result.parentMemoryByte31!=='255'||result.refund!=='0')
   throw Error('actual Lean returndata copy / parent storage differs: '+JSON.stringify(result))
 const gasRemaining=BigInt(result.gasRemaining)
 if(gasRemaining>initialGas)throw Error('Lean gas increased')
 const executionUsed=initialGas-gasRemaining
 const settled=execLean(['--tx-fee','0','0','0','0',gasLimit.toString(),
   gasPrice.toString(),'0',baseFee.toString(),startBalance.toString(),
   startNonce.toString(),executionUsed.toString(),'0'])
 const charged=BigInt(settled.chargedGas)
 const senderAfter=BigInt(settled.senderAfterBalance)
 const afterNonce=BigInt(settled.senderAfterNonce)
 const coinbaseReward=BigInt(settled.minerReward)
 if(charged!==21000n+executionUsed||senderAfter+charged*gasPrice!==startBalance||
   afterNonce!==startNonce+1n||coinbaseReward!==charged*(gasPrice-baseFee))
   throw Error('Lean settlement/fee conservation mismatch')
 const vm=await createVM({common})
 const senderA=createAddressFromString(sender)
 const parentA=createAddressFromString(parentAddress)
 const childA=createAddressFromString(childAddress)
 const minerA=createAddressFromString(miner)
 await vm.stateManager.putAccount(senderA,createAccount({nonce:afterNonce,balance:senderAfter}))
 await vm.stateManager.putAccount(parentA,createAccount({
   nonce:parseHex(parentPre.nonce,'parent nonce'),balance:0n}))
 await vm.stateManager.putCode(parentA,hexToBytes(parentPre.code))
 await vm.stateManager.putStorage(parentA,new Uint8Array(32),byteValue(1n))
 const slotOne=new Uint8Array(32);slotOne[31]=1
 await vm.stateManager.putStorage(parentA,slotOne,byteValue(255n))
 await vm.stateManager.putAccount(childA,createAccount({
   nonce:parseHex(childPre.nonce,'child nonce'),balance:0n}))
 await vm.stateManager.putCode(childA,hexToBytes(childPre.code))
 if(coinbaseReward>0n)
   await vm.stateManager.putAccount(minerA,createAccount({balance:coinbaseReward,nonce:0n}))
 const computed=bytesToHex(await vm.stateManager.getStateRoot())
 const published=Object.fromEntries(Object.entries(post.state??{})
   .map(([a,x])=>[a.toLowerCase(),x]))
 if(Object.keys(published).length!==4 ||
   ![sender,parentAddress,childAddress,miner].every(a=>Object.hasOwn(published,a)))
   throw Error('published post-account set differs')
 const pa=published[parentAddress],sa=published[sender],ca=published[childAddress],ma=published[miner]
 const storage=pa.storage??{}
 if(Object.keys(storage).length!==2 ||
   parseHex(storage['0x00'],'slot zero')!==1n ||
   parseHex(storage['0x01'],'slot one')!==255n ||
   parseHex(pa.balance,'parent post balance')!==0n||
   parseHex(pa.nonce,'parent post nonce')!==parseHex(parentPre.nonce,'parent nonce')||
   pa.code.toLowerCase()!==parentPre.code.toLowerCase()||
   parseHex(ca.balance,'child post balance')!==0n||
   ca.code.toLowerCase()!==childPre.code.toLowerCase()||
   parseHex(ca.nonce,'child post nonce')!==parseHex(childPre.nonce,'child nonce')||
   Object.keys(ca.storage??{}).length!==0||
   parseHex(sa.balance,'sender post balance')!==senderAfter||
   parseHex(sa.nonce,'sender post nonce')!==afterNonce||
   parseHex(ma.balance,'miner post balance')!==coinbaseReward)
   throw Error('published post-account and storage values differ')
 const EMPTY_LOG_HASH='0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347'
 if(computed.toLowerCase()!==post.hash.toLowerCase()||post.logs!==EMPTY_LOG_HASH)
   throw Error('published CALL state root/log hash differs: '+computed+' expected '+post.hash)
 cases.push({id:CASE_ID,status:'pass',fork:'Cancun',
  executableBytecode:{parent:parentPre.code,child:childPre.code},
  returndataCopied:'0xff',parentSlots:{'0x00':'1','0x01':'255'},
  leanExecutionGas:executionUsed.toString(),
  chargedGas:charged.toString(),coinbaseReward:coinbaseReward.toString(),
  expectedStateRoot:post.hash,computedStateRoot:computed,
  proofBoundary:'Lean bytecode CALL→child RETURN→RETURNDATACOPY→MLOAD→SSTORE and Lean tx-fee settlement; trusted JS signature/recovery and EthereumJS code/storage/world trie hashing'
 })
} catch(e){
 cases.push({id:CASE_ID,status:'fail',reason:String(e)})
}
const pass=cases.filter(c=>c.status==='pass').length
const failed=cases.filter(c=>c.status==='fail').length
const unsupported=cases.filter(c=>c.status==='unsupported').length
const report={schemaVersion:1,
 kind:'EELS-Cancun-CALL-return-data-state-root-replay',
 status:failed?'fail':pass?'pass':'unsupported-only',
 provenance:{mirrorCommit:'3c4287ae3aea1f45af9288629834f0584fcde69a',
   fixtureSha256:sha256,fixtureCases:16,fork:'Cancun'},
 counts:{totalFixtureCases:16,CancunCases:4,passed:pass,failed,unsupported,
  otherForkNotExecuted:12},
 cases,
 limits:['One Cancun CALL case, three other Cancun call families unsupported',
   'Zero-value legacy signed transaction and empty calldata',
   'No full EthereumJS execution in replay; trusted account/storage MPT and Keccak',
   'Single parent-child CALL, return-data observation <=4096 bytes',
   'No independent EELS semantic refinement, receipts, full network or mainnet replay']}
mkdirSync(dirname(opt.out),{recursive:true})
writeFileSync(opt.out,JSON.stringify(report,null,2)+'\n')
console.log(JSON.stringify({status:report.status,...report.counts,
 fixtureSha256:sha256,firstFailure:cases.find(c=>c.status==='fail')??null}))
if(failed||pass!==1||unsupported!==3)process.exitCode=1
