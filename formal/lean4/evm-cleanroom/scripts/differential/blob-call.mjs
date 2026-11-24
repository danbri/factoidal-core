import assert from 'node:assert/strict'
import {spawnSync} from 'node:child_process'
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {keccak_256} from '@noble/hashes/sha3.js'
import {createEVM} from '@ethereumjs/evm'
import {Common,Hardfork,Mainnet} from '@ethereumjs/common'
import {hexToBytes} from '@ethereumjs/util'

// Independent test-only RLP, EIP-4844 fee series, EIP-1559 settlement.
// EthereumJS independently executes each frame; it does not authenticate
// these synthetic headers or settle a signed type-3 transaction.
const nat=n=>{n=BigInt(n);if(n===0n)return Buffer.alloc(0);let h=n.toString(16);return Buffer.from(h.length%2?'0'+h:h,'hex')}
const len=(n,s,l)=>n<56?Buffer.of(s+n):Buffer.concat([Buffer.of(l+nat(n).length),nat(n)])
const rlp=x=>Array.isArray(x)?(()=>{const p=Buffer.concat(x.map(rlp));return Buffer.concat([len(p.length,192,247),p])})():x.length===1&&x[0]<128?x:Buffer.concat([len(x.length,128,183),x])
const hex=b=>Buffer.from(b).toString('hex')
const U=131072n,D=3338477n
const price=e=>{const terms=[D];while(terms.at(-1)!==0n)terms.push(terms.at(-1)*e/(D*BigInt(terms.length)));return terms.reduce((s,t)=>s+t,0n)/D}
assert.equal(price(0n),1n);assert.equal(price(2n*D),7n)
const header=(n,t,used,blobs,excess)=>[Buffer.alloc(32),Buffer.alloc(32),Buffer.concat([Buffer.alloc(19),Buffer.of(195)]),Buffer.alloc(32),Buffer.alloc(32),Buffer.alloc(32),Buffer.alloc(256),nat(0),nat(n),nat(30000000),nat(used),nat(t),nat(0),Buffer.alloc(32),Buffer.alloc(8),nat(100),Buffer.alloc(32),nat(blobs),nat(excess),Buffer.alloc(32)]
const account=(address,balance,nonce,codeHex='')=>({address:String(address),exists:true,balance:String(balance),nonce:String(nonce),codeHex,storage:[]})
function request({excess=0n,count=1,code='00',gas=25000n,value=7n,prior=0,priorGas=0n,data='00ff',cap=price(excess)+2n,balance=1000000000000n}={}){
 const p=header(19500000,1710338235,15000000,3n*U,excess),c=header(19500001,1710338236,1000000,BigInt(count+prior)*U,excess)
 c[0]=Buffer.from(keccak_256(rlp(p)))
 return {schemaVersion:1,fork:'cancun',fuel:'100',transaction:{type:3,chainId:'1',sender:'161',to:'162',nonce:'1',value:String(value),gasLimit:String(gas),gasPriceCap:'110',priorityFeeCap:'3',dataHex:data,accessList:[]},
 block:{chainId:'99',coinbase:'255',number:'0',timestamp:'0',gasLimit:'0',gasUsedBefore:String(priorGas),baseFee:'999',prevRandao:'99',blobBaseFee:'999'},
 accounts:[account(161,balance,1),account(162,11,1,code),account(195,11,1)],parentHeader:p.map(hex),childHeader:c.map(hex),blobVersionedHashes:Array.from({length:count},(_,i)=>'01'+i.toString(16).padStart(62,'0')),maxFeePerBlobGas:String(cap),priorBlobGas:String(BigInt(prior)*U)}
}
const evm=await createEVM({common:new Common({chain:Mainnet,hardfork:Hardfork.Cancun})})
const cases=[]
for(const excess of [0n,10n*U,30n*U,80n*U,160n*U,400n*U])for(const count of [1,2,3,4,5,6])for(const code of ['00','5f5ffd','fe','4a5f5260205ff3','4a']) {
 const data='00ff',intrinsic=21020n,gas=code==='4a'?intrinsic+1n:25000n
 const value=BigInt(count*7),prior=count===6?0:1,priorGas=123n
 const fee=price(excess),cap=fee+2n,balance=gas*110n+value+BigInt(count)*U*cap
 const q=request({excess,count,code,gas,value,prior,priorGas,data,cap,balance})
 const ref=await evm.runCode({code:hexToBytes('0x'+code),gasLimit:gas-intrinsic,block:{header:{getBlobGasPrice:()=>fee}}})
 const fault=String(ref.exceptionError?.error??'')
 const exceptional=code==='fe'||code==='4a'
 const reverted=code==='5f5ffd'
 assert.equal(!!fault,exceptional||reverted)
 const used=exceptional?gas:intrinsic+ref.executionGasUsed
 const success=!(exceptional||reverted),burn=BigInt(count)*U*fee
 const expected={status:'executed',blobGasUsed:String(BigInt(count)*U),blobFeeBurn:String(burn),result:{
 receiptStatus:success?1:0,frameStatus:exceptional?'exceptional':reverted?'reverted':code==='4a5f5260205ff3'?'returned':'stopped',
 gasUsedBeforeRefund:String(used),refundGas:'0',gasUsed:String(used),cumulativeGasUsed:String(priorGas+used),effectiveGasPrice:'103',
 gasWeiReturned:String((gas-used)*103n),beneficiaryTip:String(used*3n),baseFeeBurn:String(used*100n),returnBytesHex:hex(ref.returnValue),
 logs:[],accounts:[{address:'161',balance:String(balance-burn-used*103n-(success?value:0n)),nonce:'2'},{address:'162',balance:String(11n+(success?value:0n)),nonce:'1'},{address:'195',balance:String(11n+used*3n),nonce:'1'}]}}
 if(exceptional)expected.result.frameError=code==='fe'?'invalidOpcode':'outOfGas'
 cases.push({q,expected})
}
const bad=(change,status,reason)=>{const q=request();change(q);cases.push({q,expected:{status,reason}})}
bad(q=>q.blobVersionedHashes=[],'rejected','missing-blob')
bad(q=>q.blobVersionedHashes=Array(7).fill(q.blobVersionedHashes[0]),'rejected','too-many-blobs')
bad(q=>q.blobVersionedHashes=['02'+'00'.repeat(31)],'rejected','invalid-versioned-hash')
bad(q=>q.blobVersionedHashes=['01'],'rejected','invalid-versioned-hash')
bad(q=>q.maxFeePerBlobGas=String(2n**256n),'rejected','blob-cap-out-of-range')
bad(q=>q.maxFeePerBlobGas='0','rejected','blob-cap-below-current-fee')
bad(q=>q.accounts[0].balance=String(25000n*110n+7n+U*3n-1n),'rejected','insufficient-upfront-balance')
bad(q=>q.priorBlobGas='1','indeterminate','inconsistent-block-position')
bad(q=>q.priorBlobGas=String(U),'indeterminate','inconsistent-block-position')
bad(q=>q.block.gasUsedBefore='1000001','indeterminate','inconsistent-block-position')
bad(q=>q.accounts.shift(),'indeterminate','missing-sender-witness')
bad(q=>q.accounts.push(q.accounts[0]),'indeterminate','invalid-witness')
bad(q=>q.fuel='1000001','indeterminate','resource-limit')
bad(q=>q.childHeader[0]='ff'.repeat(32),'indeterminate','header-pair-refused')
bad(q=>q.childHeader[15]='65','indeterminate','header-pair-refused')
bad(q=>q.transaction.type=2,'indeterminate','not-type-3')
bad(q=>q.transaction.gasLimit='21019','rejected','below-intrinsic-gas')
bad(q=>q.accounts[1].codeHex='49','indeterminate','invalidOpcode')
bad(q=>q.childHeader[10]=hex(nat(21000)),'indeterminate','inconsistent-block-position')
const resource=request({excess:64n*D+1n});cases.push({q:resource,expected:{status:'indeterminate',reason:'header-pair-refused'}})
function compare(actual){
 assert.equal(actual.length,cases.length)
 function subset(a,e,path){if(Array.isArray(e)){assert.equal(a.length,e.length,path);e.forEach((v,i)=>subset(a[i],v,path+'.'+i))}else if(e!==null&&typeof e==='object'){for(const [k,v] of Object.entries(e))subset(a[k],v,path+'.'+k)}else assert.equal(a,e,path)}
 actual.forEach((a,i)=>subset(a,cases[i].expected,String(i)))
}
const dir=mkdtempSync(join(tmpdir(),'blob-call-')),file=join(dir,'cases.jsonl'),exe=process.argv[2]
assert(exe)
try{
 writeFileSync(file,cases.map(x=>JSON.stringify(x.q)).join('\n')+'\n')
 const run=(args)=>spawnSync(exe,args,{encoding:'utf8',maxBuffer:16*1024*1024,timeout:180000})
 const out=run(['--dangerously-enable-unverified-keccak','--batch',file])
 assert.equal(out.status,0,out.stderr)
 const actual=out.stdout.trim().split('\n').map(JSON.parse)
 compare(actual)
 const mutations=[a=>a[0].blobFeeBurn='0',a=>a[1].result.accounts[0].balance='0',a=>a[2].result.receiptStatus=1,a=>a[3].result.returnBytesHex='00',a=>a[0].result.beneficiaryTip='0',a=>a.pop(),a=>a.at(-1).status='rejected']
 for(const mutate of mutations){const x=structuredClone(actual);mutate(x);assert.throws(()=>compare(x))}
 assert.equal(run(['--batch',file]).status,2)
 writeFileSync(file,'{\n')
 const malformed=run(['--dangerously-enable-unverified-keccak','--batch',file])
 assert.equal(malformed.status,2);assert.equal(JSON.parse(malformed.stdout).status,'inputError')
 const malformedRequests=[
  q=>delete q.parentHeader,
  q=>delete q.childHeader,
  q=>delete q.blobVersionedHashes,
  q=>delete q.maxFeePerBlobGas,
  q=>delete q.priorBlobGas,
  q=>q.parentHeader='not-an-array',
  q=>q.childHeader[0]='zz',
  q=>q.blobVersionedHashes=[42],
  q=>q.maxFeePerBlobGas=3
 ]
 for(const mutate of malformedRequests){
  const q=request();mutate(q)
  writeFileSync(file,JSON.stringify(q)+'\n')
  const invalid=run(['--dangerously-enable-unverified-keccak','--batch',file])
  assert.equal(invalid.status,2,invalid.stderr)
  assert.equal(JSON.parse(invalid.stdout).status,'inputError')
 }
 const counts={};for(const x of actual)counts[x.status]=(counts[x.status]??0)+1
 console.log(JSON.stringify({cases:actual.length,matched:actual.length,counts,mutationsRejected:mutations.length,frameOracle:'EthereumJS 10.1.3 Cancun',signedTransactionOracle:false,missingOptInRejected:true,malformedRejected:true,malformedRequestsRejected:malformedRequests.length}))
}finally{rmSync(dir,{recursive:true,force:true})}
