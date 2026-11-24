import assert from 'node:assert/strict'
import {spawnSync} from 'node:child_process'
import {mkdtempSync,writeFileSync,rmSync,readFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {keccak_256} from '@noble/hashes/sha3.js'

// Test-only independent generic RLP byte/list encoder.
const nat=n=>{n=BigInt(n);if(n===0n)return Buffer.alloc(0);let h=n.toString(16);return Buffer.from(h.length%2?'0'+h:h,'hex')}
const lengthPrefix=(len,short,long)=>len<56?Buffer.of(short+len):Buffer.concat([Buffer.of(long+nat(len).length),nat(len)])
const rlp=x=>Array.isArray(x)?(()=>{const payload=Buffer.concat(x.map(rlp));return Buffer.concat([lengthPrefix(payload.length,192,247),payload])})():
  x.length===1&&x[0]<128?x:Buffer.concat([lengthPrefix(x.length,128,183),x])
const hex=b=>Buffer.from(b).toString('hex')
const hash=f=>Buffer.from(keccak_256(rlp(f)))
const digest=f=>BigInt('0x'+hex(hash(f))).toString()
const london=12965000, shanghai=1681338455, cancun=1710338135, prague=1746612311, osaka=1764798551
let seed=0x1559
const bytes=n=>Buffer.from(Array.from({length:n},()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed>>>24}))
const header=(num,time,limit,used,fee,i)=>[
 bytes(32),bytes(32),bytes(20),bytes(32),bytes(32),bytes(32),bytes(256),
 nat(i%2?0:127),nat(num),nat(limit),nat(used),nat(time),bytes(i%33),bytes(32),bytes(8),
 ...(fee===null?[]:[nat(fee)])]
const text=f=>f.map(b=>'0x'+hex(b)).join('\t')
const cases=[]
const add=(line,expected)=>cases.push({line,expected})
const H=(f,e={status:'ok',wire:hex(rlp(f)),hash:digest(f)})=>add('H\t'+text(f),e)
const P=(p,c,e)=>add('P\t'+text(p)+'|'+text(c),e)
const err=reason=>({status:'error',reason})
const ind=reason=>({status:'indeterminate',reason})
for(let i=0;i<256;i++){
 const first=i%8===0
 const n=first?london-1:london+i
 const time=1628166800+i*2
 const fee=first?null:[0n,1n,127n,128n,255n,256n,1000000000n,2n**255n][i%8]
 const p=header(n,time,first?15000000:30000000,first?14000000:15000000,fee,i)
 const cf=first?1000000000n:fee
 const c=header(n+1,time+1,30000000,1,cf,i+1)
 c[0]=hash(p)
 H(p);H(c)
 P(p,c,{status:'ok',fee:String(cf)})
 const changed=p.map(b=>Buffer.from(b));changed[3][0]^=1
 P(changed,c,err('parent-hash-mismatch'))
 const bad=c.slice();bad[0]=Buffer.from(c[0]);bad[0][31]^=1
 P(p,bad,err('parent-hash-mismatch'))
 const badFee=c.slice();badFee[15]=nat(cf+1n)
 P(p,badFee,err('fee-check'))
}
const sample=header(london,1628166800,30000000,15000000,100n,0)
for(const i of [0,1,2,3,4,5,6,13,14]){
 const f=sample.slice();f[i]=f[i].subarray(1);H(f,err('invalid-shape'))
}
for(const i of [7,8,9,10,11,15]){
 const f=sample.slice();f[i]=Buffer.concat([Buffer.of(0),f[i]]);H(f,err('invalid-shape'))
}
const extra=sample.slice();extra[12]=bytes(33);H(extra,err('invalid-shape'))
const later=sample.slice();later[11]=nat(osaka);H(later,ind('later-fork'))
H(sample.slice(0,15),err('wrong-fork-shape'))
H([...sample,bytes(32),bytes(32)],ind('unsupported-layout'))
H([...sample,bytes(32)],err('wrong-fork-shape'))
H(sample.slice(0,14),ind('unsupported-layout'))
// Independent modern field layouts, activation boundaries and actual parent
// linkage. Pair verdict also checks declared blob use and excess.
const modern=(num,time,i)=>{
 const f=header(num,time,30000000,15000000,100n,i)
 if(time>=shanghai)f.push(bytes(32))
 if(time>=cancun)f.push(nat([0n,1n,127n,128n,131072n,2n**64n-1n][i%6]),nat([0n,255n,256n,2n**64n-1n][i%4]),bytes(32))
 if(time>=prague)f.push(bytes(32))
 return f
}
// Test-only independent arithmetic on integer fields, not client logic.
const number=b=>b.length?BigInt('0x'+hex(b)):0n
const blobUnit=131072n
const target=t=>t>=prague?786432n:393216n
const maxUsed=t=>t>=prague?1179648n:786432n
const parentBlob=(p,i)=>p.length>=20?number(p[i]):0n
const excess=(p,t)=>{const total=parentBlob(p,17)+parentBlob(p,18);return total>target(t)?total-target(t):0n}
const setBlobFields=(p,c,pt,ct,i)=>{
 if(pt>=cancun){
   p[17]=nat(BigInt(i%(pt>=prague?10:7))*blobUnit)
   p[18]=nat([0n,blobUnit,3n*blobUnit,6n*blobUnit,2n**64n-1n][i%5])
 }
 if(ct>=cancun){
   c[17]=nat(BigInt((i+1)%(ct>=prague?10:7))*blobUnit)
   c[18]=nat(excess(p,ct))
 }
}
for(const activation of [shanghai,cancun,prague]){
 for(let i=0;i<128;i++){
  const time=activation+(i%2===0?-1:i)
  const p=modern(23000000+i,time,i)
  const c=modern(23000001+i,time+1,i+1)
  // Retain the former width-only hash vectors, then construct valid
  // blob fields for the pair tests (uint64 overflow is tested separately).
  c[0]=hash(p);H(p);H(c)
  setBlobFields(p,c,time,time+1,i)
  if(c.length>=20&&number(c[18])>=2n**64n){
   c[18]=nat(0);c[0]=hash(p)
   P(p,c,err('excess-blob-gas-mismatch'))
   p[18]=nat(3n*blobUnit);c[18]=nat(excess(p,time+1))
  }
  c[0]=hash(p)
  H(p);H(c);P(p,c,{status:'ok',fee:'100'})
  if(c.length>=20){
   const wrong=c.slice();wrong[18]=nat(number(c[18])+1n)
   if(number(wrong[18])<2n**64n)P(p,wrong,err('excess-blob-gas-mismatch'))
   for(const used of [1n,maxUsed(time+1)+blobUnit]){
    const bad=c.slice();bad[17]=nat(used);P(p,bad,err('child-blob-gas-used'))
   }
  }
  if(p.length>=20){
   for(const used of [1n,maxUsed(time)+blobUnit]){
    const bad=p.slice();bad[17]=nat(used)
    const linked=c.slice();linked[0]=hash(bad)
    P(bad,linked,err('parent-blob-gas-used'))
   }
  }
  const altered=p.map(b=>Buffer.from(b));altered[3][0]^=1
  P(altered,c,err('parent-hash-mismatch'))
  const badFee=c.slice();badFee[15]=nat(101);P(p,badFee,err('fee-check'))
  const badLink=c.map(b=>Buffer.from(b));badLink[0][0]^=1
  P(p,badLink,err('parent-hash-mismatch'))
 }
 const f=modern(23000000,activation,0)
 for(const idx of [16,19,20].filter(j=>j<f.length)){
  for(const size of [0,31,33]){
   const bad=f.slice();bad[idx]=bytes(size);H(bad,err('invalid-shape'))
  }
 }
 if(activation>=cancun){
  for(const idx of [17,18]){
   for(const val of [Buffer.of(0),Buffer.of(0,1),Buffer.alloc(9,1)]){
    const bad=f.slice();bad[idx]=val;H(bad,err('invalid-shape'))
   }
  }
 }
 const short=f.slice(0,16);H(short,err('wrong-fork-shape'))
 const early=f.slice();early[11]=nat(activation-1);H(early,err('wrong-fork-shape'))
 const lowHeight=f.slice();lowHeight[8]=nat(london-1);H(lowHeight,err('wrong-fork-shape'))
}
// Full transition grid: Cancun parent target/max must not be replaced by
// Prague's target/max, while the child excess uses the new target.
for(let used=0;used<=6;used++)for(let prior=0;prior<=12;prior++){
 const p=modern(23000000,prague-1,used), c=modern(23000001,prague,prior)
 p[17]=nat(BigInt(used)*blobUnit);p[18]=nat(BigInt(prior)*blobUnit)
 c[17]=nat(9n*blobUnit);c[18]=nat(excess(p,prague));c[0]=hash(p)
 P(p,c,{status:'ok',fee:'100'})
 const wrong=c.slice();wrong[18]=nat(number(c[18])+blobUnit)
 P(p,wrong,err('excess-blob-gas-mismatch'))
}
// Independent integer series: retain all terms and sum only at the end.
// Test oracle, never a runtime provider. The denominator is selected by the
// child fork, not the parent. Fixed anchor vectors are checked separately.
const den=t=>t>=prague?5007716n:3338477n
const blobPrice=(n,d)=>{
 const terms=[d]
 while(terms.at(-1)!==0n)terms.push(terms.at(-1)*n/(d*BigInt(terms.length)))
 return terms.reduce((s,t)=>s+t,0n)/d
}
assert.equal(blobPrice(0n,3338477n),1n)
assert.equal(blobPrice(6676954n,3338477n),7n)
assert.equal(blobPrice(10015432n,5007716n),7n)
assert.equal(blobPrice(213662528n,3338477n),6235149080797199216264525102n)
assert.equal(blobPrice(320493824n,5007716n),6235149080802028382733105041n)
const B=(p,c,e)=>add('B\t'+text(p)+'|'+text(c),e)
const bExpected=(n,d,fee=100n)=>{
 if(n>64n*d)return ind('blob-fee-resource-limit')
 const price=String(blobPrice(n,d))
 return {status:'ok',fee:String(fee),blobFee:price,stack:price,gas:'0'}
}
for(const time of [cancun+1,prague,prague+1]){
 const d=den(time)
 const ns=[0n,1n,d-1n,d,d+1n,2n*d,64n*d-1n,64n*d,64n*d+1n,2n**64n-1n]
 for(let i=0;i<256;i++)ns.push(BigInt(i)*d/4n)
 for(const n of ns){
  const p=modern(23000000,time-1,0),c=modern(23000001,time,1)
  // Parent used exactly the child target (also permitted for the last
  // Cancun block before Prague), so child excess equals parent excess.
  p[17]=nat(target(time));p[18]=nat(n)
  c[17]=nat(0);c[18]=nat(n);c[0]=hash(p)
  B(p,c,bExpected(n,d))
 }
}
{
 const p=modern(23000000,cancun-1,0),c=modern(23000001,cancun,1)
 c[17]=nat(0);c[18]=nat(0);c[0]=hash(p)
 B(p,c,bExpected(0n,den(cancun)))
 const wrong=c.slice();wrong[18]=nat(1);B(p,wrong,err('excess-blob-gas-mismatch'))
 const badLink=c.map(b=>Buffer.from(b));badLink[0][0]^=1;B(p,badLink,err('parent-hash-mismatch'))
 const badFee=c.slice();badFee[15]=nat(101);B(p,badFee,err('fee-check'))
 const badShape=c.slice();badShape[19]=Buffer.alloc(31);B(p,badShape,err('invalid-shape'))
 const old=modern(23000001,cancun-1,1),older=modern(23000000,cancun-2,0)
 old[0]=hash(older);B(older,old,ind('blob-fee-unavailable'))
}
// Sample 512 distinct whole-blob excesses across each complete admitted
// range, including its endpoints. Unlike the arithmetic stress values
// above, these excesses respect the from-zero whole-blob invariant.
for(const time of [cancun+1,prague+1]){
 const d=den(time),maxBlobs=64n*d/blobUnit
 for(let i=0;i<512;i++){
  const n=(BigInt(i)*maxBlobs/511n)*blobUnit
  const p=modern(23000000,time-1,i),c=modern(23000001,time,i+1)
  const normalFee=[0n,1n,100n,1000000000n,2n**128n,2n**255n][i%6]
  p[15]=nat(normalFee);c[15]=nat(normalFee)
  p[17]=nat(target(time));p[18]=nat(n)
  c[17]=nat(0);c[18]=nat(n);c[0]=hash(p)
  B(p,c,bExpected(n,d,normalFee))
 }
}
const last=modern(24000000,osaka-1,1);H(last)
const future=modern(24000001,osaka,1);H(future,ind('later-fork'))
future[0]=hash(last);P(last,future,ind('later-fork'));B(last,future,ind('later-fork'))
// Existing independently captured canonical Frontier header: pin its published digest.
const fixture=JSON.parse(readFileSync(new URL('../../evidence/frontier-mainnet-46147.json',import.meta.url),'utf8'))
const block=fixture.block
const raw=k=>Buffer.from(block[k].slice(2),'hex')
const actualHeader=[raw('parentHash'),raw('sha3Uncles'),raw('miner'),raw('stateRoot'),raw('transactionsRoot'),raw('receiptsRoot'),Buffer.alloc(256),
 nat(BigInt(block.difficulty)),nat(BigInt(block.number)),nat(BigInt(block.gasLimit)),nat(BigInt(block.gasUsed)),nat(BigInt(block.timestamp)),raw('extraData'),raw('mixHash'),raw('nonce')]
assert(block.zeroLogsBloom)
assert.equal('0x'+hex(hash(actualHeader)),block.hash)
H(actualHeader,{status:'ok',wire:hex(rlp(actualHeader)),hash:BigInt(block.hash).toString()})
const exe=process.argv[2]
assert(exe,'provide absolute Lean executable path')
const dir=mkdtempSync(join(tmpdir(),'header-rlp-'))
try{
 const file=join(dir,'cases.tsv');writeFileSync(file,cases.map(c=>c.line).join('\n')+'\n')
 const out=spawnSync(exe,['--dangerously-enable-unverified-keccak','--batch',file],{encoding:'utf8',maxBuffer:16*1024*1024})
 assert.equal(out.status,0,out.stderr)
 const actual=out.stdout.trim().split('\n').map(JSON.parse)
 const compare=(observed)=>{assert.equal(observed.length,cases.length);for(let i=0;i<cases.length;i++)assert.deepEqual(observed[i],cases[i].expected,'row '+i)}
 compare(actual)
 for(const mutation of [
   a=>a[0].hash='0',
   a=>a[0].wire='00',
   a=>a.pop(),
   a=>{const i=cases.findIndex(c=>c.expected.reason==='excess-blob-gas-mismatch');assert(i>=0);a[i]={status:'ok',fee:'100'}},
   a=>{const i=cases.findIndex(c=>c.expected.blobFee!==undefined);assert(i>=0);a[i].blobFee='0'},
   a=>{const i=cases.findIndex(c=>c.expected.stack!==undefined);assert(i>=0);a[i].stack='0'},
   a=>{const i=cases.findIndex(c=>c.expected.gas!==undefined);assert(i>=0);a[i].gas='2'},
   a=>{const i=cases.findIndex(c=>c.expected.reason==='blob-fee-resource-limit');assert(i>=0);a[i]={status:'error',reason:'blob-fee-resource-limit'}},
 ]){const a=structuredClone(actual);mutation(a);assert.throws(()=>compare(a))}
 const noOpt=spawnSync(exe,['--batch',file]);assert.equal(noOpt.status,2)
 writeFileSync(file,'H\t0x0g\n')
 const malformed=spawnSync(exe,['--dangerously-enable-unverified-keccak','--batch',file],{encoding:'utf8'})
 assert.equal(malformed.status,2);assert.deepEqual(JSON.parse(malformed.stdout),{status:'inputError'})
 const counts={};for(const c of cases)counts[c.expected.status]=(counts[c.expected.status]??0)+1
 console.log(JSON.stringify({cases:cases.length,matched:actual.length,counts,mutationsRejected:8,blobFeeCases:cases.filter(c=>c.line.startsWith('B\t')).length,missingOptInRejected:true,malformedRejected:true}))
}finally{rmSync(dir,{recursive:true,force:true})}
