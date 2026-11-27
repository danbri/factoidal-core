import {buildTransactionLists} from './transaction-lists.mjs';
import assert from 'node:assert/strict';
import {RLP,bytes,hex,nat,bytesToBigInt,checkSources,fixed,keccak,ecrecover,publicToAddress,clone,buildStateWitness,checkStateWitness} from './oracle.mjs';
import {spawnSync} from 'node:child_process';
import {writeFileSync,mkdtempSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
const [rawBin,oldBin]=process.argv.slice(2);
assert(rawBin && oldBin);
const dir=mkdtempSync(join(tmpdir(),'signed-lists-'));
const path=join(dir,'input.json');
const flags=['--dangerously-enable-unverified-keccak','--dangerously-enable-unverified-secp256k1'];
function run(bin,args,input){
  writeFileSync(path,JSON.stringify(input));
  const p=spawnSync(bin,[...args,path],{encoding:'utf8',timeout:240000,maxBuffer:33554432});
  assert.equal(p.status,0,p.stderr||p.stdout||String(p.error));
  return JSON.parse(p.stdout);
}
try {
  const cases=await buildTransactionLists();
  checkSources();
  let txs=0, inspections=0;
  function signing(rawHex){
    const raw=bytes(rawHex), typed=raw[0]<128, kind=typed?raw[0]:0;
    const fields=RLP.decode(typed?raw.slice(1):raw), last=fields.length-3;
    const v=bytesToBigInt(fields[last]);
    const unsigned=kind===0&&v>=35n?[...fields.slice(0,6),nat((v-35n)/2n),bytes(''),bytes('')]:fields.slice(0,last);
    const body=RLP.encode(unsigned);
    return hex(typed?Uint8Array.from([kind,...body]):body);
  }
  for(const c of cases){
    const old=run(oldBin,[flags[0],'--authenticated-transaction-list'],c.request);
    const tx=c.request.transactions.map((t,i)=>({rawHex:c.expected.txBytes[i],fuel:t.fuel}));
    assert.equal(tx.length,c.expected.txBytes.length);
    const out=run(rawBin,[...flags,'--raw-signed-list'],{...c.request,schemaVersion:3,transactions:tx});
    const {secpOptIn,...rest}=out;
    assert.deepEqual({...rest,schemaVersion:2},old,c.id);
    if(tx.length){
      const inspected=run(rawBin,[...flags,'--inspect-raw-signed'],tx.map(t=>t.rawHex));
      assert.equal(inspected.status,'inspected');
      assert.equal(inspected.rows.length,tx.length);
      for(let i=0;i<tx.length;i++){
        const entry=c.request.transactions[i], {type,...decoded}=entry.transaction;
        assert.deepEqual(inspected.rows[i],{status:'recovered',kind:type,...decoded,
          signingHex:signing(tx[i].rawHex),
          blobVersionedHashes:entry.blobVersionedHashes??null,maxFeePerBlobGas:entry.maxFeePerBlobGas??null},c.id+' decoded '+i);
        inspections++;
      }
    }
    txs+=tx.length;
  }
  assert.equal(cases.length,36);
  assert.equal(txs,344);
  const valid=cases.flatMap(c=>c.expected.txBytes).find(h=>bytes(h)[0]===2);
  assert(valid);
  const fields=RLP.decode(bytes(valid).slice(1));
  const mutate=(i,value)=>{const f=fields.slice();f[i]=value;return '02'+hex(RLP.encode(f));};
  const n=0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n;
  const bad=[mutate(10,nat(0)),mutate(11,nat(0)),mutate(11,nat(n-bytesToBigInt(fields[11]))),mutate(9,nat(2)),mutate(1,bytes('00')),'04c0','80'];
  const result=run(rawBin,[...flags,'--inspect-raw-signed'],bad);
  assert.deepEqual(result.rows.map(r=>r.status),['invalid-signature','invalid-signature','invalid-signature','invalid-signature','malformed','unsupported','malformed']);
  // Published EIP-155 example; no private key or signing operation needed.
  const eip155='f86c098504a817c800825208943535353535353535353535353535353535353535880de0b6b3a76400008025a028ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276a067cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83';
  const sample=run(rawBin,[...flags,'--inspect-raw-signed'],[eip155]).rows[0];
  assert.equal(sample.status,'recovered');
  assert.equal(sample.signingHex,'ec098504a817c800825208943535353535353535353535353535353535353535880de0b6b3a764000080018080');
  assert.equal(sample.sender,BigInt('0x9d8a62f656a8d1615c1294fd71e9cfb3e4855a4f').toString());
  const source=cases.find(c=>c.request.transactions.length);
  const rawRequest={...source.request,schemaVersion:3,transactions:source.request.transactions.map((t,i)=>({rawHex:source.expected.txBytes[i],fuel:t.fuel}))};
  function refusal(args,input){
    writeFileSync(path,JSON.stringify(input));
    const p=spawnSync(rawBin,[...args,path],{encoding:'utf8',timeout:240000});
    assert.equal(p.status,2);
    assert.equal(JSON.parse(p.stdout).status,'inputError');
  }
  refusal([flags[0],'--raw-signed-list'],rawRequest);
  refusal([...flags,'--raw-signed-list'],{...rawRequest,transactions:[{...rawRequest.transactions[0],sender:'0'}]});

  // Mutate public fixture envelopes and independently recover the resulting
  // senders. No signing key, wallet, or network is used.
  const template=cases.find(c=>c.id==='single-blobhash').request;
  const retained=cases.flatMap(c=>c.expected.txBytes);
  let creationComparisons=0, creationControls=0;
  for(const spec of [{kind:0},{kind:1},{kind:2},{kind:2,revert:true},{kind:2,zero:true}]){
    const kind=spec.kind;
    const original=bytes(retained.find(h=>kind===0?bytes(h)[0]>=192:bytes(h)[0]===kind));
    const fs=RLP.decode(kind===0?original:original.slice(1));
    const gi=kind===0?2:kind===1?3:4;
    fs[kind===0?0:1]=nat(0);
    fs[gi-1]=nat(3);
    if(kind===2)fs[2]=nat(1);
    fs[gi]=nat(100000);
    fs[gi+1]=spec.zero?fixed(0,20):bytes('');
    fs[gi+2]=nat(0);
    fs[gi+3]=bytes(spec.revert?'5f5ffd':'');
    if(kind>0)fs[gi+4]=[];
    const v=bytesToBigInt(fs.at(-3));
    const chain=kind===0?(v>=35n?(v-35n)/2n:null):bytesToBigInt(fs[0]);
    const recovery=kind===0?(chain===null?v:v-chain*2n-8n):v+27n;
    const body=RLP.encode(fs);
    const rawHex=hex(kind===0?body:Uint8Array.from([kind,...body]));
    const sender=bytesToBigInt(publicToAddress(ecrecover(keccak(bytes(signing(rawHex))),recovery,
      fixed(bytesToBigInt(fs.at(-2)),32),fixed(bytesToBigInt(fs.at(-1)),32))));
    const created=bytesToBigInt(keccak(RLP.encode([fixed(sender,20),nat(0)])).slice(12));
    const target=spec.zero?0n:created;
    assert.notEqual(sender,target);
    assert.notEqual(sender,196n);
    assert.notEqual(target,196n);
    const record=(address,exists,balance,nonce)=>({address:String(address),exists,balance:String(balance),nonce:String(nonce),codeHex:'',storage:[]});
    const initial=[record(sender,true,1000000000000000n,0),record(196,true,11,1),record(target,false,0,0)];
    const witnesses=await buildStateWitness(initial);
    await checkStateWitness(witnesses,initial);
    const request=clone(template);
    request.accounts=witnesses.accounts;
    request.parentHeader[3]=witnesses.stateRoot;
    request.childHeader[0]=hex(keccak(RLP.encode(request.parentHeader.map(bytes))));
    const gas=spec.zero?21000:spec.revert?53054:53000;
    request.childHeader[10]=hex(nat(gas));
    request.childHeader[17]=hex(nat(0));
    request.transactions=[{fuel:'1000',transaction:{type:kind,chainId:chain===null?null:String(chain),
      sender:String(sender),to:spec.zero?'0':null,nonce:'0',value:'0',gasLimit:'100000',gasPriceCap:'3',
      priorityFeeCap:kind===2?'1':'0',dataHex:hex(fs[gi+3]),accessList:[]}}];
    const rawReq={...request,schemaVersion:3,transactions:[{rawHex,fuel:'1000'}]};
    const old=run(oldBin,[flags[0],'--authenticated-transaction-list'],request);
    const out=run(rawBin,[...flags,'--raw-signed-list'],rawReq);
    const {secpOptIn,...rest}=out;
    assert.deepEqual({...rest,schemaVersion:2},old);
    assert.equal(out.status,'executed');
    assert.equal(out.gasUsed,String(gas));
    const receipt=out.receipts[0];
    assert.equal(receipt.receiptStatus,spec.revert?0:1);
    const createdExpected=spec.revert||spec.zero?undefined:String(created);
    assert.equal(receipt.createdAddress,createdExpected);
    const after=out.accounts.find(a=>a.address===String(target));
    assert.equal(after.exists,!spec.revert&&!spec.zero);
    assert.equal(after.nonce,spec.revert||spec.zero?'0':'1');
    assert.equal(out.accounts.find(a=>a.address===String(sender)).nonce,'1');
    const inspection=run(rawBin,[...flags,'--inspect-raw-signed'],[rawHex]).rows[0];
    assert.equal(inspection.sender,String(sender));
    assert.equal(inspection.to,spec.zero?'0':null);
    creationComparisons++;
    if(kind===2&&!spec.revert&&!spec.zero){
      const missing=run(rawBin,[...flags,'--raw-signed-list'],{...rawReq,accounts:rawReq.accounts.filter(a=>a.address!==String(target))});
      assert.equal(missing.status,'indeterminate');
      assert.equal(missing.index,0);
      assert(!('receipts' in missing)&&!('accounts' in missing));
      creationControls++;
      const wrong={...receipt,createdAddress:'0'};
      assert.throws(()=>assert.equal(wrong.createdAddress,createdExpected));
      creationControls++;
    }
  }
  const blob=bytes(retained.find(h=>bytes(h)[0]===3));
  const blobFields=RLP.decode(blob.slice(1));
  blobFields[5]=bytes('');
  const blobCreation=hex(Uint8Array.from([3,...RLP.encode(blobFields)]));
  const blobResult=run(rawBin,[...flags,'--inspect-raw-signed'],[blobCreation]).rows[0];
  assert.deepEqual(blobResult,{status:'malformed',reason:'blob-creation'});
  creationControls++;
  assert.equal(creationComparisons,5);
  assert.equal(creationControls,3);
  assert.equal(inspections,344);
  console.log(JSON.stringify({status:'pass',lists:cases.length,signedOccurrences:txs,inspections,negativeControls:bad.length+2,publishedVectors:1,creationComparisons,creationControls}));
} finally {rmSync(dir,{recursive:true,force:true});}
