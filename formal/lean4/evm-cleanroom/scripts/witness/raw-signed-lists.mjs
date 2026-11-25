import {buildTransactionLists} from './transaction-lists.mjs';
import assert from 'node:assert/strict';
import {RLP,bytes,hex,nat,bytesToBigInt,checkSources} from './oracle.mjs';
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
  assert.equal(inspections,344);
  console.log(JSON.stringify({status:'pass',lists:cases.length,signedOccurrences:txs,inspections,negativeControls:bad.length+2,publishedVectors:1}));
} finally {rmSync(dir,{recursive:true,force:true});}
