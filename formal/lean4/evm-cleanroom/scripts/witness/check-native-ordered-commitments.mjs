/** Independent test only. No reference-client answers enter the Lean runner. */
import assert from 'node:assert/strict';
import {buildTransactionLists} from './transaction-lists.mjs';
import {bytes, hex, nat, fixed, keccak, RLP, MerklePatriciaTrie, checkSources} from './oracle.mjs';
import {spawnSync} from 'node:child_process';
import {writeFileSync,mkdtempSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
const binary=process.argv[2];
assert(binary);
const directory=mkdtempSync(join(tmpdir(),'ordered-commitment-'));
const path=join(directory,'request.json');
const flags=['--dangerously-enable-unverified-keccak','--dangerously-enable-unverified-secp256k1'];
const run=(mode,value)=>{
  writeFileSync(path,JSON.stringify(value));
  const p=spawnSync(binary,[...flags,mode,path],{encoding:'utf8',timeout:240000,maxBuffer:33554432});
  assert.equal(p.status,0,p.stderr||p.stdout||String(p.error));
  return JSON.parse(p.stdout);
};
const normalized=value=>hex(bytes(value));
// Independent integer bitset formulation, rather than the Lean byte-array fold.
function referenceBloom(receipts) {
  let bloom=0n;
  for (const receipt of receipts) for (const log of receipt.logs) {
    for (const value of [fixed(log.address,20), ...log.topics.map(t=>fixed(t,32))]) {
      const hash=keccak(value);
      for(let offset=0;offset<6;offset+=2)
        bloom |= 1n << BigInt(((hash[offset]<<8)|hash[offset+1])&2047);
    }
  }
  return hex(fixed(bloom,256));
}
let checked=0, refused=0, occurrences=0, rootMutations=0, rootCases=0;
let zeroBlooms=0, nonzeroBlooms=0, bloomMutations=0;
try {
  checkSources();
  const cases=await buildTransactionLists();
  assert.equal(cases.length,36);
  let selected, zeroSelected, nonzeroSelected;
  for(const c of cases){
    const transactions=c.request.transactions.map((t,i)=>({rawHex:c.expected.txBytes[i],fuel:t.fuel}));
    const request={...c.request,schemaVersion:3,transactions,childHeader:[...c.request.childHeader]};
    assert.equal(transactions.length,c.expected.txBytes.length);
    if(c.category==='execution'){
      request.childHeader[4]=normalized(c.expected.transactionRoot);
      request.childHeader[5]=normalized(c.expected.receiptsRoot);
      request.childHeader[6]=referenceBloom(c.expected.receipts);
      if (/^0+$/.test(request.childHeader[6])) { zeroBlooms++; zeroSelected ??= request; }
      else { nonzeroBlooms++; nonzeroSelected ??= request; }
      const result=run('--checked',request);
      assert.equal(result.status,'commitment-checked',c.id);
      assert.equal(normalized(result.transactionRoot),request.childHeader[4],c.id);
      assert.equal(normalized(result.receiptsRoot),request.childHeader[5],c.id);
      assert.equal(normalized(result.logsBloom),request.childHeader[6],c.id);
      assert.equal(result.receipts,transactions.length,c.id);
      checked++; occurrences+=transactions.length;
      if(transactions.length && !selected) selected=request;
    } else {
      const result=run('--checked',request);
      assert.equal(result.status,c.expected.status,c.id);
      assert.equal(result.index,c.expected.index,c.id);
      assert.equal(result.reason,c.expected.reason,c.id);
      refused++;
    }
  }
  assert(selected);
  for(const index of [4,5]){
    const request=structuredClone(selected);
    const old=request.childHeader[index];
    request.childHeader[index]=(old[0]==='0'?'1':'0')+old.slice(1);
    const result=run('--checked',request);
    assert.equal(result.status,'commitment-refused');
    assert.match(result.reason,index===4?/transactionRootMismatch/:/receiptRootMismatch/);
    rootMutations++;
  }
  assert(zeroSelected && nonzeroSelected);
  for(const original of [zeroSelected, nonzeroSelected]){
    const request=structuredClone(original);
    const old=request.childHeader[6];
    request.childHeader[6]=(old[0]==='0'?'1':'0')+old.slice(1);
    const result=run('--checked',request);
    assert.equal(result.status,'commitment-refused');
    assert.match(result.reason,/logsBloomMismatch/);
    bloomMutations++;
  }
  // Exercise the RLP index boundary (127->128), short/long node cutoff and
  // mixed value sizes with an independently built non-secure trie.
  for(const n of [0,1,2,15,16,17,127,128,129,255,256]){
    const values=Array.from({length:n},(_,i)=>hex(Uint8Array.from({length:1+i%65},(_,j)=>(i*19+j*7)%256)));
    const trie=new MerklePatriciaTrie({useKeyHashing:false});
    for(const [i,v] of values.entries()) await trie.put(RLP.encode(nat(i)),bytes(v));
    const result=run('--root',values);
    assert.equal(result.status,'root');
    assert.equal(normalized(result.root),hex(trie.root()));
    rootCases++;
  }
  assert.equal(run('--root',['']).status,'commitment-refused');
  assert.equal(run('--root',Array(257).fill('01')).status,'commitment-refused');
  assert.deepEqual({checked,refused,occurrences,rootMutations,rootCases},
    {checked:30,refused:6,occurrences:327,rootMutations:2,rootCases:11});
  assert.deepEqual({zeroBlooms,nonzeroBlooms,bloomMutations},{zeroBlooms:20,nonzeroBlooms:10,bloomMutations:2});
  console.log(JSON.stringify({checked,refused,occurrences,rootMutations,rootCases,resourceOrShapeControls:2,zeroBlooms,nonzeroBlooms,bloomMutations}));
} finally { rmSync(directory,{recursive:true,force:true}); }
