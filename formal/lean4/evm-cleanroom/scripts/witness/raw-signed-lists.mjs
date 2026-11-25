import {buildTransactionLists} from './transaction-lists.mjs';
import assert from 'node:assert/strict';
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
  let txs=0;
  for(const c of cases){
    const old=run(oldBin,[flags[0],'--authenticated-transaction-list'],c.request);
    const tx=c.request.transactions.map((t,i)=>({rawHex:c.expected.txBytes[i],fuel:t.fuel}));
    assert.equal(tx.length,c.expected.txBytes.length);
    const out=run(rawBin,[...flags,'--raw-signed-list'],{...c.request,schemaVersion:3,transactions:tx});
    const {secpOptIn,...rest}=out;
    assert.deepEqual({...rest,schemaVersion:2},old,c.id);
    txs+=tx.length;
  }
  assert.equal(cases.length,36);
  assert.equal(txs,344);
  console.log(JSON.stringify({status:'pass',lists:cases.length,signedOccurrences:txs}));
} finally {rmSync(dir,{recursive:true,force:true});}
