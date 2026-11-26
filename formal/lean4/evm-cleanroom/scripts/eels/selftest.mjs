#!/usr/bin/env node
/**
 * Verify the real EELS state-test runner FAILS CLOSED when an expected
 * official post-root or expected balance has been tampered with.
 *
 * This is a harness negative control, not an Ethereum semantic bug.
 * Usage: node scripts/eels/selftest.mjs PUBLISHED_FIXTURE_JSON OUTPUT_DIR
 */
import { readFileSync,writeFileSync,mkdirSync } from 'node:fs';
import { join,resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const [file,directory]=process.argv.slice(2);
if(!file||!directory||process.argv.length!==4)
  throw Error('usage: selftest.mjs PUBLISHED_FIXTURE_JSON OUTPUT_DIR');
const original=JSON.parse(readFileSync(file,'utf8'));
const key=Object.keys(original).find(k=>k.endsWith('type_0_protected]'));
if(!key)throw Error('published EELS fixture lacks a supported type-0 case');
const base=original[key];
const clone=()=>JSON.parse(JSON.stringify(original));
mkdirSync(directory,{recursive:true});
const runner=fileURLToPath(new URL('./run-lean-state-tests.mjs',import.meta.url));
const mutations=[
  {name:'alter-post-root',apply:fixture=>{
    const row=fixture[key].post.Prague[0];
    const old=row.hash;
    row.hash=old.slice(0,-1)+(old.at(-1)==='0'?'1':'0');
  }},
  {name:'alter-post-sender-balance',apply:fixture=>{
    const row=fixture[key].post.Prague[0];
    const sender=fixture[key].transaction.sender;
    const old=BigInt(row.state[sender].balance);
    row.state[sender].balance='0x'+(old+1n).toString(16);
  }}
];
const checks=[];
for(const mutation of mutations){
  const fixture=clone();
  mutation.apply(fixture);
  const path=resolve(directory,mutation.name+'.json');
  const report=resolve(directory,mutation.name+'.report.json');
  writeFileSync(path,JSON.stringify(fixture)+'\n');
  const proc=spawnSync(process.execPath,[runner,
    '--fixture',path,'--out',report],{
    encoding:'utf8',timeout:120000,maxBuffer:1024*1024
  });
  if(proc.status!==1||proc.error)
    throw Error('tampered fixture not rejected: '+mutation.name+
      ' exit='+proc.status+' stderr='+proc.stderr);
  const result=JSON.parse(readFileSync(report,'utf8'));
  const failed=result.cases.find(r=>r.id===key);
  if(result.status!=='fail' || result.failed!==1 || result.passed!==3 ||
     result.unsupported!==2 || result.actualLeanStateTestsExecuted!==4 ||
     !failed || failed.status!=='fail' ||
     !String(failed.reason).includes('official post-state mismatch')){
    throw Error('tampered EELS output was not correctly classified: '+
      mutation.name+' '+JSON.stringify(result).slice(0,1300));
  }
  checks.push({name:mutation.name,detected:true,
    counterexampleId:failed.id,reason:failed.reason});
}
const summary={kind:'eels-post-state-negative-controls',status:'pass',
  checked:checks.length,checks};
writeFileSync(join(directory,'selftest-summary.json'),JSON.stringify(summary,null,2)+'\n');
process.stdout.write(JSON.stringify(summary)+'\n');
