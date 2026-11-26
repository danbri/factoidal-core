#!/usr/bin/env node
/**
 * Reproduce a saved differential counterexample by its stable corpus ID.
 *
 * Runs the *same independent comparator* on the original bytecode and inputs.
 * The output identifies whether the previously reported disagreement is
 * still observable, changed, or no longer present.
 *
 * node scripts/differential/reproduce.mjs --failures saved/failures.jsonl
 *     --id synthetic-20261119-000017 --out /tmp/reproduce-000017
 *
 * Requires installed, locked @ethereumjs/evm and a built Lean executable.
 */
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { resolve, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';

function optionsOf(args) {
  const o={};
  for(let i=0;i<args.length;i+=2){
    if(!args[i]?.startsWith('--')||args[i+1]===undefined) throw Error('usage: --failures PATH --id ID --out DIR');
    o[args[i].slice(2)]=args[i+1];
  }
  if(!o.failures||!o.id||!o.out) throw Error('usage: --failures PATH --id ID --out DIR');
  return o;
}
const flags=optionsOf(process.argv.slice(2));
const failureBytes=readFileSync(flags.failures);
const failures=failureBytes.toString('utf8').trim().split('\n')
  .filter(Boolean).map(JSON.parse);
const original=failures.find(x=>x.id===flags.id);
if(!original||original.kind!=='mismatch'||!original.input){
  throw Error('no saved mismatch with this id: '+flags.id);
}
const dir=resolve(flags.out);
mkdirSync(dir,{recursive:true});
const inputPath=join(dir,'case.jsonl');
const reportPath=join(dir,'report.json');
const failuresPath=join(dir,'failures.jsonl');
const rawInput=JSON.stringify(original.input)+'\n';
writeFileSync(inputPath,rawInput);
const proc=spawnSync(process.execPath,[
  fileURLToPath(new URL('./run.mjs',import.meta.url)),
  '--corpus',inputPath,'--out',reportPath,'--failures',failuresPath
],{encoding:'utf8',timeout:120000,maxBuffer:1024*1024});
let replay=null;
try{
  replay=JSON.parse(readFileSync(reportPath,'utf8'));
}catch{}
let repeated=null;
try{
  repeated=readFileSync(failuresPath,'utf8').split('\n').filter(Boolean).map(JSON.parse)[0];
}catch{}
const originalReasons=[...(original.differing??[])].sort();
const currentReasons=[...(repeated?.differing??[])].sort();
const sameReason=JSON.stringify(originalReasons)===JSON.stringify(currentReasons);
const reproduced=proc.status===1&&replay?.status==='mismatch'&&
  replay?.compared===1&&replay?.mismatches===1&&replay?.oracleErrors===0&&
  repeated?.id===original.id&&sameReason;
const status=reproduced?'reproduced':
  (proc.status===0&&replay?.status==='pass'?'no-longer-disagrees':
   (proc.status===1&&replay?.status==='mismatch'?'changed-disagreement':'harness-error'));
const outcome={
  kind:'differential-counterexample-reproduction',
  status,
  caseId:original.id,
  sourceFailureFileSha256:createHash('sha256').update(failureBytes).digest('hex'),
  inputSha256:createHash('sha256').update(rawInput).digest('hex'),
  originalReasons,currentReasons,
  processExit:proc.status,
  original:{expected:original.expected,observed:original.observed},
  current:{expected:repeated?.expected,observed:repeated?.observed},
  replayReport:reportPath
};
writeFileSync(join(dir,'reproduction.json'),JSON.stringify(outcome,null,2)+'\n');
process.stdout.write(JSON.stringify({
  status,caseId:original.id,originalReasons,currentReasons,
  output:join(dir,'reproduction.json')
})+'\n');
if(!reproduced) process.exit(1);
