#!/usr/bin/env node
/**
 * Deterministic, bounded delta-debugging of a saved EVM disagreement.
 *
 * Only retain bytecode deletions that preserve the SAME disagreement
 * signature (mismatch fields, reference/Lean status and error categories).
 * The comparator remains the pinned independent EthereumJS-vs-Lean runner.
 *
 * Usage:
 *   node scripts/differential/minimize.mjs
 *     --failures saved/failures.jsonl --id synthetic-... --out /tmp/min
 *     --max-runs 64
 *
 * This is diagnostic infrastructure, not a proof or automatically accepted
 * regression. A human reviewer must validate and retain any minimized case.
 */
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';

function parseArgs(args) {
  const o={};
  for(let i=0;i<args.length;i+=2){
    if(!args[i]?.startsWith('--')||args[i+1]===undefined){
      throw Error('usage: --failures PATH --id ID --out DIR [--max-runs N]');
    }
    o[args[i].slice(2)]=args[i+1];
  }
  if(!o.failures||!o.id||!o.out) throw Error('missing failures/id/out');
  const n=o['max-runs']===undefined?64:Number(o['max-runs']);
  if(!Number.isInteger(n)||n<1||n>256) throw Error('max-runs must be 1..256');
  return {...o,maxRuns:n};
}
const options=parseArgs(process.argv.slice(2));
const originalFile=readFileSync(options.failures);
const rows=originalFile.toString('utf8').split('\n').filter(Boolean).map(JSON.parse);
const original=rows.find(r=>r.id===options.id);
if(!original||original.kind!=='mismatch'||!original.input||
   !Array.isArray(original.differing)){
  throw Error('saved semantic mismatch not found: '+options.id);
}
const signature=r=>JSON.stringify({
  differing:[...(r.differing??[])].sort(),
  expectedStatus:r.expected?.status,
  expectedError:r.expected?.error??null,
  observedStatus:r.observed?.status,
  observedError:r.observed?.error??null
});
const targetSignature=signature(original);
let best=Buffer.from(original.input.hex,'hex');
if(!best.length||best.toString('hex')!==original.input.hex) {
  throw Error('invalid original hex bytecode');
}
const out=resolve(options.out);
mkdirSync(out,{recursive:true});
const runner=fileURLToPath(new URL('./run.mjs',import.meta.url));
const casePath=join(out,'candidate.jsonl');
const reportPath=join(out,'candidate-report.json');
const failurePath=join(out,'candidate-failures.jsonl');
const inputSha256=createHash('sha256').update(best).digest('hex');
let attempts=0;
const progress=[];
function check(candidate) {
  attempts++;
  const modified={...original.input,hex:candidate.toString('hex')};
  writeFileSync(casePath,JSON.stringify(modified)+'\n');
  const p=spawnSync(process.execPath,[runner,
    '--corpus',casePath,'--out',reportPath,'--failures',failurePath
  ],{encoding:'utf8',timeout:90000,maxBuffer:1024*1024});
  if(p.error||p.status!==1) return false;
  let report, failure;
  try{
    report=JSON.parse(readFileSync(reportPath,'utf8'));
    failure=JSON.parse(readFileSync(failurePath,'utf8').trim().split('\n')[0]);
  }catch{return false;}
  return report.mismatches===1&&report.oracleErrors===0&&
    report.unsupported===0&&failure.id===original.id&&
    signature(failure)===targetSignature;
}
// Verify that the saved mismatch still exists before claiming to minimise it.
if(!check(best)){
  throw Error('original archived counterexample does not reproduce its stated signature');
}
let granularity=2;
while(best.length>1&&attempts<options.maxRuns) {
  const chunk=Math.ceil(best.length/granularity);
  let reduced=false;
  for(let offset=0;offset<best.length&&attempts<options.maxRuns;offset+=chunk){
    const candidate=Buffer.concat([
      best.subarray(0,offset),best.subarray(Math.min(best.length,offset+chunk))
    ]);
    if(candidate.length===0||candidate.length>=best.length)continue;
    if(check(candidate)){
      progress.push({fromBytes:best.length,toBytes:candidate.length,
        removedAt:offset,removedBytes:Math.min(chunk,best.length-offset)});
      best=candidate;
      granularity=Math.max(2,granularity-1);
      reduced=true;
      break;
    }
  }
  if(!reduced) {
    if(granularity>=best.length)break;
    granularity=Math.min(best.length,granularity*2);
  }
}
const minimized={...original.input,hex:best.toString('hex')};
const minimizedText=JSON.stringify(minimized)+'\n';
writeFileSync(join(out,'minimized.jsonl'),minimizedText);
const result={
  kind:'differential-bytecode-minimization',
  status:'reproduced',
  id:original.id,
  limit:options.maxRuns,
  attempts,
  originalBytes:Buffer.from(original.input.hex,'hex').length,
  minimizedBytes:best.length,
  originalBytecodeSha256:inputSha256,
  minimizedBytecodeSha256:createHash('sha256').update(best).digest('hex'),
  originalFailureFileSha256:createHash('sha256').update(originalFile).digest('hex'),
  signature:JSON.parse(targetSignature),
  originalInput:original.input,
  minimizedInput:minimized,
  reductions:progress,
  provenance:{
    oracle:'@ethereumjs/evm 10.1.3 versus Lean evm-subset',
    sameHardfork:original.input.hardfork,
    gasAndFuelUnmodified:true
  }
};
writeFileSync(join(out,'minimization.json'),JSON.stringify(result,null,2)+'\n');
process.stdout.write(JSON.stringify({
  status:result.status,id:result.id,attempts,
  originalBytes:result.originalBytes,minimizedBytes:result.minimizedBytes,
  output:join(out,'minimization.json')
})+'\n');
