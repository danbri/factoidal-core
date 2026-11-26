#!/usr/bin/env node
/**
 * The differential harness must demonstrably DETECT false fixture labels.
 *
 * Negative controls deliberately corrupt a known failure label and a
 * known success label, run the exact production comparator, and demand
 * non-zero exit + machine-readable mismatches. These are NOT EVM bugs.
 *
 * node scripts/differential/selftest.mjs CORPUS_JSONL OUTPUT_DIRECTORY
 */
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const [corpusPath, outputDir] = process.argv.slice(2);
if (!corpusPath || !outputDir || process.argv.length !== 4) {
  throw Error('usage: node scripts/differential/selftest.mjs CORPUS_JSONL OUTPUT_DIRECTORY');
}
mkdirSync(outputDir, {recursive: true});
const source=readFileSync(corpusPath, 'utf8').split('\n').filter(Boolean).map(JSON.parse);
const runner=fileURLToPath(new URL('./run.mjs', import.meta.url));
const tests=[
  {
    name:'wrong-expected-error',
    base:source.find(x => x.expectedDisposition==='error'),
    mutate:x => ({...x,expectedError:x.expectedError==='outOfGas'?'invalidOpcode':'outOfGas'}),
    required:['reference-disagrees-with-declared-error','lean-disagrees-with-declared-error']
  },
  {
    name:'wrong-expected-success',
    base:source.find(x => x.expectedDisposition==='ok'),
    mutate:x => ({...x,expectedDisposition:'error',expectedError:'invalidOpcode'}),
    required:['reference-disagrees-with-declared-error','lean-disagrees-with-declared-error']
  }
];
const results=[];
for (const t of tests) {
  if (!t.base) throw Error('corpus lacks ' + t.name + ' control example');
  const inputPath=resolve(outputDir,t.name+'.jsonl');
  const reportPath=resolve(outputDir,t.name+'.report.json');
  const failurePath=resolve(outputDir,t.name+'.failures.jsonl');
  writeFileSync(inputPath,JSON.stringify(t.mutate(t.base))+'\n');
  const proc=spawnSync(process.execPath,[runner,
    '--corpus',inputPath,'--out',reportPath,'--failures',failurePath
  ], {encoding:'utf8',timeout:120000,maxBuffer:1024*1024});
  if (proc.status!==1 || proc.error) {
    throw Error('negative control was not rejected: '+t.name+
      ' exit='+proc.status+' stderr='+proc.stderr+' error='+proc.error);
  }
  const report=JSON.parse(readFileSync(reportPath,'utf8'));
  const failures=readFileSync(failurePath,'utf8').trim().split('\n').map(JSON.parse);
  const actual=failures[0]?.differing ?? [];
  if (report.status!=='mismatch' || report.compared!==1 ||
      report.passed!==0 || report.mismatches!==1 ||
      report.oracleErrors!==0 || failures.length!==1 ||
      !t.required.every(reason => actual.includes(reason))) {
    throw Error('negative control did not produce expected counterexample: '+
      t.name+' report='+JSON.stringify(report).slice(0,2000));
  }
  // Independently replay the archived JSONL mismatch and require that the
  // same reason is reproduced. A saved failure is not useful unless it can be
  // turned back into a one-case regression deterministically.
  const reproduce=fileURLToPath(new URL('./reproduce.mjs',import.meta.url));
  const replayDir=resolve(outputDir,t.name+'-replay');
  const replay=spawnSync(process.execPath,[reproduce,
    '--failures',failurePath,'--id',failures[0].id,'--out',replayDir
  ], {encoding:'utf8',timeout:120000,maxBuffer:1024*1024});
  if(replay.status!==0||replay.error){
    throw Error('single-case counterexample reproduction failed: '+t.name+
      ' exit='+replay.status+' stderr='+replay.stderr);
  }
  const reproduced=JSON.parse(readFileSync(resolve(replayDir,'reproduction.json'),'utf8'));
  if(reproduced.status!=='reproduced'||reproduced.caseId!==failures[0].id){
    throw Error('replayed counterexample no longer matches its archive: '+t.name);
  }
  let minimized=false;
  if(t.name==='wrong-expected-error'){
    const minimizer=fileURLToPath(new URL('./minimize.mjs',import.meta.url));
    const minimizedDir=resolve(outputDir,t.name+'-minimized');
    const minProc=spawnSync(process.execPath,[minimizer,
      '--failures',failurePath,'--id',failures[0].id,
      '--out',minimizedDir,'--max-runs','12'
    ],{encoding:'utf8',timeout:180000,maxBuffer:1024*1024});
    if(minProc.status!==0||minProc.error){
      throw Error('bounded minimizer failed: '+minProc.stderr+
        ' exit='+minProc.status+' error='+minProc.error);
    }
    const data=JSON.parse(readFileSync(resolve(minimizedDir,'minimization.json'),'utf8'));
    if(data.status!=='reproduced'||data.id!==failures[0].id||
       data.attempts>12||data.minimizedBytes>data.originalBytes||
       data.signature.differing.length!==actual.length){
      throw Error('minimizer changed the mismatch signature or exceeded the bound');
    }
    minimized=true;
  }
  results.push({control:t.name,detected:true,reproduced:true,minimized,
    caseId:t.base.id,differing:actual,report:reportPath});
}
// Third negative control: valid, successful EVM execution whose allocated
// memory exceeds our 4 KiB observation window. Both engines may agree on
// their visible prefix, but we MUST refuse a full-conformance pass.
const largeMemory={
  schemaVersion:1,id:'harness-memory-truncation',
  kind:'synthetic-bytecode',category:'selftest-memory-truncation',
  hardfork:'prague',hex:'6110005100',gas:'1000',fuel:'6',
  expectedDisposition:'ok'
};
const truncInput=resolve(outputDir,'truncated-memory.jsonl');
const truncReport=resolve(outputDir,'truncated-memory.report.json');
const truncFailures=resolve(outputDir,'truncated-memory.failures.jsonl');
writeFileSync(truncInput,JSON.stringify(largeMemory)+'\n');
const truncProc=spawnSync(process.execPath,[runner,
  '--corpus',truncInput,'--out',truncReport,'--failures',truncFailures
],{encoding:'utf8',timeout:120000,maxBuffer:1024*1024});
if(truncProc.status!==1||truncProc.error){
  throw Error('truncated-memory control not rejected: exit='+truncProc.status+
    ' stderr='+truncProc.stderr);
}
const trunc=JSON.parse(readFileSync(truncReport,'utf8'));
const truncCases=readFileSync(truncFailures,'utf8').trim().split('\n').map(JSON.parse);
if(trunc.status!=='incomplete'||trunc.compared!==1||trunc.passed!==0||
   trunc.mismatches!==0||trunc.oracleErrors!==0||trunc.unsupported!==1||
   truncCases.length!==1||truncCases[0]?.kind!=='unsupported'||
   truncCases[0]?.reason!=='memory-snapshot-truncated'){
  throw Error('truncated memory not classified as unsupported: '+JSON.stringify(trunc).slice(0,900));
}
results.push({control:'truncated-memory-is-unsupported',detected:true,
  caseId:largeMemory.id,classification:'unsupported',report:truncReport});

const output={status:'pass',kind:'harness-negative-controls',
  controls:results,allDetected:true};
writeFileSync(resolve(outputDir,'selftest-summary.json'),JSON.stringify(output,null,2)+'\n');
process.stdout.write(JSON.stringify(output)+'\n');
