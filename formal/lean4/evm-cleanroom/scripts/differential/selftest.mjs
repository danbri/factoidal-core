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
  results.push({control:t.name,detected:true,caseId:t.base.id,
    differing:actual,report:reportPath});
}
const output={status:'pass',kind:'harness-negative-controls',
  controls:results,allDetected:true};
writeFileSync(resolve(outputDir,'selftest-summary.json'),JSON.stringify(output,null,2)+'\n');
process.stdout.write(JSON.stringify(output)+'\n');
