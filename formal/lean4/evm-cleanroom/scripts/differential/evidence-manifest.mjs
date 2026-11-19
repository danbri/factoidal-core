#!/usr/bin/env node
/**
 * Reproducible comparison evidence: link corpus, generator, dependency lock,
 * CI source revision and verdict by cryptographic hash.
 *
 * The manifest does not claim Ethereum consensus conformance. It makes
 * both passing and failing synthetic differential runs auditable.
 *
 * node scripts/differential/evidence-manifest.mjs .lake/differential
 */
import { createHash } from 'node:crypto';
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { resolve, join } from 'node:path';

if (process.argv.length !== 3) throw Error('usage: evidence-manifest.mjs RESULTS_DIR');
const dir=resolve(process.argv[2]);
const lock=resolve('scripts/differential/package-lock.json');
const files={
  corpus:join(dir,'corpus.jsonl'),
  generator:join(dir,'generator.json'),
  report:join(dir,'report.json'),
  disagreements:join(dir,'failures.jsonl'),
  dependencyLock:lock,
  negativeControls:join(dir,'negative-controls','selftest-summary.json'),
};
const fileSha256=file => createHash('sha256').update(readFileSync(file)).digest('hex');
const evidence={};
for (const [label,path] of Object.entries(files)) {
  if (existsSync(path)) evidence[label]={sha256:fileSha256(path),
    bytes:readFileSync(path).length};
}
const required=['corpus','generator','report','disagreements','dependencyLock'];
const problems=[];
for (const label of required) if (!evidence[label]) problems.push('missing '+label);
let report=null;
let generator=null;
try { if (evidence.report) report=JSON.parse(readFileSync(files.report,'utf8')); }
catch(e){ problems.push('invalid report JSON: '+String(e));}
try { if (evidence.generator) generator=JSON.parse(readFileSync(files.generator,'utf8')); }
catch(e){ problems.push('invalid generator JSON: '+String(e));}
if (report&&generator&&evidence.corpus) {
  if (report.corpus?.sha256!==evidence.corpus.sha256 ||
      generator.sha256!==evidence.corpus.sha256) {
    problems.push('corpus SHA-256 inconsistency across generator/report/bytes');
  }
  if (report.corpus?.count!==generator.count ||
      report.compared!==generator.count) {
    problems.push('generated/counted/executed totals differ');
  }
  if (report.passed + report.mismatches + report.oracleErrors +
      report.unsupported !== report.compared) {
    problems.push('outcomes do not partition the input corpus');
  }
  if (Object.values(report.byCategory??{}).reduce((a,b)=>a+b,0) !== report.compared) {
    problems.push('per-category counts differ from execution denominator');
  }
  if (report.matchedExceptionalCases > report.declaredExceptionalCases) {
    problems.push('matched exceptional count exceeds declared exceptions');
  }
  if (report.corpus?.uniqueExecutionInputs < report.compared * 0.95) {
    problems.push('under 95% distinct execution inputs');
  }
  const coverage=report.referenceExecutionCoverage;
  const hist=coverage?.opcodeHistogram;
  const values=hist && typeof hist === 'object' &&
    !Array.isArray(hist) ? Object.values(hist) : [];
  if (!coverage || !Number.isSafeInteger(coverage.totalStepEvents) ||
      !Number.isSafeInteger(coverage.distinctOpcodes) ||
      values.length !== coverage.distinctOpcodes ||
      values.some(n => !Number.isSafeInteger(n) || n <= 0) ||
      values.reduce((a,b) => a + b,0) !== coverage.totalStepEvents) {
    problems.push('missing or inconsistent executed-opcode coverage');
  } else if (report.compared >= 1000 &&
      (coverage.distinctOpcodes < 20 || coverage.totalStepEvents < report.compared)) {
    problems.push('executed-opcode coverage below CI minimum');
  }
  const isPass = report.passed === report.compared &&
    report.mismatches === 0 && report.oracleErrors === 0 && report.unsupported === 0;
  if ((report.status === 'pass') !== isPass) {
    problems.push('report pass/fail status inconsistent with counts');
  }
}
let revision='unknown';
try{revision=execFileSync('git',['rev-parse','HEAD'],{encoding:'utf8'}).trim();}
catch {problems.push('failed to obtain git source revision');}
let toolchain='unknown';
try{toolchain=readFileSync('lean-toolchain','utf8').trim();}
catch{problems.push('failed to read Lean toolchain pin');}
const result={
  schemaVersion:1,
  kind:'evm-cleanroom-differential-evidence',
  status:problems.length?'invalid-evidence':'consistent',
  scope:'synthetic one-frame raw bytecode; not EELS state tests or mainnet',
  sourceRevision:revision,
  leanToolchain:toolchain,
  nodeVersion:process.version,
  platform:process.platform,
  arch:process.arch,
  claims:{
    compared:report?.compared??null,
    passed:report?.passed??null,
    mismatches:report?.mismatches??null,
    oracleErrors:report?.oracleErrors??null,
    unsupported:report?.unsupported??null,
    declaredExceptional:report?.declaredExceptionalCases??null,
    matchedExceptional:report?.matchedExceptionalCases??null
  },
  evidence,
  problems
};
writeFileSync(join(dir,'evidence-manifest.json'),JSON.stringify(result,null,2)+'\n');
process.stdout.write(JSON.stringify({
  status:result.status,sourceRevision:revision,
  corpusSha256:evidence.corpus?.sha256,
  compared:result.claims.compared,problems
})+'\n');
if (problems.length) process.exit(1);
