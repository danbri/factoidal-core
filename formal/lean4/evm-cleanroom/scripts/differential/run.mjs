#!/usr/bin/env node
/**
 * Differential execution: one batched run of the REAL Lean EVM binary
 * versus the independently maintained @ethereumjs/evm 10.1.3, Prague rules.
 *
 * No opcode implementation is duplicated here. This is a narrow raw-bytecode
 * comparison, NOT transaction/mainnet replay or an EELS conformance proof.
 *
 * Working directory: formal/lean4/evm-cleanroom
 * node scripts/differential/run.mjs --corpus /tmp/cases.jsonl --out /tmp/report.json --failures /tmp/failures.jsonl
 */
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { spawnSync } from 'node:child_process';
import { createEVM } from '@ethereumjs/evm';
import { Common, Hardfork, Mainnet } from '@ethereumjs/common';

function args(argv) {
  const flags = {};
  for (let i = 0; i < argv.length; i += 2) {
    if (!argv[i]?.startsWith('--') || argv[i + 1] === undefined) {
      throw Error('expected --corpus PATH --out PATH --failures PATH [--lean-exe PATH]');
    }
    flags[argv[i].slice(2)] = argv[i + 1];
  }
  if (!flags.corpus || !flags.out || !flags.failures) throw Error('missing corpus/out/failures');
  return flags;
}
const options = args(process.argv.slice(2));
const corpusContent = readFileSync(options.corpus, 'utf8');
const corpusSha256 = createHash('sha256').update(corpusContent).digest('hex');
const cases = corpusContent.split('\n').filter(s => s.length).map((s, i) => {
  const x = JSON.parse(s);
  if (x.schemaVersion !== 1 || x.kind !== 'synthetic-bytecode' ||
      x.hardfork !== 'prague' || typeof x.id !== 'string' ||
      !/^(?:[0-9a-f]{2})+$/.test(x.hex) ||
      !/^\d+$/.test(x.gas) || !/^\d+$/.test(x.fuel) ||
      !['ok','error'].includes(x.expectedDisposition) ||
      (x.expectedDisposition === 'error' && typeof x.expectedError !== 'string')) {
    throw Error('malformed or unsupported synthetic corpus record at line ' + (i + 1));
  }
  return x;
});
if (cases.length === 0 || cases.length > 100000) throw Error('bad case count');
const seen = new Set();
for (const x of cases) {
  if (seen.has(x.id)) throw Error('duplicate corpus id: ' + x.id);
  seen.add(x.id);
}
const distinctInputs = new Set(cases.map(x => [x.hardfork, x.hex, x.gas, x.fuel].join(':'))).size;
const duplicateInputCount = cases.length - distinctInputs;
if (distinctInputs / cases.length < 0.95) {
  throw Error('corpus repeats over 5% of exact execution inputs; refuse inflated pass counts');
}
const batchInput = cases.map(x => [x.hex, x.gas, x.fuel].join('\t')).join('\n') + '\n';
const batchPath = options.out + '.lean-input.tsv';
mkdirSync(dirname(options.out), {recursive:true});
mkdirSync(dirname(options.failures), {recursive:true});
writeFileSync(batchPath, batchInput);
const [leanExecutable, ...leanPrefix] = options['lean-exe']
  ? [options['lean-exe']] : ['lake', 'exe', 'evm-subset'];
const leanCommand = [...leanPrefix, '--batch'];
const leanProc = spawnSync(leanExecutable, [...leanCommand, batchPath], {
  encoding:'utf8', maxBuffer:128 * 1024 * 1024, timeout:600000
});
if (leanProc.error || leanProc.status !== 0) {
  const errorReport = {
    kind:'differential-oracle-failure',status:'harness-error',corpusSha256,
    leanProcessExit:leanProc.status,stderr:leanProc.stderr?.slice(-8000) ?? '',
    processError:String(leanProc.error ?? '')
  };
  writeFileSync(options.out, JSON.stringify(errorReport,null,2) + '\n');
  throw Error('Lean batch execution failed; see ' + options.out);
}
const leanLines = leanProc.stdout.trimEnd().split('\n');
if (leanLines.length !== cases.length) {
  throw Error('Lean emitted ' + leanLines.length + ' results for ' + cases.length + ' cases');
}
const leanResults = leanLines.map((s,i) => {
  try { return JSON.parse(s); }
  catch { throw Error('non-JSON Lean result for case ' + cases[i].id + ': ' + s.slice(0,100)); }
});
const common = new Common({chain:Mainnet,hardfork:Hardfork.Prague});
const evm = await createEVM({common});
// Dynamic opcode execution coverage from the INDEPENDENT reference engine.
// These counts are not a Lean execution trace and don't prove correctness.
const referenceOpcodeHistogram = Object.create(null);
let referenceStepEvents = 0;
evm.events.on('step', (data, resolve) => {
  const opcode = data?.opcode?.code;
  if (Number.isInteger(opcode) && opcode >= 0 && opcode <= 255) {
    const hex = '0x' + opcode.toString(16).padStart(2, '0');
    referenceOpcodeHistogram[hex] = (referenceOpcodeHistogram[hex] ?? 0) + 1;
    referenceStepEvents++;
  }
  resolve?.();
});
const tested = {};
const failures = [];
let passes = 0, errors = 0, unsupported = 0;
const fields = ['status','gasRemaining','pc','halted','stack','memorySizeBytes','memoryWord0','memoryObservedBytes','memoryTruncated','memoryHex'];
const normalizeError = error => {
  const s=String(error).toLowerCase();
  if (s.includes('out of gas')) return 'outOfGas';
  if (s.includes('stack underflow')) return 'stackUnderflow';
  if (s.includes('stack overflow')) return 'stackOverflow';
  if (s.includes('invalid jump')) return 'invalidJump';
  if (s.includes('invalid opcode')) return 'invalidOpcode';
  return 'unclassified:' + String(error).slice(0,100);
};
let expectedExceptional = 0;
let matchedExceptional = 0;
for (let i = 0; i < cases.length; ++i) {
  const item = cases[i];
  tested[item.category] = (tested[item.category] ?? 0) + 1;
  let expected;
  try {
    const gasLimit=BigInt(item.gas);
    const result=await evm.runCode({
      code: Uint8Array.from(Buffer.from(item.hex,'hex')),
      gasLimit
    });
    const rs=result.runState;
    if (result.exceptionError) {
      expected={status:'error',error:normalizeError(result.exceptionError.error ?? result.exceptionError)};
    } else if (!rs) {
      throw Error('EthereumJS runCode did not expose runState');
    } else {
      // Stack.getStack() returns bottom-to-top; Lean outputs top-to-bottom.
      const stack=rs.stack.getStack().slice().reverse().map(v=>v.toString());
      const words=BigInt(rs.memoryWordCount);
      const word0=words===0n ? 0n :
        BigInt('0x' + Buffer.from(rs.memory.read(0,32)).toString('hex'));
      const allocatedBytes=32n * words;
      const cap=4096n;
      const observedBytes=allocatedBytes < cap ? allocatedBytes : cap;
      const snapshotHex=observedBytes===0n ? '' :
        Buffer.from(rs.memory.read(0, Number(observedBytes))).toString('hex');
      expected={
        status:'ok',
        gasRemaining:(gasLimit-BigInt(result.executionGasUsed)).toString(),
        pc:BigInt(rs.programCounter).toString(),
        halted:true,
        stack,
        memorySizeBytes:allocatedBytes.toString(),
        memoryWord0:word0.toString(),
        memoryObservedBytes:observedBytes.toString(),
        memoryTruncated:allocatedBytes > cap,
        memoryHex:snapshotHex
      };
    }
  } catch(e) {
    errors++;
    failures.push({id:item.id,category:item.category,input:item,kind:'oracle-error',detail:String(e)});
    continue;
  }
  const observed=leanResults[i];
  const comparisonFields=expected.status === 'ok' ? fields : ['status','error'];
  const differing=comparisonFields.filter(field => JSON.stringify(expected[field]) !== JSON.stringify(observed[field]));
  // Snapshot truncation is a *coverage limit*, not a semantic disagreement.
  // Count it as unsupported and retain the input as evidence. Never count it
  // as passed, and keep the CI gate non-green until coverage is expanded.
  if (expected.status==='ok' && observed.status==='ok' &&
      item.expectedDisposition==='ok' &&
      (expected.memoryTruncated || observed.memoryTruncated)) {
    unsupported++;
    failures.push({id:item.id,category:item.category,kind:'unsupported',
      reason:'memory-snapshot-truncated',input:item,expected,observed});
    continue;
  }
  // Deliberate EVM exceptions are legitimate test expectations, but they
  // count only if BOTH independent engines agree with the declared category.
  if (item.expectedDisposition === 'error') {
    expectedExceptional++;
    if (expected.status !== 'error' || expected.error !== item.expectedError) {
      differing.push('reference-disagrees-with-declared-error');
    }
    if (observed.status !== 'error' || observed.error !== item.expectedError) {
      differing.push('lean-disagrees-with-declared-error');
    }
  } else if (expected.status !== 'ok') {
    differing.push('unexpected-reference-exception');
  }
  if (differing.length === 0) {
    passes++;
    if (item.expectedDisposition === 'error') matchedExceptional++;
  } else {
    failures.push({id:item.id,category:item.category,kind:'mismatch',input:item,expected,observed,differing});
  }
}
writeFileSync(options.failures, failures.map(x=>JSON.stringify(x)).join('\n')+(failures.length?'\n':''));
const semanticDisagreements=failures.filter(x=>x.kind==='mismatch').length;
const report={
  kind:'synthetic-raw-bytecode-differential',
  status:errors?'harness-error':
    (semanticDisagreements?'mismatch':(unsupported?'incomplete':'pass')),
  scope:'restricted opcode subset; NOT state-test or mainnet replay',
  oracle:{name:'@ethereumjs/evm',version:'10.1.3',hardfork:'Prague'},
  lean:{command:[leanExecutable, ...leanCommand].join(' ')},
  corpus:{sha256:corpusSha256,count:cases.length,uniqueExecutionInputs:distinctInputs,
    duplicatedExecutionInputs:duplicateInputCount,kind:'synthetic-bytecode'},
  compared:cases.length,
  passed:passes,
  mismatches:semanticDisagreements,
  oracleErrors:errors,
  unsupported,
  declaredExceptionalCases:expectedExceptional,
  matchedExceptionalCases:matchedExceptional,
  exceptionalComparisonScope:'error category only; no gas burn, rollback or failure-state equivalence',
  byCategory:tested,
  referenceExecutionCoverage:{
    source:'@ethereumjs/evm step events; reference-only',
    totalStepEvents:referenceStepEvents,
    distinctOpcodes:Object.keys(referenceOpcodeHistogram).length,
    opcodeHistogram:referenceOpcodeHistogram
  },
  firstDisagreements:failures.filter(x=>x.kind==='mismatch').slice(0,10),
  firstUnsupported:failures.filter(x=>x.kind==='unsupported').slice(0,10),
  reportSchemaVersion:1
};
writeFileSync(options.out, JSON.stringify(report,null,2)+'\n');
process.stdout.write(JSON.stringify({
  status:report.status,compared:report.compared,passed:report.passed,
  mismatches:report.mismatches,oracleErrors:errors,unsupported,
  uniqueExecutionInputs:distinctInputs,
  matchedExceptionalCases:matchedExceptional,
  distinctReferenceOpcodes:Object.keys(referenceOpcodeHistogram).length,
  referenceStepEvents,
  corpusSha256,report:options.out,failures:options.failures
})+'\n');
if(failures.length) process.exit(1);
