#!/usr/bin/env node
/**
 * Narrow independent EELS comparison of actual memory-opcode execution.
 *
 * EELS Prague vm/gas.py and vm/instructions/memory.py are pinned by CI.
 * This compares local Lean observable values and gas to a separately
 * implemented JS oracle using EELS's published gas constants/formula.
 * It does not execute an official state-test fixture and is NOT an
 * equivalence theorem for full EVM semantics.
 */
import { readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';

if (process.argv.length !== 4) {
  throw new Error('usage: node scripts/check-eels-memory.mjs EELS_GAS_PY EELS_MEMORY_PY');
}
const gasPy = readFileSync(process.argv[2], 'utf8');
const memPy = readFileSync(process.argv[3], 'utf8');
const definitions = new Map();
for (const m of gasPy.matchAll(/^\s+([A-Z][A-Z0-9_]*):\s*Final\[[^\]]+\]\s*=\s*(Uint\(\d+\)|[A-Z][A-Z0-9_]*)\s*$/gm)) {
  definitions.set(m[1], m[2]);
}
function gasConstant(name, seen = new Set()) {
  if (seen.has(name)) throw Error('cyclic tier ' + name);
  seen.add(name);
  const raw = definitions.get(name);
  if (!raw) throw Error('EELS gas constant unavailable: ' + name);
  const value = /^Uint\((\d+)\)$/.exec(raw);
  return value ? BigInt(value[1]) : gasConstant(raw, seen);
}
if (!gasPy.includes('size_in_words ** Uint(2) // Uint(512)') ||
    !gasPy.includes('linear_cost = size_in_words * GasCosts.MEMORY_PER_WORD')) {
  throw Error('Pinned EELS memory gas semantics changed: review this oracle before running');
}
for (const fn of ['def mload(', 'def mstore(', 'def mstore8(', 'def msize(']) {
  if (!memPy.includes(fn)) throw Error('missing EELS memory instruction: ' + fn);
}
const price = words => words * gasConstant('MEMORY_PER_WORD') + words * words / 512n;
const expand = (oldWords, newWords) => price(newWords > oldWords ? newWords : oldWords) - price(oldWords);
const op = name => gasConstant('OPCODE_' + name);
const cases = [
  {name:'MLOAD_zero',code:'60005100',gas:op('PUSH')+op('MLOAD_BASE')+expand(0n,1n),size:'32',word0:'0',stack:['0']},
  {name:'MLOAD_cross_word',code:'601f5100',gas:op('PUSH')+op('MLOAD_BASE')+expand(0n,2n),size:'64',word0:'0',stack:['0']},
  {name:'MSTORE_roundtrip',code:'600260005260005100',gas:3n*op('PUSH')+op('MSTORE_BASE')+op('MLOAD_BASE')+expand(0n,1n),size:'32',word0:'2',stack:['2']},
  {name:'MSTORE8_truncation',code:'61012c601f5360005100',gas:3n*op('PUSH')+op('MSTORE8_BASE')+op('MLOAD_BASE')+expand(0n,1n),size:'32',word0:'44',stack:['44']},
  {name:'MSIZE_after_cross_boundary',code:'60016020535900',gas:2n*op('PUSH')+op('MSTORE8_BASE')+op('MSIZE')+expand(0n,2n),size:'64',word0:'0',stack:['64']},
];
const initialGas=1000n, output=[];
let mismatches=0;
for (const t of cases) {
  const p=spawnSync('lake',['exe','evm-subset',t.code,initialGas.toString(),'16'],{encoding:'utf8',maxBuffer:1024*1024});
  if (p.status!==0 || p.error){mismatches++;output.push({name:t.name,status:'process-failure',stderr:p.stderr});continue;}
  let actual;
  try{actual=JSON.parse(p.stdout.trim().split('\n').at(-1));}
  catch(e){mismatches++;output.push({name:t.name,status:'invalid-json',detail:String(e)});continue;}
  const charged=initialGas-BigInt(actual.gasRemaining);
  const pass=actual.schemaVersion===2 && actual.status==='ok' && actual.halted===true &&
    charged===t.gas && actual.memorySizeBytes===t.size &&
    actual.memoryWord0===t.word0 && JSON.stringify(actual.stack)===JSON.stringify(t.stack);
  if(!pass)mismatches++;
  output.push({name:t.name,status:pass?'pass':'fail',expectedGas:t.gas.toString(),chargedGas:charged.toString(),expectedMemorySizeBytes:t.size,observedMemorySizeBytes:actual.memorySizeBytes,expectedWord0:t.word0,observedWord0:actual.memoryWord0});
}
// Extreme 256-bit pointer must refuse on gas, without requiring dense allocation.
const hugeCode='7f'+'ff'.repeat(32)+'5100';
const huge=spawnSync('lake',['exe','evm-subset',hugeCode,'100','5'],{encoding:'utf8'});
let hugeData;
try{hugeData=JSON.parse(huge.stdout.trim().split('\n').at(-1));}catch{hugeData=null;}
const hugePass=huge.status===0 && hugeData?.status==='error' && hugeData?.error==='outOfGas';
if(!hugePass)mismatches++;
output.push({name:'MLOAD_maxUint256_outOfGas',status:hugePass?'pass':'fail'});
const summary={status:mismatches?'mismatch':'pass',kind:'limited-external-EELS-memory-check',checked:cases.length+1,mismatches,tests:output};
process.stdout.write(JSON.stringify(summary)+'\n');
if(mismatches)process.exit(1);
