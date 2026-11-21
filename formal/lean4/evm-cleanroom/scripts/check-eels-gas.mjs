#!/usr/bin/env node
/**
 * Narrow EXTERNAL consistency check: compare the *actual* Lean interpreter
 * gas consumption for a representative supported opcode with the static
 * GasCosts values in a pinned Ethereum EELS Prague gas.py.
 *
 * This is not an EELS state-test run, not a full opcode conformance check,
 * and not a formal refinement proof. It intentionally checks the executable
 * process rather than merely inspecting constants in our Lean source.
 *
 * Usage: node scripts/check-eels-gas.mjs PATH_TO_PINNED_GAS_PY
 */
import { readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';

if (process.argv.length !== 3) {
  throw new Error('usage: node scripts/check-eels-gas.mjs EELS_GAS_PY');
}
const source = readFileSync(process.argv[2], 'utf8');
const declarations = new Map();
for (const match of source.matchAll(/^\s+([A-Z][A-Z0-9_]*):\s*Final\[[^\]]+\]\s*=\s*(Uint\(\d+\)|[A-Z][A-Z0-9_]*)\s*$/gm)) {
  declarations.set(match[1], match[2]);
}
function resolve(name, seen = new Set()) {
  if (seen.has(name)) throw new Error('cyclic EELS gas tier: ' + name);
  seen.add(name);
  const raw = declarations.get(name);
  if (!raw) throw new Error('missing EELS gas constant: ' + name);
  const literal = /^Uint\((\d+)\)$/.exec(raw);
  return literal ? Number(literal[1]) : resolve(raw, seen);
}
const tests = [
  { name: 'ADD', code: '600260030100', charges: ['PUSH','PUSH','ADD'] },
  { name: 'MUL', code: '600260030200', charges: ['PUSH','PUSH','MUL'] },
  { name: 'SUB', code: '600260030300', charges: ['PUSH','PUSH','SUB'] },
  { name: 'DIV', code: '600260030400', charges: ['PUSH','PUSH','DIV'] },
  { name: 'POP', code: '60015000', charges: ['PUSH','POP'] },
  { name: 'PUSH0', code: '5f00', charges: ['PUSH0'] },
  { name: 'PUSH1', code: '600100', charges: ['PUSH'] },
  { name: 'DUP1', code: '60098000', charges: ['PUSH','DUP'] },
  { name: 'SWAP1', code: '600260039000', charges: ['PUSH','PUSH','SWAP'] },
  { name: 'PC', code: '5800', charges: ['PC'] },
  { name: 'GAS', code: '5a00', charges: ['GAS'] },
  { name: 'JUMPDEST', code: '5b00', charges: ['JUMPDEST'] },
  { name: 'JUMP', code: '6003565b00', charges: ['PUSH','JUMP','JUMPDEST'] },
  { name: 'JUMPI', code: '6001600657005b00', charges: ['PUSH','PUSH','JUMPI','JUMPDEST'] },
];
const initialGas = 1000;
const checks = [];
let errors = 0;
for (const item of tests) {
  const expected = item.charges.reduce((sum, name) => sum + resolve('OPCODE_' + name), 0);
  const proc = spawnSync('lake', ['exe','evm-subset',item.code,String(initialGas),'32'], {
    encoding:'utf8', maxBuffer:1024*1024
  });
  if (proc.error || proc.status !== 0) {
    errors++;
    checks.push({ name:item.name, status:'error', reason:proc.error?.message ?? proc.stderr ?? 'CLI failure' });
    continue;
  }
  let data;
  try { data = JSON.parse(proc.stdout.trim().split('\n').at(-1)); }
  catch { errors++; checks.push({name:item.name,status:'error',reason:'non-JSON executable output'}); continue; }
  const spent = BigInt(initialGas) - BigInt(data.gasRemaining);
  const pass = data.schemaVersion === 2 &&
    data.status === 'ok' && data.halted === true && spent === BigInt(expected);
  if (!pass) errors++;
  checks.push({name:item.name,status:pass?'pass':'fail',expectedGas:expected,observedGas:Number(spent),reportedStatus:data.status});
}
const report = {
  status:errors?'mismatch':'pass',
  reference:'ethereum/execution-specs Prague vm/gas.py, pinned by CI',
  scope:'representative supported static opcode gas charges only',
  checked:tests.length,
  mismatches:errors,
  checks
};
process.stdout.write(JSON.stringify(report) + '\n');
if (errors) process.exit(1);
