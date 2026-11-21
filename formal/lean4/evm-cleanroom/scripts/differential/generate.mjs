#!/usr/bin/env node
/**
 * Deterministic *synthetic bytecode* corpus. This is NOT a sample of
 * mainnet transactions and does not constitute EELS state-test coverage.
 * Inputs have no external state, contract calls, or environmental opcodes.
 *
 * node scripts/differential/generate.mjs --seed 20261119 --count 512 --out /tmp/evm-corpus.jsonl
 */
import { createHash } from 'node:crypto';
import { writeFileSync } from 'node:fs';

function flags(argv) {
  const opts = {};
  for (let i = 0; i < argv.length; i += 2) {
    if (!argv[i]?.startsWith('--') || argv[i + 1] === undefined) {
      throw Error('expected --seed N --count N --out PATH');
    }
    opts[argv[i].slice(2)] = argv[i + 1];
  }
  return opts;
}
const opts = flags(process.argv.slice(2));
const seed = Number(opts.seed);
const count = Number(opts.count);
if (!Number.isSafeInteger(seed) || seed < 1 || seed > 0xffffffff ||
    !Number.isSafeInteger(count) || count < 1 || count > 100_000 || !opts.out) {
  throw Error('invalid seed/count/out; count must be 1..100000 and seed a nonzero uint32');
}
let state = seed >>> 0;
function next() {
  state ^= state << 13; state ^= state >>> 17; state ^= state << 5;
  return state >>> 0;
}
const choose = values => values[next() % values.length];
const byteHex = x => (x & 255).toString(16).padStart(2, '0');
const pushBytes = bytes => {
  if (bytes.length < 1 || bytes.length > 32) throw Error('PUSH width out of range');
  return byteHex(0x5f + bytes.length) + Buffer.from(bytes).toString('hex');
};
const pushSmall = x => pushBytes([x & 255]);
const randomBytes = n => Array.from({length:n}, () => next() & 255);
const pushWord = () => {
  const width = choose([1, 1, 2, 4, 8, 16, 32, 32]);
  const mode = next() % 8;
  const bytes = Array.from({length: width}, () => next() & 255);
  if (mode === 0) bytes.fill(0);
  if (mode === 1) bytes.fill(255);
  if (mode === 2) { bytes.fill(0); bytes[width - 1] = 1; }
  if (mode === 3) { bytes.fill(0); bytes[0] = 0x80; }
  if (mode === 4) { bytes.fill(0); bytes[width - 1] = 0x5b; }
  return pushBytes(bytes);
};
const categories = [
  'arithmetic', 'memory-word', 'memory-byte', 'memory-load',
  'memory-size', 'stack-ops', 'jump', 'jumpi',
  'gas', 'pc', 'push', 'memory-cross-word',
  'out-of-gas', 'stack-underflow', 'invalid-jump', 'invalid-opcode',
  'jumpi-invalid-unselected', 'high-pointer-out-of-gas'
];
// Independent metadata check: a category labelled as exceptional must
// actually declare its expected error. Prevents unreachable label assignments.
const categoryError = {
  'out-of-gas': 'outOfGas',
  'stack-underflow': 'stackUnderflow',
  'invalid-jump': 'invalidJump',
  'invalid-opcode': 'invalidOpcode',
  'high-pointer-out-of-gas': 'outOfGas'
};
const rows = [];
const hist = {};
for (let i = 0; i < count; i++) {
  const category = categories[i % categories.length];
  const position = choose([0,1,2,7,16,30,31,32,33,63,64,95]);
  let code;
  let gas = String(500 + (next() % 3500));
  let expectedError = null;
  switch (category) {
    case 'arithmetic':
      code = pushWord() + pushWord() + byteHex(choose([0x01,0x02,0x03,0x04])) + '00';
      break;
    case 'memory-word':
      code = pushWord() + pushSmall(position) + '52' + pushSmall(position) + '5100';
      break;
    case 'memory-byte':
      code = pushWord() + pushSmall(position) + '53' + pushSmall(position) + '5100';
      break;
    case 'memory-load':
      code = pushWord() + '50' + pushSmall(position) + '5100';
      break;
    case 'memory-size':
      code = pushSmall(next() & 255) + pushSmall(position) + '535900';
      break;
    case 'stack-ops':
      code = pushWord() + pushWord() + '90805000';
      break;
    case 'jump': {
      const fillerWidth = choose([1,2,4,8,16,32]);
      const filler = pushBytes(randomBytes(fillerWidth));
      const target = 4 + fillerWidth;
      code = pushSmall(target) + '56' + filler + '5b00';
      break;
    }
    case 'jumpi': {
      const fillerWidth = choose([1,2,4,8,16,32]);
      const filler = pushBytes(randomBytes(fillerWidth));
      const target = 8 + fillerWidth;
      code = pushSmall(next() & 1) + pushSmall(target) + '57' + filler + '50005b00';
      break;
    }
    case 'gas':
      code = pushWord() + '5a0100';
      break;
    case 'pc':
      code = '58' + pushWord() + '0100';
      break;
    case 'push':
      code = pushWord() + '00';
      break;
    case 'memory-cross-word':
      code = pushWord() + pushSmall(31) + '52' + pushSmall(32) + '5100';
      break;
    case 'out-of-gas':
      code = pushWord() + '00'; // Any PUSH requires 3 gas.
      gas = String(next() % 3); expectedError = 'outOfGas';
      break;
    case 'stack-underflow':
      code = pushWord() + '0100'; // ADD with only one operand.
      expectedError = 'stackUnderflow';
      break;
    case 'invalid-jump':
      code = pushSmall(choose([0,1,2,3,4,255])) + '56' + pushWord() + '5b00';
      // No chosen destination is the actual decoded JUMPDEST after the filler.
      expectedError = 'invalidJump';
      break;
    case 'invalid-opcode':
      code = pushWord() + 'fe00';
      expectedError = 'invalidOpcode';
      break;
    case 'jumpi-invalid-unselected':
      code = pushSmall(0) + pushSmall(choose([0,1,2,3,4,255])) +
        '57' + pushWord() + '5000'; // Invalid target, untaken branch.
      break;
    case 'high-pointer-out-of-gas': {
      const bytes = randomBytes(32);
      bytes[0] |= 0x80;
      code = pushBytes(bytes) + '5100';
      expectedError = 'outOfGas';
      break;
    }
    default:
      throw Error('generator category not handled: ' + category);
  }
  if ((categoryError[category] ?? null) !== expectedError) {
    throw Error('incorrect expected-error metadata for category: ' + category);
  }
  hist[category] = (hist[category] ?? 0) + 1;
  rows.push({
    schemaVersion: 1,
    id: 'synthetic-' + String(seed) + '-' + String(i).padStart(6,'0'),
    kind: 'synthetic-bytecode',
    category,
    hardfork: 'prague',
    hex: code,
    gas,
    fuel: '64',
    expectedDisposition: expectedError ? 'error' : 'ok',
    ...(expectedError ? {expectedError} : {})
  });
}
const corpusText = rows.map(row => JSON.stringify(row)).join('\n') + '\n';
writeFileSync(opts.out, corpusText);
process.stdout.write(JSON.stringify({
  status:'generated', generator:'evm-cleanroom/differential/v1',
  seed, count, sha256:createHash('sha256').update(corpusText).digest('hex'),
  categories:hist, path:opts.out
}) + '\n');
