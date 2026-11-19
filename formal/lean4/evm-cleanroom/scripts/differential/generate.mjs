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
  'gas', 'pc', 'push', 'memory-cross-word'
];
const rows = [];
const hist = {};
for (let i = 0; i < count; i++) {
  const category = categories[i % categories.length];
  const position = choose([0,1,2,7,16,30,31,32,33,63,64,95]);
  let code;
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
      code = pushSmall(position) + '5100';
      break;
    case 'memory-size':
      code = pushSmall(next() & 255) + pushSmall(position) + '535900';
      break;
    case 'stack-ops':
      code = pushWord() + pushWord() + '90805000';
      break;
    case 'jump':
      code = '600556605b5b00'; // PUSH1 5; JUMP; PUSH1 0x5b; JUMPDEST; STOP
      break;
    case 'jumpi':
      code = '60' + byteHex(next() & 1) + '60095760ff50005b00';
      break;
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
    default:
      throw Error('generator category not handled: ' + category);
  }
  hist[category] = (hist[category] ?? 0) + 1;
  rows.push({
    schemaVersion: 1,
    id: 'synthetic-' + String(seed) + '-' + String(i).padStart(6,'0'),
    kind: 'synthetic-bytecode',
    category,
    hardfork: 'prague',
    hex: code,
    gas: '1000',
    fuel: '64'
  });
}
const corpusText = rows.map(row => JSON.stringify(row)).join('\n') + '\n';
writeFileSync(opts.out, corpusText);
process.stdout.write(JSON.stringify({
  status:'generated', generator:'evm-cleanroom/differential/v1',
  seed, count, sha256:createHash('sha256').update(corpusText).digest('hex'),
  categories:hist, path:opts.out
}) + '\n');
