#!/usr/bin/env node
// tests/crypto/rsa-oaep-diff.mjs — differential run of the Lean 4 RSA-OAEP
// (formal/lean4/L4Factoidal/Crypto/RsaOaep.lean over the HACL* RSA
// operations) against Node's node:crypto (OpenSSL).
// Tracking: https://github.com/danbri/factoidal/issues/1082.
//
// node:crypto makes the keys, the messages and the labels. For each case:
//   1. Node encrypts (publicEncrypt, RSA_PKCS1_OAEP_PADDING); the Lean probe
//      decrypts. The result must be the message.
//   2. The Lean probe encrypts with a random seed from node:crypto; Node
//      decrypts (privateDecrypt). The result must be the message.
//   3. A one-bit change of Node's ciphertext must make BOTH sides refuse.
//   4. Decryption under a different label must make both sides refuse.
// Every difference is printed. The exit code is 0 only with 0 differences.
//
// No cryptographic decision is made in this file (iron rule 7): it makes
// test inputs, passes bytes and compares answers. The Lean side runs as
// `l4crypto-probe --oaep-batch` (Harness/CryptoProbe.lean), one process for
// all requests.
//
// Usage: node tests/crypto/rsa-oaep-diff.mjs [cases-per-key]   (default 10)
// Needs formal/lean4/.lake/build/bin/l4crypto-probe
// (cd formal/lean4 && lake build l4crypto-probe).

import crypto from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..', '..');
const probe = join(root, 'formal', 'lean4', '.lake', 'build', 'bin', 'l4crypto-probe');
if (!existsSync(probe)) {
  console.error(`rsa-oaep-diff: ${probe} is missing; run: cd formal/lean4 && lake build l4crypto-probe`);
  process.exit(2);
}

const perKey = Number(process.argv[2] ?? 10);
const hex = (b) => (b.length === 0 ? '-' : Buffer.from(b).toString('hex'));
const b64u = (s) => Buffer.from(s, 'base64url');
const unhex = (s) => (s === '-' ? Buffer.alloc(0) : Buffer.from(s, 'hex'));

const configs = [
  { bits: 2048, hash: 'sha1', hLen: 20 },
  { bits: 2048, hash: 'sha256', hLen: 32 },
  { bits: 3072, hash: 'sha256', hLen: 32 },
  { bits: 4096, hash: 'sha1', hLen: 20 },
  { bits: 4096, hash: 'sha256', hLen: 32 },
];

const cases = [];
const lines = [];
for (const cfg of configs) {
  const { publicKey, privateKey } = crypto.generateKeyPairSync('rsa', { modulusLength: cfg.bits });
  const jwk = privateKey.export({ format: 'jwk' });
  const n = b64u(jwk.n), e = b64u(jwk.e), d = b64u(jwk.d);
  const k = n.length;
  const maxLen = k - 2 * cfg.hLen - 2;
  for (let i = 0; i < perKey; i++) {
    // Lengths 0, the maximum, and random ones between.
    const mLen = i === 0 ? 0 : i === 1 ? maxLen : crypto.randomInt(0, maxLen + 1);
    const msg = crypto.randomBytes(mLen);
    const label = i % 3 === 0 ? Buffer.alloc(0) : crypto.randomBytes(crypto.randomInt(1, 40));
    const otherLabel = Buffer.concat([label, Buffer.from([0x01])]);
    const opts = { key: publicKey, padding: crypto.constants.RSA_PKCS1_OAEP_PADDING, oaepHash: cfg.hash };
    if (label.length > 0) opts.oaepLabel = label;
    const ctNode = crypto.publicEncrypt(opts, msg);
    const flipped = Buffer.from(ctNode);
    flipped[crypto.randomInt(0, k)] ^= 1 << crypto.randomInt(0, 8);
    const seed = crypto.randomBytes(cfg.hLen);
    const name = `${cfg.bits}-${cfg.hash} #${i} (mLen ${mLen}, label ${label.length})`;
    cases.push({ name, kind: 'node-enc/lean-dec', expect: msg });
    lines.push(`dec ${cfg.hash} ${hex(n)} ${hex(d)} ${hex(ctNode)} ${hex(label)}`);
    cases.push({ name, kind: 'lean-enc', cfg, privateKey, label, msg });
    lines.push(`enc ${cfg.hash} ${hex(n)} ${hex(e)} ${hex(msg)} ${hex(label)} ${hex(seed)}`);
    cases.push({ name, kind: 'flipped', cfg, privateKey, label, ct: flipped });
    lines.push(`dec ${cfg.hash} ${hex(n)} ${hex(d)} ${hex(flipped)} ${hex(label)}`);
    cases.push({ name, kind: 'other-label', cfg, privateKey, label: otherLabel, ct: ctNode });
    lines.push(`dec ${cfg.hash} ${hex(n)} ${hex(d)} ${hex(ctNode)} ${hex(otherLabel)}`);
  }
}

const run = spawnSync(probe, ['--oaep-batch'], { input: lines.join('\n') + '\n', maxBuffer: 1 << 28 });
if (run.status !== 0) {
  console.error(`rsa-oaep-diff: probe exited ${run.status}: ${run.stderr}`);
  process.exit(2);
}
const answers = run.stdout.toString().split('\n').filter((l) => l.length > 0);
if (answers.length !== cases.length) {
  console.error(`rsa-oaep-diff: ${cases.length} requests, ${answers.length} answers`);
  process.exit(2);
}

function nodeDecrypt(c, ct) {
  const opts = { key: c.privateKey, padding: crypto.constants.RSA_PKCS1_OAEP_PADDING, oaepHash: c.cfg.hash };
  if (c.label.length > 0) opts.oaepLabel = c.label;
  try { return crypto.privateDecrypt(opts, ct); } catch { return null; }
}

let pass = 0, fail = 0;
const diff = (c, msg) => { fail++; console.log(`  [DIFF] ${c.name} ${c.kind}: ${msg}`); };
cases.forEach((c, i) => {
  const a = answers[i];
  if (c.kind === 'node-enc/lean-dec') {
    if (a !== 'none' && a !== 'error' && unhex(a).equals(c.expect)) pass++;
    else diff(c, `Lean answered ${a.slice(0, 40)}`);
  } else if (c.kind === 'lean-enc') {
    if (a === 'none' || a === 'error') { diff(c, `Lean refused to encrypt (${a})`); return; }
    const got = nodeDecrypt(c, unhex(a));
    if (got && got.equals(c.msg)) pass++;
    else diff(c, 'Node could not decrypt the Lean ciphertext to the message');
  } else {
    const node = nodeDecrypt(c, c.ct);
    if (a === 'none' && node === null) pass++;
    else diff(c, `expected both to refuse; Lean ${a.slice(0, 20)}, Node ${node === null ? 'refused' : 'decrypted'}`);
  }
});

console.log(`rsa-oaep-diff (Lean HACL* vs node:crypto ${process.versions.openssl ? 'OpenSSL ' + process.versions.openssl : ''}): ${pass} pass, ${fail} fail (out of ${pass + fail})`);
process.exit(fail === 0 ? 0 : 1);
