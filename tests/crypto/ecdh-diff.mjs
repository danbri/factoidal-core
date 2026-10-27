#!/usr/bin/env node
// Differential test: Lean P256.p256Ecdh (HACL* Hacl_P256_dh_responder,
// formal/lean4/L4Factoidal/Crypto/P256Native.lean) against node:crypto ECDH
// on prime256v1. For https://github.com/danbri/factoidal/issues/1083.
//
// The Lean side runs through the native probe, `l4crypto-probe --ecdh-stdin`
// (one line `<theirXY hex> <sk hex>` in, the shared-secret hex or `refused`
// out). This script makes no cryptographic decision: it generates inputs,
// asks both implementations, and reports every difference.
//
// Usage: node tests/crypto/ecdh-diff.mjs [N]   (default N = 500 key pairs)
// Needs: formal/lean4/.lake/build/bin/l4crypto-probe (lake build l4crypto-probe).
// Exit: 0 when every case agrees, 1 on any difference, 2 when the probe is absent.

import crypto from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const here = path.dirname(fileURLToPath(import.meta.url));
const probe = path.resolve(here, '../../formal/lean4/.lake/build/bin/l4crypto-probe');
if (!existsSync(probe)) {
  console.error(`ecdh-diff: ${probe} is absent; run "lake build l4crypto-probe" in formal/lean4`);
  process.exit(2);
}

const N = Number(process.argv[2] ?? 500);
const pad32 = (b) => Buffer.concat([Buffer.alloc(Math.max(0, 32 - b.length)), b]);

// Each case: { kind, theirXY (64 bytes), sk (32 bytes), expect (hex | 'refused') }.
const cases = [];
const nodeEcdh = (theirXY, sk) => {
  try {
    const e = crypto.createECDH('prime256v1');
    e.setPrivateKey(sk);
    return e.computeSecret(Buffer.concat([Buffer.from([4]), theirXY])).toString('hex');
  } catch {
    return 'refused';
  }
};

for (let i = 0; i < N; i++) {
  const a = crypto.createECDH('prime256v1');
  const b = crypto.createECDH('prime256v1');
  a.generateKeys();
  b.generateKeys();
  const bXY = b.getPublicKey().subarray(1);
  const aSk = pad32(a.getPrivateKey());
  // 1. A valid pair.
  cases.push({ kind: 'random-valid', theirXY: bXY, sk: aSk, expect: nodeEcdh(bXY, aSk) });
  // 2. The same public key with one bit of y flipped: off the curve.
  const off = Buffer.from(bXY);
  off[63 - (i % 32)] ^= 1 << (i % 8);
  cases.push({ kind: 'off-curve', theirXY: off, sk: aSk, expect: nodeEcdh(off, aSk) });
  // 3. 64 random bytes as a point (almost never on the curve).
  const rnd = crypto.randomBytes(64);
  cases.push({ kind: 'random-point', theirXY: rnd, sk: aSk, expect: nodeEcdh(rnd, aSk) });
}
// Fixed edge cases: scalar 1 and n-1, the point at (0, 0).
const n = Buffer.from('ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551', 'hex');
const nm1 = Buffer.from(n); nm1[31] -= 1;
const one = pad32(Buffer.from([1]));
const g = crypto.createECDH('prime256v1'); g.generateKeys();
const gXY = g.getPublicKey().subarray(1);
for (const [kind, sk] of [['scalar-1', one], ['scalar-n-1', nm1]]) {
  cases.push({ kind, theirXY: gXY, sk, expect: nodeEcdh(gXY, sk) });
}
cases.push({ kind: 'point-0-0', theirXY: Buffer.alloc(64), sk: one, expect: nodeEcdh(Buffer.alloc(64), one) });
// Scalars node refuses to set (0 and n): HACL* must refuse them too.
cases.push({ kind: 'scalar-0', theirXY: gXY, sk: Buffer.alloc(32), expect: 'refused' });
cases.push({ kind: 'scalar-n', theirXY: gXY, sk: n, expect: 'refused' });

const input = cases.map((c) => `${c.theirXY.toString('hex')} ${c.sk.toString('hex')}`).join('\n') + '\n';
const r = spawnSync(probe, ['--ecdh-stdin'], { input, encoding: 'utf8', maxBuffer: 1 << 26 });
if (r.status !== 0) {
  console.error(`ecdh-diff: probe exited ${r.status}: ${r.stderr}`);
  process.exit(1);
}
const got = r.stdout.trimEnd().split('\n');
if (got.length !== cases.length) {
  console.error(`ecdh-diff: ${cases.length} cases sent, ${got.length} answers received`);
  process.exit(1);
}

const perKind = new Map();
let diffs = 0;
cases.forEach((c, i) => {
  const k = perKind.get(c.kind) ?? { agree: 0, differ: 0, accepted: 0, refused: 0 };
  if (got[i] === c.expect) k.agree++;
  else {
    k.differ++;
    diffs++;
    console.log(`DIFF ${c.kind} #${i}: node=${c.expect} lean=${got[i]} xy=${c.theirXY.toString('hex')} sk=${c.sk.toString('hex')}`);
  }
  if (c.expect === 'refused') k.refused++; else k.accepted++;
  perKind.set(c.kind, k);
});
for (const [kind, k] of perKind) {
  console.log(`${kind}: ${k.agree} agree, ${k.differ} differ (out of ${k.agree + k.differ}; node accepted ${k.accepted}, refused ${k.refused})`);
}
console.log(`ecdh-diff TOTAL: ${cases.length - diffs} agree, ${diffs} differ (out of ${cases.length})`);
process.exit(diffs === 0 ? 0 : 1);
