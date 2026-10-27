#!/usr/bin/env node
// Differential test of AES across implementations, for
// https://github.com/danbri/factoidal/issues/1081 (XML Encryption and JWE) and
// https://github.com/danbri/factoidal/issues/677 (AES-GCM). Owner, 2026-10-27,
// verbatim: "For testing hammer both and flag differences if that makes sense,
// seek trustworthy tests too".
//
// WebCrypto is not formally verified (skills/crypto-policy/SKILL.md § AES
// through WebCrypto); this run is the measured obligation that replaces the
// proof. The same requests (the CipherCall request format of
// formal/lean4/L4Factoidal/Crypto/CipherCall.lean) go to:
//
//   node      Node WebCrypto (OpenSSL), through npm/factoidal/lib/cipher-host.mjs
//   chromium  headless Chromium WebCrypto (BoringSSL), the same cipher-host.mjs
//             code run inside the page through Playwright
//   firefox   Firefox WebCrypto (NSS), the same code, when Playwright's
//             Firefox is installed; otherwise "not available"
//   vale      HACL* Vale AES-GCM (formal/lean4/L4Factoidal/Crypto/AesGcmNative.lean)
//             through `l4crypto-probe --gcm-stdin`; GCM only (Vale has no Key
//             Wrap and no CBC)
//
// Cases: random AES-GCM, Key Wrap and CBC requests (keys of 16 and 32 bytes,
// 12-byte GCM IVs, random AAD and plaintext lengths 0..1024) with tampered
// ciphertexts, tags, AAD and wrapped keys; then the published vectors:
// Wycheproof aes_gcm_test.json (96-bit IV, 128-bit tag, 128/256-bit keys),
// aes_wrap_test.json, aes_cbc_pkcs5_test.json, RFC 3394 §4, and McGrew-Viega
// GCM (SP 800-38D) Appendix B cases 1-4 and 13-16. node:crypto (the cipher
// API, not WebCrypto) builds the valid ciphertexts that the decrypt cases
// start from; it is an input generator, never a judge.
//
// Any difference in output bytes or in accept/refuse between two
// implementations is a failure, printed with its input in hex. A vector
// answered against its published result is a failure too.
//
// Usage: node tests/crypto/aes-diff.mjs [N]   (default N = 200 rounds; each
//        round makes 5 GCM, 3 Key Wrap and 3 CBC cases). A vector gives
//        two checks when valid (encrypt or wrap, and decrypt or unwrap) and one
//        when invalid (the decrypt or unwrap must be refused).
// Needs: formal/lean4/.lake/build/bin/l4crypto-probe (lake build l4crypto-probe)
//        for the vale column; Playwright for the browser columns.
// Exit: 0 when every case agrees and every vector passes, 1 otherwise.

import crypto from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { answerCipherRequest } from '../../npm/factoidal/lib/cipher-host.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, '../..');
const hostSrc = path.join(root, 'npm/factoidal/lib/cipher-host.mjs');
const probe = path.join(root, 'formal/lean4/.lake/build/bin/l4crypto-probe');
const wp = path.join(root, 'third_party/testing/wycheproof/testvectors_v1');
const N = Number(process.argv[2] ?? 200);

const H = (b) => Buffer.from(b).toString('hex');
const B = (hex) => Buffer.from(hex, 'hex');
const b64 = (buf) => Buffer.from(buf).toString('base64');
const rnd = (n) => crypto.randomBytes(n);
const rint = (n) => crypto.randomInt(n);
const flip = (buf, i) => { const c = Buffer.from(buf); c[i] ^= 1 << rint(8); return c; };

// ---- case construction --------------------------------------------------
// A case: {id, file, req: {op, key, iv, aad, data} as Buffers, expect?}
// expect: 'ok:<hex>' | 'refused' | 'any' (Wycheproof "acceptable").
const cases = [];
const add = (id, file, op, key, iv, aad, data, expect) =>
  cases.push({ id, file, req: { op, key: B(H(key)), iv: B(H(iv ?? [])), aad: B(H(aad ?? [])), data: B(H(data)) }, expect });

const gcmSeal = (key, iv, aad, pt) => {
  const c = crypto.createCipheriv(`aes-${key.length * 8}-gcm`, key, iv);
  c.setAAD(aad);
  return Buffer.concat([c.update(pt), c.final(), c.getAuthTag()]);
};
const kwWrap = (kek, k) => {
  const c = crypto.createCipheriv(`id-aes${kek.length * 8}-wrap`, kek, B('a6a6a6a6a6a6a6a6'));
  return Buffer.concat([c.update(k), c.final()]);
};
const cbcSeal = (key, iv, pt) => {
  const c = crypto.createCipheriv(`aes-${key.length * 8}-cbc`, key, iv);
  return Buffer.concat([c.update(pt), c.final()]);
};

for (let i = 0; i < N; i++) {
  const ks = i % 2 ? 32 : 16;
  // AES-GCM.
  {
    const key = rnd(ks), iv = rnd(12), aad = rnd(rint(65)), pt = rnd(rint(1025));
    const ct = gcmSeal(key, iv, aad, pt);
    add(`gcm-${i}-encrypt`, 'random', 'aes-gcm-encrypt', key, iv, aad, pt);
    add(`gcm-${i}-decrypt`, 'random', 'aes-gcm-decrypt', key, iv, aad, ct);
    add(`gcm-${i}-tampered-body`, 'random', 'aes-gcm-decrypt', key, iv, aad, pt.length ? flip(ct, rint(pt.length)) : ct, undefined);
    add(`gcm-${i}-tampered-tag`, 'random', 'aes-gcm-decrypt', key, iv, aad, flip(ct, pt.length + rint(16)));
    if (i % 10 === 0) add(`gcm-${i}-short`, 'random', 'aes-gcm-decrypt', key, iv, aad, ct.subarray(0, rint(16)));
    else add(`gcm-${i}-tampered-aad`, 'random', 'aes-gcm-decrypt', key, iv, aad.length ? flip(aad, rint(aad.length)) : B('00'), ct);
  }
  // AES Key Wrap.
  {
    const kek = rnd(ks), k = rnd(16 + 8 * rint(7));
    const w = kwWrap(kek, k);
    add(`kw-${i}-wrap`, 'random', 'aes-kw-wrap', kek, null, null, k);
    add(`kw-${i}-unwrap`, 'random', 'aes-kw-unwrap', kek, null, null, w);
    add(`kw-${i}-tampered`, 'random', 'aes-kw-unwrap', kek, null, null, flip(w, rint(w.length)));
  }
  // AES-CBC, PKCS #7.
  {
    const key = rnd(ks), iv = rnd(16), pt = rnd(rint(1025));
    const ct = cbcSeal(key, iv, pt);
    add(`cbc-${i}-encrypt`, 'random', 'aes-cbc-encrypt', key, iv, null, pt);
    add(`cbc-${i}-decrypt`, 'random', 'aes-cbc-decrypt', key, iv, null, ct);
    // Flip a bit of the second-last block (or the IV when there is one block):
    // the change reaches the padding bytes of the last block.
    const tampered = ct.length >= 32 ? flip(ct, ct.length - 17 - rint(16)) : ct;
    const tiv = ct.length >= 32 ? iv : flip(iv, 16 - 1 - rint(16));
    add(`cbc-${i}-tampered`, 'random', 'aes-cbc-decrypt', key, tiv, null, tampered);
  }
}

// ---- published vectors ---------------------------------------------------
const notRun = {}; // file -> count of vectors outside the profile
const skip = (file, n = 1) => { notRun[file] = (notRun[file] ?? 0) + n; };
const readJson = (f) => { try { return JSON.parse(readFileSync(path.join(wp, f), 'utf8')); } catch { return null; } };
const missing = [];

{
  const f = 'aes_gcm_test.json', j = readJson(f);
  if (!j) missing.push(f);
  else for (const g of j.testGroups) for (const t of g.tests) {
    if (g.ivSize !== 96 || g.tagSize !== 128 || (g.keySize !== 128 && g.keySize !== 256)) { skip(f); continue; }
    const id = `wycheproof gcm tcId ${t.tcId}`;
    const ctTag = B(t.ct + t.tag);
    if (t.result === 'valid') add(`${id} encrypt`, f, 'aes-gcm-encrypt', B(t.key), B(t.iv), B(t.aad), B(t.msg), `ok:${t.ct}${t.tag}`);
    add(`${id} decrypt`, f, 'aes-gcm-decrypt', B(t.key), B(t.iv), B(t.aad), ctTag,
      t.result === 'valid' ? `ok:${t.msg}` : t.result === 'invalid' ? 'refused' : 'any');
  }
}
{
  const f = 'aes_wrap_test.json', j = readJson(f);
  if (!j) missing.push(f);
  else for (const g of j.testGroups) for (const t of g.tests) {
    if (g.keySize !== 128 && g.keySize !== 256) { skip(f); continue; }
    const id = `wycheproof kw tcId ${t.tcId}`;
    if (t.result === 'valid') add(`${id} wrap`, f, 'aes-kw-wrap', B(t.key), null, null, B(t.msg), `ok:${t.ct}`);
    add(`${id} unwrap`, f, 'aes-kw-unwrap', B(t.key), null, null, B(t.ct),
      t.result === 'valid' ? `ok:${t.msg}` : t.result === 'invalid' ? 'refused' : 'any');
  }
}
{
  const f = 'aes_cbc_pkcs5_test.json', j = readJson(f);
  if (!j) missing.push(f);
  else for (const g of j.testGroups) for (const t of g.tests) {
    if (g.keySize !== 128 && g.keySize !== 256) { skip(f); continue; }
    const id = `wycheproof cbc tcId ${t.tcId}`;
    if (t.result === 'valid') add(`${id} encrypt`, f, 'aes-cbc-encrypt', B(t.key), B(t.iv), null, B(t.msg), `ok:${t.ct}`);
    add(`${id} decrypt`, f, 'aes-cbc-decrypt', B(t.key), B(t.iv), null, B(t.ct),
      t.result === 'valid' ? `ok:${t.msg}` : t.result === 'invalid' ? 'refused' : 'any');
  }
}
{
  // RFC 3394 §4. 4.2 and 4.4 use a 192-bit KEK, which CipherCall refuses.
  const f = 'RFC 3394 §4';
  const k128 = '000102030405060708090a0b0c0d0e0f';
  const k256 = '000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f';
  const data = '00112233445566778899aabbccddeeff';
  const rows = [
    ['4.1', k128, data, '1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5'],
    ['4.3', k256, data, '64e8c3f9ce0f5ba263e9777905818a2a93c8191e7d6e8ae7'],
    ['4.5', k256, data + '0001020304050607', 'a8f9bc1612c68b3ff6e6f4fbe30e71e4769c8b80a32cb8958cd5d17d6b254da1'],
    ['4.6', k256, data + '000102030405060708090a0b0c0d0e0f',
      '28c9f404c4b810f4cbccb35cfb87f8263f5786e2d80ed326cbc7f0e71a99f43bfb988b9b7a02dd21'],
  ];
  skip(f, 2);
  for (const [s, kek, k, w] of rows) {
    add(`RFC 3394 ${s} wrap`, f, 'aes-kw-wrap', B(kek), null, null, B(k), `ok:${w}`);
    add(`RFC 3394 ${s} unwrap`, f, 'aes-kw-unwrap', B(kek), null, null, B(w), `ok:${k}`);
  }
}
{
  // McGrew and Viega, "The Galois/Counter Mode of Operation (GCM)", revised
  // 2005, Appendix B (the SP 800-38D reference vectors), 96-bit IV cases.
  // Cases 5, 6, 11, 12, 17, 18 (other IV lengths) and 7-10 (192-bit keys)
  // are outside the CipherCall profile.
  const f = 'McGrew-Viega GCM';
  const p64 = 'd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255';
  const p60 = p64.slice(0, 120);
  const a = 'feedfacedeadbeeffeedfacedeadbeefabaddad2';
  const k = 'feffe9928665731c6d6a8f9467308308';
  const iv = 'cafebabefacedbaddecaf888';
  const z12 = '0'.repeat(24), z16 = '0'.repeat(32);
  const c3 = '42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985';
  const c15 = '522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662898015ad';
  const rows = [
    [1, z16, z12, '', '', '', '58e2fccefa7e3061367f1d57a4e7455a'],
    [2, z16, z12, '', z16, '0388dace60b6a392f328c2b971b2fe78', 'ab6e47d42cec13bdf53a67b21257bddf'],
    [3, k, iv, '', p64, c3, '4d5c2af327cd64a62cf35abd2ba6fab4'],
    [4, k, iv, a, p60, c3.slice(0, 120), '5bc94fbc3221a5db94fae95ae7121a47'],
    [13, z16 + z16, z12, '', '', '', '530f8afbc74536b9a963b4f1c4cb738b'],
    [14, z16 + z16, z12, '', z16, 'cea7403d4d606b6e074ec5d3baf39d18', 'd0d1c8a799996bf0265b98b5d48ab919'],
    [15, k + k, iv, '', p64, c15, 'b094dac5d93471bdec1a502270e3cc6c'],
    [16, k + k, iv, a, p60, c15.slice(0, 120), '76fc6ece0f4e1768cddf8853bb2d551b'],
  ];
  skip(f, 10);
  for (const [n, key, nonce, aad, pt, ct, tag] of rows) {
    add(`McGrew-Viega case ${n} encrypt`, f, 'aes-gcm-encrypt', B(key), B(nonce), B(aad), B(pt), `ok:${ct}${tag}`);
    add(`McGrew-Viega case ${n} decrypt`, f, 'aes-gcm-decrypt', B(key), B(nonce), B(aad), B(ct + tag), `ok:${pt}`);
  }
}

// ---- implementations -----------------------------------------------------
const toWire = (r) => ({ op: r.op, key: b64(r.key), iv: b64(r.iv), aad: b64(r.aad), data: b64(r.data) });
const norm = (a) => (a && typeof a.ok === 'string' ? `ok:${H(Buffer.from(a.ok, 'base64'))}` : 'refused');

async function runNode() {
  const out = [];
  for (const c of cases) out.push(norm(await answerCipherRequest(toWire(c.req))));
  return out;
}

async function runBrowser(kind) {
  let pw;
  try { pw = createRequire(import.meta.url)('playwright'); } catch { return { unavailable: 'playwright is not installed' }; }
  let browser;
  try { browser = await pw[kind].launch(); } catch (e) { return { unavailable: String(e.message).split('\n')[0] }; }
  try {
    const page = await browser.newPage();
    // WebCrypto needs a secure context: serve an empty page at an https URL.
    await page.route('**/*', (r) => r.fulfill({ status: 200, contentType: 'text/html', body: '<!doctype html><title>aes-diff</title>' }));
    await page.goto('https://aes-diff.invalid/');
    const src = readFileSync(hostSrc, 'utf8').replace(/^export /gm, '');
    await page.addScriptTag({ content: `${src}\nglobalThis.__answer = answerCipherRequest;` });
    const version = browser.version();
    const out = [];
    const wire = cases.map((c) => toWire(c.req));
    for (let i = 0; i < wire.length; i += 400) {
      const part = await page.evaluate(async (reqs) => {
        const r = [];
        for (const q of reqs) r.push(await globalThis.__answer(q));
        return r;
      }, wire.slice(i, i + 400));
      out.push(...part.map(norm));
    }
    return { out, version };
  } finally {
    await browser.close();
  }
}

function runVale() {
  if (!existsSync(probe)) return { unavailable: `${probe} is absent; run "lake build l4crypto-probe" in formal/lean4` };
  const idx = [];
  const lines = [];
  const f = (b) => (b.length ? H(b) : '-');
  cases.forEach((c, i) => {
    if (c.req.op !== 'aes-gcm-encrypt' && c.req.op !== 'aes-gcm-decrypt') return;
    idx.push(i);
    lines.push(`${c.req.op === 'aes-gcm-encrypt' ? 'enc' : 'dec'} ${f(c.req.key)} ${f(c.req.iv)} ${f(c.req.aad)} ${f(c.req.data)}`);
  });
  const r = spawnSync(probe, ['--gcm-stdin'], { input: lines.join('\n') + '\n', maxBuffer: 1 << 28 });
  if (r.status !== 0) return { unavailable: `l4crypto-probe exited ${r.status}` };
  const outLines = r.stdout.toString().replace(/\n$/, '').split('\n');
  if (outLines[0] !== 'available') return { unavailable: 'HACL* Vale AES-GCM is not available on this CPU (issue 677)' };
  const out = new Array(cases.length).fill(null);
  idx.forEach((ci, k) => {
    const s = outLines[k + 1];
    out[ci] = s === undefined ? 'missing' : s === 'refused' ? 'refused' : `ok:${s}`;
  });
  return { out };
}

// ---- run and compare ------------------------------------------------------
const impls = {};
const unavailable = {};
impls.node = { out: await runNode(), label: `Node ${process.version} WebCrypto (OpenSSL ${process.versions.openssl})` };
for (const [name, kind, lib] of [['chromium', 'chromium', 'BoringSSL'], ['firefox', 'firefox', 'NSS']]) {
  const r = await runBrowser(kind);
  if (r.unavailable) unavailable[name] = r.unavailable;
  else impls[name] = { out: r.out, label: `${kind} ${r.version} WebCrypto (${lib})` };
}
{
  const r = runVale();
  if (r.unavailable) unavailable.vale = r.unavailable;
  else impls.vale = { out: r.out, label: 'HACL* Vale AES-GCM (l4crypto-probe --gcm-stdin; GCM only)' };
}

console.log('aes-diff: implementations');
for (const [n, i] of Object.entries(impls)) console.log(`  ${n.padEnd(9)} ${i.label}`);
for (const [n, why] of Object.entries(unavailable)) console.log(`  ${n.padEnd(9)} NOT AVAILABLE: ${why}`);
if (missing.length) console.log(`  missing vector files (run tools/ensure-test-env.sh): ${missing.join(', ')}`);

let agree = 0, differ = 0;
const showReq = (r) => `op=${r.op} key=${H(r.key)} iv=${H(r.iv)} aad=${H(r.aad)} data=${H(r.data)}`;
cases.forEach((c, i) => {
  const answers = Object.entries(impls).filter(([, v]) => v.out[i] !== null).map(([n, v]) => [n, v.out[i]]);
  const distinct = new Set(answers.map(([, a]) => a));
  if (distinct.size <= 1) { agree++; return; }
  differ++;
  console.log(`DIFFER ${c.id}\n  input: ${showReq(c.req)}`);
  for (const [n, a] of answers) console.log(`  ${n}: ${a.length > 140 ? a.slice(0, 140) + '...' : a}`);
});

// Per implementation, per vector file.
let vectorFail = 0;
const files = [...new Set(cases.filter((c) => c.expect !== undefined).map((c) => c.file))];
console.log('aes-diff: published vectors (each line: one implementation, one file)');
for (const file of files) {
  const fc = cases.map((c, i) => [c, i]).filter(([c]) => c.file === file);
  for (const [n, v] of Object.entries(impls)) {
    let pass = 0, fail = 0, acceptable = 0, notApplicable = 0;
    for (const [c, i] of fc) {
      const a = v.out[i];
      if (a === null) { notApplicable++; continue; }
      if (c.expect === 'any') { acceptable++; continue; }
      if (a === c.expect) pass++;
      else {
        fail++;
        console.log(`  FAIL ${n} ${c.id}: expected ${c.expect.slice(0, 80)}, got ${a.slice(0, 80)}\n    input: ${showReq(c.req)}`);
      }
    }
    if (notApplicable === fc.length) continue;
    vectorFail += fail;
    const extra = [acceptable ? `${acceptable} acceptable (either answer)` : '', notRun[file] ? `${notRun[file]} vectors outside the profile not run` : '']
      .filter(Boolean).join('; ');
    console.log(`  ${file} [${n}]: ${pass} pass, ${fail} fail (out of ${pass + fail} checks)${extra ? '; ' + extra : ''}`);
  }
}

const T = cases.length;
console.log(`aes-diff: ${agree} agree, ${differ} differ (out of ${T})`);
console.log(`aes-diff: ${Object.keys(impls).length} implementations ran; ${Object.keys(unavailable).length} not available (counted apart: ${Object.keys(unavailable).join(', ') || 'none'})`);
process.exit(differ === 0 && vectorFail === 0 && missing.length === 0 ? 0 : 1);
