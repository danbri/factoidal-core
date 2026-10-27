#!/usr/bin/env node
// jwe-wasm.mjs — JWE (RFC 7516) through the Lean wasm ops `jweDecrypt` and
// `jweEncrypt`, with every AES request answered by WebCrypto
// (https://github.com/danbri/factoidal/issues/1085).
//
// Sections:
//   vectors     tests/jose/jwe-vectors.json: RFC 7516 Appendix A and RFC 7520
//               section 5 compact serializations, ALL of them (Key Wrap and
//               AES-CBC included, which the native probe cannot run).
//   rfc7518-b   the AES-CBC half of RFC 7518 Appendix B.1 and B.3: the host's
//               answer to the request the engine makes gives the vector's E.
//               (The HMAC half is a #guard in L4Factoidal/JOSE/JweTests.lean.)
//   rfc7518-c   a token from Alice's ephemeral key (Appendix C) that the wasm
//               decrypts with Bob's key.
//   round-trip  every alg and enc pair, random keys and plaintexts, encrypt
//               then decrypt in the wasm; one changed bit in each part gives
//               "decryption failed"; a CBC-HMAC tag change makes no
//               aes-cbc-decrypt request.
//
// Exit codes: 0 no failure; 1 a failure; 77 the wasm engine is absent.
//
// Usage: node tests/jose/jwe-wasm.mjs [rounds]   (default 3)

import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { answerCipherRequest } from '../../npm/factoidal/lib/cipher-host.mjs';
import { engine, callJwe, repoRoot, b64, unb64, b64u, unb64u } from './jwe-engine.mjs';

const ROUNDS = Number(process.argv[2] ?? 3);
const subtle = globalThis.crypto.subtle;
const rnd = (n) => globalThis.crypto.getRandomValues(new Uint8Array(n));
const enc8 = (s) => new TextEncoder().encode(s);
const eq = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);

if ((await engine()) === null) process.exit(77);

const score = {};
let failures = 0;
function check(section, name, ok, detail = '') {
  score[section] ??= { pass: 0, fail: 0 };
  if (ok) score[section].pass++;
  else {
    score[section].fail++; failures++;
    console.log(`  [FAIL] ${section}: ${name}${detail ? ' — ' + detail : ''}`);
  }
}
// The engine's loader prefixes its name to an error message.
const isFailed = (r) => r.ok === false && /(^|: )jweDecrypt: decryption failed$/.test(r.error);

// ---- vectors
const vectors = JSON.parse(readFileSync(resolve(repoRoot, 'tests/jose/jwe-vectors.json'), 'utf8'));
for (const c of vectors.cases) {
  const r = await callJwe('jweDecrypt', { token: c.token, jwk: c.jwk });
  if (c.expect === 'ok') {
    const ok = r.ok === true && r.plaintext !== undefined &&
      Buffer.from(unb64(r.plaintext)).toString('utf8') === c.plaintext;
    check('vectors', c.name, ok, JSON.stringify(r).slice(0, 200));
  } else if (c.expect === 'refused') {
    check('vectors', c.name, r.ok === false && !isFailed(r) && /not allowed|refused/.test(r.error),
      JSON.stringify(r).slice(0, 200));
  } else {
    // 'failed': an allowed alg with a key this tree does not take.
    check('vectors', c.name, r.ok === false && (isFailed(r) || /"jwk" is not/.test(r.error)),
      JSON.stringify(r).slice(0, 200));
  }
}

// ---- RFC 7518 Appendix B, the AES-CBC half
const hex = (s) => new Uint8Array(Buffer.from(s.replace(/\s+/g, ''), 'hex'));
const P = enc8('A cipher system must not be required to be secret, and it must be able ' +
  'to fall into the hands of the enemy without inconvenience');
const IV = hex('1af38c2dc2b96ffdd866940923 41bc04');
const B = [
  ['B.1', hex('101112131415161718191a1b1c1d1e1f'),
    hex('c80edfa32ddf39d5ef00c0b468834279a2e46a1b8049f792f76bfe54b903a9c9a94ac9b47ad2655c5f10f9aef71427e2' +
        'fc6f9b3f399a221489f16362c703233609d45ac69864e3321cf82935ac4096c86e133314c54019e8ca7980dfa4b9cf1b' +
        '384c486f3a54c51078158ee5d79de59fbd34d848b3d69550a67646344427ade54b8851ffb598f7f80074b9473c82e2db')],
  ['B.3', hex('202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f'),
    hex('4affaaadb78c31c5da4b1b590d10ffbd3dd8d5d302423526912da037ecbcc7bd822c301dd67c373bccb584ad3e9279c2' +
        'e6d12a1374b77f077553df829410446b36ebd97066296ae6427ea75c2e0846a11a09ccf5370dc80bfecbad28c73f09b3' +
        'a3b75e662a2594410ae496b2e2e6609e31e6e02cc837f053d21f37ff4f51950bbe2638d09dd7a4930930806d0703b1f6')],
];
for (const [name, encKey, E] of B) {
  const a = await answerCipherRequest({ op: 'aes-cbc-encrypt', key: b64(encKey), iv: b64(IV), aad: '', data: b64(P) });
  check('rfc7518-b', `${name} AES-CBC(ENC_KEY, IV, P) = E`, a.ok !== undefined && eq(unb64(a.ok), E));
  const d = await answerCipherRequest({ op: 'aes-cbc-decrypt', key: b64(encKey), iv: b64(IV), aad: '', data: b64(E) });
  check('rfc7518-b', `${name} AES-CBC decrypt(E) = P`, d.ok !== undefined && eq(unb64(d.ok), P));
}

// ---- RFC 7518 Appendix C
const alice = { x: 'gI0GAILBdu7T53akrFmMyGcsF3n5dO7MmwNBHKW5SV0', d: '0_NxaRPUMQoAJt50Gz8YiTr8gRTwyEaCumd-MToTmIo' };
const bob = { kty: 'EC', crv: 'P-256', x: 'weNJy2HscCSM6AEDTDg04biOvhFhyyWvOHQfeF_PxMQ',
  y: 'e8lnCO-AlStT-NJVX-crhB7QRYhiix03illJOVAOyck', d: 'VEmDZpDXXK8p8N0Cndsxs924q6nS1RXFASRl6BfUqdw' };
{
  const random = new Uint8Array([...rnd(12), ...unb64u(alice.d)]);
  const bobPub = { kty: 'EC', crv: 'P-256', x: bob.x, y: bob.y };
  const e = await callJwe('jweEncrypt', { alg: 'ECDH-ES', enc: 'A128GCM', jwk: bobPub,
    plaintext: b64(enc8('Appendix C')), header: { apu: 'QWxpY2U', apv: 'Qm9i' }, random: b64(random) });
  check('rfc7518-c', 'Alice encrypts to Bob', e.ok === true && typeof e.token === 'string', JSON.stringify(e));
  if (e.token) {
    const h = JSON.parse(Buffer.from(e.token.split('.')[0], 'base64url').toString());
    check('rfc7518-c', 'epk is Alice\'s public key', h.epk && h.epk.x === alice.x);
    // The derived CEK of Appendix C, used directly as an AES-128-GCM key, opens the token.
    const [hb, , iv, ct, tag] = e.token.split('.');
    let opened = false;
    try {
      const key = await subtle.importKey('raw', unb64u('VqqN6vgjbSBcIijNcacQGg'), 'AES-GCM', false, ['decrypt']);
      const pt = await subtle.decrypt({ name: 'AES-GCM', iv: unb64u(iv), additionalData: enc8(hb) }, key,
        new Uint8Array([...unb64u(ct), ...unb64u(tag)]));
      opened = Buffer.from(pt).toString() === 'Appendix C';
    } catch { opened = false; }
    check('rfc7518-c', 'the CEK is VqqN6vgjbSBcIijNcacQGg', opened);
    const d = await callJwe('jweDecrypt', { token: e.token, jwk: bob });
    check('rfc7518-c', 'Bob decrypts', d.ok === true && Buffer.from(unb64(d.plaintext)).toString() === 'Appendix C');
  }
}

// ---- round trips
const ALGS = ['RSA-OAEP', 'RSA-OAEP-256', 'ECDH-ES', 'ECDH-ES+A128KW', 'ECDH-ES+A256KW', 'A128KW', 'A256KW', 'dir'];
const ENCS = { 'A128GCM': 16, 'A256GCM': 32, 'A128CBC-HS256': 32, 'A256CBC-HS512': 64 };

async function keyPairs() {
  const rsa = await subtle.generateKey({ name: 'RSA-OAEP', modulusLength: 2048,
    publicExponent: new Uint8Array([1, 0, 1]), hash: 'SHA-256' }, true, ['encrypt', 'decrypt']);
  const ec = await subtle.generateKey({ name: 'ECDH', namedCurve: 'P-256' }, true, ['deriveBits']);
  const x = await subtle.generateKey({ name: 'X25519' }, true, ['deriveBits']);
  const pub = async (k) => { const j = await subtle.exportKey('jwk', k.publicKey); delete j.key_ops; delete j.ext; return j; };
  const priv = async (k) => { const j = await subtle.exportKey('jwk', k.privateKey); delete j.key_ops; delete j.ext; return j; };
  return { rsa: [await pub(rsa), await priv(rsa)], ec: [await pub(ec), await priv(ec)], x: [await pub(x), await priv(x)] };
}
function octFor(alg, enc) {
  const n = alg === 'A128KW' ? 16 : alg === 'A256KW' ? 32 : ENCS[enc];
  const k = { kty: 'oct', k: b64u(rnd(n)) };
  return [k, k];
}
function flip(token, part) {
  const ps = token.split('.');
  const b = unb64u(ps[part]);
  if (b.length === 0) return null;
  b[0] ^= 1;
  ps[part] = b64u(b);
  return ps.join('.');
}

for (let round = 0; round < ROUNDS; round++) {
  const kp = await keyPairs();
  for (const alg of ALGS) {
    for (const enc of Object.keys(ENCS)) {
      const pairs = alg.startsWith('RSA') ? [kp.rsa] : alg.startsWith('ECDH') ? [kp.ec, kp.x] : [octFor(alg, enc)];
      for (const [pubJwk, privJwk] of pairs) {
        const name = `#${round} ${alg} ${enc}${pubJwk.crv ? ' ' + pubJwk.crv : ''}`;
        const pt = rnd(Math.floor(Math.random() * 100));
        const e = await callJwe('jweEncrypt', { alg, enc, jwk: pubJwk, plaintext: b64(pt),
          header: { kid: `k${round}` }, random: b64(rnd(112)) });
        if (!(e.ok === true && e.token)) { check('round-trip', name + ' encrypt', false, JSON.stringify(e)); continue; }
        const d = await callJwe('jweDecrypt', { token: e.token, jwk: privJwk });
        check('round-trip', name, d.ok === true && eq(unb64(d.plaintext), pt), JSON.stringify(d).slice(0, 200));
        // Part 0 (the header) is covered by the Lean #guards: a flipped octet
        // there is usually not JSON, a refusal before the key.
        for (const part of [1, 2, 3, 4]) {
          const bad = flip(e.token, part);
          if (bad === null) continue;
          const seen = [];
          const r = await callJwe('jweDecrypt', { token: bad, jwk: privJwk }, seen);
          check('round-trip', `${name} part ${part} changed`, isFailed(r), JSON.stringify(r).slice(0, 200));
          if (enc.includes('CBC') && part === 4) {
            check('round-trip', `${name} tag changed: no aes-cbc-decrypt request`,
              !seen.some((q) => q.op === 'aes-cbc-decrypt'));
          }
        }
      }
    }
  }
}

let pass = 0; let fail = 0;
for (const [s, t] of Object.entries(score)) {
  console.log(`${s}: ${t.pass} pass, ${t.fail} fail (out of ${t.pass + t.fail})`);
  pass += t.pass; fail += t.fail;
}
console.log(`TOTAL: ${pass} pass, ${fail} fail (out of ${pass + fail})`);
process.exit(failures === 0 ? 0 : 1);
