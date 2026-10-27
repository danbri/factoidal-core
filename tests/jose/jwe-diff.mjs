#!/usr/bin/env node
// jwe-diff.mjs — differential run of the Lean 4 JWE (L4Factoidal/JOSE/Jwe.lean,
// through the wasm ops jweEncrypt and jweDecrypt) against a second JWE
// written in this file from WebCrypto calls only (Node 22: OpenSSL)
// (https://github.com/danbri/factoidal/issues/1085).
//
// No npm dependency: `jose` is not in node_modules, and none is added. The
// JavaScript JWE below is TEST CODE, an independent reading of RFC 7516 and
// RFC 7518 (Concat KDF, CBC-HMAC, Key Wrap, ECDH-ES) to compare the engine
// against. It is not used by the package (iron rule 7 is about the package).
//
// For each round, each alg and enc pair, and each curve for ECDH-ES:
//   1. the wasm encrypts, the JavaScript JWE decrypts: the plaintext must match;
//   2. the JavaScript JWE encrypts, the wasm decrypts: the plaintext must match;
//   3. one bit changed in the JavaScript token's tag: the wasm must answer
//      "decryption failed", and the JavaScript JWE must refuse it too.
// The RFC 7518 Appendix C derivation is checked in the JavaScript JWE first,
// so a wrong KDF here cannot agree with a wrong KDF in Lean by chance.
//
// Exit codes: 0 all agree; 1 a difference; 77 the wasm engine is absent.
// Usage: node tests/jose/jwe-diff.mjs [rounds]   (default 5)

import { engine, callJwe, b64, unb64, b64u, unb64u } from './jwe-engine.mjs';

const ROUNDS = Number(process.argv[2] ?? 5);
const subtle = globalThis.crypto.subtle;
const rnd = (n) => globalThis.crypto.getRandomValues(new Uint8Array(n));
const enc8 = (s) => new TextEncoder().encode(s);
const cat = (...xs) => { const out = new Uint8Array(xs.reduce((n, x) => n + x.length, 0)); let o = 0; for (const x of xs) { out.set(x, o); o += x.length; } return out; };
const eq = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);
const u32 = (n) => new Uint8Array([n >>> 24, (n >>> 16) & 255, (n >>> 8) & 255, n & 255]);

if ((await engine()) === null) process.exit(77);

// ---------------------------------------------------------------- JS JWE
const ENC = {
  'A128GCM': { cek: 16, iv: 12 }, 'A256GCM': { cek: 32, iv: 12 },
  'A128CBC-HS256': { cek: 32, iv: 16, hash: 'SHA-256', t: 16 },
  'A256CBC-HS512': { cek: 64, iv: 16, hash: 'SHA-512', t: 32 },
};

async function concatKdf(z, algId, apu, apv, bits) {
  const other = cat(u32(algId.length), algId, u32(apu.length), apu, u32(apv.length), apv, u32(bits));
  const out = [];
  for (let c = 1; out.length * 32 < bits / 8; c++) {
    out.push(new Uint8Array(await subtle.digest('SHA-256', cat(u32(c), z, other))));
  }
  return cat(...out).slice(0, bits / 8);
}

async function contentEncrypt(enc, cek, iv, aad, pt) {
  const e = ENC[enc];
  if (!e.hash) {
    const key = await subtle.importKey('raw', cek, 'AES-GCM', false, ['encrypt']);
    const out = new Uint8Array(await subtle.encrypt({ name: 'AES-GCM', iv, additionalData: aad }, key, pt));
    return [out.slice(0, out.length - 16), out.slice(out.length - 16)];
  }
  const h = cek.length / 2;
  const ek = await subtle.importKey('raw', cek.slice(h), 'AES-CBC', false, ['encrypt']);
  const ct = new Uint8Array(await subtle.encrypt({ name: 'AES-CBC', iv }, ek, pt));
  const mk = await subtle.importKey('raw', cek.slice(0, h), { name: 'HMAC', hash: e.hash }, false, ['sign']);
  const al = new Uint8Array(8); new DataView(al.buffer).setBigUint64(0, BigInt(aad.length * 8));
  const mac = new Uint8Array(await subtle.sign('HMAC', mk, cat(aad, iv, ct, al)));
  return [ct, mac.slice(0, e.t)];
}

async function contentDecrypt(enc, cek, iv, aad, ct, tag) {
  const e = ENC[enc];
  if (!e.hash) {
    const key = await subtle.importKey('raw', cek, 'AES-GCM', false, ['decrypt']);
    return new Uint8Array(await subtle.decrypt({ name: 'AES-GCM', iv, additionalData: aad }, key, cat(ct, tag)));
  }
  const h = cek.length / 2;
  const mk = await subtle.importKey('raw', cek.slice(0, h), { name: 'HMAC', hash: e.hash }, false, ['sign']);
  const al = new Uint8Array(8); new DataView(al.buffer).setBigUint64(0, BigInt(aad.length * 8));
  const mac = new Uint8Array(await subtle.sign('HMAC', mk, cat(aad, iv, ct, al))).slice(0, e.t);
  if (!eq(mac, tag)) throw new Error('tag');
  const ek = await subtle.importKey('raw', cek.slice(h), 'AES-CBC', false, ['decrypt']);
  return new Uint8Array(await subtle.decrypt({ name: 'AES-CBC', iv }, ek, ct));
}

async function kwWrap(kek, cek) {
  const k = await subtle.importKey('raw', kek, 'AES-KW', false, ['wrapKey']);
  const inner = await subtle.importKey('raw', cek, { name: 'HMAC', hash: 'SHA-256' }, true, ['sign']);
  return new Uint8Array(await subtle.wrapKey('raw', inner, k, 'AES-KW'));
}
async function kwUnwrap(kek, ek) {
  const k = await subtle.importKey('raw', kek, 'AES-KW', false, ['unwrapKey']);
  const inner = await subtle.unwrapKey('raw', ek, k, 'AES-KW', { name: 'HMAC', hash: 'SHA-256' }, true, ['sign']);
  return new Uint8Array(await subtle.exportKey('raw', inner));
}

function curveAlg(jwk) { return jwk.kty === 'OKP' ? { name: 'X25519' } : { name: 'ECDH', namedCurve: 'P-256' }; }
const pubOnly = (j) => (j.kty === 'OKP' ? { kty: j.kty, crv: j.crv, x: j.x } : { kty: j.kty, crv: j.crv, x: j.x, y: j.y });

async function ecdhZ(privJwk, pubJwk) {
  const a = curveAlg(pubJwk);
  const priv = await subtle.importKey('jwk', privJwk, a, false, ['deriveBits']);
  const pub = await subtle.importKey('jwk', pubOnly(pubJwk), a, false, []);
  return new Uint8Array(await subtle.deriveBits({ name: a.name, public: pub }, priv, 256));
}

const kwBits = (alg) => (alg.endsWith('A128KW') ? 128 : alg.endsWith('A256KW') ? 256 : 0);

async function jsEncrypt(alg, enc, pubJwk, pt, extra = {}) {
  const e = ENC[enc];
  const header = { alg, enc, ...extra };
  let cek = rnd(e.cek); let ek = new Uint8Array(0);
  if (alg === 'dir') cek = unb64u(pubJwk.k);
  else if (alg === 'A128KW' || alg === 'A256KW') ek = await kwWrap(unb64u(pubJwk.k), cek);
  else if (alg.startsWith('RSA-OAEP')) {
    const key = await subtle.importKey('jwk', { kty: 'RSA', n: pubJwk.n, e: pubJwk.e },
      { name: 'RSA-OAEP', hash: alg === 'RSA-OAEP' ? 'SHA-1' : 'SHA-256' }, false, ['encrypt']);
    ek = new Uint8Array(await subtle.encrypt({ name: 'RSA-OAEP' }, key, cek));
  } else {
    const eph = await subtle.generateKey(curveAlg(pubJwk), true, ['deriveBits']);
    const ephPriv = await subtle.exportKey('jwk', eph.privateKey);
    header.epk = pubOnly(ephPriv);
    const z = await ecdhZ(ephPriv, pubJwk);
    const apu = extra.apu ? unb64u(extra.apu) : new Uint8Array(0);
    const apv = extra.apv ? unb64u(extra.apv) : new Uint8Array(0);
    if (alg === 'ECDH-ES') cek = await concatKdf(z, enc8(enc), apu, apv, e.cek * 8);
    else ek = await kwWrap(await concatKdf(z, enc8(alg), apu, apv, kwBits(alg)), cek);
  }
  const hb = b64u(enc8(JSON.stringify(header)));
  const iv = rnd(e.iv);
  const [ct, tag] = await contentEncrypt(enc, cek, iv, enc8(hb), pt);
  return [hb, b64u(ek), b64u(iv), b64u(ct), b64u(tag)].join('.');
}

async function jsDecrypt(token, privJwk) {
  const [hb, ekb, ivb, ctb, tagb] = token.split('.');
  const h = JSON.parse(Buffer.from(hb, 'base64url').toString());
  const e = ENC[h.enc];
  const ek = unb64u(ekb);
  let cek;
  if (h.alg === 'dir') cek = unb64u(privJwk.k);
  else if (h.alg === 'A128KW' || h.alg === 'A256KW') cek = await kwUnwrap(unb64u(privJwk.k), ek);
  else if (h.alg.startsWith('RSA-OAEP')) {
    const key = await subtle.importKey('jwk', { kty: 'RSA', n: privJwk.n, e: privJwk.e, d: privJwk.d,
      p: privJwk.p, q: privJwk.q, dp: privJwk.dp, dq: privJwk.dq, qi: privJwk.qi },
    { name: 'RSA-OAEP', hash: h.alg === 'RSA-OAEP' ? 'SHA-1' : 'SHA-256' }, false, ['decrypt']);
    cek = new Uint8Array(await subtle.decrypt({ name: 'RSA-OAEP' }, key, ek));
  } else {
    const z = await ecdhZ(privJwk, h.epk);
    const apu = h.apu ? unb64u(h.apu) : new Uint8Array(0);
    const apv = h.apv ? unb64u(h.apv) : new Uint8Array(0);
    if (h.alg === 'ECDH-ES') cek = await concatKdf(z, enc8(h.enc), apu, apv, e.cek * 8);
    else cek = await kwUnwrap(await concatKdf(z, enc8(h.alg), apu, apv, kwBits(h.alg)), ek);
  }
  return contentDecrypt(h.enc, cek, unb64u(ivb), enc8(hb), unb64u(ctb), unb64u(tagb));
}

// ---------------------------------------------------------------- checks
let agree = 0; let differ = 0;
function check(name, ok, detail = '') {
  if (ok) agree++;
  else { differ++; console.log(`  [DIFFER] ${name}${detail ? ' — ' + detail : ''}`); }
}

// The JavaScript KDF against RFC 7518 Appendix C.
{
  const z = new Uint8Array([158, 86, 217, 29, 129, 113, 53, 211, 114, 131, 66, 131, 191, 132,
    38, 156, 251, 49, 110, 163, 218, 128, 106, 72, 246, 218, 167, 121, 140, 254, 144, 196]);
  const k = await concatKdf(z, enc8('A128GCM'), enc8('Alice'), enc8('Bob'), 128);
  check('JavaScript Concat KDF = RFC 7518 Appendix C', b64u(k) === 'VqqN6vgjbSBcIijNcacQGg');
}

const ALGS = ['RSA-OAEP', 'RSA-OAEP-256', 'ECDH-ES', 'ECDH-ES+A128KW', 'ECDH-ES+A256KW', 'A128KW', 'A256KW', 'dir'];
// The engine's loader prefixes its name to an error message.
const isFailed = (r) => r.ok === false && /(^|: )jweDecrypt: decryption failed$/.test(r.error);

async function exportPair(k) {
  const clean = (j) => { delete j.key_ops; delete j.ext; delete j.alg; return j; };
  return [clean(await subtle.exportKey('jwk', k.publicKey)), clean(await subtle.exportKey('jwk', k.privateKey))];
}

for (let round = 0; round < ROUNDS; round++) {
  const rsa = await exportPair(await subtle.generateKey({ name: 'RSA-OAEP', modulusLength: 2048,
    publicExponent: new Uint8Array([1, 0, 1]), hash: 'SHA-256' }, true, ['encrypt', 'decrypt']));
  const ec = await exportPair(await subtle.generateKey({ name: 'ECDH', namedCurve: 'P-256' }, true, ['deriveBits']));
  const x = await exportPair(await subtle.generateKey({ name: 'X25519' }, true, ['deriveBits']));
  for (const alg of ALGS) {
    for (const enc of Object.keys(ENC)) {
      let pairs;
      if (alg.startsWith('RSA')) pairs = [rsa];
      else if (alg.startsWith('ECDH')) pairs = [ec, x];
      else {
        const n = alg === 'A128KW' ? 16 : alg === 'A256KW' ? 32 : ENC[enc].cek;
        const k = { kty: 'oct', k: b64u(rnd(n)) };
        pairs = [[k, k]];
      }
      for (const [pub, priv] of pairs) {
        const name = `#${round} ${alg} ${enc}${pub.crv ? ' ' + pub.crv : ''}`;
        const pt = rnd(Math.floor(Math.random() * 300));
        const extra = round % 2 === 1 && alg.startsWith('ECDH') ? { apu: b64u(rnd(9)), apv: b64u(enc8('Bob')) } : {};
        // 1. Lean encrypts, JavaScript decrypts.
        const le = await callJwe('jweEncrypt', { alg, enc, jwk: pub, plaintext: b64(pt), header: extra,
          random: b64(rnd(112)) });
        if (le.ok === true && le.token) {
          let out = null;
          try { out = await jsDecrypt(le.token, priv); } catch (err) { out = err; }
          check(`${name} lean-enc/js-dec`, out instanceof Uint8Array && eq(out, pt), String(out).slice(0, 100));
        } else check(`${name} lean-enc`, false, JSON.stringify(le).slice(0, 200));
        // 2. JavaScript encrypts, Lean decrypts.
        const jt = await jsEncrypt(alg, enc, pub, pt, extra);
        const ld = await callJwe('jweDecrypt', { token: jt, jwk: priv });
        check(`${name} js-enc/lean-dec`, ld.ok === true && eq(unb64(ld.plaintext), pt), JSON.stringify(ld).slice(0, 200));
        // 3. One bit of the tag changed: both refuse.
        const ps = jt.split('.'); const t = unb64u(ps[4]); t[t.length - 1] ^= 0x80; ps[4] = b64u(t);
        const bad = ps.join('.');
        const lb = await callJwe('jweDecrypt', { token: bad, jwk: priv });
        let jsRefused = false;
        try { await jsDecrypt(bad, priv); } catch { jsRefused = true; }
        check(`${name} tag changed`, isFailed(lb) && jsRefused, JSON.stringify(lb));
      }
    }
  }
}

console.log(`jwe-diff: ${agree} agree, ${differ} differ (out of ${agree + differ})`);
process.exit(differ === 0 ? 0 : 1);
