// The package functions xmlDecrypt, xmlEncrypt, jweDecrypt and jweEncrypt
// (https://github.com/danbri/factoidal/issues/1084,
// https://github.com/danbri/factoidal/issues/1085): AES through WebCrypto,
// everything else in the wasm. Cross-checks use node:crypto only, so each
// direction is checked by a second implementation.

import test from 'node:test';
import assert from 'node:assert/strict';
import {
  generateKeyPairSync, createCipheriv, createDecipheriv, publicEncrypt, privateDecrypt,
  constants, randomBytes
} from 'node:crypto';
import { xmlDecrypt, xmlEncrypt, jweDecrypt, jweEncrypt, FactoidalError } from '../index.mjs';

const rsa = generateKeyPairSync('rsa', { modulusLength: 2048 });
const rsaPublic = { ...rsa.publicKey.export({ format: 'jwk' }), kid: 'rsa-1' };
const rsaPrivate = { ...rsa.privateKey.export({ format: 'jwk' }), kid: 'rsa-1' };
const ec = generateKeyPairSync('ec', { namedCurve: 'P-256' });
const ecPublic = ec.publicKey.export({ format: 'jwk' });
const ecPrivate = ec.privateKey.export({ format: 'jwk' });

const DOC = '<r xmlns="urn:x"><a k="1">text &amp; more</a><b/></r>';
const b64u = (b) => Buffer.from(b).toString('base64url');

async function rejectsWith(promise, pattern) {
  await assert.rejects(promise, (e) => e instanceof FactoidalError && pattern.test(e.message));
}

test('xmlEncrypt then xmlDecrypt (RSA-OAEP, AES-128-GCM) gives the canonical form of the input', async () => {
  const enc = await xmlEncrypt(DOC, { recipient: rsaPublic });
  assert.match(enc.document, /EncryptedData/);
  assert.doesNotMatch(enc.document, /text &amp; more/);
  const plain = await xmlDecrypt(DOC, { keys: [] });
  const dec = await xmlDecrypt(enc.document, { keys: [rsaPrivate] });
  assert.equal(dec.canonical, plain.canonical);
});

test('xmlEncrypt then xmlDecrypt (ECDH-ES P-256, kw-aes256, AES-256-GCM, content only)', async () => {
  const enc = await xmlEncrypt(DOC, { recipient: ecPublic, algorithm: 'aes256-gcm', keyWrap: 'kw-aes256', content: true });
  const dec = await xmlDecrypt(enc.document, { keys: [ecPrivate] });
  assert.equal(dec.canonical, (await xmlDecrypt(DOC, { keys: [] })).canonical);
});

test('xmlDecrypt reads an EncryptedData made by node:crypto (rsa-oaep-mgf1p, aes128-gcm)', async () => {
  const cek = randomBytes(16);
  const iv = randomBytes(12);
  const c = createCipheriv('aes-128-gcm', cek, iv);
  const ct = Buffer.concat([iv, c.update(DOC, 'utf8'), c.final(), c.getAuthTag()]);
  const ek = publicEncrypt({ key: rsa.publicKey, padding: constants.RSA_PKCS1_OAEP_PADDING, oaepHash: 'sha1' }, cek);
  const X = 'http://www.w3.org/2001/04/xmlenc#';
  const doc = `<xenc:EncryptedData xmlns:xenc="${X}" Type="${X}Element">` +
    '<xenc:EncryptionMethod Algorithm="http://www.w3.org/2009/xmlenc11#aes128-gcm"/>' +
    '<ds:KeyInfo xmlns:ds="http://www.w3.org/2000/09/xmldsig#"><xenc:EncryptedKey>' +
    `<xenc:EncryptionMethod Algorithm="${X}rsa-oaep-mgf1p"/>` +
    `<xenc:CipherData><xenc:CipherValue>${ek.toString('base64')}</xenc:CipherValue></xenc:CipherData>` +
    '</xenc:EncryptedKey></ds:KeyInfo>' +
    `<xenc:CipherData><xenc:CipherValue>${ct.toString('base64')}</xenc:CipherValue></xenc:CipherData></xenc:EncryptedData>`;
  const dec = await xmlDecrypt(doc, { keys: [rsaPrivate] });
  assert.equal(dec.canonical, (await xmlDecrypt(DOC, { keys: [] })).canonical);
  // One changed ciphertext octet: the one decryption error.
  const bad = doc.replace(ct.toString('base64'), Buffer.from(ct.map((x, i) => (i === ct.length - 1 ? x ^ 1 : x))).toString('base64'));
  await rejectsWith(xmlDecrypt(bad, { keys: [rsaPrivate] }), /XML decryption failed/);
});

test('xmlDecrypt with the wrong key gives the one decryption error', async () => {
  const enc = await xmlEncrypt(DOC, { recipient: rsaPublic });
  const other = { ...generateKeyPairSync('rsa', { modulusLength: 2048 }).privateKey.export({ format: 'jwk' }), kid: 'rsa-1' };
  await rejectsWith(xmlDecrypt(enc.document, { keys: [other] }), /XML decryption failed/);
});

test('jweEncrypt then jweDecrypt: RSA-OAEP-256 A256GCM and ECDH-ES+A128KW A128CBC-HS256', async () => {
  for (const [alg, enc, pub, priv] of [
    ['RSA-OAEP-256', 'A256GCM', rsaPublic, rsaPrivate],
    ['ECDH-ES+A128KW', 'A128CBC-HS256', ecPublic, ecPrivate],
    ['ECDH-ES', 'A128GCM', ecPublic, ecPrivate]
  ]) {
    const token = await jweEncrypt('Live long and prosper.', { alg, enc, jwk: pub });
    assert.equal(token.split('.').length, 5);
    const out = await jweDecrypt(token, { jwk: priv });
    assert.equal(out.header.alg, alg);
    assert.equal(out.header.enc, enc);
    assert.equal(new TextDecoder().decode(out.plaintext), 'Live long and prosper.');
  }
});

test('jweEncrypt output (RSA-OAEP-256, A256GCM) decrypts with node:crypto', async () => {
  const bytes = randomBytes(300);
  const token = await jweEncrypt(new Uint8Array(bytes), { alg: 'RSA-OAEP-256', enc: 'A256GCM', jwk: rsaPublic });
  const [h, ek, iv, ct, tag] = token.split('.');
  const cek = privateDecrypt({ key: rsa.privateKey, padding: constants.RSA_PKCS1_OAEP_PADDING, oaepHash: 'sha256' },
    Buffer.from(ek, 'base64url'));
  const d = createDecipheriv('aes-256-gcm', cek, Buffer.from(iv, 'base64url'));
  d.setAAD(Buffer.from(h, 'ascii'));
  d.setAuthTag(Buffer.from(tag, 'base64url'));
  const pt = Buffer.concat([d.update(Buffer.from(ct, 'base64url')), d.final()]);
  assert.deepEqual(pt, bytes);
});

test('jweDecrypt reads a JWE made by node:crypto (RSA-OAEP, A128GCM); a changed tag is refused', async () => {
  const header = b64u(JSON.stringify({ alg: 'RSA-OAEP', enc: 'A128GCM' }));
  const cek = randomBytes(16);
  const iv = randomBytes(12);
  const c = createCipheriv('aes-128-gcm', cek, iv);
  c.setAAD(Buffer.from(header, 'ascii'));
  const ct = Buffer.concat([c.update('node made this', 'utf8'), c.final()]);
  const tag = c.getAuthTag();
  const ek = publicEncrypt({ key: rsa.publicKey, padding: constants.RSA_PKCS1_OAEP_PADDING, oaepHash: 'sha1' }, cek);
  const token = [header, b64u(ek), b64u(iv), b64u(ct), b64u(tag)].join('.');
  const out = await jweDecrypt(token, { jwk: rsaPrivate });
  assert.equal(new TextDecoder().decode(out.plaintext), 'node made this');
  tag[0] ^= 1;
  await rejectsWith(jweDecrypt([header, b64u(ek), b64u(iv), b64u(ct), b64u(tag)].join('.'), { jwk: rsaPrivate }),
    /decryption failed/);
});

test('jweDecrypt refuses RSA1_5 before any key is used', async () => {
  const header = b64u(JSON.stringify({ alg: 'RSA1_5', enc: 'A128GCM' }));
  await rejectsWith(jweDecrypt(`${header}.AA.AA.AA.AA`, { jwk: rsaPrivate }), /RSA1_5/);
});

test('argument checks', async () => {
  await assert.rejects(xmlDecrypt(1, { keys: [] }), TypeError);
  await assert.rejects(xmlDecrypt(DOC, {}), TypeError);
  await assert.rejects(xmlEncrypt(DOC, {}), TypeError);
  await assert.rejects(jweDecrypt('x', {}), TypeError);
  await assert.rejects(jweEncrypt(5, { alg: 'dir', enc: 'A128GCM', jwk: {} }), TypeError);
});
