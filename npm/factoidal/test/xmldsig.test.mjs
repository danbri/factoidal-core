// The package functions xmlVerify and xmlSign (XML Signature 1.1,
// https://github.com/danbri/factoidal/issues/1165, track B, item 4). Every
// decision is in Lean (formal/lean4/Wasm/Ops/XmlDsig.lean). Each signed
// document is checked by node:crypto too: the signature value over the
// canonical ds:SignedInfo the engine reports, and each DigestValue over the
// reference octets it reports.

import test from 'node:test';
import assert from 'node:assert/strict';
import { generateKeyPairSync, createHash, createHmac, verify as nodeVerify, randomBytes } from 'node:crypto';
import { xmlVerify, xmlSign, FactoidalError } from '../index.mjs';

const DS = 'http://www.w3.org/2000/09/xmldsig#';
const MORE = 'http://www.w3.org/2001/04/xmldsig-more#';
const DOC = '<doc xmlns="urn:example:doc" ID="d1"><item n="1">one &amp; two</item></doc>';

const rsa = generateKeyPairSync('rsa', { modulusLength: 2048 });
const rsaPrivate = rsa.privateKey.export({ format: 'jwk' });
const rsaPublic = rsa.publicKey.export({ format: 'jwk' });
const ec = generateKeyPairSync('ec', { namedCurve: 'P-256' });
const ecPrivate = ec.privateKey.export({ format: 'jwk' });
const ecPublic = ec.publicKey.export({ format: 'jwk' });
const macKey = randomBytes(32);
const macJwk = { kty: 'oct', k: macKey.toString('base64url') };

const signatureValue = (doc) =>
  Buffer.from(/<ds:SignatureValue[^>]*>([^<]*)<\/ds:SignatureValue>/.exec(doc)[1].replace(/\s+/g, ''), 'base64');
const digestValues = (doc) =>
  [...doc.matchAll(/<ds:DigestValue>([^<]*)<\/ds:DigestValue>/g)].map((m) => m[1].replace(/\s+/g, ''));

// Digest of each reference by node:crypto equals the document's DigestValue.
function checkDigests(doc, references, hash) {
  assert.ok(references.length > 0);
  const want = digestValues(doc);
  assert.equal(want.length, references.length);
  references.forEach((r, i) => {
    assert.ok(r.octets instanceof Uint8Array);
    assert.equal(createHash(hash).update(r.octets).digest('base64'), want[i]);
  });
}

async function rejectsWith(promise, pattern) {
  await assert.rejects(promise, (e) => e instanceof FactoidalError && pattern.test(e.message));
}

test('xmlSign with an RSA key (defaults), xmlVerify, and node:crypto agree', async () => {
  const { document } = await xmlSign(DOC, { key: rsaPrivate });
  assert.match(document, /rsa-sha256/);
  assert.match(document, /xml-exc-c14n#/);
  const v = await xmlVerify(document);
  assert.equal(v.valid, true);
  assert.equal(v.key.kty, 'RSA');
  assert.equal(v.key.n, rsaPublic.n);
  assert.equal(v.certificate, null);
  assert.ok(v.signedInfo.startsWith('<ds:SignedInfo'));
  assert.ok(nodeVerify('sha256', Buffer.from(v.signedInfo, 'utf8'), rsa.publicKey, signatureValue(document)));
  checkDigests(document, v.references, 'sha256');
  // The same with the caller's key, and with no key at all.
  assert.equal((await xmlVerify(document, { key: rsaPublic, keyFromKeyInfo: false })).valid, true);
  const none = await xmlVerify(document, { keyFromKeyInfo: false });
  assert.equal(none.valid, false);
  assert.match(none.reason, /no key/);
});

test('xmlSign ecdsa-sha384 at P-256 over #d1 with C14N 1.1; node:crypto checks the signature', async () => {
  const { document } = await xmlSign(DOC, {
    key: ecPrivate,
    signatureMethod: MORE + 'ecdsa-sha384',
    references: [{
      uri: '#d1',
      transforms: [DS + 'enveloped-signature', 'http://www.w3.org/2006/12/xml-c14n11'],
      digestMethod: 'http://www.w3.org/2001/04/xmldsig-more#sha384'
    }]
  });
  assert.match(document, /ECKeyValue/);
  const v = await xmlVerify(document, { key: ecPublic });
  assert.equal(v.valid, true);
  assert.ok(nodeVerify('sha384', Buffer.from(v.signedInfo, 'utf8'),
    { key: ec.publicKey, dsaEncoding: 'ieee-p1363' }, signatureValue(document)));
  checkDigests(document, v.references, 'sha384');
  // Two signatures of one document differ: a fresh nonce for each call.
  const again = await xmlSign(DOC, { key: ecPrivate });
  const once = await xmlSign(DOC, { key: ecPrivate });
  assert.notEqual(signatureValue(again.document).toString('hex'), signatureValue(once.document).toString('hex'));
});

test('xmlSign hmac-sha256 enveloping; xmlVerify with hmacKey; node:crypto computes the same HMAC', async () => {
  const { document } = await xmlSign('', {
    key: macJwk,
    enveloping: { id: 'obj', content: '<item xmlns="urn:example:doc">one</item>' }
  });
  assert.ok(document.startsWith('<ds:Signature'));
  const v = await xmlVerify(document, { hmacKey: new Uint8Array(macKey) });
  assert.equal(v.valid, true);
  assert.equal(v.key, null);
  assert.deepEqual(signatureValue(document), createHmac('sha256', macKey).update(v.signedInfo, 'utf8').digest());
  checkDigests(document, v.references, 'sha256');
  const wrong = await xmlVerify(document, { hmacKey: new Uint8Array(32) });
  assert.equal(wrong.valid, false);
});

test('a changed document, a changed signature value and the wrong key do not validate', async () => {
  const { document } = await xmlSign(DOC, { key: rsaPrivate });
  const changed = await xmlVerify(document.replace('one &amp; two', 'One &amp; two'));
  assert.equal(changed.valid, false);
  assert.equal(typeof changed.reason, 'string');
  const sv = signatureValue(document);
  sv[sv.length - 1] ^= 1;
  const badValue = document.replace(/(<ds:SignatureValue[^>]*>)[^<]*/, `$1${sv.toString('base64')}`);
  assert.equal((await xmlVerify(badValue)).valid, false);
  const other = generateKeyPairSync('rsa', { modulusLength: 2048 }).publicKey.export({ format: 'jwk' });
  assert.equal((await xmlVerify(document, { key: other, keyFromKeyInfo: false })).valid, false);
});

test('refusals: a method of another key kind, DSA, wrong arguments', async () => {
  await rejectsWith(xmlSign(DOC, { key: rsaPrivate, signatureMethod: MORE + 'hmac-sha256' }), /kind of key/);
  await rejectsWith(xmlSign(DOC, { key: rsaPrivate, signatureMethod: DS + 'dsa-sha1' }), /1224/);
  await rejectsWith(xmlVerify(DOC, { key: { kty: 'EC', crv: 'P-192' } }), /P-256/);
  await assert.rejects(xmlSign(DOC, {}), TypeError);
  await assert.rejects(xmlVerify(42), TypeError);
  await assert.rejects(xmlVerify(DOC, { hmacKey: 'secret' }), TypeError);
  await assert.rejects(xmlVerify(DOC, { certificates: 'x' }), TypeError);
});
