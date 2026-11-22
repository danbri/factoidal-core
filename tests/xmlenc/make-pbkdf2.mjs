// Writes tests/xmlenc/pbkdf2.json: XML Encryption 1.1 documents whose key
// agreement uses the PBKDF2 key derivation method (§5.4.2,
// https://www.w3.org/TR/xmlenc-core1/#sec-PBKDF2), made with Node's crypto
// (OpenSSL), independent of the Lean engine. Track B item 5 of
// https://github.com/danbri/factoidal/issues/1165.
//
//   node tests/xmlenc/make-pbkdf2.mjs > tests/xmlenc/pbkdf2.json
//
// Keys, salts, IVs and content keys are fresh random values each run; the
// file holds the keys (test keys only) and, for each case, the expected
// document and the key encryption key PBKDF2 gives (hex), so the native Lean
// probe can check the derived key of a case whose AES Key Wrap is host-only.
import crypto from 'node:crypto';

const XENC = 'http://www.w3.org/2001/04/xmlenc#';
const XENC11 = 'http://www.w3.org/2009/xmlenc11#';
const DS = 'http://www.w3.org/2000/09/xmldsig#';
const DSIG11 = 'http://www.w3.org/2009/xmldsig11#';
const PRF = {
  sha1: 'http://www.w3.org/2000/09/xmldsig#hmac-sha1',
  sha256: 'http://www.w3.org/2001/04/xmldsig-more#hmac-sha256',
  sha384: 'http://www.w3.org/2001/04/xmldsig-more#hmac-sha384',
  sha512: 'http://www.w3.org/2001/04/xmldsig-more#hmac-sha512',
  sha224: 'http://www.w3.org/2001/04/xmldsig-more#hmac-sha224',
};
const plainEl = '<a xmlns="urn:x"><b>secret é</b></a>';
const wrapDoc = (inner) => `<r xmlns="urn:r"><keep>1</keep>${inner}</r>`;

const p256 = crypto.generateKeyPairSync('ec', { namedCurve: 'P-256' });
const x25519 = crypto.generateKeyPairSync('x25519');
const keys = [
  { ...p256.privateKey.export({ format: 'jwk' }), kid: 'ec-pbkdf2' },
  { ...x25519.privateKey.export({ format: 'jwk' }), kid: 'x-pbkdf2' },
];

function gcm(cek, data) {
  const iv = crypto.randomBytes(12);
  const c = crypto.createCipheriv(`aes-${cek.length * 8}-gcm`, cek, iv);
  const ct = Buffer.concat([c.update(data), c.final()]);
  return Buffer.concat([iv, ct, c.getAuthTag()]);
}
function kwWrap(kek, cek) {
  const c = crypto.createCipheriv(`id-aes${kek.length * 8}-wrap`, kek, Buffer.from('A6A6A6A6A6A6A6A6', 'hex'));
  return Buffer.concat([c.update(cek), c.final()]);
}

/** Ephemeral-static agreement: the originator element and Z. */
function agree(curve) {
  if (curve === 'p256') {
    const e = crypto.generateKeyPairSync('ec', { namedCurve: 'P-256' });
    const z = crypto.diffieHellman({ privateKey: e.privateKey, publicKey: p256.publicKey });
    const jwk = e.publicKey.export({ format: 'jwk' });
    const pt = Buffer.concat([Buffer.from([4]), Buffer.from(jwk.x, 'base64url'), Buffer.from(jwk.y, 'base64url')]);
    return { z, orig: `<ds:KeyValue><dsig11:ECKeyValue xmlns:dsig11="${DSIG11}"><dsig11:NamedCurve URI="urn:oid:1.2.840.10045.3.1.7"/><dsig11:PublicKey>${pt.toString('base64')}</dsig11:PublicKey></dsig11:ECKeyValue></ds:KeyValue>` };
  }
  const e = crypto.generateKeyPairSync('x25519');
  const z = crypto.diffieHellman({ privateKey: e.privateKey, publicKey: x25519.publicKey });
  const spki = e.publicKey.export({ format: 'der', type: 'spki' });
  return { z, orig: `<dsig11:DEREncodedKeyValue xmlns:dsig11="${DSIG11}">${spki.toString('base64')}</dsig11:DEREncodedKeyValue>` };
}

/** The PBKDF2-params element; `mutate` may change any of its parts. */
function params({ salt, iterations, keyLength, prf }, mutate = {}) {
  const saltEl = mutate.saltEl ?? `<xenc11:Salt><xenc11:Specified>${salt.toString('base64')}</xenc11:Specified></xenc11:Salt>`;
  const itEl = `<xenc11:IterationCount>${mutate.iterations ?? iterations}</xenc11:IterationCount>`;
  const lenEl = `<xenc11:KeyLength>${mutate.keyLength ?? keyLength}</xenc11:KeyLength>`;
  const prfEl = `<xenc11:PRF Algorithm="${PRF[mutate.prf ?? prf]}"/>`;
  const seq = mutate.swap ? [saltEl, lenEl, itEl, prfEl] : [saltEl, itEl, lenEl, prfEl];
  return `<xenc11:KeyDerivationMethod xmlns:xenc11="${XENC11}" Algorithm="${XENC11}pbkdf2"><xenc11:PBKDF2-params>${seq.join('')}</xenc11:PBKDF2-params></xenc11:KeyDerivationMethod>`;
}

/**
 * One document. `wrap`: the key wrap size (16 or 32), or 0 for direct key
 * agreement (the derived key is the content key).
 */
function make({ name, curve, agreement, prf, iterations, wrap, cekLen, mutate, outcome, reason }) {
  const { z, orig } = agree(curve);
  const keyLength = wrap || cekLen;
  const salt = crypto.randomBytes(16);
  const kek = crypto.pbkdf2Sync(z, salt, iterations, keyLength, prf === 'sha224' ? 'sha256' : prf);
  const cek = wrap ? crypto.randomBytes(cekLen) : kek;
  const am = `<xenc:AgreementMethod Algorithm="${agreement}">${params({ salt, iterations, keyLength, prf }, mutate)}<xenc:OriginatorKeyInfo>${orig}</xenc:OriginatorKeyInfo><xenc:RecipientKeyInfo><ds:KeyName>${curve === 'p256' ? 'ec-pbkdf2' : 'x-pbkdf2'}</ds:KeyName></xenc:RecipientKeyInfo></xenc:AgreementMethod>`;
  const keyInfo = wrap
    ? `<xenc:EncryptedKey><xenc:EncryptionMethod Algorithm="${XENC}kw-aes${wrap * 8}"/><ds:KeyInfo>${am}</ds:KeyInfo><xenc:CipherData><xenc:CipherValue>${kwWrap(kek, cek).toString('base64')}</xenc:CipherValue></xenc:CipherData></xenc:EncryptedKey>`
    : am;
  const ed = `<xenc:EncryptedData xmlns:xenc="${XENC}" xmlns:ds="${DS}" Type="${XENC}Element"><xenc:EncryptionMethod Algorithm="http://www.w3.org/2009/xmlenc11#aes${cekLen * 8}-gcm"/><ds:KeyInfo>${keyInfo}</ds:KeyInfo><xenc:CipherData><xenc:CipherValue>${gcm(cek, Buffer.from(plainEl, 'utf8')).toString('base64')}</xenc:CipherValue></xenc:CipherData></xenc:EncryptedData>`;
  const c = { name, outcome, native: !wrap, document: wrapDoc(ed) };
  if (outcome === 'ok') { c.expected = wrapDoc(plainEl); if (wrap) c.kek = kek.toString('hex'); }
  else c.reason = reason;
  return c;
}

const ECDH = `${XENC11}ECDH-ES`;
const X25519 = 'http://www.w3.org/2021/04/xmldsig-more#x25519';
const cases = [
  make({ name: 'p256-pbkdf2-sha256-kw256-gcm128', curve: 'p256', agreement: ECDH, prf: 'sha256', iterations: 2000, wrap: 32, cekLen: 16, outcome: 'ok' }),
  make({ name: 'p256-pbkdf2-sha1-kw128-gcm128', curve: 'p256', agreement: ECDH, prf: 'sha1', iterations: 4096, wrap: 16, cekLen: 16, outcome: 'ok' }),
  make({ name: 'x25519-pbkdf2-sha512-kw128-gcm256', curve: 'x25519', agreement: X25519, prf: 'sha512', iterations: 1000, wrap: 16, cekLen: 32, outcome: 'ok' }),
  make({ name: 'p256-pbkdf2-sha384-direct-gcm128', curve: 'p256', agreement: ECDH, prf: 'sha384', iterations: 1500, wrap: 0, cekLen: 16, outcome: 'ok' }),
  make({ name: 'x25519-pbkdf2-sha256-direct-gcm256', curve: 'x25519', agreement: ECDH, prf: 'sha256', iterations: 3, wrap: 0, cekLen: 32, outcome: 'ok' }),
  make({ name: 'keylength-not-kw', curve: 'p256', agreement: ECDH, prf: 'sha256', iterations: 2000, wrap: 32, cekLen: 16, mutate: { keyLength: 16 }, outcome: 'refused', reason: 'is not the 32 octets' }),
  make({ name: 'salt-othersource', curve: 'p256', agreement: ECDH, prf: 'sha256', iterations: 2000, wrap: 32, cekLen: 16, mutate: { saltEl: `<xenc11:Salt><xenc11:OtherSource Algorithm="urn:example:salt"/></xenc11:Salt>` }, outcome: 'refused', reason: 'OtherSource' }),
  make({ name: 'iterations-above-limit', curve: 'p256', agreement: ECDH, prf: 'sha256', iterations: 2000, wrap: 32, cekLen: 16, mutate: { iterations: 1000001 }, outcome: 'refused', reason: 'above the limit' }),
  make({ name: 'iterations-zero', curve: 'p256', agreement: ECDH, prf: 'sha256', iterations: 2000, wrap: 32, cekLen: 16, mutate: { iterations: '0' }, outcome: 'refused', reason: 'not a positive integer' }),
  make({ name: 'prf-hmac-sha224', curve: 'p256', agreement: ECDH, prf: 'sha256', iterations: 2000, wrap: 32, cekLen: 16, mutate: { prf: 'sha224' }, outcome: 'refused', reason: 'PRF' }),
  make({ name: 'params-out-of-order', curve: 'p256', agreement: ECDH, prf: 'sha256', iterations: 2000, wrap: 32, cekLen: 16, mutate: { swap: true }, outcome: 'refused', reason: 'IterationCount' }),
];
process.stdout.write(JSON.stringify({
  generator: `tests/xmlenc/make-pbkdf2.mjs, Node ${process.version}, OpenSSL ${process.versions.openssl}`,
  spec: 'https://www.w3.org/TR/xmlenc-core1/#sec-PBKDF2',
  keys,
  cases,
}, null, 1) + '\n');
