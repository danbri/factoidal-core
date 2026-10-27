// Test fixtures for the authorization server host tests
// (https://github.com/danbri/factoidal/issues/916): a client that makes
// subject credentials with node:crypto, and a local document server for
// controlled identifier documents and an OpenID Provider.
//
// This is TEST CLIENT code: it plays the agent and the identity provider.
// Nothing here is part of the server, whose every decision is made in
// formal/lean4/L4Factoidal/Authz/.

import http from 'node:http'
import { generateKeyPairSync, sign, verify, createPublicKey, createHash, randomBytes, createCipheriv, publicEncrypt, constants as cryptoConstants } from 'node:crypto'

export const TOKEN_EXCHANGE = 'urn:ietf:params:oauth:grant-type:token-exchange'
export const JWT_TYPE = 'urn:ietf:params:oauth:token-type:jwt'
export const ID_TOKEN_TYPE = 'urn:ietf:params:oauth:token-type:id_token'
export const SAML2_TYPE = 'urn:ietf:params:oauth:token-type:saml2'
export const OPENID_PROVIDER = 'https://www.w3.org/ns/lws#OpenIdProvider'

export function b64url (bytes) {
  return Buffer.from(bytes).toString('base64url')
}

export function nowSeconds () {
  return Math.floor(Date.now() / 1000)
}

const B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'

/** base58btc (the did:key and Multikey encoding), for the test client. */
export function base58 (bytes) {
  let n = 0n
  for (const b of bytes) n = n * 256n + BigInt(b)
  let out = ''
  while (n > 0n) { out = B58[Number(n % 58n)] + out; n /= 58n }
  for (const b of bytes) { if (b === 0) out = '1' + out; else break }
  return out
}

/** An ES256 (P-256) or EdDSA (Ed25519) key pair with its public JWK. */
export function keyPair (alg = 'ES256', kid) {
  const pair = alg === 'ES256'
    ? generateKeyPairSync('ec', { namedCurve: 'P-256' })
    : generateKeyPairSync('ed25519')
  const jwk = pair.publicKey.export({ format: 'jwk' })
  return { alg, kid, privateKey: pair.privateKey, publicKey: pair.publicKey, jwk: kid ? { ...jwk, kid } : jwk }
}

/** The did:key of a key pair: P-256 compressed point (multicodec 0x1200)
 *  or Ed25519 (0xed). */
export function didKeyOf (pair) {
  if (pair.alg === 'ES256') {
    const x = Buffer.from(pair.jwk.x, 'base64url')
    const y = Buffer.from(pair.jwk.y, 'base64url')
    const point = Buffer.concat([Buffer.from([(y[31] & 1) === 1 ? 3 : 2]), x])
    return 'did:key:z' + base58(Buffer.concat([Buffer.from([0x80, 0x24]), point]))
  }
  return 'did:key:z' + base58(Buffer.concat([Buffer.from([0xed, 0x01]), Buffer.from(pair.jwk.x, 'base64url')]))
}

/** A compact JWS signed with a key pair. */
export function signJwt (header, claims, pair) {
  const input = `${b64url(JSON.stringify(header))}.${b64url(JSON.stringify(claims))}`
  const sig = pair.alg === 'ES256'
    ? sign('sha256', Buffer.from(input), { key: pair.privateKey, dsaEncoding: 'ieee-p1363' })
    : sign(null, Buffer.from(input), pair.privateKey)
  return `${input}.${b64url(sig)}`
}

/** Verify a compact JWS against a JWK with node:crypto (the test's own
 *  check of what the server issued). */
export function verifyJwt (token, jwk) {
  const [h, p, s] = token.split('.')
  const header = JSON.parse(Buffer.from(h, 'base64url').toString('utf8'))
  const key = createPublicKey({ key: jwk, format: 'jwk' })
  const data = Buffer.from(`${h}.${p}`)
  const sig = Buffer.from(s, 'base64url')
  const ok = header.alg === 'ES256'
    ? verify('sha256', data, { key, dsaEncoding: 'ieee-p1363' }, sig)
    : verify(null, data, key, sig)
  return { ok, header, claims: JSON.parse(Buffer.from(p, 'base64url').toString('utf8')) }
}

/** A self-issued credential (lws10-authn-ssi-cid) for `subject`. */
export function selfIssued (subject, pair, { kid, audience, claims = {}, drop = [], header = {} } = {}) {
  const now = nowSeconds()
  const body = { sub: subject, iss: subject, client_id: subject, aud: [audience], iat: now, exp: now + 300, ...claims }
  for (const name of drop) delete body[name]
  return signJwt({ alg: pair.alg, typ: 'JWT', kid, ...header }, body, pair)
}

/** A token-exchange form body. */
export function exchangeForm (fields) {
  return new URLSearchParams(fields).toString()
}

export async function postForm (url, body, contentType = 'application/x-www-form-urlencoded') {
  const answer = await fetch(url, { method: 'POST', headers: { 'content-type': contentType }, body })
  const text = await answer.text()
  let json = null
  try { json = JSON.parse(text) } catch (_error) { json = null }
  return { status: answer.status, headers: answer.headers, json, text }
}

/** A local document server: path -> JSON document. */
export async function startDocuments () {
  const docs = new Map()
  const server = http.createServer((req, res) => {
    const doc = docs.get(new URL(req.url, 'http://x').pathname)
    if (doc === undefined) { res.statusCode = 404; res.end(); return }
    res.setHeader('content-type', 'application/json')
    res.end(JSON.stringify(doc))
  })
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
  const origin = `http://127.0.0.1:${server.address().port}`
  return {
    origin,
    put (path, doc) { docs.set(path, doc) },
    close () { return new Promise((resolve) => server.close(resolve)) }
  }
}

/** Host an OpenID Provider (discovery + JWKS) at `origin + path`. */
export function hostProvider (documents, path, pair) {
  const iss = documents.origin + path
  documents.put(`${path}/.well-known/openid-configuration`, { issuer: iss, jwks_uri: `${iss}/jwks` })
  documents.put(`${path}/jwks`, { keys: [{ ...pair.jwk, alg: 'ES256', use: 'sig' }] })
  return iss
}

// ------------------------------------------------------------ SAML 2.0
//
// A signed SAML 2.0 assertion for the SAML suite
// (https://github.com/danbri/factoidal/issues/926). The XML is written here
// already in its exclusive canonical form (Exclusive XML Canonicalization
// 1.0: explicit end tags, attributes in order, the ds namespace declared on
// ds:Signature and so rendered on ds:SignedInfo when it is the apex), so the
// two octet strings the signature covers are known without an XML library:
// the assertion without ds:Signature (digested), and ds:SignedInfo with
// xmlns:ds (signed with RSA PKCS #1 v1.5 SHA-256 by node:crypto). The engine
// computes both again from the parsed document.

const SAML_NS = 'urn:oasis:names:tc:SAML:2.0:assertion'
const DS_NS = 'http://www.w3.org/2000/09/xmldsig#'
const EXC_C14N = 'http://www.w3.org/2001/10/xml-exc-c14n#'

function isoSeconds (s) {
  return new Date(s * 1000).toISOString().replace(/\.\d{3}Z$/, 'Z')
}

/** An RSA 2048 key pair for a SAML identity provider: { privateKey, publicJwk }. */
export function samlIdpKey () {
  const { privateKey, publicKey } = generateKeyPairSync('rsa', { modulusLength: 2048 })
  return { privateKey, publicJwk: publicKey.export({ format: 'jwk' }) }
}

/**
 * A base64url SAML 2.0 assertion (RFC 8693 section 3).
 * fault: undefined, 'altered' (NameID changed after signing), 'unsigned'.
 */
export function samlAssertion ({ issuer, nameId, recipient, audiences, key, fault, now = nowSeconds() }) {
  const id = '_' + randomBytesHex(8)
  const nb = isoSeconds(now - 5)
  const na = isoSeconds(now + 300)
  const body = (sub) =>
    `<saml:Subject><saml:NameID>${sub}</saml:NameID>` +
    '<saml:SubjectConfirmation Method="urn:oasis:names:tc:SAML:2.0:cm:bearer">' +
    `<saml:SubjectConfirmationData NotOnOrAfter="${na}" Recipient="${recipient}"></saml:SubjectConfirmationData>` +
    '</saml:SubjectConfirmation></saml:Subject>' +
    `<saml:Conditions NotBefore="${nb}" NotOnOrAfter="${na}"><saml:AudienceRestriction>` +
    audiences.map((a) => `<saml:Audience>${a}</saml:Audience>`).join('') +
    '</saml:AudienceRestriction></saml:Conditions>'
  const open = `<saml:Assertion xmlns:saml="${SAML_NS}" ID="${id}" IssueInstant="${nb}" Version="2.0">` +
    `<saml:Issuer>${issuer}</saml:Issuer>`
  const close = '</saml:Assertion>'
  const signedXml = open + body(nameId) + close
  if (fault === 'unsigned') return Buffer.from(signedXml, 'utf8').toString('base64url')
  const digest = createHash('sha256').update(signedXml, 'utf8').digest('base64')
  const signedInfo = (decl) =>
    `<ds:SignedInfo${decl}><ds:CanonicalizationMethod Algorithm="${EXC_C14N}"></ds:CanonicalizationMethod>` +
    '<ds:SignatureMethod Algorithm="http://www.w3.org/2001/04/xmldsig-more#rsa-sha256"></ds:SignatureMethod>' +
    `<ds:Reference URI="#${id}"><ds:Transforms>` +
    '<ds:Transform Algorithm="http://www.w3.org/2000/09/xmldsig#enveloped-signature"></ds:Transform>' +
    `<ds:Transform Algorithm="${EXC_C14N}"></ds:Transform></ds:Transforms>` +
    '<ds:DigestMethod Algorithm="http://www.w3.org/2001/04/xmlenc#sha256"></ds:DigestMethod>' +
    `<ds:DigestValue>${digest}</ds:DigestValue></ds:Reference></ds:SignedInfo>`
  const value = sign('sha256', Buffer.from(signedInfo(` xmlns:ds="${DS_NS}"`), 'utf8'), key).toString('base64')
  const signature = `<ds:Signature xmlns:ds="${DS_NS}">${signedInfo('')}` +
    `<ds:SignatureValue>${value}</ds:SignatureValue></ds:Signature>`
  const sub = fault === 'altered' ? nameId + '/other' : nameId
  return Buffer.from(open + signature + body(sub) + close, 'utf8').toString('base64url')
}

function randomBytesHex (n) {
  return randomBytes(n).toString('hex')
}

/**
 * A SAML assertion token in a saml:EncryptedAssertion, made with node:crypto
 * only (issue 1073): the assertion text encrypted with AES-128-GCM (XML
 * Encryption 1.1 aes128-gcm: IV || ciphertext || tag), its key with RSA-OAEP
 * under `publicKey` (rsa-oaep-mgf1p, SHA-1) or, with `sha256`, xmlenc11
 * rsa-oaep with SHA-256 and MGF1 SHA-256.
 */
export function samlEncrypted (token, publicKey, { sha256 = false, tamper = false } = {}) {
  const XENC = 'http://www.w3.org/2001/04/xmlenc#'
  const xml = Buffer.from(token, 'base64url')
  const cek = randomBytes(16)
  const iv = randomBytes(12)
  const gcm = createCipheriv('aes-128-gcm', cek, iv)
  const ct = Buffer.concat([gcm.update(xml), gcm.final(), gcm.getAuthTag()])
  if (tamper) ct[ct.length - 1] ^= 1
  const wrapped = publicEncrypt({
    key: publicKey, padding: cryptoConstants.RSA_PKCS1_OAEP_PADDING, oaepHash: sha256 ? 'sha256' : 'sha1'
  }, cek)
  const keyMethod = sha256
    ? '<xenc:EncryptionMethod Algorithm="http://www.w3.org/2009/xmlenc11#rsa-oaep">' +
      '<ds:DigestMethod Algorithm="http://www.w3.org/2001/04/xmlenc#sha256"/>' +
      '<xenc11:MGF xmlns:xenc11="http://www.w3.org/2009/xmlenc11#" Algorithm="http://www.w3.org/2009/xmlenc11#mgf1sha256"/>' +
      '</xenc:EncryptionMethod>'
    : `<xenc:EncryptionMethod Algorithm="${XENC}rsa-oaep-mgf1p">` +
      '<ds:DigestMethod Algorithm="http://www.w3.org/2000/09/xmldsig#sha1"/></xenc:EncryptionMethod>'
  const doc = `<saml:EncryptedAssertion xmlns:saml="${SAML_NS}">` +
    `<xenc:EncryptedData xmlns:xenc="${XENC}" Type="${XENC}Element">` +
    '<xenc:EncryptionMethod Algorithm="http://www.w3.org/2009/xmlenc11#aes128-gcm"/>' +
    `<ds:KeyInfo xmlns:ds="${DS_NS}"><xenc:EncryptedKey>${keyMethod}` +
    `<xenc:CipherData><xenc:CipherValue>${wrapped.toString('base64')}</xenc:CipherValue></xenc:CipherData>` +
    '</xenc:EncryptedKey></ds:KeyInfo>' +
    `<xenc:CipherData><xenc:CipherValue>${Buffer.concat([iv, ct]).toString('base64')}</xenc:CipherValue></xenc:CipherData>` +
    '</xenc:EncryptedData></saml:EncryptedAssertion>'
  return Buffer.from(doc, 'utf8').toString('base64url')
}
