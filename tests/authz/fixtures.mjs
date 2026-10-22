// Test fixtures for the authorization server host tests
// (https://github.com/danbri/factoidal/issues/916): a client that makes
// subject credentials with node:crypto, and a local document server for
// controlled identifier documents and an OpenID Provider.
//
// This is TEST CLIENT code: it plays the agent and the identity provider.
// Nothing here is part of the server, whose every decision is made in
// formal/lean4/L4Factoidal/Authz/.

import http from 'node:http'
import { generateKeyPairSync, sign, verify, createPublicKey } from 'node:crypto'

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
