// Host tests for the authorization server component
// (https://github.com/danbri/factoidal/issues/916).
//
//   node tests/authz/server.mjs
//
// The server is `npm/factoidal/authz/server.mjs` over the wasm module; every
// decision checked here (metadata, error codes, subject-token validation,
// the private-address guard, the token's claims, rotation, the key file) is
// made by formal/lean4/L4Factoidal/Authz/, and every signature by the
// vendored HACL* code. This file plays the client and the identity
// providers with node:crypto, and checks the issued tokens with node:crypto
// too, so the engine is not checked against itself.
//
// Score line: "N pass, M fail, X xfail, S skipped (out of T)". An xfail is an
// expected failure that names its open issue; an unexpected pass is a FAIL.

import { mkdtempSync, rmSync, statSync, readFileSync } from 'node:fs'
import { generateKeyPairSync } from 'node:crypto'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import {
  TOKEN_EXCHANGE, JWT_TYPE, ID_TOKEN_TYPE, SAML2_TYPE, OPENID_PROVIDER,
  keyPair, didKeyOf, signJwt, verifyJwt, selfIssued, exchangeForm, postForm,
  startDocuments, hostProvider, nowSeconds, samlIdpKey, samlAssertion
} from './fixtures.mjs'

let passed = 0
let failed = 0
let xfailed = 0
let skipped = 0
const failures = []

async function check (name, body) {
  try {
    await body()
    passed += 1
    console.log(`  ok    ${name}`)
  } catch (error) {
    failed += 1
    failures.push(`${name}: ${error && error.message ? error.message : String(error)}`)
    console.log(`  FAIL  ${name}`)
  }
}

async function xfail (name, issue, body) {
  try {
    await body()
  } catch (error) {
    xfailed += 1
    console.log(`  xfail ${name} (${issue}): ${error && error.message ? error.message : error}`)
    return
  }
  failed += 1
  failures.push(`${name}: unexpected pass: flip to an assertion and close ${issue}`)
  console.log(`  FAIL  ${name} (unexpected pass; close ${issue})`)
}

function skip (name, reason) {
  skipped += 1
  console.log(`  skip  ${name} - ${reason}`)
}

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

const STORAGE = 'https://storage.example/.well-known/lws-storage'
const KEY_HEX = '00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff'

function tempDir () {
  return mkdtempSync(join(process.env.AUTHZ_TEST_TMP || tmpdir(), 'factoidal-authz-'))
}

async function main () {
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  const { listen, openAuthorizationServer } = await import('../../npm/factoidal/authz/server.mjs')
  let engine
  try {
    engine = await loadEngine()
    engine.call('authzClose', ['probe'])
  } catch (error) {
    if (String(error.message).indexOf('unknown op') >= 0 || String(error.message).indexOf('assets are missing') >= 0) {
      skip('every check', `the wasm module carries no authz ops (rebuild formal/lean4/Wasm): ${error.message}`)
      return
    }
  }

  const docs = await startDocuments()
  const dir = tempDir()
  const running = await listen({
    engine, dir, port: 0, resources: [STORAGE], allowHttp: true, allowPrivateFetch: true, storageKey: null
  })
  const as = running.issuer
  const tokenUrl = `${running.origin}/token`
  const exchange = (fields) => postForm(tokenUrl, exchangeForm({ grant_type: TOKEN_EXCHANGE, resource: STORAGE, ...fields }))
  const jwks = async () => (await (await fetch(`${running.origin}/jwks`)).json()).keys

  /** Check an issued access token against the published JWK Set. */
  async function checkIssued (answer, subject, client) {
    assert(answer.status === 200, `status ${answer.status}: ${answer.text}`)
    assert(/no-store/.test(answer.headers.get('cache-control') || ''), 'no Cache-Control: no-store')
    assert(answer.json.token_type === 'Bearer', 'token_type')
    assert(answer.json.issued_token_type === 'urn:ietf:params:oauth:token-type:access_token', 'issued_token_type')
    assert(answer.json.expires_in === 300, 'expires_in')
    const token = answer.json.access_token
    const header = JSON.parse(Buffer.from(token.split('.')[0], 'base64url').toString('utf8'))
    const key = (await jwks()).find((k) => k.kid === header.kid)
    assert(key !== undefined, `no published key ${header.kid}`)
    const v = verifyJwt(token, key)
    assert(v.ok, 'the access token does not verify under the published key (node:crypto)')
    assert(v.header.typ === 'at+jwt', `typ ${v.header.typ}`)
    assert(v.claims.iss === as, `iss ${v.claims.iss}`)
    assert(JSON.stringify(v.claims.aud) === JSON.stringify([STORAGE]), `aud ${JSON.stringify(v.claims.aud)}`)
    assert(v.claims.sub === subject, `sub ${v.claims.sub}`)
    assert(v.claims.client_id === client, `client_id ${v.claims.client_id}`)
    assert(v.claims.exp - v.claims.iat === 300, 'exp - iat')
    assert(typeof v.claims.jti === 'string' && v.claims.jti.length > 0, 'jti')
    return { token, header: v.header, claims: v.claims }
  }

  const p256 = keyPair('ES256')
  const did = didKeyOf(p256)
  const mb = did.slice('did:key:'.length)
  const didToken = (opts = {}) => selfIssued(did, p256, { kid: mb, audience: as, ...opts })

  try {
    await check('Authorization Server Metadata: /.well-known/lws-configuration is RFC 8414 with the LWS members', async () => {
      const m = await (await fetch(`${running.origin}/.well-known/lws-configuration`)).json()
      assert(m.issuer === as, `issuer ${m.issuer}`)
      assert(m.token_endpoint === `${as}/token` && m.jwks_uri === `${as}/jwks`, 'endpoints')
      assert(m.grant_types_supported.includes(TOKEN_EXCHANGE), 'token exchange grant')
      assert(m.subject_token_types_supported.includes(JWT_TYPE) && m.subject_token_types_supported.includes(ID_TOKEN_TYPE), 'subject token types')
      assert(!m.subject_token_types_supported.includes(SAML2_TYPE), 'saml2 advertised with no trusted identity provider')
      assert(m.subject_identifier_types_supported.includes('https') && m.subject_identifier_types_supported.includes('did:key'), 'identifier types')
    })
    await check('RFC 8414: the same document at /.well-known/oauth-authorization-server', async () => {
      const m = await (await fetch(`${running.origin}/.well-known/oauth-authorization-server`)).json()
      assert(m.issuer === as, 'issuer')
    })
    await check('JWK Set: one ES256 public key with its RFC 7638 kid and no private member', async () => {
      const ks = await jwks()
      assert(ks.length === 1 && ks[0].kty === 'EC' && ks[0].crv === 'P-256' && ks[0].alg === 'ES256', JSON.stringify(ks))
      assert(ks.every((k) => k.d === undefined), 'a private member is published')
    })
    await check('Token Exchange: a did:key (P-256) credential gives an RFC 9068 token for the resource', async () => {
      await checkIssued(await exchange({ subject_token: didToken(), subject_token_type: JWT_TYPE }), did, did)
    })
    await check('Token Exchange: a did:key (Ed25519) credential gives a token too', async () => {
      const ed = keyPair('EdDSA')
      const edDid = didKeyOf(ed)
      await checkIssued(await exchange({
        subject_token: selfIssued(edDid, ed, { kid: `${edDid}#${edDid.slice(8)}`, audience: as }), subject_token_type: JWT_TYPE
      }), edDid, edDid)
    })
    const refused = async (fields, code, body) => {
      const a = body !== undefined ? await postForm(tokenUrl, body) : await exchange(fields)
      assert(a.status === 400, `status ${a.status}: ${a.text}`)
      assert(a.json && a.json.error === code, `error ${a.json && a.json.error}, wanted ${code}`)
      assert(a.json.access_token === undefined, 'a refusal carries a token')
    }
    await check('Request: an unknown resource is refused with invalid_target', () =>
      refused({ resource: 'https://unknown-storage.invalid/', subject_token: didToken(), subject_token_type: JWT_TYPE }, 'invalid_target'))
    await check('Request: no resource is invalid_request', () =>
      refused(null, 'invalid_request', exchangeForm({ grant_type: TOKEN_EXCHANGE, subject_token: didToken(), subject_token_type: JWT_TYPE })))
    await check('Request: no subject_token is invalid_request', () =>
      refused({ subject_token_type: JWT_TYPE }, 'invalid_request'))
    await check('Request: another grant type is unsupported_grant_type', () =>
      refused(null, 'unsupported_grant_type', exchangeForm({ grant_type: 'client_credentials', resource: STORAGE })))
    await check('Validation: a corrupted signature is refused', () => {
      const t = didToken()
      return refused({ subject_token: t.slice(0, -4) + (t.endsWith('AAAA') ? 'BBBB' : 'AAAA'), subject_token_type: JWT_TYPE }, 'invalid_request')
    })
    await check('Validation: alg none is refused', () => {
      const [, p] = didToken().split('.')
      const none = `${Buffer.from(JSON.stringify({ alg: 'none', kid: mb })).toString('base64url')}.${p}.`
      return refused({ subject_token: none, subject_token_type: JWT_TYPE }, 'invalid_request')
    })
    await check('Validation: an expired credential is refused', () =>
      refused({ subject_token: didToken({ claims: { iat: nowSeconds() - 3900, exp: nowSeconds() - 3600 } }), subject_token_type: JWT_TYPE }, 'invalid_request'))
    await check('Validation: aud without this server is refused', () =>
      refused({ subject_token: didToken({ audience: 'https://not-the-as.invalid/' }), subject_token_type: JWT_TYPE }, 'invalid_request'))
    await check('Validation: client_id other than sub is refused', () =>
      refused({ subject_token: didToken({ claims: { client_id: 'https://other.invalid/' } }), subject_token_type: JWT_TYPE }, 'invalid_request'))
    await check('Validation: a missing exp is refused', () =>
      refused({ subject_token: didToken({ drop: ['exp'] }), subject_token_type: JWT_TYPE }, 'invalid_request'))
    await check('Token endpoint: GET answers 405; a JSON body answers 400', async () => {
      const g = await fetch(tokenUrl)
      assert(g.status === 405, `GET ${g.status}`)
      const a = await postForm(tokenUrl, '{}', 'application/json')
      assert(a.status === 400 && a.json.error === 'invalid_request', `${a.status} ${a.text}`)
    })

    // CID suite with an http subject on this machine: allowed only because
    // this server was started with allowHttp and allowPrivateFetch.
    const cidPair = keyPair('ES256', 'k1')
    const cidPath = '/agents/cid'
    const cidSub = docs.origin + cidPath
    const method = (extra = {}) => ({ id: `${cidSub}#k1`, type: 'JsonWebKey', controller: cidSub, publicKeyJwk: cidPair.jwk, ...extra })
    docs.put(cidPath, { '@context': ['https://www.w3.org/ns/cid/v1'], id: cidSub, authentication: [method()] })
    docs.put('/agents/revoked', { id: `${docs.origin}/agents/revoked`, authentication: [{ ...method(), id: `${docs.origin}/agents/revoked#k1`, controller: `${docs.origin}/agents/revoked`, revoked: '2000-01-01T00:00:00Z' }] })
    docs.put('/agents/assert', { id: `${docs.origin}/agents/assert`, verificationMethod: [{ ...method(), id: `${docs.origin}/agents/assert#k1`, controller: `${docs.origin}/agents/assert` }], assertionMethod: [`${docs.origin}/agents/assert#k1`] })
    await check('CID suite: an https-style subject with a JsonWebKey authentication method gives a token', async () => {
      await checkIssued(await exchange({ subject_token: selfIssued(cidSub, cidPair, { kid: 'k1', audience: as }), subject_token_type: JWT_TYPE }), cidSub, cidSub)
    })
    await check('CID suite: a revoked method is refused (CID 1.0 section 2.2)', () =>
      refused({ subject_token: selfIssued(`${docs.origin}/agents/revoked`, cidPair, { kid: 'k1', audience: as }), subject_token_type: JWT_TYPE }, 'invalid_request'))
    await check('CID suite: a key listed only for assertion is refused (CID 1.0 section 3.3)', () =>
      refused({ subject_token: selfIssued(`${docs.origin}/agents/assert`, cidPair, { kid: 'k1', audience: as }), subject_token_type: JWT_TYPE }, 'invalid_request'))
    await check('CID suite: an unknown kid is refused', () =>
      refused({ subject_token: selfIssued(cidSub, cidPair, { kid: 'nope', audience: as }), subject_token_type: JWT_TYPE }, 'invalid_request'))

    // OpenID Connect suite.
    const opPair = keyPair('ES256', 'op1')
    const op = hostProvider(docs, '/op', opPair)
    const rogue = keyPair('ES256', 'rogue1')
    const rogueIss = hostProvider(docs, '/rogue', rogue)
    const oidcSub = `${docs.origin}/agents/oidc`
    docs.put('/agents/oidc', { id: oidcSub, service: [{ type: OPENID_PROVIDER, serviceEndpoint: op }] })
    const idToken = (pair, iss, drop = []) => {
      const now = nowSeconds()
      const c = { sub: oidcSub, iss, azp: 'https://client.example/app', aud: ['https://client.example/app', as], iat: now, exp: now + 300 }
      for (const d of drop) delete c[d]
      return signJwt({ alg: 'ES256', typ: 'JWT', kid: pair.kid }, c, pair)
    }
    await check('OpenID Connect suite: an ID token gives a token with sub and client_id = azp', async () => {
      await checkIssued(await exchange({ subject_token: idToken(opPair, op), subject_token_type: ID_TOKEN_TYPE }), oidcSub, 'https://client.example/app')
    })
    await check('OpenID Connect suite: a provider the subject does not name is refused', () =>
      refused({ subject_token: idToken(rogue, rogueIss), subject_token_type: ID_TOKEN_TYPE }, 'invalid_request'))
    await check('OpenID Connect suite: an ID token without azp is refused', () =>
      refused({ subject_token: idToken(opPair, op, ['azp']), subject_token_type: ID_TOKEN_TYPE }, 'invalid_request'))

    // The SAML suite (issue 926): a second server that trusts one identity
    // provider. Its issuer is the audience every assertion must name.
    const idp = samlIdpKey()
    const other = samlIdpKey()
    const idpId = 'https://idp.example'
    const saml = await listen({
      engine, port: 0, resources: [STORAGE], storageKey: null,
      samlIdps: [{ entityId: idpId, jwk: idp.publicJwk }]
    })
    try {
      const samlExchange = (token) => postForm(`${saml.origin}/token`, exchangeForm({
        grant_type: TOKEN_EXCHANGE, resource: STORAGE, subject_token: token, subject_token_type: SAML2_TYPE
      }))
      const assertionFor = (opts = {}) => samlAssertion({
        issuer: idpId, nameId: 'https://id.example/end-user', recipient: 'https://app.example/SAML',
        audiences: ['https://app.example/SAML', saml.issuer], key: idp.privateKey, ...opts
      })
      const samlRefused = async (token) => {
        const a = await samlExchange(token)
        assert(a.status === 400 && a.json.error === 'invalid_request', `${a.status} ${a.text}`)
      }
      await check('SAML suite: the metadata names the saml2 token type when an identity provider is trusted', async () => {
        const m = await (await fetch(`${saml.origin}/.well-known/lws-configuration`)).json()
        assert(m.subject_token_types_supported.includes(SAML2_TYPE), 'saml2 not advertised')
      })
      await check('SAML suite: a signed SAML 2.0 assertion is exchanged for a token naming its NameID and Recipient', async () => {
        const a = await samlExchange(assertionFor())
        assert(a.status === 200, `status ${a.status}: ${a.text}`)
        const header = JSON.parse(Buffer.from(a.json.access_token.split('.')[0], 'base64url').toString('utf8'))
        const key = (await (await fetch(`${saml.origin}/jwks`)).json()).keys.find((k) => k.kid === header.kid)
        const v = verifyJwt(a.json.access_token, key)
        assert(v.ok, 'the access token does not verify (node:crypto)')
        assert(v.claims.sub === 'https://id.example/end-user', `sub ${v.claims.sub}`)
        assert(v.claims.client_id === 'https://app.example/SAML', `client_id ${v.claims.client_id}`)
      })
      await check('SAML suite: an assertion altered after signing is refused', () => samlRefused(assertionFor({ fault: 'altered' })))
      await check('SAML suite: an unsigned assertion is refused', () => samlRefused(assertionFor({ fault: 'unsigned' })))
      await check('SAML suite: an assertion signed with another key is refused', () => samlRefused(assertionFor({ key: other.privateKey })))
      await check('SAML suite: an assertion from an untrusted issuer is refused', () => samlRefused(assertionFor({ issuer: 'https://rogue.example' })))
      await check('SAML suite: an assertion whose audience omits this server is refused', () =>
        samlRefused(assertionFor({ audiences: ['https://app.example/SAML'] })))
      await check('SAML suite: an expired assertion is refused', () => samlRefused(assertionFor({ now: nowSeconds() - 3600 })))
      await check('SAML suite: a private JWK is refused as a trust configuration', async () => {
        const { privateKey } = generateKeyPairSync('rsa', { modulusLength: 2048 })
        let refusedPrivate = false
        try {
          await openAuthorizationServer({
            engine, issuer: 'https://as.example', resources: [STORAGE], storageKey: null,
            samlIdps: [{ entityId: idpId, jwk: privateKey.export({ format: 'jwk' }) }]
          })
        } catch (_e) { refusedPrivate = true }
        assert(refusedPrivate, 'a private JWK was accepted')
      })
    } finally {
      await saml.close()
    }

    // The private-address guard: a second server without allowPrivateFetch.
    const guarded = await listen({ engine, port: 0, resources: [STORAGE], allowHttp: true, storageKey: null })
    try {
      await check('Fetch guard: a subject document on a loopback address is not fetched without --allow-private-fetch', async () => {
        const a = await postForm(`${guarded.origin}/token`, exchangeForm({
          grant_type: TOKEN_EXCHANGE, resource: STORAGE, subject_token_type: JWT_TYPE,
          subject_token: selfIssued(cidSub, cidPair, { kid: 'k1', audience: guarded.issuer })
        }))
        assert(a.status === 400 && /private/.test(a.json.error_description), `${a.status} ${a.text}`)
      })
      await check('Fetch guard: a localhost subject is refused too', async () => {
        const local = cidSub.replace('127.0.0.1', 'localhost')
        const a = await postForm(`${guarded.origin}/token`, exchangeForm({
          grant_type: TOKEN_EXCHANGE, resource: STORAGE, subject_token_type: JWT_TYPE,
          subject_token: selfIssued(local, cidPair, { kid: 'k1', audience: guarded.issuer })
        }))
        assert(a.status === 400 && /localhost/.test(a.json.error_description), `${a.status} ${a.text}`)
      })
    } finally {
      await guarded.close()
    }
    const httpOff = await listen({ engine, port: 0, resources: [STORAGE], allowPrivateFetch: true, storageKey: null })
    try {
      await check('Fetch guard: an http subject is refused without --allow-http', async () => {
        const a = await postForm(`${httpOff.origin}/token`, exchangeForm({
          grant_type: TOKEN_EXCHANGE, resource: STORAGE, subject_token_type: JWT_TYPE,
          subject_token: selfIssued(cidSub, cidPair, { kid: 'k1', audience: httpOff.issuer })
        }))
        assert(a.status === 400 && /https/.test(a.json.error_description), `${a.status} ${a.text}`)
      })
    } finally {
      await httpOff.close()
    }

    await check('Rotation: a new key signs; the old key stays published and its tokens still verify', async () => {
      const before = await checkIssued(await exchange({ subject_token: didToken(), subject_token_type: JWT_TYPE }), did, did)
      running.authz.rotate()
      const ks = await jwks()
      assert(ks.length === 2, `${ks.length} published keys`)
      const after = await checkIssued(await exchange({ subject_token: didToken(), subject_token_type: JWT_TYPE }), did, did)
      assert(after.header.kid !== before.header.kid, 'the new token is signed with the old key')
      const old = ks.find((k) => k.kid === before.header.kid)
      assert(old !== undefined && verifyJwt(before.token, old).ok, 'the old token no longer verifies')
    })
    await check('Key file: written with mode 0600 and read back with the same keys', async () => {
      const file = join(dir, 'authz-keys.json')
      assert((statSync(file).mode & 0o777) === 0o600, `mode ${(statSync(file).mode & 0o777).toString(8)}`)
      const kids = (await jwks()).map((k) => k.kid).sort()
      const again = await openAuthorizationServer({ engine, dir, issuer: as, resources: [STORAGE], storageKey: null })
      const answer = await again.step({ method: 'GET', target: '/jwks', headers: [], body: '' })
      again.close()
      assert(JSON.stringify(JSON.parse(answer.body).keys.map((k) => k.kid).sort()) === JSON.stringify(kids), 'kids differ after reopen')
    })
  } finally {
    await running.close()
    rmSync(dir, { recursive: true, force: true })
  }

  await check('Key file sealed with FACTOIDAL_LWS_KEY: sealed on disk, reopened with the key, refused without it or with another', async () => {
    const sdir = tempDir()
    try {
      const first = await openAuthorizationServer({ engine, dir: sdir, issuer: 'https://as.example', resources: [STORAGE], storageKey: KEY_HEX })
      const kid = JSON.parse((await first.step({ method: 'GET', target: '/jwks', headers: [], body: '' })).body).keys[0].kid
      first.close()
      const text = readFileSync(join(sdir, 'authz-keys.json'), 'utf8')
      assert(JSON.parse(text).format === 'lws-snapshot-sealed-1', 'the key file is not sealed')
      assert(text.indexOf('"d"') < 0, 'a private member is readable in the sealed file')
      const again = await openAuthorizationServer({ engine, dir: sdir, issuer: 'https://as.example', resources: [STORAGE], storageKey: KEY_HEX })
      const kid2 = JSON.parse((await again.step({ method: 'GET', target: '/jwks', headers: [], body: '' })).body).keys[0].kid
      again.close()
      assert(kid2 === kid, 'another key after reopen')
      let refusedNoKey = false
      try { await openAuthorizationServer({ engine, dir: sdir, issuer: 'https://as.example', resources: [STORAGE], storageKey: null }) } catch (_e) { refusedNoKey = true }
      assert(refusedNoKey, 'a sealed key file opened without a key')
      let refusedWrong = false
      try { await openAuthorizationServer({ engine, dir: sdir, issuer: 'https://as.example', resources: [STORAGE], storageKey: 'ff'.repeat(32) }) } catch (_e) { refusedWrong = true }
      assert(refusedWrong, 'a sealed key file opened with another key')
    } finally {
      rmSync(sdir, { recursive: true, force: true })
    }
  })

  await check('EdDSA: a server started with alg EdDSA signs EdDSA tokens that verify under its JWK Set', async () => {
    const ed = await listen({ engine, port: 0, resources: [STORAGE], alg: 'EdDSA', storageKey: null })
    try {
      const a = await postForm(`${ed.origin}/token`, exchangeForm({
        grant_type: TOKEN_EXCHANGE, resource: STORAGE, subject_token_type: JWT_TYPE,
        subject_token: selfIssued(did, p256, { kid: mb, audience: ed.issuer })
      }))
      assert(a.status === 200, `${a.status} ${a.text}`)
      const key = (await (await fetch(`${ed.origin}/jwks`)).json()).keys[0]
      const v = verifyJwt(a.json.access_token, key)
      assert(v.ok && v.header.alg === 'EdDSA' && key.kty === 'OKP', 'EdDSA token does not verify')
    } finally {
      await ed.close()
    }
  })

  await docs.close()
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + xfailed + skipped
console.log(`authz-server node: ${passed} pass, ${failed} fail, ${xfailed} xfail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
