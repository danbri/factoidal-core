// Host tests for Solid-OIDC access-token verification with DPoP proofs in
// the Solid server.
// https://github.com/danbri/factoidal/issues/899
//
//   node tests/solid/server/oidc.mjs
//
// A local OpenID provider runs in this process: it serves
// /.well-known/openid-configuration (OpenID Connect Discovery 1.0), a JWK
// Set and two WebID profile documents, and this file signs ES256 access
// tokens (Solid-OIDC §8.1 shape) and DPoP proofs (RFC 9449 §4.2) with
// node:crypto. The server is `npm/factoidal/solid/server/index.mjs`; every
// decision checked here is made by
// `formal/lean4/L4Factoidal/Solid/Server/Oidc.lean` and `Auth.lean`, and
// signatures are verified by the vendored HACL* P-256 code in the wasm.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import http from 'node:http'
import { generateKeyPairSync, sign, randomUUID, createHash } from 'node:crypto'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'

let passed = 0
let failed = 0
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

function skip (name, reason) {
  skipped += 1
  console.log(`  skip  ${name} - ${reason}`)
}

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

const CHECKS = [
  'Anonymous: a request with no credential answers 401 with a DPoP challenge',
  'Valid: a DPoP-bound token for the owner writes and reads',
  'DPoP: a proof with a bad signature answers 401 invalid_dpop_proof',
  'DPoP: a proof whose htu names another URI answers 401',
  'DPoP: a proof whose htm names another method answers 401',
  'DPoP: a replayed jti answers 401',
  'DPoP: a proof with iat outside the window answers 401',
  'DPoP: a proof without ath answers 401',
  'Binding: a token whose cnf.jkt is not the proof key answers 401',
  'Binding: a token with no cnf answers 401',
  'Token: an expired token answers 401 invalid_token',
  'Token: a token with no webid claim answers 401',
  'Token: a token whose aud does not include "solid" answers 401',
  'Token: a token signed by a key the issuer does not publish answers 401',
  'Token: a token from an untrusted issuer answers 401',
  'Presentation: a Bearer credential answers 401 invalid_request',
  'Presentation: a DPoP credential with no DPoP header answers 401',
  'Issuer discovery: a WebID profile that does not list the issuer answers 401',
  'Policy: a valid token whose agent has no access answers 403',
  'Fetches: the host fetched only discovery, key set and profile URLs',
  'CLI: factoidal solid-serve with no issuer option refuses to start'
]

function b64url (bytes) {
  return Buffer.from(bytes).toString('base64url')
}

function jws (header, payload, privateKey) {
  const input = `${b64url(JSON.stringify(header))}.${b64url(JSON.stringify(payload))}`
  const sig = sign('sha256', Buffer.from(input), { key: privateKey, dsaEncoding: 'ieee-p1363' })
  return `${input}.${b64url(sig)}`
}

function newKey () {
  const pair = generateKeyPairSync('ec', { namedCurve: 'P-256' })
  const jwk = pair.publicKey.export({ format: 'jwk' })
  return { privateKey: pair.privateKey, jwk: { kty: jwk.kty, crv: jwk.crv, x: jwk.x, y: jwk.y } }
}

/** RFC 7638 thumbprint of an EC public key. */
function thumbprint (jwk) {
  const canon = JSON.stringify({ crv: jwk.crv, kty: jwk.kty, x: jwk.x, y: jwk.y })
  return b64url(createHash('sha256').update(canon).digest())
}

/** A local OpenID provider that also serves the WebID profiles. */
async function startProvider (seen) {
  const signing = { ...newKey(), kid: 'op1' }
  let origin = ''
  const profiles = new Map()
  const server = http.createServer((req, res) => {
    const url = new URL(req.url, 'http://x')
    seen.push(url.pathname)
    if (url.pathname === '/.well-known/openid-configuration') {
      res.setHeader('content-type', 'application/json')
      res.end(JSON.stringify({ issuer: `${origin}/`, jwks_uri: `${origin}/jwks` }))
    } else if (url.pathname === '/jwks') {
      res.setHeader('content-type', 'application/json')
      res.end(JSON.stringify({ keys: [{ ...signing.jwk, kid: signing.kid, alg: 'ES256' }] }))
    } else if (profiles.has(url.pathname)) {
      res.setHeader('content-type', 'text/turtle')
      res.end(profiles.get(url.pathname))
    } else {
      res.statusCode = 404
      res.end()
    }
  })
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
  origin = `http://127.0.0.1:${server.address().port}`
  return {
    origin,
    issuer: `${origin}/`,
    signing,
    profile (path, issuer) {
      profiles.set(path, '@prefix solid: <http://www.w3.org/ns/solid/terms#> .\n' +
        `<#me> solid:oidcIssuer <${issuer}> .\n`)
      return `${origin}${path}#me`
    },
    close () { return new Promise((resolve) => server.close(resolve)) }
  }
}

async function main () {
  const { loadEngine } = await import('../../../npm/factoidal/bin/engine.mjs')
  const { listen, solidServerOpsAvailable } = await import('../../../npm/factoidal/solid/server/index.mjs')
  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const name of CHECKS) skip(name, `the Lean engine did not load: ${error.message}`)
    return
  }
  if (typeof solidServerOpsAvailable === 'function') {
    const probe = await solidServerOpsAvailable(engine)
    if (!probe.available) {
      for (const name of CHECKS) skip(name, probe.reason)
      return
    }
  }
  try {
    engine.call('solidFetched', ['no-such-handle', '{}'])
  } catch (error) {
    if (String(error.message).indexOf('unknown op') >= 0) {
      for (const name of CHECKS) skip(name, 'the module carries no solidFetched op (rebuild the wasm)')
      return
    }
  }

  const seen = []
  const op = await startProvider(seen)
  const rogue = await startProvider([])
  const ALICE = op.profile('/alice/card', op.issuer)
  const BOB = op.profile('/bob/card', op.issuer)
  const MALLORY = op.profile('/mallory/card', 'https://elsewhere.example/')
  const running = await listen({
    engine,
    port: 0,
    owner: ALICE,
    realClock: true,
    auth: { issuers: [{ issuer: op.issuer }], refreshInterval: 0 }
  })
  const o = running.origin
  const client = newKey()
  const now = () => Math.floor(Date.now() / 1000)

  function token ({ webid = ALICE, aud = ['solid', 'https://app.example/id'], exp, jkt,
    noCnf = false, key = op.signing, iss = op.issuer, kid = op.signing.kid } = {}) {
    const t = now()
    const claims = {
      iss, sub: 'user-1', aud, azp: 'https://app.example/id', jti: randomUUID(),
      iat: t, exp: exp !== undefined ? exp : t + 300
    }
    if (webid !== null) claims.webid = webid
    if (!noCnf) claims.cnf = { jkt: jkt !== undefined ? jkt : thumbprint(client.jwk) }
    return jws({ alg: 'ES256', typ: 'at+jwt', kid }, claims, key.privateKey)
  }

  function proof (method, url, accessToken, { key = client, signKey, iat, jti, ath = true } = {}) {
    const payload = {
      jti: jti !== undefined ? jti : randomUUID(),
      htm: method,
      htu: url,
      iat: iat !== undefined ? iat : now()
    }
    if (ath) payload.ath = b64url(createHash('sha256').update(accessToken).digest())
    return jws({ typ: 'dpop+jwt', alg: 'ES256', jwk: key.jwk }, payload,
      (signKey || key).privateKey)
  }

  function dpop (method, path, opts = {}, tokenOpts = {}) {
    const t = token(tokenOpts)
    return {
      authorization: `DPoP ${t}`,
      dpop: proof(opts.htm || method, opts.htu || `${o}${path}`, t, opts)
    }
  }

  const call = async (method, path, headers = {}, body) => {
    const r = await fetch(`${o}${path}`, {
      method,
      headers: body !== undefined ? { 'content-type': 'text/plain', ...headers } : headers,
      body
    })
    const text = await r.text()
    return { status: r.status, headers: r.headers, text }
  }
  const refused = async (headers, method = 'GET', path = '/private/a.txt') => {
    const r = await call(method, path, headers)
    assert(r.status === 401, `answered ${r.status}`)
    return r.headers.get('www-authenticate') || ''
  }

  try {
    await check(CHECKS[0], async () => {
      const c = await refused({})
      assert(/^DPoP algs="[^"]+"$/.test(c), `WWW-Authenticate: ${c}`)
    })

    await check(CHECKS[1], async () => {
      const w = await call('PUT', '/private/a.txt', dpop('PUT', '/private/a.txt'), 'hello')
      assert(w.status === 201 || w.status === 204, `PUT answered ${w.status}: ${w.text}`)
      const r = await call('GET', '/private/a.txt', dpop('GET', '/private/a.txt'))
      assert(r.status === 200 && r.text === 'hello', `GET answered ${r.status}: ${r.text}`)
      const wa = r.headers.get('wac-allow') || ''
      assert(/user="[^"]*write/.test(wa), `WAC-Allow: ${wa}`)
    })

    await check(CHECKS[2], async () => {
      const c = await refused(dpop('GET', '/private/a.txt', { signKey: newKey() }))
      assert(c.indexOf('error="invalid_dpop_proof"') >= 0, c)
    })
    await check(CHECKS[3], async () => {
      await refused(dpop('GET', '/private/a.txt', { htu: `${o}/private/other.txt` }))
    })
    await check(CHECKS[4], async () => {
      await refused(dpop('GET', '/private/a.txt', { htm: 'DELETE' }))
    })
    await check(CHECKS[5], async () => {
      const h = dpop('GET', '/private/a.txt')
      const first = await call('GET', '/private/a.txt', h)
      assert(first.status === 200, `first use answered ${first.status}`)
      await refused(h)
    })
    await check(CHECKS[6], async () => {
      await refused(dpop('GET', '/private/a.txt', { iat: now() - 3600 }))
    })
    await check(CHECKS[7], async () => {
      await refused(dpop('GET', '/private/a.txt', { ath: false }))
    })
    await check(CHECKS[8], async () => {
      const c = await refused(dpop('GET', '/private/a.txt', {}, { jkt: thumbprint(newKey().jwk) }))
      assert(c.indexOf('error=') >= 0, c)
    })
    await check(CHECKS[9], async () => {
      await refused(dpop('GET', '/private/a.txt', {}, { noCnf: true }))
    })
    await check(CHECKS[10], async () => {
      const c = await refused(dpop('GET', '/private/a.txt', {}, { exp: now() - 3600 }))
      assert(c.indexOf('error="invalid_token"') >= 0, c)
    })
    await check(CHECKS[11], async () => {
      await refused(dpop('GET', '/private/a.txt', {}, { webid: null }))
    })
    await check(CHECKS[12], async () => {
      await refused(dpop('GET', '/private/a.txt', {}, { aud: ['https://app.example/id'] }))
    })
    await check(CHECKS[13], async () => {
      await refused(dpop('GET', '/private/a.txt', {}, { key: newKey() }))
    })
    await check(CHECKS[14], async () => {
      await refused(dpop('GET', '/private/a.txt', {},
        { iss: rogue.issuer, key: rogue.signing, kid: rogue.signing.kid }))
    })
    await check(CHECKS[15], async () => {
      const c = await refused({ authorization: `Bearer ${token()}` })
      assert(c.indexOf('error="invalid_request"') >= 0, c)
    })
    await check(CHECKS[16], async () => {
      await refused({ authorization: `DPoP ${token()}` })
    })
    await check(CHECKS[17], async () => {
      await refused(dpop('GET', '/private/a.txt', {}, { webid: MALLORY }))
    })
    await check(CHECKS[18], async () => {
      const r = await call('GET', '/private/a.txt', dpop('GET', '/private/a.txt', {}, { webid: BOB }))
      assert(r.status === 403, `answered ${r.status}`)
    })
    await check(CHECKS[19], async () => {
      const allowed = new Set(['/.well-known/openid-configuration', '/jwks',
        '/alice/card', '/bob/card', '/mallory/card'])
      const other = seen.filter((p) => !allowed.has(p))
      assert(other.length === 0, `unexpected fetches: ${other.join(', ')}`)
      assert(seen.includes('/jwks') && seen.includes('/alice/card'), `fetches: ${seen.join(', ')}`)
    })
  } finally {
    await running.close()
    await op.close()
    await rogue.close()
  }

  await check(CHECKS[20], async () => {
    const cli = fileURLToPath(new URL('../../../npm/factoidal/bin/factoidal.mjs', import.meta.url))
    const r = spawnSync(process.execPath, [cli, 'solid-serve', '/tmp/so-never-created', '--port', '0'],
      { encoding: 'utf8', timeout: 30000 })
    assert(r.status !== 0, `exit ${r.status}`)
    assert(/--issuer/.test(r.stderr), `stderr: ${r.stderr}`)
  })
}

await main()
for (const f of failures) console.log(`  ${f}`)
console.log(`solid-oidc: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${passed + failed + skipped})`)
process.exitCode = failed > 0 ? 1 : 0
