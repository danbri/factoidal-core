// Host tests for storage-server authorization of the LWS 1.0 editor's
// draft (w3c/lws-protocol 9a08ff65, 2026-10-19, section "Authorization").
// https://github.com/danbri/factoidal/issues/886
//
//   node tests/lws/authorization.mjs
//
// A local authorization server runs in this process: it serves
// /.well-known/lws-configuration (RFC 8414 metadata with `jwks_uri`) and a
// JWK Set, and this file signs ES256 access tokens (RFC 9068 shape) with
// node:crypto. The storage server is `npm/factoidal/lws/server.mjs`; every
// decision checked here (status, WWW-Authenticate, metadata document,
// signature, issuer, audience, expiry, access policy, key rotation) is made
// by `formal/lean4/L4Factoidal/LWS/Authorization.lean`, and signatures are
// verified by the vendored HACL* P-256 code in the wasm module.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import http from 'node:http'
import { generateKeyPairSync, sign, randomUUID } from 'node:crypto'
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

const ALICE = 'https://id.example/alice'
const BOB = 'https://id.example/bob'

const CHECKS = [
  'Discovery: a request with no token answers 401 with resource_metadata and the storage Link',
  'Protected Resource Metadata: the RFC 9728 document names the resource and the issuer',
  'Validation: a valid owner token writes and reads',
  'Validation: an expired token answers 401 invalid_token',
  'Validation: a token for another audience answers 401 invalid_token',
  'Validation: a token from an untrusted issuer answers 401 invalid_token',
  'Validation: a bad signature answers 401 invalid_token',
  'Validation: a token with iat in the future answers 401 invalid_token',
  'Presentation: a non-Bearer scheme answers 401 invalid_request',
  'Policy: a valid token whose agent has no access answers 403',
  'Validation: key rotation, a token under a new key is accepted after a refetch',
  'Discovery: the storage description is readable with no token',
  'Default: with no auth configuration an anonymous write answers 401',
  'Development mode: insecureNoAuth must be asked for, and then writes need no token',
  'CLI: factoidal lws-serve with no authorization option refuses to start',
  'Notifications: an anonymous subscription request answers 401 with resource_metadata',
  'Notifications: a subscription naming a resource the agent cannot read answers 403',
  'Notifications: an agent may subscribe to what it can read, and not to that plus a private container',
  'Notifications: a subscriber hears of an update it may read and never of a member it may not read',
  'Discovery: the 401 lws#storage link, the storage description id and every other lws#storage link name one IRI',
  'Validation: a token for the storage root container (not the storage) answers 401 invalid_token',
  'Access grants: a read grant lets bob read and nothing more; revoking it ends the access',
  'Access grants: only the storage controller creates or revokes a grant; the endpoint needs a token',
  'Access grants: a foaf:Agent grant makes a resource public until it is revoked',
  'Access grants: dateTime, format, type and client constraints must all hold',
  'Access grants: a move needs delete of the resource and create in the destination',
  'Access grants: a read grant lets bob subscribe; after the revocation a subscription is refused',
  'Type search results resource (unstable, issue 922): alice reads her results; bob, another client and an anonymous request get 404 and none of her results; 410 after the lifetime',
  'Type search: results, totalItems and the type index hold only what the agent may read; anonymous and revoked access see nothing (issue 912)']

/** A local webhook receiver that records every POST and answers 202. */
async function startReceiver () {
  const got = []
  const server = http.createServer((req, res) => {
    const chunks = []
    req.on('data', (c) => chunks.push(c))
    req.on('end', () => {
      let body = null
      try { body = JSON.parse(Buffer.concat(chunks).toString('utf8')) } catch (_error) { body = null }
      got.push({ path: req.url, body })
      res.statusCode = 202
      res.end()
    })
  })
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
  return {
    origin: `http://127.0.0.1:${server.address().port}`,
    got,
    close () { return new Promise((resolve) => server.close(resolve)) }
  }
}

function b64url (bytes) {
  return Buffer.from(bytes).toString('base64url')
}

/** A local authorization server with a rotating ES256 key. */
async function startIssuer () {
  const keys = []
  function addKey (kid) {
    const pair = generateKeyPairSync('ec', { namedCurve: 'P-256' })
    const jwk = pair.publicKey.export({ format: 'jwk' })
    keys.push({ kid, privateKey: pair.privateKey, jwk: { ...jwk, kid, alg: 'ES256', use: 'sig' } })
    return keys[keys.length - 1]
  }
  addKey('k1')
  let published = keys.slice()
  const server = http.createServer((req, res) => {
    const url = new URL(req.url, 'http://x')
    if (url.pathname === '/.well-known/lws-configuration') {
      res.setHeader('content-type', 'application/json')
      res.end(JSON.stringify({
        issuer: origin,
        jwks_uri: `${origin}/jwks`,
        token_endpoint: `${origin}/token`,
        grant_types_supported: ['urn:ietf:params:oauth:grant-type:token-exchange']
      }))
    } else if (url.pathname === '/jwks') {
      res.setHeader('content-type', 'application/json')
      res.end(JSON.stringify({ keys: published.map((k) => k.jwk) }))
    } else {
      res.statusCode = 404
      res.end()
    }
  })
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
  const origin = `http://127.0.0.1:${server.address().port}`
  return {
    origin,
    keys,
    rotate (kid) { const k = addKey(kid); published = [k]; return k },
    token (claims, { key = keys[0], kid } = {}) {
      const header = { alg: 'ES256', typ: 'at+jwt', kid: kid !== undefined ? kid : key.kid }
      const input = `${b64url(JSON.stringify(header))}.${b64url(JSON.stringify(claims))}`
      const sig = sign('sha256', Buffer.from(input), { key: key.privateKey, dsaEncoding: 'ieee-p1363' })
      return `${input}.${b64url(sig)}`
    },
    close () { return new Promise((resolve) => server.close(resolve)) }
  }
}

function claims (issuer, audience, sub, { exp, iat } = {}) {
  const now = Math.floor(Date.now() / 1000)
  return {
    iss: issuer,
    sub,
    aud: audience,
    client_id: 'https://app.example/id',
    jti: randomUUID(),
    iat: iat !== undefined ? iat : now,
    exp: exp !== undefined ? exp : now + 300
  }
}

async function main () {
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  const { listen, lwsOpsAvailable } = await import('../../npm/factoidal/lws/server.mjs')
  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const name of CHECKS) skip(name, `the Lean engine did not load: ${error.message}`)
    return
  }
  const probe = await lwsOpsAvailable(engine)
  if (!probe.available) {
    for (const name of CHECKS) skip(name, probe.reason)
    return
  }
  try {
    engine.call('lwsFetched', ['no-such-handle', '{}'])
  } catch (error) {
    if (String(error.message).indexOf('unknown op') >= 0) {
      for (const name of CHECKS) skip(name, 'the module carries no lwsFetched op (rebuild the wasm)')
      return
    }
  }

  const issuer = await startIssuer()
  const other = await startIssuer()
  const running = await listen({
    engine,
    port: 0,
    owner: ALICE,
    realClock: true,
    auth: { issuers: [{ issuer: issuer.origin }], refreshInterval: 0 }
  })
  const o = running.origin
  // The storage IRI is the storage description's id
  // (https://github.com/danbri/factoidal/issues/911, F4); the token audience
  // and the 401 lws#storage link name it.
  const aud = `${o}/.well-known/lws-storage`
  const bearer = (t) => ({ authorization: `Bearer ${t}` })
  const put = (path, headers = {}) => fetch(`${o}${path}`, {
    method: 'PUT', headers: { 'content-type': 'text/plain', ...headers }, body: 'x'
  })
  try {
    let challenge = null
    await check(CHECKS[0], async () => {
      const r = await put('/private/a.txt')
      await r.text()
      assert(r.status === 401, `answered ${r.status}`)
      challenge = r.headers.get('www-authenticate') || ''
      assert(/^Bearer resource_metadata="[^"]+"$/.test(challenge), `WWW-Authenticate: ${challenge}`)
      const link = r.headers.get('link') || ''
      assert(link.indexOf(`<${aud}>`) >= 0 && link.indexOf('https://www.w3.org/ns/lws#storage') >= 0,
        `Link: ${link}`)
    })

    await check(CHECKS[1], async () => {
      const m = /resource_metadata="([^"]+)"/.exec(challenge || '')
      assert(m !== null, 'no resource_metadata')
      const url = new URL(m[1])
      assert(url.origin === o, `metadata URL ${m[1]} is not on the storage origin`)
      const r = await fetch(m[1])
      const doc = await r.json()
      assert(r.status === 200, `answered ${r.status}`)
      assert(doc.resource === `${o}/private/a.txt`, `resource ${doc.resource}`)
      assert(Array.isArray(doc.authorization_servers) &&
        doc.authorization_servers.length === 1 && doc.authorization_servers[0] === issuer.origin,
        JSON.stringify(doc.authorization_servers))
    })

    await check(CHECKS[2], async () => {
      const t = issuer.token(claims(issuer.origin, aud, ALICE))
      const w = await put('/private/a.txt', bearer(t))
      await w.text()
      assert(w.status === 201, `PUT answered ${w.status}`)
      const g = await fetch(`${o}/private/a.txt`, { headers: bearer(t) })
      const body = await g.text()
      assert(g.status === 200 && body === 'x', `GET answered ${g.status} ${body}`)
      const anon = await fetch(`${o}/private/a.txt`)
      await anon.text()
      assert(anon.status === 401, `anonymous GET answered ${anon.status}`)
    })

    const refusedWith = async (token, code, headers = null) => {
      const r = await put('/private/b.txt', headers !== null ? headers : bearer(token))
      await r.text()
      assert(r.status === 401, `answered ${r.status}`)
      const h = r.headers.get('www-authenticate') || ''
      assert(h.indexOf('resource_metadata=') >= 0, `no resource_metadata: ${h}`)
      assert(h.indexOf(`error="${code}"`) >= 0, `WWW-Authenticate: ${h}`)
    }
    const now = Math.floor(Date.now() / 1000)

    await check(CHECKS[3], () => refusedWith(
      issuer.token(claims(issuer.origin, aud, ALICE, { iat: now - 1000, exp: now - 600 })), 'invalid_token'))
    await check(CHECKS[4], () => refusedWith(
      issuer.token(claims(issuer.origin, 'https://storage.example/other/', ALICE)), 'invalid_token'))
    await check(CHECKS[5], () => refusedWith(
      other.token(claims(other.origin, aud, ALICE)), 'invalid_token'))
    await check(CHECKS[6], () => refusedWith(
      // Signed by the other issuer's key, under this issuer's name and kid.
      issuer.token(claims(issuer.origin, aud, ALICE), { key: other.keys[0], kid: 'k1' }), 'invalid_token'))
    await check(CHECKS[7], () => refusedWith(
      issuer.token(claims(issuer.origin, aud, ALICE, { iat: now + 3600, exp: now + 3900 })), 'invalid_token'))
    await check(CHECKS[8], () => refusedWith(null, 'invalid_request', { authorization: 'Basic dXNlcjpwdw==' }))

    await check(CHECKS[9], async () => {
      const t = issuer.token(claims(issuer.origin, aud, BOB))
      const r = await put('/private/c.txt', bearer(t))
      await r.text()
      assert(r.status === 403, `answered ${r.status}`)
    })

    await check(CHECKS[10], async () => {
      // The engine fetches keys at most once per second per issuer.
      await new Promise((resolve) => setTimeout(resolve, 1100))
      const k2 = issuer.rotate('k2')
      const t = issuer.token(claims(issuer.origin, aud, ALICE), { key: k2 })
      const r = await put('/private/d.txt', bearer(t))
      await r.text()
      assert(r.status === 201, `answered ${r.status}`)
    })

    await check(CHECKS[11], async () => {
      const r = await fetch(`${o}/.well-known/lws-storage`)
      await r.text()
      assert(r.status === 200, `answered ${r.status}`)
    })

    await check(CHECKS[19], async () => {
      const storageLink = (link) => {
        const m = /<([^>]+)>; rel="https:\/\/www\.w3\.org\/ns\/lws#storage"/.exec(link || '')
        return m === null ? null : new URL(m[1], `${o}/`).href
      }
      const r401 = await fetch(`${o}/private/a.txt`)
      await r401.text()
      assert(r401.status === 401, `anonymous GET answered ${r401.status}`)
      const d = await fetch(`${o}/.well-known/lws-storage`)
      const desc = await d.json()
      // The key published after the rotation check above.
      const t = issuer.token(claims(issuer.origin, aud, ALICE), { key: issuer.keys[issuer.keys.length - 1] })
      const g = await fetch(`${o}/private/a.txt`, { headers: bearer(t) })
      await g.text()
      assert(g.status === 200, `owner GET answered ${g.status}`)
      const iris = [storageLink(r401.headers.get('link')), desc.id,
        storageLink(d.headers.get('link')), storageLink(g.headers.get('link'))]
      assert(iris.every((i) => i === aud), `storage IRIs ${JSON.stringify(iris)}, expected ${aud}`)
    })

    await check(CHECKS[20], () => refusedWith(
      issuer.token(claims(issuer.origin, `${o}/`, ALICE), { key: issuer.keys[issuer.keys.length - 1] }),
      'invalid_token'))

    // LWS §Subscription Authorization (https://github.com/danbri/factoidal/issues/890),
    // decided by formal/lean4/L4Factoidal/LWS/Notifications.lean with Web
    // Access Control over the storage's ACL resources.
    const receiver = await startReceiver()
    try {
      // The key-rotation check above left only the newest key published.
      const current = { key: issuer.keys[issuer.keys.length - 1] }
      const aliceT = issuer.token(claims(issuer.origin, aud, ALICE), current)
      const bobT = issuer.token(claims(issuer.origin, aud, BOB), current)
      const endpoint = `${o}/.well-known/lws-subscriptions/`
      const subscribe = (token, topic, hook) => fetch(endpoint, {
        method: 'POST',
        headers: { 'content-type': 'application/lws+json', ...(token ? bearer(token) : {}) },
        body: JSON.stringify({ type: 'WebhookSubscription', topic, inbox: `${receiver.origin}/hook/${hook}` })
      })
      const write = async (path, body, contentType = 'text/plain', method = 'PUT') => {
        const r = await fetch(`${o}${path}`, { method, headers: { 'content-type': contentType, ...bearer(aliceT) }, body })
        await r.text()
        assert(r.status === 201 || r.status === 204, `${method} ${path} answered ${r.status}`)
        return r
      }
      const acl = (target, bobDefault) => '@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n' +
        `<${o}${target}.acl#owner> a acl:Authorization ; acl:agent <${ALICE}> ; acl:accessTo <${o}${target}> ;` +
        (target.endsWith('/') ? ` acl:default <${o}${target}> ;` : '') +
        ' acl:mode acl:Read, acl:Write, acl:Control .\n' +
        `<${o}${target}.acl#bob> a acl:Authorization ; acl:agent <${BOB}> ; acl:accessTo <${o}${target}> ;` +
        (bobDefault ? ` acl:default <${o}${target}> ;` : '') + ' acl:mode acl:Read .\n'

      await check(CHECKS[15], async () => {
        const r = await subscribe(null, [`${o}/private/a.txt`], 'anon')
        await r.text()
        assert(r.status === 401, `answered ${r.status}`)
        assert((r.headers.get('www-authenticate') || '').indexOf('resource_metadata=') >= 0,
          `WWW-Authenticate: ${r.headers.get('www-authenticate')}`)
      })

      await check(CHECKS[16], async () => {
        const r = await subscribe(bobT, [`${o}/private/a.txt`], 'bob1')
        await r.text()
        assert(r.status === 403, `answered ${r.status}`)
      })

      await check(CHECKS[17], async () => {
        await write('/shared/doc.txt', 'bob may read this')
        await write('/shared/doc.txt.acl', acl('/shared/doc.txt', false), 'text/turtle')
        const ok = await subscribe(bobT, [`${o}/shared/doc.txt`], 'bob2')
        const j = await ok.json()
        assert(ok.status === 201 && typeof j.subscription === 'string', `answered ${ok.status} ${JSON.stringify(j)}`)
        const both = await subscribe(bobT, [`${o}/shared/doc.txt`, `${o}/private/`], 'bob3')
        await both.text()
        assert(both.status === 403, `with a private container: ${both.status}`)
        // Negative: bob cannot see alice's subscriptions, nor alice bob's.
        const mine = await (await fetch(endpoint, { headers: bearer(aliceT) })).json()
        assert(!mine.items.some((i) => i.id === j.subscription), JSON.stringify(mine))
        const other = await fetch(j.subscription, { headers: bearer(aliceT) })
        await other.text()
        assert(other.status === 404, `alice reading bob's subscription answered ${other.status}`)
      })

      await check(CHECKS[18], async () => {
        await write('/box/', '', 'text/turtle')
        await write('/box/.acl', acl('/box/', false), 'text/turtle')
        await write('/box/visible.txt', 'bob may read this')
        await write('/box/visible.txt.acl', acl('/box/visible.txt', false), 'text/turtle')
        const r = await subscribe(bobT, [`${o}/box/`], 'box')
        await r.text()
        assert(r.status === 201, `bob subscribing to the box answered ${r.status}`)
        const created = await write('/box/', 'not for bob', 'text/plain', 'POST')
        const secret = new URL(created.headers.get('location'), `${o}/`).href
        const peek = await fetch(secret, { headers: bearer(bobT) })
        await peek.text()
        assert(peek.status === 403, `bob reading the new member answered ${peek.status}`)
        await write('/box/visible.txt', 'bob may read this, updated')
        await (await running.storage()).settled()
        const ids = receiver.got.filter((d) => d.path === '/hook/box').flatMap((d) =>
          Array.isArray(d.body.activity) ? d.body.activity : [d.body.activity])
        assert(ids.some((a) => a.type.includes('Update') && a.object.id === `${o}/box/visible.txt`),
          JSON.stringify(ids))
        assert(!ids.some((a) => a.object.id === secret), `bob heard of ${secret}`)
      })

      await check(CHECKS[CHECKS.length - 1], async () => {
        const run = randomUUID()
        const A = `https://ex.org/t/${run}#A`
        const B = `https://ex.org/t/${run}#B`
        const typed = async (path, type) => {
          const r = await fetch(`${o}${path}`, { method: 'PUT', headers: { 'content-type': 'text/plain', prefer: 'set-linkset', link: `<${type}>; rel="type"`, ...bearer(aliceT) }, body: 'x' })
          await r.text()
          assert(r.status === 201 || r.status === 204, `PUT ${path} answered ${r.status}`)
        }
        await typed('/idx/a.txt', A)
        await typed('/idx/b.txt', B)
        await write('/idx/a.txt.acl', acl('/idx/a.txt', false), 'text/turtle')
        const search = async (token, type) => {
          const r = await fetch(`${o}/.well-known/lws-type-search`, {
            method: 'QUERY',
            headers: { 'content-type': 'application/lws-query+json', ...(token ? bearer(token) : {}) },
            body: JSON.stringify({ type: [[A, B]] })
          })
          const j = await r.json()
          assert(r.status === 200, `search answered ${r.status} ${JSON.stringify(j)}`)
          return j
        }
        const types = async (token) => {
          const r = await fetch(`${o}/.well-known/lws-type-index`, { headers: token ? bearer(token) : {} })
          const j = await r.json()
          assert(r.status === 200 && r.headers.get('cache-control') === 'private', `type index answered ${r.status}`)
          return j.items.map((x) => x.id)
        }
        const forAlice = await search(aliceT)
        assert(JSON.stringify(forAlice.items.map((x) => x.id)) === JSON.stringify([`${o}/idx/a.txt`, `${o}/idx/b.txt`]), JSON.stringify(forAlice))
        const forBob = await search(bobT)
        assert(JSON.stringify(forBob.items.map((x) => x.id)) === JSON.stringify([`${o}/idx/a.txt`]), JSON.stringify(forBob))
        assert(forBob.totalItems === 1, `bob's totalItems ${forBob.totalItems}`)
        const bobTypes = await types(bobT)
        assert(bobTypes.includes(A) && !bobTypes.includes(B), JSON.stringify(bobTypes))
        const aliceTypes = await types(aliceT)
        assert(aliceTypes.includes(A) && aliceTypes.includes(B), JSON.stringify(aliceTypes))
        const anon = await search(null)
        assert(anon.items.length === 0 && anon.totalItems === 0, JSON.stringify(anon))
        const bad = await fetch(`${o}/.well-known/lws-type-search`, { method: 'QUERY', headers: { 'content-type': 'application/lws-query+json', authorization: 'Bearer not.a.token' }, body: '{}' })
        await bad.text()
        assert(bad.status === 401, `a refused token answered ${bad.status}`)
        // Revocation takes effect on the next request.
        const del = await fetch(`${o}/idx/a.txt.acl`, { method: 'DELETE', headers: bearer(aliceT) })
        await del.text()
        assert(del.status === 204, `deleting the ACL answered ${del.status}`)
        const after = await search(bobT)
        assert(after.items.length === 0 && after.totalItems === 0, JSON.stringify(after))
        assert(!(await types(bobT)).includes(A), 'the type index still lists A for bob')
      })

      // LWS §Access Requests and Grants (https://github.com/danbri/factoidal/issues/913),
      // decided by formal/lean4/L4Factoidal/LWS/AccessPolicy.lean (what a
      // grant permits), AccessGrants.lean (the endpoints) and
      // Authorization.decide (enforcement beside Web Access Control).
      const grantsUrl = `${o}/.well-known/lws-access-grants/`
      const grantDoc = (assignee, actions, targets, policy = {}) => ({
        '@context': ['https://www.w3.org/ns/lws/v1'],
        type: ['AccessGrant'],
        storage: aud,
        access: [Object.assign({
          type: ['AccessPolicy'], action: actions, assignee,
          target: { type: 'StorageResource', value: targets.map((t) => `${o}${t}`) }
        }, policy)]
      })
      const grantAs = async (token, doc) => {
        const r = await fetch(grantsUrl, {
          method: 'POST', headers: { 'content-type': 'application/lws+json', ...(token ? bearer(token) : {}) },
          body: JSON.stringify(doc)
        })
        await r.text()
        return r
      }
      const grant = async (doc) => {
        const r = await grantAs(aliceT, doc)
        assert(r.status === 201, `the grant answered ${r.status}`)
        return new URL(r.headers.get('location'), grantsUrl).href
      }
      const revoke = async (url) => {
        const r = await fetch(url, { method: 'DELETE', headers: bearer(aliceT) })
        await r.text()
        assert(r.status === 204, `revoking answered ${r.status}`)
      }
      const statusOf = async (path, token, init = {}) => {
        const r = await fetch(`${o}${path}`, { ...init, headers: { ...(init.headers || {}), ...(token ? bearer(token) : {}) } })
        await r.text()
        return r.status
      }
      await write('/granted/', '', 'text/turtle')
      await write('/granted/doc.txt', 'for bob')
      await write('/granted/c.csv', 'a,b', 'text/csv')
      await write('/granted/dest/', '', 'text/turtle')
      await write('/granted/m.txt', 'moved')

      await check('Access grants: a read grant lets bob read and nothing more; revoking it ends the access', async () => {
        assert(await statusOf('/granted/doc.txt', bobT) === 403, 'bob read before the grant')
        const g = await grant(grantDoc(BOB, ['read'], ['/granted/doc.txt']))
        assert(await statusOf('/granted/doc.txt', bobT) === 200, 'bob cannot read with the grant')
        const put = await statusOf('/granted/doc.txt', bobT, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'bob' })
        assert(put === 403, `bob PUT answered ${put}`)
        assert(await statusOf('/granted/c.csv', bobT) === 403, 'the grant reached another resource')
        assert(await statusOf('/granted/', bobT) === 403, 'the grant reached the container')
        assert(await statusOf('/granted/doc.txt', null) === 401, 'the grant reached the anonymous agent')
        await revoke(g)
        assert(await statusOf('/granted/doc.txt', bobT) === 403, 'bob still reads after the revocation')
      })

      await check('Access grants: only the storage controller creates or revokes a grant; the endpoint needs a token', async () => {
        const r = await grantAs(bobT, grantDoc(BOB, ['read'], ['/granted/doc.txt']))
        assert(r.status === 403, `bob's grant answered ${r.status}`)
        const a = await grantAs(null, grantDoc(BOB, ['read'], ['/granted/doc.txt']))
        assert(a.status === 401, `an anonymous grant answered ${a.status}`)
        assert(await statusOf('/granted/doc.txt', bobT) === 403, 'a refused grant took effect')
        const g = await grant(grantDoc(BOB, ['read'], ['/granted/doc.txt']))
        const d = await statusOf(new URL(g).pathname, bobT, { method: 'DELETE' })
        assert(d === 403, `bob revoking answered ${d}`)
        assert(await statusOf(new URL(g).pathname, bobT) === 200, 'bob cannot read the grant that names him')
        await revoke(g)
      })

      await check('Access grants: a foaf:Agent grant makes a resource public until it is revoked', async () => {
        const g = await grant(grantDoc('http://xmlns.com/foaf/0.1/Agent', ['read'], ['/granted/doc.txt']))
        assert(await statusOf('/granted/doc.txt', null) === 200, 'anonymous read refused')
        await revoke(g)
        assert(await statusOf('/granted/doc.txt', null) === 401, 'anonymous read after the revocation')
      })

      await check('Access grants: dateTime, format, type and client constraints must all hold', async () => {
        const constrained = async (targets, constraint) => grant(grantDoc(BOB, ['read'], targets, { constraint }))
        const closed = await constrained(['/granted/doc.txt'], [
          { leftOperand: 'dateTime', operator: 'gteq', rightOperand: '2000-01-01T00:00:00Z' },
          { leftOperand: 'dateTime', operator: 'lteq', rightOperand: '2000-01-02T00:00:00Z' }])
        assert(await statusOf('/granted/doc.txt', bobT) === 403, 'a closed window permitted')
        await revoke(closed)
        const open = await constrained(['/granted/doc.txt'], [
          { leftOperand: 'dateTime', operator: 'gteq', rightOperand: '2000-01-01T00:00:00Z' },
          { leftOperand: 'dateTime', operator: 'lteq', rightOperand: '2999-12-31T23:59:59Z' }])
        assert(await statusOf('/granted/doc.txt', bobT) === 200, 'an open window refused')
        await revoke(open)
        const format = await constrained(['/granted/doc.txt', '/granted/c.csv'], [
          { leftOperand: 'format', operator: 'isAnyOf', rightOperand: ['text/plain', 'application/json'] }])
        assert(await statusOf('/granted/doc.txt', bobT) === 200 && await statusOf('/granted/c.csv', bobT) === 403, 'format')
        await revoke(format)
        const type = await constrained(['/granted/', '/granted/doc.txt'], [
          { leftOperand: 'type', operator: 'eq', rightOperand: 'https://www.w3.org/ns/lws#DataResource' }])
        assert(await statusOf('/granted/doc.txt', bobT) === 200 && await statusOf('/granted/', bobT) === 403, 'type')
        await revoke(type)
        const other = await constrained(['/granted/doc.txt'], [
          { leftOperand: 'client', operator: 'eq', rightOperand: 'urn:x:not-this-client' }])
        assert(await statusOf('/granted/doc.txt', bobT) === 403, 'another client was permitted')
        await revoke(other)
        const mine = await constrained(['/granted/doc.txt'], [
          { leftOperand: 'client', operator: 'eq', rightOperand: 'https://app.example/id' }])
        assert(await statusOf('/granted/doc.txt', bobT) === 200, 'the token client_id was refused')
        await revoke(mine)
      })

      await check('Access grants: a move needs delete of the resource and create in the destination', async () => {
        const move = () => statusOf('/granted/m.txt?linkset', bobT, {
          method: 'PATCH',
          headers: { 'content-type': 'application/json-patch+json' },
          body: JSON.stringify([{ op: 'replace', path: '/linkset/0/up/0/href', value: `${o}/granted/dest/` }])
        })
        const g1 = await grant(grantDoc(BOB, ['read', 'modify', 'delete'], ['/granted/m.txt']))
        const g2 = await grant(grantDoc(BOB, ['read'], ['/granted/dest/']))
        assert(await move() === 403, 'moved without create in the destination')
        await revoke(g1)
        await revoke(g2)
        const g3 = await grant(grantDoc(BOB, ['read', 'modify'], ['/granted/m.txt']))
        const g4 = await grant(grantDoc(BOB, ['read', 'create'], ['/granted/dest/']))
        assert(await move() === 403, 'moved without delete of the resource')
        const g5 = await grant(grantDoc(BOB, ['delete'], ['/granted/m.txt']))
        const s = await move()
        assert(s === 200, `the move with all three answered ${s}`)
        for (const g of [g3, g4, g5]) await revoke(g)
      })

      await check('Access grants: a read grant lets bob subscribe; after the revocation a subscription is refused', async () => {
        const g = await grant(grantDoc(BOB, ['read'], ['/granted/doc.txt']))
        const ok = await subscribe(bobT, [`${o}/granted/doc.txt`], 'grant')
        const j = await ok.json()
        assert(ok.status === 201, `subscribe with the grant answered ${ok.status}`)
        await fetch(j.subscription, { method: 'DELETE', headers: bearer(bobT) }).then((x) => x.text())
        await revoke(g)
        const no = await subscribe(bobT, [`${o}/granted/doc.txt`], 'grant')
        await no.text()
        assert(no.status === 403, `subscribe after the revocation answered ${no.status}`)
      })
    } finally {
      await receiver.close()
    }
  } finally {
    await running.close()
  }

  await check(CHECKS[12], async () => {
    const s = await listen({ engine, port: 0 })
    try {
      const r = await fetch(`${s.origin}/x`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' })
      await r.text()
      assert(r.status === 401, `answered ${r.status}`)
    } finally {
      await s.close()
    }
  })

  await check(CHECKS[13], async () => {
    const s = await listen({ engine, port: 0, insecureNoAuth: true })
    try {
      const r = await fetch(`${s.origin}/x`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' })
      await r.text()
      assert(r.status === 201, `answered ${r.status}`)
    } finally {
      await s.close()
    }
    let refused = false
    try {
      await listen({ engine, port: 0, insecureNoAuth: true, auth: { issuers: [] } })
    } catch (_error) {
      refused = true
    }
    assert(refused, 'auth and insecureNoAuth together were accepted')
  })

  await check(CHECKS[14], async () => {
    const cli = fileURLToPath(new URL('../../npm/factoidal/bin/factoidal.mjs', import.meta.url))
    const r = spawnSync(process.execPath, [cli, 'lws-serve', '/nonexistent-lws-dir', '--port', '0'],
      { encoding: 'utf8', timeout: 60000 })
    assert(r.status !== 0, `exit ${r.status}`)
    assert((r.stderr || '').indexOf('--insecure-no-auth') >= 0, `stderr: ${r.stderr}`)
  })

  // ANTICIPATORY AND UNSTABLE (https://github.com/danbri/factoidal/issues/922):
  // the type search results resource named by Content-Location, with real
  // tokens. lws10-index: "a server that nonetheless exposes one MUST subject
  // it to the same authorization filtering on every access and MUST prevent
  // its reuse across clients."
  await check(CHECKS[CHECKS.length - 2], async () => {
    const rs = await listen({
      engine,
      port: 0,
      owner: ALICE,
      realClock: true,
      searchResults: true,
      searchResultsTtl: 2,
      auth: { issuers: [{ issuer: issuer.origin }], refreshInterval: 0 }
    })
    try {
      const ro = rs.origin
      const raud = `${ro}/.well-known/lws-storage`
      const bearer = (t) => ({ authorization: `Bearer ${t}` })
      // The key the issuer publishes now (an earlier check rotates it).
      const signing = { key: issuer.keys[issuer.keys.length - 1] }
      const aliceT = issuer.token(claims(issuer.origin, raud, ALICE), signing)
      const aliceOtherClient = issuer.token({ ...claims(issuer.origin, raud, ALICE), client_id: 'https://other-app.example/id' }, signing)
      const bobT = issuer.token(claims(issuer.origin, raud, BOB), signing)
      const T = `https://ex.org/t/${randomUUID()}#Secret`
      const w = await fetch(`${ro}/private/secret.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain', prefer: 'set-linkset', link: `<${T}>; rel="type"`, ...bearer(aliceT) }, body: 'secret' })
      const wt = await w.text()
      assert(w.status === 201, `PUT answered ${w.status} ${w.headers.get('www-authenticate')} ${wt}`)
      const query = (headers) => fetch(`${ro}/.well-known/lws-type-search`, {
        method: 'QUERY', headers: { 'content-type': 'application/lws-query+json', ...headers }, body: JSON.stringify({ type: [T] })
      })
      const q = await query(bearer(aliceT))
      const qj = await q.json()
      assert(q.status === 200 && qj.items.length === 1, `alice's QUERY answered ${q.status} ${JSON.stringify(qj)}`)
      const results = q.headers.get('content-location')
      assert(results !== null, 'no Content-Location')
      // alice, with the same client: her results.
      const mine = await fetch(results, { headers: bearer(aliceT) })
      const mj = await mine.json()
      assert(mine.status === 200 && mj.items.length === 1 && mj.items[0].id === `${ro}/private/secret.txt`, `alice's GET answered ${mine.status} ${JSON.stringify(mj)}`)
      // bob: 404, and nothing of alice's result reaches him.
      const his = await fetch(results, { headers: bearer(bobT) })
      const hb = await his.text()
      assert(his.status === 404, `bob's GET answered ${his.status}`)
      assert(hb.indexOf('#Secret') < 0 && hb.indexOf('secret.txt') < 0, `bob saw ${hb}`)
      // alice through another client, and an anonymous request: 404.
      const other = await fetch(results, { headers: bearer(aliceOtherClient) })
      await other.text()
      assert(other.status === 404, `alice through another client answered ${other.status}`)
      const anon = await fetch(results)
      await anon.text()
      assert(anon.status === 404, `an anonymous GET answered ${anon.status}`)
      // An anonymous QUERY names no results resource.
      const aq = await query({})
      await aq.text()
      assert(aq.status === 200 && aq.headers.get('content-location') === null, `anonymous QUERY: ${aq.status} ${aq.headers.get('content-location')}`)
      // After searchResultsTtl (2 s here): 410 for alice, still 404 for bob.
      await new Promise((resolve) => setTimeout(resolve, 3100))
      const late = await fetch(results, { headers: bearer(aliceT) })
      await late.text()
      assert(late.status === 410, `alice's GET after the lifetime answered ${late.status}`)
      const lateBob = await fetch(results, { headers: bearer(bobT) })
      await lateBob.text()
      assert(lateBob.status === 404, `bob's GET after the lifetime answered ${lateBob.status}`)
    } finally {
      await rs.close()
    }
  })

  await issuer.close()
  await other.close()
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`lws-authorization node: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
