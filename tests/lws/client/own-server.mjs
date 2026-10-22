// Host tests of the LWS client (https://github.com/danbri/factoidal/issues/917)
// against this repository's LWS server (`npm/factoidal/lws/server.mjs`).
//
//   node tests/lws/client/own-server.mjs
//
// The client is `npm/factoidal/lws/client.mjs`; every decision it makes is
// `formal/lean4/L4Factoidal/LWS/Client/` (the wasm ops lwsClientStart and
// lwsClientStep). A recording `fetch` keeps every request the client sends,
// so a check can say what went on the wire. A local authorization server in
// this file does RFC 8693 token exchange (ES256 access tokens from
// node:crypto) for the checks with authorization on.
//
// Client and server are ours on both ends, so a shared misreading of the
// drafts passes here: tools/lws-touchstone-client.sh runs the client against
// Touchstone's client lab, another implementer's reading.
//
// Check names start with the draft section they check.
// Score line: "N pass, M fail, S skipped (out of T)".

import http from 'node:http'
import { generateKeyPairSync, sign, randomUUID } from 'node:crypto'
import { spawn } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { createServer as createNetServer } from 'node:net'
import { mkdtempSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { keyPair, didKeyOf } from '../../authz/fixtures.mjs'

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
const CREDENTIAL = 'alice-test-credential'
const SAML2 = 'urn:ietf:params:oauth:token-type:saml2'

const CHECKS = [
  'Discovery: discover reads the storage description named by rel lws#storage',
  'Create Resource: a container create carries Link rel=type lws#Container and gives its Location',
  'Create Resource: a data resource round-trips byte for byte (NUL and 0xFF)',
  'Update Resource: an update reads the ETag and sends If-Match with it',
  'Update Resource: a stale If-Match ends with preconditionFailed; with retry412 the client reads the tag again and succeeds',
  'Update Resource: Link fields on an update go with Prefer set-linkset',
  'Pagination: ten members over four pages, each member once, only URLs the server gave',
  'Metadata: readLinkset follows rel=linkset; updateLinkset by JSON Patch is conditional and changes the linkset',
  'Metadata: with no PUT advertised, a linkset document is not PUT',
  'Delete Resource: a container with members needs Depth infinity; without it the delete is refused',
  'Type Index and Type Search: the client finds a type and a resource of it',
  'Notifications: subscribe, receive a signed notification, verify it with the published key, unsubscribe',
  'Notifications: the receiver refuses a forged notification (signature, digest, keyid without fragment)',
  'Access Requests and Grants: request, grant, read the grant, revoke it',
  'Moving Resources: move changes the up link and the destination lists the resource',
  'Injected fetch: the client runs over a fetch that carries each request as a serialized message',
  'CLI: factoidal lws-client read prints the result; a failure exits 1',
  'Authorization: a 401 leads to the three checks, one token exchange for the storage, and the request with Bearer',
  'Authorization: a 401 whose storage puts its root on another origin gives no token request',
  'Authorization: a refused token is dropped and exchanged again',
  'Authorization: with no subject token the 401 is the result',
  'Authorization (lws10-authn-ssi-cid): a self-issued did:key credential, signed by the engine, exchanged at factoidal authz-serve'
]

function b64url (bytes) { return Buffer.from(bytes).toString('base64url') }

/** Wrap a fetch so every request is recorded. */
function recording (inner = globalThis.fetch) {
  const log = []
  const wire = async (url, init = {}) => {
    const headers = new Headers(init.headers || [])
    log.push({ url: String(url), method: init.method || 'GET', headers })
    return inner(url, init)
  }
  return { wire, log }
}

async function readBody (req) {
  const chunks = []
  for await (const chunk of req) chunks.push(chunk)
  return Buffer.concat(chunks).toString('utf8')
}

/** A local authorization server: RFC 8414 metadata, a JWK Set, and an RFC
 *  8693 token endpoint that exchanges CREDENTIAL for an ES256 access token
 *  whose audience is the `resource` asked for. */
async function startIssuer () {
  const pair = generateKeyPairSync('ec', { namedCurve: 'P-256' })
  const jwk = { ...pair.publicKey.export({ format: 'jwk' }), kid: 'k1', alg: 'ES256', use: 'sig' }
  const tokenRequests = []
  let origin = ''
  const token = (claims) => {
    const input = `${b64url(JSON.stringify({ alg: 'ES256', typ: 'at+jwt', kid: 'k1' }))}.${b64url(JSON.stringify(claims))}`
    return `${input}.${b64url(sign('sha256', Buffer.from(input), { key: pair.privateKey, dsaEncoding: 'ieee-p1363' }))}`
  }
  const server = http.createServer(async (req, res) => {
    const url = new URL(req.url, 'http://x')
    if (url.pathname === '/.well-known/lws-configuration') {
      res.setHeader('content-type', 'application/json')
      res.end(JSON.stringify({
        issuer: origin, jwks_uri: `${origin}/jwks`, token_endpoint: `${origin}/token`,
        grant_types_supported: ['urn:ietf:params:oauth:grant-type:token-exchange']
      }))
    } else if (url.pathname === '/jwks') {
      res.setHeader('content-type', 'application/json')
      res.end(JSON.stringify({ keys: [jwk] }))
    } else if (url.pathname === '/token' && req.method === 'POST') {
      const form = new URLSearchParams(await readBody(req))
      tokenRequests.push({ form, contentType: req.headers['content-type'] })
      res.setHeader('content-type', 'application/json')
      if (form.get('grant_type') !== 'urn:ietf:params:oauth:grant-type:token-exchange' ||
          form.get('subject_token') !== CREDENTIAL || !form.get('resource')) {
        res.statusCode = 400
        res.end(JSON.stringify({ error: 'invalid_request' }))
        return
      }
      const now = Math.floor(Date.now() / 1000)
      res.end(JSON.stringify({
        access_token: token({ iss: origin, sub: ALICE, aud: form.get('resource'), client_id: 'https://app.example/id',
          jti: randomUUID(), iat: now, exp: now + 300 }),
        token_type: 'Bearer', expires_in: 300
      }))
    } else {
      res.statusCode = 404
      res.end()
    }
  })
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
  origin = `http://127.0.0.1:${server.address().port}`
  return { origin, tokenRequests, close: () => new Promise((resolve) => server.close(resolve)) }
}

/** A stub server whose every resource answers a 401 that is in order but
 *  for its storage link: the storage description puts its root on another
 *  origin (lws10-core §Discovery Validation by a Client, check 3). */
async function startDecoy (issuerOrigin) {
  let origin = ''
  const server = http.createServer((req, res) => {
    const url = new URL(req.url, 'http://x')
    if (url.pathname.startsWith('/.well-known/oauth-protected-resource')) {
      res.setHeader('content-type', 'application/json')
      res.end(JSON.stringify({ resource: `${origin}${url.pathname.slice('/.well-known/oauth-protected-resource'.length)}`,
        authorization_servers: [issuerOrigin] }))
    } else if (url.pathname === '/storage') {
      res.setHeader('content-type', 'application/lws+cid')
      res.end(JSON.stringify({ id: `${origin}/storage`, type: 'Storage',
        service: [{ type: 'StorageRoot', serviceEndpoint: 'https://elsewhere.example/' }] }))
    } else {
      res.statusCode = 401
      res.setHeader('www-authenticate', `Bearer resource_metadata="${origin}/.well-known/oauth-protected-resource${url.pathname}"`)
      res.setHeader('link', `<${origin}/storage>; rel="https://www.w3.org/ns/lws#storage"`)
      res.end()
    }
  })
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
  origin = `http://127.0.0.1:${server.address().port}`
  return { origin, close: () => new Promise((resolve) => server.close(resolve)) }
}

async function rejects (promise, reason) {
  try {
    await promise
  } catch (error) {
    assert(error.reason === reason, `failed with ${error.reason} (${JSON.stringify(error.detail)}), expected ${reason}`)
    return error
  }
  throw new Error(`did not fail; expected ${reason}`)
}

async function main () {
  const { loadEngine } = await import('../../../npm/factoidal/bin/engine.mjs')
  const { listen, lwsOpsAvailable } = await import('../../../npm/factoidal/lws/server.mjs')
  const { createLwsClient, createNotificationReceiver, lwsClientOpsAvailable } =
    await import('../../../npm/factoidal/lws/client.mjs')
  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const name of CHECKS) skip(name, `the Lean engine did not load: ${error.message}`)
    return
  }
  for (const probe of [await lwsOpsAvailable(engine), await lwsClientOpsAvailable(engine)]) {
    if (!probe.available) {
      for (const name of CHECKS) skip(name, probe.reason)
      return
    }
  }

  const open = await listen({ engine, port: 0, insecureNoAuth: true, pageSize: 3, realClock: true })
  const noPut = await listen({ engine, port: 0, insecureNoAuth: true, linksetPut: false })
  const o = open.origin
  const rec = recording()
  const client = await createLwsClient({ engine, fetch: rec.wire })
  const sinceLog = () => { const n = rec.log.length; return () => rec.log.slice(n) }
  try {
    await check(CHECKS[0], async () => {
      const d = await client.discover(`${o}/`)
      assert(d.storage === `${o}/.well-known/lws-storage`, `storage ${d.storage}`)
      assert(Array.isArray(d.description.service), 'no services')
    })

    let notes = null
    await check(CHECKS[1], async () => {
      const seen = sinceLog()
      const r = await client.create(`${o}/`, { container: true, slug: 'notes' })
      notes = r.location
      assert(typeof notes === 'string' && notes.startsWith(o), `location ${notes}`)
      const post = seen().find((x) => x.method === 'POST')
      assert((post.headers.get('link') || '').indexOf('<https://www.w3.org/ns/lws#Container>; rel="type"') >= 0,
        `Link: ${post.headers.get('link')}`)
      const l = await client.list(notes)
      assert(Array.isArray(l.items) && l.items.length === 0, JSON.stringify(l))
    })

    let a = null
    await check(CHECKS[2], async () => {
      const bytes = new Uint8Array([0, 255, 1, 128, 10, 0])
      const r = await client.create(notes, { slug: 'a.bin', mediaType: 'application/octet-stream', body: bytes })
      a = r.location
      const g = await client.read(a)
      const got = Buffer.from(g.bodyBase64 || '', 'base64')
      assert(got.equals(Buffer.from(bytes)), `read back ${got.toString('hex')}`)
    })

    let t = null
    await check(CHECKS[3], async () => {
      t = (await client.create(notes, { slug: 't.txt', mediaType: 'text/plain', body: 'one' })).location
      const seen = sinceLog()
      await client.update(t, { mediaType: 'text/plain', body: 'two' })
      const sent = seen()
      assert(sent.map((x) => x.method).join(',') === 'HEAD,PUT', sent.map((x) => x.method).join(','))
      const im = sent[1].headers.get('if-match')
      assert(typeof im === 'string' && im.length > 0, 'no If-Match')
      const g = await client.read(t)
      assert(g.body === 'two', `read ${g.body}`)
    })

    await check(CHECKS[4], async () => {
      await rejects(client.update(t, { precondition: 'ifMatch', tag: '"stale"', mediaType: 'text/plain', body: 'x' }),
        'preconditionFailed')
      const seen = sinceLog()
      await client.update(t, { precondition: 'ifMatch', tag: '"stale"', retry412: 1, mediaType: 'text/plain', body: 'three' })
      assert(seen().map((x) => x.method).join(',') === 'PUT,HEAD,PUT', seen().map((x) => x.method).join(','))
      assert((await client.read(t)).body === 'three', 'not written')
    })

    await check(CHECKS[5], async () => {
      const seen = sinceLog()
      await client.update(t, { mediaType: 'text/plain', body: 'four', links: ['<https://e.example/Note>; rel="type"'] })
      const put = seen().find((x) => x.method === 'PUT')
      assert(put.headers.get('prefer') === 'set-linkset', `Prefer: ${put.headers.get('prefer')}`)
    })

    await check(CHECKS[6], async () => {
      const c = (await client.create(`${o}/`, { container: true, slug: 'many' })).location
      for (let i = 0; i < 10; i += 1) {
        await client.create(c, { slug: `m${i}`, mediaType: 'text/plain', body: String(i) })
      }
      const seen = sinceLog()
      const l = await client.list(c)
      assert(l.items.length === 10 && new Set(l.items).size === 10, JSON.stringify(l.items))
      assert(l.pages === 4, `pages ${l.pages}`)
      const gets = seen().filter((x) => x.method === 'GET')
      assert(gets.length === 4 && gets[0].url === c, gets.map((x) => x.url).join(' '))
    })

    await check(CHECKS[7], async () => {
      const ls = await client.readLinkset(t)
      assert(ls.linkset && Array.isArray(ls.linkset.linkset), JSON.stringify(ls))
      const seen = sinceLog()
      await client.updateLinkset(t, {
        body: JSON.stringify([{ op: 'add', path: '/linkset/0/https:~1~1e.example~1rel', value: [{ href: 'https://e.example/x' }] }])
      })
      const patch = seen().find((x) => x.method === 'PATCH')
      assert(patch && (patch.headers.get('if-match') || '') !== '', 'the PATCH carried no If-Match')
      const after = await client.readLinkset(t)
      assert(JSON.stringify(after.linkset).indexOf('https://e.example/x') >= 0, JSON.stringify(after.linkset))
    })

    await check(CHECKS[8], async () => {
      const np = await createLwsClient({ engine, fetch: rec.wire })
      const x = (await np.create(`${noPut.origin}/`, { slug: 'x.txt', mediaType: 'text/plain', body: 'x' })).location
      const seen = sinceLog()
      await rejects(np.updateLinkset(x, { mediaType: 'application/linkset+json', body: '{"linkset":[]}' }), 'notAdvertised')
      assert(!seen().some((r) => r.method === 'PUT'), 'a PUT was sent')
    })

    await check(CHECKS[9], async () => {
      const c = (await client.create(`${o}/`, { container: true, slug: 'gone' })).location
      await client.create(c, { slug: 'g.txt', mediaType: 'text/plain', body: 'g' })
      await rejects(client.delete(c), 'status')
      const seen = sinceLog()
      await client.delete(c, { recursive: true })
      assert(seen()[0].headers.get('depth') === 'infinity', 'no Depth')
      await rejects(client.read(c), 'status')
    })

    await check(CHECKS[10], async () => {
      await client.create(notes, { slug: 'typed.txt', mediaType: 'text/plain', body: 't', types: ['https://e.example/Recipe'] })
      const ix = await client.typeIndex(`${o}/`)
      assert(ix.items.includes('https://e.example/Recipe'), JSON.stringify(ix.items))
      const seen = sinceLog()
      const s = await client.search(`${o}/`, { query: { type: ['https://e.example/Recipe'] } })
      assert(s.items.length === 1 && s.items[0].endsWith('typed.txt'), JSON.stringify(s.items))
      const q = seen().find((x) => x.method === 'QUERY')
      assert(q.headers.get('content-type') === 'application/lws-query+json', 'no query Content-Type')
    })

    await check(CHECKS[11], async () => {
      const received = []
      const receiver = await createNotificationReceiver({ client, onNotification: (v, body) => received.push(body) })
      try {
        const sub = await client.subscribe(t, { inbox: `${receiver.url}hook/1` })
        assert(typeof sub.location === 'string', JSON.stringify(sub))
        await client.update(t, { mediaType: 'text/plain', body: 'five' })
        for (let i = 0; i < 50 && received.length === 0; i += 1) await new Promise((resolve) => setTimeout(resolve, 100))
        assert(received.length >= 1, `no notification accepted: ${JSON.stringify(receiver.received())}`)
        assert(receiver.received().every((v) => v.accept === true), JSON.stringify(receiver.received()))
        await client.unsubscribe(sub.location)
      } finally {
        await receiver.close()
      }
    })

    await check(CHECKS[12], async () => {
      const receiver = await createNotificationReceiver({ client })
      try {
        const body = '{"type":"Notification"}'
        const digest = 'sha-256=:' + (await import('node:crypto')).createHash('sha256').update(body).digest('base64') + ':'
        const kid = `${o}/.well-known/lws-storage#k`
        const send = (keyid, dig) => fetch(`${receiver.url}hook/2`, {
          method: 'POST',
          headers: {
            'content-type': 'application/lws+json', 'content-digest': dig,
            'signature-input': `sig1=("@method" "@scheme" "@authority" "@path" "content-type" "content-digest");created=1;keyid="${keyid}";alg="ed25519"`,
            signature: `sig1=:${Buffer.alloc(64, 7).toString('base64')}:`
          },
          body
        })
        for (const [keyid, dig] of [[kid, digest], [kid, 'sha-256=:AAAA:'], [`${o}/.well-known/lws-storage`, digest]]) {
          const r = await send(keyid, dig)
          await r.arrayBuffer()
          assert(r.status === 401, `answered ${r.status} for keyid ${keyid}`)
        }
        assert(receiver.received().every((v) => v.accept === false), JSON.stringify(receiver.received()))
      } finally {
        await receiver.close()
      }
    })

    await check(CHECKS[13], async () => {
      const req = await client.requestAccess(`${o}/`, { actions: ['read'], assignee: 'https://id.example/bob', targets: [t] })
      assert(typeof req.location === 'string', JSON.stringify(req))
      const grant = await client.grantAccess(`${o}/`, { actions: ['read'], assignee: 'https://id.example/bob', targets: [t] })
      assert(typeof grant.location === 'string', JSON.stringify(grant))
      const got = await client.getAccess(grant.location)
      assert(got.body.indexOf('AccessGrant') >= 0, got.body)
      await client.revokeAccess(grant.location)
      await rejects(client.getAccess(grant.location), 'status')
    })

    await check(CHECKS[14], async () => {
      const dest = (await client.create(`${o}/`, { container: true, slug: 'archive' })).location
      const m = (await client.create(notes, { slug: 'm.txt', mediaType: 'text/plain', body: 'm' })).location
      const r = await client.move(m, { destination: dest })
      const l = await client.list(dest)
      assert(l.items.includes(r.identifier), `${r.identifier} not in ${JSON.stringify(l.items)}`)
    })

    await check(CHECKS[15], async () => {
      // A transport that carries a request as a JSON message and gets a JSON
      // message back, as an XMPP-carried fetch does.
      const remote = async (message) => {
        const m = JSON.parse(message)
        const r = await fetch(m.url, { method: m.method, headers: m.headers,
          body: m.body === null ? undefined : Buffer.from(m.body, 'base64'), redirect: 'manual' })
        const headers = []
        r.headers.forEach((v, n) => headers.push([n, v]))
        return JSON.stringify({ status: r.status, headers, body: Buffer.from(await r.arrayBuffer()).toString('base64') })
      }
      let messages = 0
      const carried = async (url, init) => {
        messages += 1
        const reply = JSON.parse(await remote(JSON.stringify({ url, method: init.method, headers: init.headers,
          body: init.body === undefined ? null : Buffer.from(init.body).toString('base64') })))
        return new Response(reply.status === 204 || reply.status === 304 ? null : Buffer.from(reply.body, 'base64'),
          { status: reply.status, headers: reply.headers })
      }
      const c = await createLwsClient({ engine, fetch: carried })
      const g = await c.read(t)
      assert(g.body === 'five' && messages === 1, `${g.body} after ${messages} messages`)
    })

    await check(CHECKS[16], async () => {
      const cli = fileURLToPath(new URL('../../../npm/factoidal/bin/factoidal.mjs', import.meta.url))
      // The server runs in this process, so the CLI runs asynchronously.
      const run = (args) => new Promise((resolve) => {
        const child = spawn(process.execPath, [cli, ...args])
        let stdout = ''
        let stderr = ''
        child.stdout.on('data', (d) => { stdout += d })
        child.stderr.on('data', (d) => { stderr += d })
        child.on('close', (status) => resolve({ status, stdout, stderr }))
      })
      const ok = await run(['lws-client', 'read', t])
      assert(ok.status === 0, `exit ${ok.status}: ${ok.stderr}`)
      assert(JSON.parse(ok.stdout).body === 'five', ok.stdout)
      const bad = await run(['lws-client', 'read', `${o}/no-such`])
      assert(bad.status === 1, `exit ${bad.status}`)
      assert(JSON.parse(bad.stdout).fail.code === 'status', bad.stdout)
    })
  } finally {
    await open.close()
    await noPut.close()
  }

  const issuer = await startIssuer()
  const secured = await listen({ engine, port: 0, owner: ALICE, realClock: true,
    auth: { issuers: [{ issuer: issuer.origin }], refreshInterval: 0 } })
  const so = secured.origin
  try {
    await check(CHECKS[17], async () => {
      const r = recording()
      const c = await createLwsClient({ engine, fetch: r.wire, subjectToken: CREDENTIAL, subjectTokenType: SAML2 })
      const created = await c.create(`${so}/`, { slug: 'p.txt', mediaType: 'text/plain', body: 'private' })
      assert(issuer.tokenRequests.length === 1, `${issuer.tokenRequests.length} token requests`)
      const form = issuer.tokenRequests[0].form
      assert(form.get('resource') === `${so}/.well-known/lws-storage`, `resource ${form.get('resource')}`)
      assert(form.get('subject_token_type') === SAML2, form.get('subject_token_type'))
      assert(issuer.tokenRequests[0].contentType === 'application/x-www-form-urlencoded', issuer.tokenRequests[0].contentType)
      const posts = r.log.filter((x) => x.method === 'POST' && x.url === `${so}/`)
      assert(posts.length === 2 && posts[0].headers.get('authorization') === null &&
        (posts[1].headers.get('authorization') || '').startsWith('Bearer '), 'the POST was not resent with Bearer')
      assert(r.log.every((x) => x.url.startsWith(so) || x.headers.get('authorization') === null),
        'a token went to another origin')
      const g = await c.read(created.location)
      assert(g.body === 'private' && issuer.tokenRequests.length === 1, 'the token was not reused')
    })

    await check(CHECKS[18], async () => {
      const decoy = await startDecoy(issuer.origin)
      try {
        const before = issuer.tokenRequests.length
        const c = await createLwsClient({ engine, fetch: globalThis.fetch, subjectToken: CREDENTIAL, subjectTokenType: SAML2 })
        const e = await rejects(c.read(`${decoy.origin}/thing`), 'discoveryValidation')
        assert(e.detail.check === 'storageRootOrigin', JSON.stringify(e.detail))
        assert(issuer.tokenRequests.length === before, 'a token request was sent')
      } finally {
        await decoy.close()
      }
    })

    await check(CHECKS[19], async () => {
      const before = issuer.tokenRequests.length
      const c = await createLwsClient({ engine, subjectToken: CREDENTIAL, subjectTokenType: SAML2,
        session: { tokens: [{ storage: `${so}/.well-known/lws-storage`, root: `${so}/`, token: 'not-a-token' }] } })
      const g = await c.read(`${so}/p.txt`)
      assert(g.body === 'private', g.body)
      assert(issuer.tokenRequests.length === before + 1, 'no new exchange')
      assert(c.session().tokens[0].token !== 'not-a-token', 'the refused token was kept')
    })

    await check(CHECKS[20], async () => {
      const c = await createLwsClient({ engine })
      await rejects(c.read(`${so}/p.txt`), 'unauthorized')
    })
  } finally {
    await secured.close()
    await issuer.close()
  }
}

/** A free loopback port. */
function freePort () {
  return new Promise((resolve) => {
    const s = createNetServer().listen(0, '127.0.0.1', () => { const p = s.address().port; s.close(() => resolve(p)) })
  })
}

/** Start `factoidal authz-serve` and wait for the origin it prints. */
function startAuthz (dir, resource) {
  const cli = fileURLToPath(new URL('../../../npm/factoidal/bin/factoidal.mjs', import.meta.url))
  const child = spawn(process.execPath, [cli, 'authz-serve', dir, '--port', '0', '--resource', resource, '--quiet'],
    { stdio: ['ignore', 'pipe', 'pipe'] })
  return new Promise((resolve, reject) => {
    let out = ''
    const timer = setTimeout(() => reject(new Error(`authz-serve printed no origin: ${out}`)), 60000)
    child.stdout.on('data', (c) => {
      out += c
      const m = /(http:\/\/[^\s]+)/.exec(out)
      if (m) { clearTimeout(timer); resolve({ child, origin: m[1].replace(/\/$/, '') }) }
    })
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`authz-serve exited ${code}: ${out}`)) })
  })
}

/** The CID check: our client signs a self-issued credential (ES256, HACL*
 *  in the engine) for a did:key agent and exchanges it at authz-serve. */
async function cidCheck () {
  const { loadEngine } = await import('../../../npm/factoidal/bin/engine.mjs')
  const { listen } = await import('../../../npm/factoidal/lws/server.mjs')
  const { createLwsClient } = await import('../../../npm/factoidal/lws/client.mjs')
  const engine = await loadEngine()
  const port = await freePort()
  const base = `http://127.0.0.1:${port}/`
  const storage = `${base}.well-known/lws-storage`
  const agent = keyPair('ES256')
  const did = didKeyOf(agent)
  const dir = mkdtempSync(join(tmpdir(), 'lws-client-authz-'))
  let authz = null
  let lws = null
  try {
    authz = await startAuthz(join(dir, 'authz'), storage)
    lws = await listen({ engine, port, owner: did, realClock: true,
      auth: { issuers: [{ issuer: authz.origin }], refreshInterval: 0 } })
    const rec = recording()
    const c = await createLwsClient({ engine, fetch: rec.wire,
      selfIssued: { subject: did, keyId: did.slice(8), jwk: agent.privateKey.export({ format: 'jwk' }) } })
    const made = await c.create(base, { slug: 'cid.txt', mediaType: 'text/plain', body: 'self-issued' })
    const back = await c.read(made.location)
    assert(back.body === 'self-issued', `read ${back.body}`)
    const tokenRequests = rec.log.filter((x) => x.method === 'POST' && x.url.startsWith(authz.origin))
    assert(tokenRequests.length === 1, `${tokenRequests.length} token requests`)
  } finally {
    if (lws !== null) await lws.close()
    if (authz !== null) {
      authz.child.kill('SIGTERM')
      await new Promise((resolve) => authz.child.on('close', resolve))
    }
    rmSync(dir, { recursive: true, force: true })
  }
}

await main()
if (passed + failed + skipped < CHECKS.length) {
  await check(CHECKS[CHECKS.length - 1], cidCheck)
}

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`lws-client node: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
