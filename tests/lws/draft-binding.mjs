// Host tests for the HTTP binding of the LWS 1.0 editor's draft
// (w3c/lws-protocol 9a08ff65, 2026-10-19), and for durable storage
// under `lws-serve DIR`.
// https://github.com/danbri/factoidal/issues/659
//
//   node tests/lws/draft-binding.mjs
//
// Every decision checked here is made by `formal/lean4/L4Factoidal/LWS/`
// (Binding.lean, Operations.lean, Snapshot.lean); the host only routes.
// The `#guard`s beside those modules decide the same rules without a
// socket; this file checks that they reach the wire.
//
// Score line: "N pass, M fail, X xfail, S skipped (out of T)". An xfail
// is a known shortfall with an open issue: it must FAIL today, and the
// run fails when one passes ("unexpected pass"), so the flip to a real
// check and the issue closure cannot be forgotten.

import { mkdtempSync, readdirSync, rmSync, existsSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import http from 'node:http'
import { spawn } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { createHash, createPublicKey, verify as verifySignature } from 'node:crypto'

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

/** A request with the target sent exactly as given (fetch would remove
 *  dot segments before sending). */
function rawRequest (origin, method, target, headers = {}, body = '') {
  const url = new URL(origin)
  return new Promise((resolve, reject) => {
    const req = http.request({ host: url.hostname, port: url.port, method, path: target, headers },
      (res) => {
        const chunks = []
        res.on('data', (c) => chunks.push(c))
        res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, body: Buffer.concat(chunks) }))
      })
    req.on('error', reject)
    req.end(body)
  })
}

const CHECKS = [
  'Read: GET carries ETag, and If-None-Match answers 304',
  'Update: PUT with a stale If-Match answers 412 and does not write',
  'Read: a byte Range answers 206 with Content-Range',
  'Container Representation: application/lws+json listing',
  'Content Negotiation: Turtle in the LWS profile, with Vary',
  'Metadata: the linkset resource is application/linkset+json and allows PATCH',
  'Discovery: the lws#storage link leads to an application/lws+cid description',
  'Create: POST with rel=type lws:Container creates a container',
  'Delete: 409 for a non-empty container, 204 with Depth: infinity',
  'Update: JSON Patch applies; another patch format is 415',
  'Errors: a 404 is application/problem+json (RFC 9457)',
  'Paths: a dot segment or encoded traversal answers 400',
  'Persistence: a restarted server reads DIR/lws-state.json back',
  'Persistence: a traversal target writes no file outside DIR',
  'Authorization: an unauthenticated write answers 401 with resource_metadata',
  'Data resources: a non-UTF-8 body round-trips byte for byte',
  'Pagination: a container of 120 members answers with rel="first", rel="next" and no rel="prev"',
  'Pagination: following rel="next" lists every member once, in path order, totalItems 120',
  'Pagination: each page has its own ETag, If-None-Match answers 304, a missing page answers 404',
  'Pagination: a container at the threshold (100 members) is not paginated',
  'Metadata: PUT with Prefer: set-linkset stores the client Link in the linkset',
  'Metadata: a server-managed rel with Prefer: set-linkset answers 409 and writes nothing',
  'Metadata: a malformed Link answers 400; a Link without Prefer is not stored',
  'Metadata: PATCH on the linkset adds a client link; changing a server link answers 409',
  'Persistence: client links survive a restart',
  'Notifications: the storage description advertises a NotificationService (WebhookSubscription) and a signing key',
  'Notifications: a WebhookSubscription POST answers 201 with type and subscription, and the endpoint lists it',
  'Notifications: a request without type, with an unadvertised type, or without topic answers 400',
  'Notifications: Create, Update and Delete arrive with object id and type, target and origin, and no actor',
  'Notifications: a delivery is an application/lws+json POST whose HTTP Message Signature verifies under the published key',
  'Notifications: a change outside the topic, or to a sibling of a data resource topic, is not delivered',
  'Notifications: DELETE of the subscription answers 204, then GET answers 404, and nothing more arrives',
  'Notifications: a delivery answered 503 is tried again; deliveries answered 410 deactivate the subscription',
  'Notifications: subscriptions survive a restart',
  'Create: POST with no content and no Content-Type creates a container (issue 911, F1)',
  'Create: POST with no content, no Content-Type and no type link creates an empty data resource; content without Content-Type is 400 (issue 911, F1)',
  'LWS Profile: the Turtle form uses http://schema.org/size, as the lws+json context does (issue 911, F2)',
  'Read: a container ETag changes when a member is deleted in the same second (issue 911, F3)',
  'Authorization: the 401 lws#storage link names the storage description id (issue 911, F4)',
  'Conditional requests: If-Unmodified-Since before the last modification answers 412 for GET, PUT and DELETE (issue 911, F5)',
  'Conditional requests: If-Modified-Since is compared as an HTTP-date in all three formats (issue 911, F5)',
  'CLI: lws-serve --page-size N passes the page size to the engine',
  'Create: five POSTs to one container in one second create five resources (issue 911, F6)',
  'Moving Resources: the storage description describes MoveResource for DataResource and Container, preservesIdentifier false',
  'Moving Resources: a JSON Patch of the up link moves a data resource (200, Content-Location, both listings, both container ETags)',
  'Moving Resources: a container moves with its descendants',
  'Moving Resources: a move to a missing container, to a data resource, into itself or a descendant, or without an up link answers 409 and moves nothing',
  'Moving Resources: a subscriber to the old container receives one Move activity with origin and target',
  'Type index: the storage description advertises TypeIndexService and TypeSearchService with their endpoints',
  'Type search: QUERY finds a type from a Link header and from Turtle content; AND, OR and the native classes',
  'Type search: a describedby link is an indexed relation; an unindexed relation and up give the same empty answer',
  'Type search: Cache-Control private, Vary, Accept-Query; OPTIONS; 400 without Content-Type, 415, 406, 400, 422',
  'Type search: rel="next" pages through the answer with GET; an altered page link answers 404',
  'Type index: GET lists the types in application/lws+json, paged, with Cache-Control private',
  'Type search: a set-linkset update, a delete and a move are reflected in the next search',
  'Type search: the index is rebuilt from DIR/lws-state.json after a restart',
  'Access Requests and Grants: the storage description advertises AccessRequestService and AccessGrantService with conformsTo the Access Profile',
  'Access Requests and Grants: the grant endpoint is an LWS container (application/lws+json, rel="type" Container, items)',
  'Access Requests and Grants: POST of a grant answers 201 with Location, and the grant reads back in the access data model',
  'Access Requests and Grants: a grant missing type, storage, access, policy type, action or assignee, or with a bad inbox, target or action, answers 400',
  'Access Requests and Grants: an access request answers 201 and reads back as an AccessRequest; DELETE cancels it',
  'Access Requests and Grants: a grant with an inbox, and a grant answering an access request with an inbox, are announced there',
  'Access Requests and Grants: DELETE revokes a grant (204, then 404)',
  'Access Requests and Grants: grants and requests survive a restart'
]

/** A local webhook receiver: records every POST and answers with the
 *  scripted statuses (the last one repeats), 202 by default. */
async function startReceiver () {
  const got = []
  let script = [202]
  const server = http.createServer((req, res) => {
    const chunks = []
    req.on('data', (c) => chunks.push(c))
    req.on('end', () => {
      const status = script.length > 1 ? script.shift() : script[0]
      const text = Buffer.concat(chunks).toString('utf8')
      let body = null
      try { body = JSON.parse(text) } catch (_error) { body = text }
      got.push({ method: req.method, path: req.url, headers: req.headers, text, body, status })
      res.statusCode = status
      res.end()
    })
  })
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
  const origin = `http://127.0.0.1:${server.address().port}`
  return {
    origin,
    got,
    respond (list) { script = list.slice() },
    close () { return new Promise((resolve) => server.close(resolve)) }
  }
}

/** The activities of a recorded delivery, as an array. */
function activitiesOf (delivery) {
  const a = delivery.body && delivery.body.activity
  if (Array.isArray(a)) return a
  return a ? [a] : []
}

/** Every activity received at `path` on the receiver. */
function received (receiver, path) {
  return receiver.got.filter((d) => d.path === path).flatMap(activitiesOf)
}

/** RFC 9421: rebuild the signature base of a delivery to `url` and verify
 *  it with the verification method the storage description publishes. */
function verifyDelivery (delivery, url, description) {
  const input = delivery.headers['signature-input'] || ''
  const sigHeader = delivery.headers.signature || ''
  const m = /^sig1=(\(([^)]*)\)(.*))$/.exec(input)
  if (m === null) throw new Error(`Signature-Input ${input}`)
  const components = m[2].split(' ').map((c) => c.replace(/"/g, ''))
  const params = m[3]
  const keyid = /;keyid="([^"]+)"/.exec(params)[1]
  const created = /;created=(\d+)/.exec(params)
  if (created === null) throw new Error('no created parameter')
  const u = new URL(url)
  const values = {
    '@method': 'POST',
    '@scheme': u.protocol.replace(':', ''),
    '@authority': u.host,
    '@path': u.pathname || '/'
  }
  const lines = components.map((c) => `"${c}": ${c.startsWith('@') ? values[c] : delivery.headers[c]}`)
  lines.push(`"@signature-params": ${m[1]}`)
  const base = Buffer.from(lines.join('\n'))
  const vm = (description.verificationMethod || []).find((v) => v.id === keyid)
  if (vm === undefined) throw new Error(`keyid ${keyid} is not a published verification method`)
  if (!(description.authentication || []).includes(keyid)) throw new Error('key not referenced from authentication')
  if (keyid.split('#')[0] !== description.id) throw new Error(`keyid ${keyid} is not under ${description.id}`)
  const key = createPublicKey({ key: vm.publicKeyJwk, format: 'jwk' })
  const sig = Buffer.from(/^sig1=:([^:]+):$/.exec(sigHeader)[1], 'base64')
  const digest = 'sha-256=:' + createHash('sha256').update(delivery.text).digest('base64') + ':'
  return {
    components,
    digestOk: delivery.headers['content-digest'] === digest,
    verified: verifySignature(null, base, key, sig)
  }
}

/** The target of the link with relation `rel` in a Link field value. */
function linkTarget (field, rel) {
  for (const part of (field || '').split(', ')) {
    if (part.indexOf(`; rel="${rel}"`) >= 0) return part.slice(1, part.indexOf('>'))
  }
  return null
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
    engine.call('lwsSnapshot', ['no-such-handle'])
  } catch (error) {
    if (String(error.message).indexOf('unknown op') >= 0) {
      for (const name of CHECKS) skip(name, 'the module carries no lwsSnapshot op (rebuild the wasm)')
      return
    }
  }

  const running = await listen({ engine, port: 0, insecureNoAuth: true, now: 1000 })
  const o = running.origin
  try {
    await fetch(`${o}/docs/a.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'abcdefghij' }).then((r) => r.text())

    await check(CHECKS[0], async () => {
      const r = await fetch(`${o}/docs/a.txt`)
      await r.text()
      const tag = r.headers.get('etag')
      assert(tag !== null, 'no ETag')
      const again = await fetch(`${o}/docs/a.txt`, { headers: { 'if-none-match': tag } })
      await again.text()
      assert(again.status === 304, `If-None-Match answered ${again.status}`)
    })

    await check(CHECKS[1], async () => {
      const r = await fetch(`${o}/docs/a.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain', 'if-match': '"stale"' }, body: 'other' })
      await r.text()
      assert(r.status === 412, `stale If-Match answered ${r.status}`)
      const g = await fetch(`${o}/docs/a.txt`)
      assert((await g.text()) === 'abcdefghij', 'the resource was written')
    })

    await check(CHECKS[2], async () => {
      const r = await fetch(`${o}/docs/a.txt`, { headers: { range: 'bytes=2-4' } })
      const body = await r.text()
      assert(r.status === 206, `Range answered ${r.status}`)
      assert(body === 'cde', `body ${body}`)
      assert(r.headers.get('content-range') === 'bytes 2-4/10', `Content-Range ${r.headers.get('content-range')}`)
    })

    await check(CHECKS[3], async () => {
      const r = await fetch(`${o}/docs/`, { headers: { accept: 'application/lws+json' } })
      assert(r.headers.get('content-type') === 'application/lws+json', `content-type ${r.headers.get('content-type')}`)
      const j = await r.json()
      assert(j.type === 'Container' && j.totalItems === 1 && Array.isArray(j.items), JSON.stringify(j))
      const item = j.items[0]
      assert(item.type === 'DataResource' && item.format === 'text/plain' && item.size === 10 &&
        typeof item.modified === 'string' && item.id.endsWith('/docs/a.txt'), JSON.stringify(item))
    })

    await check(CHECKS[4], async () => {
      const r = await fetch(`${o}/docs/`, { headers: { accept: 'text/turtle' } })
      const body = await r.text()
      assert(r.headers.get('content-type') === 'text/turtle; profile="https://www.w3.org/ns/lws/v1"', `content-type ${r.headers.get('content-type')}`)
      assert((r.headers.get('vary') || '').toLowerCase().indexOf('accept') >= 0, 'no Vary: Accept')
      assert(body.indexOf('a lws:Container') >= 0, body.slice(0, 200))
    })

    await check(CHECKS[5], async () => {
      const r = await fetch(`${o}/docs/a.txt`, { method: 'HEAD' })
      const link = r.headers.get('link') || ''
      assert(link.indexOf('rel="linkset"') >= 0 && link.indexOf('</docs/>; rel="up"') >= 0, link)
      const ls = await fetch(`${o}/docs/a.txt?linkset`)
      const body = await ls.text()
      assert(ls.headers.get('content-type') === 'application/linkset+json', `content-type ${ls.headers.get('content-type')}`)
      assert((ls.headers.get('allow') || '').indexOf('PATCH') >= 0, 'Allow has no PATCH')
      assert(JSON.parse(body).linkset[0].anchor.endsWith('/docs/a.txt'), body)
    })

    await check(CHECKS[6], async () => {
      const r = await fetch(`${o}/docs/a.txt`, { method: 'HEAD' })
      const link = r.headers.get('link') || ''
      const m = /<([^>]+)>; rel="https:\/\/www\.w3\.org\/ns\/lws#storage"/.exec(link)
      assert(m !== null, `no lws#storage link: ${link}`)
      const d = await fetch(m[1])
      assert(d.headers.get('content-type') === 'application/lws+cid', `content-type ${d.headers.get('content-type')}`)
      const j = await d.json()
      assert(j.type === 'Storage' && j.service.some((s) => s.type === 'StorageRoot'), JSON.stringify(j))
    })

    await check(CHECKS[7], async () => {
      const r = await fetch(`${o}/docs/`, { method: 'POST', headers: { 'content-type': 'text/plain', link: '<https://www.w3.org/ns/lws#Container>; rel="type"' }, body: '' })
      await r.text()
      assert(r.status === 201, `POST answered ${r.status}`)
      const loc = r.headers.get('location') || ''
      assert(loc.endsWith('/'), `Location ${loc}`)
      assert((r.headers.get('link') || '').indexOf('rel="up"') >= 0, 'no up link')
    })

    await check(CHECKS[8], async () => {
      await fetch(`${o}/tree/x/y`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'y' }).then((r) => r.text())
      const no = await fetch(`${o}/tree/`, { method: 'DELETE' })
      await no.text()
      assert(no.status === 409, `DELETE without Depth answered ${no.status}`)
      const yes = await fetch(`${o}/tree/`, { method: 'DELETE', headers: { depth: 'infinity' } })
      await yes.text()
      assert(yes.status === 204, `DELETE with Depth answered ${yes.status}`)
      const gone = await fetch(`${o}/tree/x/y`)
      await gone.text()
      assert(gone.status === 404, `descendant answered ${gone.status}`)
    })

    await check(CHECKS[9], async () => {
      await fetch(`${o}/d.json`, { method: 'PUT', headers: { 'content-type': 'application/json' }, body: '{"n":1}' }).then((r) => r.text())
      const p = await fetch(`${o}/d.json`, { method: 'PATCH', headers: { 'content-type': 'application/json-patch+json' }, body: '[{"op":"replace","path":"/n","value":2}]' })
      await p.text()
      assert(p.status === 204, `JSON Patch answered ${p.status}`)
      const g = await fetch(`${o}/d.json`)
      assert((await g.text()) === '{"n":2}', 'patch not applied')
      const bad = await fetch(`${o}/d.json`, { method: 'PATCH', headers: { 'content-type': 'application/merge-patch+json' }, body: '{}' })
      await bad.text()
      assert(bad.status === 415, `merge patch answered ${bad.status}`)
    })

    await check(CHECKS[10], async () => {
      const r = await fetch(`${o}/missing`)
      const j = await r.json()
      assert(r.status === 404 && r.headers.get('content-type') === 'application/problem+json', `${r.status} ${r.headers.get('content-type')}`)
      assert(j.status === 404 && j.title === 'Not Found', JSON.stringify(j))
    })

    await check(CHECKS[11], async () => {
      for (const t of ['/../escape', '/docs/../escape', '/docs/%2e%2e/escape', '/docs%2fescape', '/./x']) {
        const r = await rawRequest(o, 'PUT', t, { 'content-type': 'text/plain' }, 'x')
        assert(r.status === 400, `${t} answered ${r.status}`)
      }
    })

    // https://github.com/danbri/factoidal/issues/886: authorization is on
    // unless the host opts out, so this server (no insecureNoAuth, one
    // trusted issuer) refuses the write. The full validation suite is
    // tests/lws/authorization.mjs.
    await check(CHECKS[14], async () => {
      const guarded = await listen({ engine, port: 0, auth: { issuers: [{ issuer: 'https://as.example' }] } })
      try {
        const r = await fetch(`${guarded.origin}/private`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' })
        await r.text()
        assert(r.status === 401, `answered ${r.status}`)
        assert((r.headers.get('www-authenticate') || '').indexOf('resource_metadata') >= 0, 'no resource_metadata')
      } finally {
        await guarded.close()
      }
    })

    // https://github.com/danbri/factoidal/issues/887: pagination
    // (L4Factoidal/LWS/Pagination.lean; default page size 100). The members
    // are written in an order that is not the path order.
    const names = Array.from({ length: 120 }, (_, i) => `r${String((i * 37) % 120).padStart(3, '0')}`)
    for (const n of names) {
      await fetch(`${o}/many/${n}`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: n }).then((r) => r.text())
    }
    const lj = { accept: 'application/lws+json' }

    await check(CHECKS[16], async () => {
      const r = await fetch(`${o}/many/`, { headers: lj })
      const j = await r.json()
      const link = r.headers.get('link')
      assert(r.status === 200, `answered ${r.status}`)
      assert(linkTarget(link, 'first') === '/many/?page=1', `first: ${link}`)
      assert(linkTarget(link, 'next') === '/many/?page=2', `next: ${link}`)
      assert(linkTarget(link, 'last') === '/many/?page=2', `last: ${link}`)
      assert(linkTarget(link, 'prev') === null, `prev on the first page: ${link}`)
      assert(j.items.length === 100 && j.totalItems === 120, `${j.items.length} items, totalItems ${j.totalItems}`)
    })

    await check(CHECKS[17], async () => {
      const seen = []
      let target = '/many/'
      let pages = 0
      let last = null
      while (target !== null && pages < 10) {
        const r = await fetch(`${o}${target}`, { headers: lj })
        const j = await r.json()
        assert(j.totalItems === 120, `totalItems ${j.totalItems}`)
        for (const it of j.items) seen.push(it.id)
        last = r.headers.get('link')
        target = linkTarget(last, 'next')
        pages += 1
      }
      assert(pages === 2, `${pages} pages`)
      assert(linkTarget(last, 'prev') === '/many/?page=1', `prev on the last page: ${last}`)
      const expected = [...names].sort().map((n) => `${o}/many/${n}`)
      assert(JSON.stringify(seen) === JSON.stringify(expected), `listing differs: ${seen.slice(0, 3)}...`)
    })

    await check(CHECKS[18], async () => {
      const p1 = await fetch(`${o}/many/?page=1`, { headers: lj })
      await p1.text()
      const p2 = await fetch(`${o}/many/?page=2`, { headers: lj })
      await p2.text()
      const t1 = p1.headers.get('etag')
      const t2 = p2.headers.get('etag')
      assert(t1 && t2 && t1 !== t2, `tags ${t1} ${t2}`)
      const nm = await fetch(`${o}/many/?page=2`, { headers: { ...lj, 'if-none-match': t2 } })
      await nm.text()
      assert(nm.status === 304, `If-None-Match answered ${nm.status}`)
      const other = await fetch(`${o}/many/?page=2`, { headers: { ...lj, 'if-none-match': t1 } })
      await other.text()
      assert(other.status === 200, `another page's tag answered ${other.status}`)
      const missing = await fetch(`${o}/many/?page=3`, { headers: lj })
      await missing.text()
      assert(missing.status === 404, `page 3 answered ${missing.status}`)
    })

    await check(CHECKS[19], async () => {
      for (let i = 0; i < 100; i++) {
        await fetch(`${o}/hundred/r${i}`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' }).then((r) => r.text())
      }
      const r = await fetch(`${o}/hundred/`, { headers: lj })
      const j = await r.json()
      assert(linkTarget(r.headers.get('link'), 'first') === null, 'rel="first" at the threshold')
      assert(j.items.length === 100 && j.totalItems === 100, `${j.items.length} items`)
    })

    // https://github.com/danbri/factoidal/issues/888: client-managed links
    // (L4Factoidal/LWS/Linkset.lean).
    const lic = '<https://creativecommons.org/licenses/by/4.0/>; rel="license"'
    const linksetOf = async (p) => (await fetch(`${o}${p}?linkset`)).json()

    await check(CHECKS[20], async () => {
      const r = await fetch(`${o}/lic.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain', prefer: 'set-linkset', link: lic }, body: 'x' })
      await r.text()
      assert(r.status === 201, `PUT answered ${r.status}`)
      const ls = (await linksetOf('/lic.txt')).linkset[0]
      assert(ls.license && ls.license[0].href === 'https://creativecommons.org/licenses/by/4.0/', JSON.stringify(ls))
      assert(ls.type && ls.type[0].href === 'https://www.w3.org/ns/lws#DataResource', 'server type link lost')
    })

    await check(CHECKS[21], async () => {
      // A `type` link is server-managed when it names a class of the server;
      // another target is a declared type (lws10-index, issue 912).
      for (const rel of ['type', 'up', 'linkset', 'items', 'https://www.w3.org/ns/lws#storage']) {
        const target = rel === 'type' ? 'https://www.w3.org/ns/lws#Container' : 'https://example.org/x'
        const r = await fetch(`${o}/lic.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain', prefer: 'set-linkset', link: `<${target}>; rel="${rel}"` }, body: 'changed' })
        const j = await r.json()
        assert(r.status === 409 && j.status === 409, `rel ${rel} answered ${r.status}`)
      }
      const g = await fetch(`${o}/lic.txt`)
      assert((await g.text()) === 'x', 'the content was written')
      const ls = (await linksetOf('/lic.txt')).linkset[0]
      assert(ls.license && ls.type[0].href === 'https://www.w3.org/ns/lws#DataResource', JSON.stringify(ls))
    })

    await check(CHECKS[22], async () => {
      const bad = await fetch(`${o}/lic.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain', prefer: 'set-linkset', link: '<https://example.org/x>; rel="Not A Rel"' }, body: 'y' })
      await bad.text()
      assert(bad.status === 400, `a malformed rel answered ${bad.status}`)
      const plain = await fetch(`${o}/plain.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain', link: lic }, body: 'y' })
      await plain.text()
      assert(plain.status === 201, `PUT answered ${plain.status}`)
      const ls = (await linksetOf('/plain.txt')).linkset[0]
      assert(ls.license === undefined, JSON.stringify(ls))
    })

    await check(CHECKS[23], async () => {
      const add = await fetch(`${o}/lic.txt?linkset`, {
        method: 'PATCH',
        headers: { 'content-type': 'application/json-patch+json' },
        body: JSON.stringify([{ op: 'add', path: '/linkset/0/author', value: [{ href: 'https://example.org/me' }] }])
      })
      await add.text()
      assert(add.status === 204, `add answered ${add.status}`)
      const ls = (await linksetOf('/lic.txt')).linkset[0]
      assert(ls.author && ls.author[0].href === 'https://example.org/me' && ls.license, JSON.stringify(ls))
      const change = await fetch(`${o}/lic.txt?linkset`, {
        method: 'PATCH',
        headers: { 'content-type': 'application/json-patch+json' },
        body: JSON.stringify([{ op: 'replace', path: '/linkset/0/type/0/href', value: 'https://www.w3.org/ns/lws#Container' }])
      })
      await change.text()
      assert(change.status === 409, `changing type answered ${change.status}`)
    })

    // https://github.com/danbri/factoidal/issues/889, repaired: bodies are
    // bytes end to end. The full byte suite is tests/lws/binary-bodies.mjs.
    await check(CHECKS[15], async () => {
        const bytes = new Uint8Array([0xff, 0x00, 0x80, 0xfe])
        await fetch(`${o}/bin`, { method: 'PUT', headers: { 'content-type': 'application/octet-stream' }, body: bytes }).then((r) => r.arrayBuffer())
        const g = new Uint8Array(await (await fetch(`${o}/bin`)).arrayBuffer())
        assert(g.length === 4 && g.every((b, i) => b === bytes[i]), `got ${Array.from(g)}`)
      })

    // https://github.com/danbri/factoidal/issues/911: the five defects the
    // Touchstone harness found. The decisions are in Operations.lean,
    // Binding.lean, HttpDate.lean and Authorization.lean.
    await check(CHECKS[34], async () => {
      const r = await rawRequest(o, 'POST', '/', {
        link: '<https://www.w3.org/ns/lws#Container>; rel="type"', 'content-length': '0'
      })
      assert(r.status === 201, `POST answered ${r.status}: ${r.body}`)
      const loc = r.headers.location || ''
      assert(loc.endsWith('/'), `Location ${loc}`)
      const g = await fetch(new URL(loc, o), { headers: { accept: 'application/lws+json' } })
      const j = await g.json()
      assert(g.status === 200 && j.type === 'Container' && j.totalItems === 0, JSON.stringify(j))
    })

    await check(CHECKS[35], async () => {
      const r = await rawRequest(o, 'POST', '/docs/', { slug: 'empty', 'content-length': '0' })
      assert(r.status === 201, `POST answered ${r.status}: ${r.body}`)
      const g = await fetch(`${o}/docs/empty`)
      const body = await g.arrayBuffer()
      assert(g.status === 200 && body.byteLength === 0 &&
        g.headers.get('content-type') === 'application/octet-stream',
        `${g.status} ${g.headers.get('content-type')} ${body.byteLength} bytes`)
      const bad = await rawRequest(o, 'POST', '/docs/', { 'content-length': '1' }, 'x')
      assert(bad.status === 400, `content without Content-Type answered ${bad.status}`)
    })

    await check(CHECKS[36], async () => {
      const r = await fetch(`${o}/docs/`, { headers: { accept: 'text/turtle' } })
      const body = await r.text()
      assert(body.indexOf('@prefix schema: <http://schema.org/> .') >= 0, body.slice(0, 300))
      assert(body.indexOf('https://schema.org/') < 0, 'https://schema.org/ in the Turtle form')
      assert(/schema:size "10"\^\^xsd:long/.test(body), body)
      // A contained container: no dcterms:modified (the context defines
      // `modified` for a DataResource only), as in the lws+json RDF.
      assert(/\/> a lws:Container \.$/m.test(body), `no contained container line: ${body}`)
    })

    const epoch = 'Thu, 01 Jan 1970 00:00:00 GMT'
    await check(CHECKS[39], async () => {
      await fetch(`${o}/ius.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'kept' }).then((r) => r.text())
      const g = await fetch(`${o}/ius.txt`, { headers: { 'if-unmodified-since': epoch } })
      await g.text()
      assert(g.status === 412, `GET answered ${g.status}`)
      const lm = (await fetch(`${o}/ius.txt`, { method: 'HEAD' })).headers.get('last-modified')
      const ok = await fetch(`${o}/ius.txt`, { headers: { 'if-unmodified-since': lm } })
      assert(ok.status === 200 && (await ok.text()) === 'kept', `GET with the Last-Modified date answered ${ok.status}`)
      const p = await fetch(`${o}/ius.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain', 'if-unmodified-since': epoch }, body: 'lost' })
      await p.text()
      assert(p.status === 412, `PUT answered ${p.status}`)
      const d = await fetch(`${o}/ius.txt`, { method: 'DELETE', headers: { 'if-unmodified-since': epoch } })
      await d.text()
      assert(d.status === 412, `DELETE answered ${d.status}`)
      const after = await fetch(`${o}/ius.txt`)
      assert(after.status === 200 && (await after.text()) === 'kept', 'the resource was changed')
    })

    await check(CHECKS[40], async () => {
      const lm = (await fetch(`${o}/ius.txt`, { method: 'HEAD' })).headers.get('last-modified')
      const t = Date.parse(lm)
      const later = new Date(t + 86400000)
      const days = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday']
      const months = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec']
      const p2 = (n) => String(n).padStart(2, '0')
      const hms = `${p2(later.getUTCHours())}:${p2(later.getUTCMinutes())}:${p2(later.getUTCSeconds())}`
      const rfc850 = `${days[later.getUTCDay()]}, ${p2(later.getUTCDate())}-${months[later.getUTCMonth()]}-` +
        `${p2(later.getUTCFullYear() % 100)} ${hms} GMT`
      const asctime = `${days[later.getUTCDay()].slice(0, 3)} ${months[later.getUTCMonth()]} ` +
        `${String(later.getUTCDate()).padStart(2, ' ')} ${hms} ${later.getUTCFullYear()}`
      for (const v of [later.toUTCString(), rfc850, asctime]) {
        const r = await fetch(`${o}/ius.txt`, { headers: { 'if-modified-since': v } })
        await r.text()
        assert(r.status === 304, `If-Modified-Since ${v} answered ${r.status}`)
      }
      for (const v of [epoch, 'not a date']) {
        const r = await fetch(`${o}/ius.txt`, { headers: { 'if-modified-since': v } })
        await r.text()
        assert(r.status === 200, `If-Modified-Since ${v} answered ${r.status}`)
      }
    })

    // LWS 1.0 core §Moving Resources
    // (https://github.com/danbri/factoidal/issues/914). Decided by
    // formal/lean4/L4Factoidal/LWS/Move.lean.
    const movePatch = (target, dest, ifMatch) => fetch(`${target}?linkset`, {
      method: 'PATCH',
      headers: { 'content-type': 'application/json-patch+json', ...(ifMatch ? { 'if-match': ifMatch } : {}) },
      body: JSON.stringify([{ op: 'replace', path: '/linkset/0/up/0/href', value: dest }])
    })
    const ids = async (container) => {
      const r = await fetch(container, { headers: { accept: 'application/lws+json' } })
      return (await r.json()).items.map((i) => i.id)
    }
    await check(CHECKS[43], async () => {
      const d = await (await fetch(`${o}/.well-known/lws-storage`, { headers: { accept: 'application/lws+cid' } })).json()
      const cap = (d.capability || []).find((c) => c.type === 'MoveResource')
      assert(cap !== undefined, JSON.stringify(d))
      assert(JSON.stringify(cap.appliesTo) === '["DataResource","Container"]' && cap.preservesIdentifier === false,
        JSON.stringify(cap))
    })
    for (const t of ['/mv/src/', '/mv/dst/']) {
      await fetch(`${o}${t}`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' }).then((r) => r.text())
    }
    await fetch(`${o}/mv/src/a.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'a resource on the move' }).then((r) => r.text())
    await check(CHECKS[44], async () => {
      const tagOf = async (c) => {
        const r = await fetch(c, { headers: { accept: 'application/lws+json' } })
        await r.text()
        return r.headers.get('etag')
      }
      const srcTag = await tagOf(`${o}/mv/src/`)
      const dstTag = await tagOf(`${o}/mv/dst/`)
      const ls = await fetch(`${o}/mv/src/a.txt?linkset`)
      const doc = await ls.json()
      assert(doc.linkset[0].up[0].href === `${o}/mv/src/`, JSON.stringify(doc))
      const r = await movePatch(`${o}/mv/src/a.txt`, `${o}/mv/dst/`, ls.headers.get('etag'))
      const moved = await r.json()
      assert(r.status === 200, `move answered ${r.status} ${JSON.stringify(moved)}`)
      assert(r.headers.get('content-location') === '/mv/dst/a.txt?linkset', r.headers.get('content-location'))
      assert(moved.linkset[0].anchor === `${o}/mv/dst/a.txt` && moved.linkset[0].up[0].href === `${o}/mv/dst/`,
        JSON.stringify(moved))
      const g = await fetch(`${o}/mv/dst/a.txt`)
      assert(g.status === 200 && (await g.text()) === 'a resource on the move', `GET new ${g.status}`)
      assert(linkTarget(g.headers.get('link'), 'up') === '/mv/dst/', g.headers.get('link'))
      const old = await fetch(`${o}/mv/src/a.txt`)
      await old.text()
      assert(old.status === 404, `GET old ${old.status}`)
      assert(JSON.stringify(await ids(`${o}/mv/dst/`)) === JSON.stringify([`${o}/mv/dst/a.txt`]), 'destination listing')
      assert((await ids(`${o}/mv/src/`)).length === 0, 'source listing')
      assert(await tagOf(`${o}/mv/src/`) !== srcTag && await tagOf(`${o}/mv/dst/`) !== dstTag, 'a container ETag did not change')
    })
    await check(CHECKS[45], async () => {
      await fetch(`${o}/mv/src/box/inner.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'carried along' }).then((r) => r.text())
      const r = await movePatch(`${o}/mv/src/box/`, `${o}/mv/dst/`)
      await r.text()
      assert(r.status === 200, `move answered ${r.status}`)
      assert((await ids(`${o}/mv/dst/`)).includes(`${o}/mv/dst/box/`), 'destination listing')
      assert(JSON.stringify(await ids(`${o}/mv/dst/box/`)) === JSON.stringify([`${o}/mv/dst/box/inner.txt`]), 'moved container listing')
      const g = await fetch(`${o}/mv/dst/box/inner.txt`)
      assert(g.status === 200 && (await g.text()) === 'carried along', `GET inner ${g.status}`)
      assert((await ids(`${o}/mv/src/`)).length === 0, 'source listing')
    })
    await check(CHECKS[46], async () => {
      await fetch(`${o}/mv/dst/box/deeper/`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' }).then((r) => r.text())
      await fetch(`${o}/mv/plain.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'no container' }).then((r) => r.text())
      const tries = [
        [`${o}/mv/dst/a.txt`, `${o}/mv/nowhere/`],
        [`${o}/mv/dst/a.txt`, `${o}/mv/plain.txt`],
        [`${o}/mv/dst/box/`, `${o}/mv/dst/box/`],
        [`${o}/mv/dst/box/`, `${o}/mv/dst/box/deeper/`]
      ]
      for (const [t, d] of tries) {
        const r = await movePatch(t, d)
        const j = await r.json()
        assert(r.status === 409 && r.headers.get('content-type') === 'application/problem+json',
          `${t} to ${d} answered ${r.status} ${JSON.stringify(j)}`)
      }
      const rm = await fetch(`${o}/mv/dst/a.txt?linkset`, {
        method: 'PATCH',
        headers: { 'content-type': 'application/json-patch+json' },
        body: JSON.stringify([{ op: 'remove', path: '/linkset/0/up' }])
      })
      await rm.text()
      assert(rm.status === 409, `removing up answered ${rm.status}`)
      const g = await fetch(`${o}/mv/dst/a.txt`)
      await g.text()
      assert(g.status === 200 && linkTarget(g.headers.get('link'), 'up') === '/mv/dst/', 'the resource moved')
      assert((await ids(`${o}/mv/dst/box/`)).includes(`${o}/mv/dst/box/deeper/`), 'the container moved')
    })
    // LWS §Moving Resources: "Such a server SHOULD respond to subsequent
    // requests on the previous identifiers of the resource and of its
    // auxiliary resources with 301 Moved Permanently". Not implemented;
    // the xfail turns the run red when it starts to pass.
    await xfail('Moving Resources: a request to the previous identifier of a moved resource answers 301 with Location',
      'https://github.com/danbri/factoidal/issues/914', async () => {
        const r = await fetch(`${o}/mv/src/a.txt`, { redirect: 'manual' })
        await r.text()
        assert(r.status === 301 && r.headers.get('location') !== null, `answered ${r.status}`)
      })

    // LWS 1.0 core §Notifications and the webhook notification suite
    // (https://github.com/danbri/factoidal/issues/890). Decided by
    // formal/lean4/L4Factoidal/LWS/Notifications.lean.
    const receiver = await startReceiver()
    const settle = async () => { await (await running.storage()).settled() }
    try {
      let description = null
      let endpoint = null
      await check(CHECKS[25], async () => {
        const r = await fetch(`${o}/.well-known/lws-storage`, { headers: { accept: 'application/lws+cid' } })
        description = await r.json()
        const svc = description.service.find((s) => s.type === 'NotificationService')
        assert(svc !== undefined, JSON.stringify(description.service))
        assert(typeof svc.serviceEndpoint === 'string' && Array.isArray(svc.subscriptionType) &&
          svc.subscriptionType.includes('WebhookSubscription'), JSON.stringify(svc))
        endpoint = new URL(svc.serviceEndpoint, `${o}/`).href
        const vm = description.verificationMethod && description.verificationMethod[0]
        assert(vm && vm.type === 'JsonWebKey' && vm.publicKeyJwk.crv === 'Ed25519' &&
          description.authentication.includes(vm.id), JSON.stringify(description))
      })

      const subscribe = (body, contentType = 'application/lws+json') => fetch(endpoint, {
        method: 'POST', headers: { 'content-type': contentType }, body: JSON.stringify(body)
      })
      const ctx = ['https://www.w3.org/ns/lws/v1']
      await fetch(`${o}/watched/`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' }).then((r) => r.text())
      await fetch(`${o}/watched/old.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'old' }).then((r) => r.text())
      let subscription = null
      await check(CHECKS[26], async () => {
        const r = await subscribe({ '@context': ctx, type: 'WebhookSubscription', topic: [`${o}/watched/`], inbox: `${receiver.origin}/hook/a` })
        const j = await r.json()
        assert(r.status === 201, `answered ${r.status} ${JSON.stringify(j)}`)
        assert(r.headers.get('content-type') === 'application/lws+json', r.headers.get('content-type'))
        assert(j.type === 'WebhookSubscription' && typeof j.subscription === 'string', JSON.stringify(j))
        subscription = j.subscription
        const l = await fetch(endpoint, { headers: { accept: 'application/lws+json' } })
        const listing = await l.json()
        assert(listing.type === 'Container' && listing.items.some((i) => i.id === subscription), JSON.stringify(listing))
        const g = await fetch(subscription)
        const state = await g.json()
        assert(g.status === 200 && state.active === true && state.inbox === `${receiver.origin}/hook/a`, JSON.stringify(state))
      })

      await check(CHECKS[27], async () => {
        const bad = [
          { '@context': ctx, topic: [`${o}/watched/`], inbox: `${receiver.origin}/hook/x` },
          { '@context': ctx, type: 'TouchstoneUnadvertisedSubscription', topic: [`${o}/watched/`], inbox: `${receiver.origin}/hook/x` },
          { '@context': ctx, type: 'WebhookSubscription', inbox: `${receiver.origin}/hook/x` }
        ]
        for (const b of bad) {
          const r = await subscribe(b)
          const j = await r.json()
          assert(r.status === 400, `${JSON.stringify(b)} answered ${r.status}`)
          assert(r.headers.get('content-type') === 'application/problem+json', JSON.stringify(j))
        }
      })

      await check(CHECKS[28], async () => {
        const c = await fetch(`${o}/watched/`, { method: 'POST', headers: { 'content-type': 'text/plain', slug: 'new.txt' }, body: 'new' })
        await c.text()
        const created = new URL(c.headers.get('location'), `${o}/`).href
        await fetch(`${o}/watched/old.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'old, changed' }).then((r) => r.text())
        await fetch(`${o}/watched/old.txt`, { method: 'DELETE' }).then((r) => r.text())
        await settle()
        const acts = received(receiver, '/hook/a')
        const find = (type, id) => acts.find((a) => a.type.includes(type) && a.object.id === id)
        const cr = find('Create', created)
        const up = find('Update', `${o}/watched/old.txt`)
        const de = find('Delete', `${o}/watched/old.txt`)
        assert(cr && up && de, JSON.stringify(acts))
        assert(cr.target === `${o}/watched/` && de.origin === `${o}/watched/`, JSON.stringify([cr, de]))
        assert(cr.object.type.includes('DataResource') && Array.isArray(cr.type), JSON.stringify(cr))
        assert(acts.every((a) => a.actor === undefined && typeof a.id === 'string' &&
          /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$/.test(a.published)), JSON.stringify(acts))
        const envelope = receiver.got.find((d) => d.path === '/hook/a').body
        assert(envelope.type === 'Notification' && envelope.storage === `${o}/.well-known/lws-storage`, JSON.stringify(envelope))
      })

      await check(CHECKS[29], async () => {
        const d = receiver.got.find((x) => x.path === '/hook/a')
        assert(d.method === 'POST' && d.headers['content-type'] === 'application/lws+json', JSON.stringify(d.headers))
        const v = verifyDelivery(d, `${receiver.origin}/hook/a`, description)
        for (const c of ['@method', '@scheme', '@authority', '@path', 'content-type', 'content-digest']) {
          assert(v.components.includes(c), `not covered: ${c}`)
        }
        assert(v.digestOk, 'Content-Digest does not match the body')
        assert(v.verified, 'the signature does not verify under the published key')
        // Negative: a changed body does not verify.
        const forged = { ...d, text: d.text + ' ', headers: { ...d.headers } }
        assert(!verifyDelivery(forged, `${receiver.origin}/hook/a`, description).digestOk, 'a changed body kept its digest')
        const moved = verifyDelivery(d, `${receiver.origin}/hook/elsewhere`, description)
        assert(!moved.verified, 'the signature verified for another path')
      })

      await check(CHECKS[30], async () => {
        const r = await subscribe({ '@context': ctx, type: 'WebhookSubscription', topic: [`${o}/watched/one.txt`], inbox: `${receiver.origin}/hook/b` })
        await r.text()
        assert(r.status === 201, `answered ${r.status}`)
        const before = receiver.got.length
        await fetch(`${o}/elsewhere.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' }).then((x) => x.text())
        await fetch(`${o}/watched/sibling.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' }).then((x) => x.text())
        await settle()
        assert(received(receiver, '/hook/b').length === 0, JSON.stringify(received(receiver, '/hook/b')))
        const ids = receiver.got.slice(before).flatMap(activitiesOf).map((a) => a.object.id)
        assert(!ids.includes(`${o}/elsewhere.txt`), JSON.stringify(ids))
        await fetch(`${o}/watched/one.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' }).then((x) => x.text())
        await settle()
        assert(received(receiver, '/hook/b').map((a) => a.object.id).join() === `${o}/watched/one.txt`,
          JSON.stringify(received(receiver, '/hook/b')))
      })

      await check(CHECKS[31], async () => {
        const d = await fetch(subscription, { method: 'DELETE' })
        await d.text()
        assert(d.status === 204, `DELETE answered ${d.status}`)
        const g = await fetch(subscription)
        await g.text()
        assert(g.status === 404, `GET after DELETE answered ${g.status}`)
        const before = received(receiver, '/hook/a').length
        await fetch(`${o}/watched/after.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' }).then((x) => x.text())
        await settle()
        assert(received(receiver, '/hook/a').length === before, 'a cancelled subscription still delivers')
      })

      await check(CHECKS[32], async () => {
        receiver.respond([503, 202])
        const r = await subscribe({ '@context': ctx, type: 'WebhookSubscription', topic: [`${o}/retry.txt`], inbox: `${receiver.origin}/hook/c` })
        await r.text()
        await fetch(`${o}/retry.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' }).then((x) => x.text())
        await settle()
        const tries = receiver.got.filter((x) => x.path === '/hook/c').map((x) => x.status)
        assert(tries.join() === '503,202', `statuses ${tries}`)
        receiver.respond([410])
        const s2 = await (await subscribe({ '@context': ctx, type: 'WebhookSubscription', topic: [`${o}/gone.txt`], inbox: `${receiver.origin}/hook/d` })).json()
        for (const n of [1, 2]) {
          await fetch(`${o}/gone.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: `v${n}` }).then((x) => x.text())
          await settle()
        }
        const gone = receiver.got.filter((x) => x.path === '/hook/d')
        assert(gone.length === 1 && gone[0].status === 410, `deliveries to a 410 hook: ${gone.length}`)
        const state = await (await fetch(s2.subscription)).json()
        assert(state.active === false, JSON.stringify(state))
        receiver.respond([202])
      })

      await check(CHECKS[47], async () => {
        await fetch(`${o}/mvn/src/`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' }).then((r) => r.text())
        await fetch(`${o}/mvn/dst/`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' }).then((r) => r.text())
        await fetch(`${o}/mvn/src/m.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'm' }).then((r) => r.text())
        receiver.respond([202])
        const s = await subscribe({ '@context': ctx, type: 'WebhookSubscription', topic: [`${o}/mvn/src/`], inbox: `${receiver.origin}/hook/move` })
        await s.text()
        assert(s.status === 201, `subscribe answered ${s.status}`)
        const r = await movePatch(`${o}/mvn/src/m.txt`, `${o}/mvn/dst/`)
        await r.text()
        assert(r.status === 200, `move answered ${r.status}`)
        await settle()
        const acts = received(receiver, '/hook/move')
        assert(acts.length === 1, JSON.stringify(acts))
        const a = acts[0]
        assert(a.type.includes('Move') && a.origin === `${o}/mvn/src/` && a.target === `${o}/mvn/dst/` &&
          a.object.id === `${o}/mvn/dst/m.txt` && a.object.type.includes('DataResource'), JSON.stringify(a))
      })

      // https://github.com/danbri/factoidal/issues/915: an inbox that names
      // this server through another host name is not detected, and
      // deliveries are not rate limited. Each xfail turns the run red when
      // it starts to pass.
      await xfail('Notifications: an inbox that names this server by another host name (localhost) is refused with 400',
        'https://github.com/danbri/factoidal/issues/915', async () => {
          const port = new URL(o).port
          const r = await subscribe({ '@context': ctx, type: 'WebhookSubscription', topic: [`${o}/loop/`], inbox: `http://localhost:${port}/loop/` })
          const j = await r.json()
          // Cancel at once, so that a subscription made here cannot loop.
          if (typeof j.subscription === 'string') await fetch(j.subscription, { method: 'DELETE' }).then((x) => x.text())
          assert(r.status === 400, `answered ${r.status}`)
        })
      await xfail('Notifications: deliveries to one inbox are rate limited (30 changes in one burst give fewer than 30 POSTs)',
        'https://github.com/danbri/factoidal/issues/915', async () => {
          const s = await (await subscribe({ '@context': ctx, type: 'WebhookSubscription', topic: [`${o}/burst/`], inbox: `${receiver.origin}/hook/burst` })).json()
          try {
            for (let i = 0; i < 30; i += 1) {
              await fetch(`${o}/burst/r${i}.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: `${i}` }).then((x) => x.text())
            }
            await settle()
            const posts = receiver.got.filter((x) => x.path === '/hook/burst').length
            assert(posts < 30, `${posts} POSTs for 30 changes`)
          } finally {
            await fetch(s.subscription, { method: 'DELETE' }).then((x) => x.text())
          }
        })

      // LWS §Access Requests and Grants
      // (https://github.com/danbri/factoidal/issues/913). Decided by
      // formal/lean4/L4Factoidal/LWS/AccessGrants.lean and AccessPolicy.lean.
      // This server runs without authorization, so every agent is the
      // storage controller here; enforcement is checked with real tokens in
      // tests/lws/authorization.mjs.
      const storageId = `${o}/.well-known/lws-storage`
      let grants = `${o}/.well-known/lws-access-grants/`
      let requests = `${o}/.well-known/lws-access-requests/`
      const grantDoc = (extra = {}, policy = {}) => Object.assign({
        '@context': ctx,
        type: ['AccessGrant'],
        storage: storageId,
        access: [Object.assign({
          type: ['AccessPolicy'], action: ['read'], assignee: 'https://id.example/bob',
          target: { type: 'StorageResource', value: [`${o}/watched/old.txt`] }
        }, policy)]
      }, extra)
      const post = (url, body) => fetch(url, {
        method: 'POST', headers: { 'content-type': 'application/lws+json' }, body: JSON.stringify(body)
      })
      await check('Access Requests and Grants: the storage description advertises AccessRequestService and AccessGrantService with conformsTo the Access Profile', async () => {
        const d = await (await fetch(`${o}/.well-known/lws-storage`)).json()
        const g = d.service.find((s) => s.type === 'AccessGrantService')
        const q = d.service.find((s) => s.type === 'AccessRequestService')
        assert(g && q, JSON.stringify(d.service))
        for (const s of [g, q]) {
          assert(Array.isArray(s.conformsTo) && s.conformsTo.includes('https://www.w3.org/ns/lws#AccessProfile'), JSON.stringify(s))
        }
        grants = new URL(g.serviceEndpoint, `${o}/`).href
        requests = new URL(q.serviceEndpoint, `${o}/`).href
      })
      await check('Access Requests and Grants: the grant endpoint is an LWS container (application/lws+json, rel="type" Container, items)', async () => {
        const r = await fetch(grants, { headers: { accept: 'application/lws+json' } })
        const j = await r.json()
        assert(r.status === 200, `answered ${r.status}`)
        assert((r.headers.get('content-type') || '').startsWith('application/lws+json'), r.headers.get('content-type'))
        assert(linkTarget(r.headers.get('link'), 'type') === 'https://www.w3.org/ns/lws#Container', r.headers.get('link'))
        assert(Array.isArray(j.items) && j.type === 'Container', JSON.stringify(j))
      })
      let grant = null
      await check('Access Requests and Grants: POST of a grant answers 201 with Location, and the grant reads back in the access data model', async () => {
        const r = await post(grants, grantDoc())
        await r.text()
        assert(r.status === 201, `answered ${r.status}`)
        grant = new URL(r.headers.get('location'), grants).href
        const g = await fetch(grant, { headers: { accept: 'application/lws+json' } })
        const j = await g.json()
        assert(g.status === 200, `GET answered ${g.status}`)
        assert(Array.isArray(j['@context']) && j['@context'].includes('https://www.w3.org/ns/lws/v1'), JSON.stringify(j))
        assert(j.type.includes('AccessGrant') && j.storage === storageId && j.id === grant, JSON.stringify(j))
        const p = j.access[0]
        assert(p.type.includes('AccessPolicy') && Array.isArray(p.action) && p.assignee === 'https://id.example/bob' &&
          p.target.type === 'StorageResource' && Array.isArray(p.target.value), JSON.stringify(p))
        const list = await (await fetch(grants)).json()
        assert(list.items.some((i) => i.id === grant && i.type === 'DataResource'), JSON.stringify(list))
      })
      await check('Access Requests and Grants: a grant missing type, storage, access, policy type, action or assignee, or with a bad inbox, target or action, answers 400', async () => {
        const drop = (x, k) => { const c = Object.assign({}, x); delete c[k]; return c }
        const p0 = grantDoc().access[0]
        const bad = [
          drop(grantDoc(), 'type'), drop(grantDoc(), 'storage'), drop(grantDoc(), 'access'),
          grantDoc({ access: [] }), grantDoc({ access: [drop(p0, 'type')] }),
          grantDoc({}, { type: ['urn:x:not-a-policy'] }), grantDoc({ access: [drop(p0, 'action')] }),
          grantDoc({ access: [drop(p0, 'assignee')] }), grantDoc({}, { target: `${o}/watched/old.txt` }),
          grantDoc({ inbox: 'not a uri' }), grantDoc({}, { action: ['write'] }),
          grantDoc({ storage: 'https://other.example/' })
        ]
        for (const b of bad) {
          const r = await post(grants, b)
          await r.text()
          assert(r.status === 400, `${JSON.stringify(b)} answered ${r.status}`)
        }
        const t = await fetch(grants, { method: 'POST', headers: { 'content-type': 'text/turtle' }, body: 'x' })
        await t.text()
        assert(t.status === 415, `text/turtle answered ${t.status}`)
      })
      await check('Access Requests and Grants: an access request answers 201 and reads back as an AccessRequest; DELETE cancels it', async () => {
        const r = await post(requests, grantDoc({ type: ['AccessRequest'] }))
        await r.text()
        assert(r.status === 201, `answered ${r.status}`)
        const q = new URL(r.headers.get('location'), requests).href
        const j = await (await fetch(q)).json()
        assert(j.type.includes('AccessRequest'), JSON.stringify(j))
        const d = await fetch(q, { method: 'DELETE' })
        await d.text()
        assert(d.status === 204, `DELETE answered ${d.status}`)
        const g = await fetch(q)
        await g.text()
        assert(g.status === 404, `after DELETE: ${g.status}`)
      })
      await check('Access Requests and Grants: a grant with an inbox, and a grant answering an access request with an inbox, are announced there', async () => {
        const g1 = await post(grants, grantDoc({ inbox: `${receiver.origin}/hook/grant` }))
        await g1.text()
        const q = await post(requests, grantDoc({ type: ['AccessRequest'], inbox: `${receiver.origin}/hook/request` },
          { assignee: 'https://id.example/carol' }))
        await q.text()
        const g2 = await post(grants, grantDoc({}, { assignee: 'https://id.example/carol' }))
        await g2.text()
        await settle()
        for (const [path, location] of [['/hook/grant', g1.headers.get('location')], ['/hook/request', g2.headers.get('location')]]) {
          const ds = receiver.got.filter((d) => d.path === path)
          assert(ds.length === 1, `${path}: ${ds.length} deliveries`)
          const a = activitiesOf(ds[0])[0]
          assert(ds[0].body.type === 'Notification' && a.type.includes('Create') && typeof a.id === 'string' &&
            typeof a.published === 'string' && a.object.id === new URL(location, grants).href, JSON.stringify(ds[0].body))
        }
      })
      // The draft names no inbox for the storage controller; the xfail
      // turns the run red when it starts to pass.
      await xfail('Access Requests and Grants: creating an access request notifies the storage controller',
        'https://github.com/danbri/factoidal/issues/920', async () => {
          const before = receiver.got.length
          const r = await post(requests, grantDoc({ type: ['AccessRequest'] }))
          await r.text()
          await settle()
          assert(receiver.got.length > before, 'no delivery for a new access request')
        })
      await check('Access Requests and Grants: DELETE revokes a grant (204, then 404)', async () => {
        const d = await fetch(grant, { method: 'DELETE' })
        await d.text()
        assert(d.status === 204, `DELETE answered ${d.status}`)
        const g = await fetch(grant)
        await g.text()
        assert(g.status === 404, `after DELETE: ${g.status}`)
      })
    } finally {
      await receiver.close()
    }
  } finally {
    await running.close()
  }

  // F3 needs the host's real clock: it sets the engine clock to the current
  // second on every request, so two changes in one second carry one
  // Last-Modified. The sequence is repeated until both reads fall in the
  // same second, so the check exercises that case.
  // LWS Search and Type Index Services (lws10-index), issue 912.
  {
    const s = await listen({ engine, port: 0, insecureNoAuth: true, pageSize: 2 })
    const so = s.origin
    const SP = 'https://schema.org/Person'
    const SE = 'https://schema.org/Event'
    const search = (filter, headers = {}) => fetch(`${so}/.well-known/lws-type-search`, {
      method: 'QUERY', headers: { 'content-type': 'application/lws-query+json', ...headers },
      body: typeof filter === 'string' ? filter : JSON.stringify(filter)
    })
    const allIds = async (filter) => {
      const out = []
      let r = await search(filter)
      for (let i = 0; i < 20; i++) {
        const j = await r.json()
        assert(r.status === 200, `search answered ${r.status} ${JSON.stringify(j)}`)
        out.push(...j.items.map((x) => x.id))
        const next = linkTarget(r.headers.get('link'), 'next')
        if (next === null) break
        r = await fetch(next)
      }
      return out
    }
    const post = async (slug, contentType, body, link) => {
      const headers = { 'content-type': contentType, slug }
      if (link) headers.link = link
      const r = await fetch(`${so}/c/`, { method: 'POST', headers, body })
      await r.text()
      assert(r.status === 201, `POST ${slug} answered ${r.status}`)
    }
    try {
      const c = await fetch(`${so}/`, { method: 'POST', headers: { slug: 'c', link: '<https://www.w3.org/ns/lws#Container>; rel="type"' } })
      await c.text()
      await post('a', 'text/plain', 'typed by its Link header', `<${SP}>; rel="type"`)
      await post('b', 'text/turtle', `<> a <${SE}> .`)
      await post('p', 'text/turtle', '<> a <http://xmlns.com/foaf/0.1/Person> .', `<${SP}>; rel="type", <https://ex.org/shape>; rel="describedby"`)

      await check('Type index: the storage description advertises TypeIndexService and TypeSearchService with their endpoints', async () => {
        const d = await (await fetch(`${so}/.well-known/lws-storage`, { headers: { accept: 'application/lws+cid' } })).json()
        const ti = d.service.find((x) => x.type === 'TypeIndexService')
        const ts = d.service.find((x) => x.type === 'TypeSearchService')
        assert(ti && ti.serviceEndpoint === `${so}/.well-known/lws-type-index`, JSON.stringify(d.service))
        assert(ts && ts.serviceEndpoint === `${so}/.well-known/lws-type-search`, JSON.stringify(d.service))
        // Negative: a storage opened with typeIndex: false advertises neither.
        const off = await listen({ engine, port: 0, insecureNoAuth: true, typeIndex: false })
        try {
          const d2 = await (await fetch(`${off.origin}/.well-known/lws-storage`)).json()
          assert(!d2.service.some((x) => /^Type(Index|Search)Service$/.test(x.type)), JSON.stringify(d2.service))
        } finally {
          await off.close()
        }
      })

      await check('Type search: QUERY finds a type from a Link header and from Turtle content; AND, OR and the native classes', async () => {
        const eq = (a, b, what) => assert(JSON.stringify(a) === JSON.stringify(b), `${what}: ${JSON.stringify(a)}`)
        eq(await allIds({ type: [SP] }), [`${so}/c/a`, `${so}/c/p`], 'Person')
        eq(await allIds({ type: [SE] }), [`${so}/c/b`], 'Event from content')
        eq(await allIds({ type: [[SE, 'http://xmlns.com/foaf/0.1/Person']] }), [`${so}/c/b`, `${so}/c/p`], 'OR')
        eq(await allIds({ type: [SP, 'http://xmlns.com/foaf/0.1/Person'] }), [`${so}/c/p`], 'AND')
        eq(await allIds({ type: [SP, 'https://www.w3.org/ns/lws#Container'] }), [], 'Person AND Container')
        eq(await allIds({ type: ['https://www.w3.org/ns/lws#Container'] }), [`${so}/`, `${so}/c/`], 'Container')
        const r = await search({ type: [SP] })
        const j = await r.json()
        assert(j.type === 'ContainerPage' && j.totalItems === 2, JSON.stringify(j))
        assert(j.items[0].type.includes('DataResource') && j.items[0].type.includes(SP), JSON.stringify(j.items[0]))
      })

      await check('Type search: a describedby link is an indexed relation; an unindexed relation and up give the same empty answer', async () => {
        const hit = await allIds({ type: [SP], describedby: ['https://ex.org/shape'] })
        assert(JSON.stringify(hit) === JSON.stringify([`${so}/c/p`]), JSON.stringify(hit))
        const a = await (await search({ type: [SP], 'urn:x:unindexed': ['urn:x:x'] })).text()
        const b = await (await search({ type: [SP], describedby: ['urn:x:none'] })).text()
        const u = await (await search({ type: [SP], up: [`${so}/c/`] })).text()
        assert(a === b && b === u && JSON.parse(a).items.length === 0, `${a} | ${b} | ${u}`)
      })

      await check('Type search: Cache-Control private, Vary, Accept-Query; OPTIONS; 400 without Content-Type, 415, 406, 400, 422', async () => {
        const r = await search({ type: [SP] })
        await r.text()
        assert(r.headers.get('cache-control') === 'private', `Cache-Control ${r.headers.get('cache-control')}`)
        assert(/accept/.test(r.headers.get('vary') || ''), `Vary ${r.headers.get('vary')}`)
        assert(r.headers.get('accept-query') === 'application/lws-query+json', `Accept-Query ${r.headers.get('accept-query')}`)
        const opt = await fetch(`${so}/.well-known/lws-type-search`, { method: 'OPTIONS' })
        await opt.text()
        assert(opt.headers.get('accept-query') === 'application/lws-query+json' && /QUERY/.test(opt.headers.get('allow')), 'OPTIONS')
        // fetch adds text/plain to a string body, so this one goes out raw.
        const noCt = await rawRequest(so, 'QUERY', '/.well-known/lws-type-search', {}, '{"type":[]}')
        assert(noCt.status === 400, `no Content-Type: ${noCt.status}`)
        const other = await search('{}', { 'content-type': 'application/x-touchstone-query' })
        await other.text()
        assert(other.status === 415 && /lws-query/.test(other.headers.get('accept-query') || ''), `415: ${other.status}`)
        const na = await search('{}', { accept: 'image/png' })
        await na.text()
        assert(na.status === 406, `406: ${na.status}`)
        const ld = await search('{}', { accept: 'application/ld+json' })
        await ld.text()
        assert(ld.status === 200 && ld.headers.get('content-type') === 'application/ld+json', `ld+json: ${ld.status}`)
        for (const bad of ['{"type": ["urn:x:a"', '{"type":"urn:x:a"}', '{"type":[42]}', '{"type":[[]]}', '{"type":["Person"]}']) {
          const x = await search(bad)
          await x.text()
          assert(x.status === 400, `${bad} answered ${x.status}`)
        }
        const many = await search({ type: Array.from({ length: 65 }, (_, i) => `urn:x:${i}`) })
        await many.text()
        assert(many.status === 422, `65 IRIs answered ${many.status}`)
      })

      await check('Type search: rel="next" pages through the answer with GET; an altered page link answers 404', async () => {
        const r = await search({})
        const j = await r.json()
        assert(j.items.length === 2 && j.totalItems === 5, JSON.stringify(j))
        const next = linkTarget(r.headers.get('link'), 'next')
        const first = linkTarget(r.headers.get('link'), 'first')
        assert(next !== null && first !== null, r.headers.get('link'))
        const p2 = await fetch(next, { headers: { accept: 'application/lws+json' } })
        const j2 = await p2.json()
        assert(p2.status === 200 && j2.type === 'ContainerPage', JSON.stringify(j2))
        assert(!j2.items.some((x) => x.id === j.items[0].id), 'page 2 repeats page 1')
        const all = await allIds({})
        assert(JSON.stringify(all) === JSON.stringify([`${so}/`, `${so}/c/`, `${so}/c/a`, `${so}/c/b`, `${so}/c/p`]), JSON.stringify(all))
        const altered = await fetch(`${first}-touchstone-unrecognized`)
        await altered.text()
        assert(altered.status === 404 || altered.status === 410, `altered page link answered ${altered.status}`)
      })

      await check('Type index: GET lists the types in application/lws+json, paged, with Cache-Control private', async () => {
        const types = []
        let r = await fetch(`${so}/.well-known/lws-type-index`)
        assert(r.headers.get('content-type') === 'application/lws+json' && r.headers.get('cache-control') === 'private', 'headers')
        for (let i = 0; i < 10; i++) {
          const j = await r.json()
          assert(j.type === 'TypeIndex', JSON.stringify(j))
          types.push(...j.items.map((x) => x.id))
          const next = linkTarget(r.headers.get('link'), 'next')
          if (next === null) break
          r = await fetch(next)
        }
        for (const t of [SP, SE, 'http://xmlns.com/foaf/0.1/Person', 'https://www.w3.org/ns/lws#Container', 'https://www.w3.org/ns/lws#DataResource']) {
          assert(types.includes(t), `${t} missing from ${JSON.stringify(types)}`)
        }
        assert(types.length === 5, JSON.stringify(types))
      })

      await check('Type search: a set-linkset update, a delete and a move are reflected in the next search', async () => {
        const u = await fetch(`${so}/c/a`, { method: 'PUT', headers: { 'content-type': 'text/plain', prefer: 'set-linkset', link: `<${SE}>; rel="type"` }, body: 'an event now' })
        await u.text()
        assert(u.headers.get('preference-applied') === 'set-linkset', `Preference-Applied ${u.headers.get('preference-applied')}`)
        assert(JSON.stringify(await allIds({ type: [SP] })) === JSON.stringify([`${so}/c/p`]), 'Person after the update')
        assert(JSON.stringify(await allIds({ type: [SE] })) === JSON.stringify([`${so}/c/a`, `${so}/c/b`]), 'Event after the update')
        const d = await fetch(`${so}/c/b`, { method: 'DELETE' })
        await d.text()
        assert(JSON.stringify(await allIds({ type: [SE] })) === JSON.stringify([`${so}/c/a`]), 'Event after the delete')
        const mk = await fetch(`${so}/d/x.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'x' })
        await mk.text()
        const mv = await fetch(`${so}/c/a?linkset`, { method: 'PATCH', headers: { 'content-type': 'application/json-patch+json' }, body: JSON.stringify([{ op: 'replace', path: '/linkset/0/up/0/href', value: `${so}/d/` }]) })
        await mv.text()
        assert(mv.status === 200, `move answered ${mv.status}`)
        assert(JSON.stringify(await allIds({ type: [SE] })) === JSON.stringify([`${so}/d/a`]), 'Event after the move')
      })
    } finally {
      await s.close()
    }

    await check('Type search: the index is rebuilt from DIR/lws-state.json after a restart', async () => {
      const idir = mkdtempSync(join(tmpdir(), 'lws912-index-'))
      try {
        const first = await listen({ engine, port: 0, insecureNoAuth: true, dir: idir })
        const fo = first.origin
        try {
          const r = await fetch(`${fo}/kept/a.ttl`, { method: 'PUT', headers: { 'content-type': 'text/turtle', link: '<https://schema.org/Thing>; rel="type"' }, body: '<> a <https://schema.org/Event> .' })
          await r.text()
          const l = await fetch(`${fo}/kept/a.ttl`, { method: 'PUT', headers: { 'content-type': 'text/turtle', prefer: 'set-linkset', link: '<https://schema.org/Thing>; rel="type"' }, body: '<> a <https://schema.org/Event> .' })
          await l.text()
        } finally {
          await first.close()
        }
        const second = await listen({ engine, port: 0, insecureNoAuth: true, dir: idir, baseIri: `${fo}/` })
        try {
          for (const t of ['https://schema.org/Thing', 'https://schema.org/Event']) {
            const r = await fetch(`${second.origin}/.well-known/lws-type-search`, { method: 'QUERY', headers: { 'content-type': 'application/lws-query+json' }, body: JSON.stringify({ type: [t] }) })
            const j = await r.json()
            assert(j.items.length === 1 && j.items[0].id === `${fo}/kept/a.ttl`, `${t}: ${JSON.stringify(j)}`)
          }
        } finally {
          await second.close()
        }
      } finally {
        rmSync(idir, { recursive: true, force: true })
      }
    })
  }

  await check(CHECKS[37], async () => {
    const rc = await listen({ engine, port: 0, insecureNoAuth: true, realClock: true })
    try {
      let tried = 0
      for (;;) {
        tried += 1
        // The Touchstone sequence: a container, a member made by POST, a
        // read, the member's DELETE, a read.
        const c = `/same${tried}/`
        await fetch(`${rc.origin}${c}`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' }).then((r) => r.text())
        const p = await fetch(`${rc.origin}${c}`, { method: 'POST', headers: { 'content-type': 'text/plain', slug: 'x' }, body: 'x' })
        await p.text()
        assert(p.status === 201, `POST answered ${p.status}`)
        const g1 = await fetch(`${rc.origin}${c}`)
        await g1.text()
        const d = await fetch(new URL(p.headers.get('location'), rc.origin), { method: 'DELETE' })
        await d.text()
        const g2 = await fetch(`${rc.origin}${c}`)
        const j = await g2.json()
        assert(d.status === 204 && j.totalItems === 0, `DELETE ${d.status}, totalItems ${j.totalItems}`)
        if (g1.headers.get('last-modified') !== g2.headers.get('last-modified')) {
          assert(tried < 10, 'no two reads in one second after 10 tries')
          continue
        }
        const t1 = g1.headers.get('etag')
        assert(t1 !== g2.headers.get('etag'), `same ETag ${t1} before and after the DELETE`)
        const nm = await fetch(`${rc.origin}${c}`, { headers: { 'if-none-match': t1 } })
        await nm.text()
        assert(nm.status === 200, `If-None-Match with the old tag answered ${nm.status}`)
        break
      }
    } finally {
      await rc.close()
    }
  })

  await check(CHECKS[42], async () => {
    const rc = await listen({ engine, port: 0, insecureNoAuth: true, realClock: true })
    try {
      await fetch(`${rc.origin}/five/`, { method: 'PUT', headers: { 'content-type': 'text/turtle' }, body: '' }).then((r) => r.text())
      const posts = await Promise.all(['1', '2', '3', '4', '5'].map((n) =>
        fetch(`${rc.origin}/five/`, { method: 'POST', headers: { 'content-type': 'text/plain' }, body: n })
          .then(async (r) => { await r.text(); return r })))
      const locs = posts.map((r) => r.headers.get('location'))
      assert(posts.every((r) => r.status === 201), `statuses ${posts.map((r) => r.status)}`)
      assert(new Set(locs).size === 5, `locations ${locs}`)
      const bodies = await Promise.all(locs.map((l) => fetch(new URL(l, rc.origin)).then((r) => r.text())))
      assert(JSON.stringify([...bodies].sort()) === '["1","2","3","4","5"]', `bodies ${bodies}`)
      const j = await (await fetch(`${rc.origin}/five/`, { headers: { accept: 'application/lws+json' } })).json()
      assert(j.totalItems === 5, `totalItems ${j.totalItems}`)
    } finally {
      await rc.close()
    }
  })

  await check(CHECKS[38], async () => {
    const guarded = await listen({ engine, port: 0, auth: { issuers: [{ issuer: 'https://as.example' }] } })
    try {
      const r = await fetch(`${guarded.origin}/private`)
      await r.text()
      assert(r.status === 401, `answered ${r.status}`)
      const link = linkTarget(r.headers.get('link'), 'https://www.w3.org/ns/lws#storage')
      const d = await fetch(`${guarded.origin}/.well-known/lws-storage`)
      const desc = await d.json()
      const descLink = linkTarget(d.headers.get('link'), 'https://www.w3.org/ns/lws#storage')
      assert(link === desc.id && new URL(descLink, guarded.origin).href === desc.id,
        `401 link ${link}, description id ${desc.id}, description link ${descLink}`)
    } finally {
      await guarded.close()
    }
  })

  await check(CHECKS[41], async () => {
    const cliDir = mkdtempSync(join(tmpdir(), 'lws-page-size-'))
    const cli = fileURLToPath(new URL('../../npm/factoidal/bin/factoidal.mjs', import.meta.url))
    const child = spawn(process.execPath, [cli, 'lws-serve', cliDir, '--insecure-no-auth',
      '--port', '0', '--page-size', '2'], { stdio: ['ignore', 'pipe', 'pipe'] })
    try {
      const origin = await new Promise((resolve, reject) => {
        let out = ''
        const timer = setTimeout(() => reject(new Error('lws-serve did not print its origin')), 60000)
        child.stdout.on('data', (c) => {
          out += c
          const m = /^(http:\/\/\S+)$/m.exec(out)
          if (m !== null) { clearTimeout(timer); resolve(m[1]) }
        })
        child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`lws-serve exited ${code}`)) })
      })
      for (const n of ['m1', 'm2', 'm3']) {
        await fetch(`${origin}/p/${n}`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: n }).then((r) => r.text())
      }
      const r = await fetch(`${origin}/p/`, { headers: { accept: 'application/lws+json' } })
      const j = await r.json()
      const link = r.headers.get('link')
      assert(linkTarget(link, 'next') === '/p/?page=2' && linkTarget(link, 'last') === '/p/?page=2', `Link: ${link}`)
      assert(j.items.length === 2 && j.totalItems === 3, `${j.items.length} items, totalItems ${j.totalItems}`)
    } finally {
      child.kill()
      rmSync(cliDir, { recursive: true, force: true })
    }
  })

  // Durable storage under DIR.
  const dir = mkdtempSync(join(tmpdir(), 'lws-draft-binding-'))
  try {
    await check(CHECKS[12], async () => {
      const first = await listen({ engine, port: 0, insecureNoAuth: true, now: 2000, dir })
      try {
        const r = await fetch(`${first.origin}/kept/note.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'kept' })
        await r.text()
        assert(r.status === 201, `PUT answered ${r.status}`)
      } finally {
        await first.close()
      }
      assert(existsSync(join(dir, 'lws-state.json')), 'no lws-state.json')
      const names = readdirSync(dir)
      assert(names.length === 1 && names[0] === 'lws-state.json', `DIR holds ${names}`)
      const second = await listen({ engine, port: 0, insecureNoAuth: true, dir })
      try {
        const g = await fetch(`${second.origin}/kept/note.txt`)
        const body = await g.text()
        assert(g.status === 200 && body === 'kept', `after restart: ${g.status} ${body}`)
      } finally {
        await second.close()
      }
    })

    await check(CHECKS[24], async () => {
      const first = await listen({ engine, port: 0, insecureNoAuth: true, now: 3000, dir })
      try {
        const r = await fetch(`${first.origin}/kept/lic.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain', prefer: 'set-linkset', link: '<https://creativecommons.org/licenses/by/4.0/>; rel="license"' }, body: 'x' })
        await r.text()
        assert(r.status === 201, `PUT answered ${r.status}`)
      } finally {
        await first.close()
      }
      const second = await listen({ engine, port: 0, insecureNoAuth: true, dir })
      try {
        const ls = await (await fetch(`${second.origin}/kept/lic.txt?linkset`)).json()
        assert(ls.linkset[0].license && ls.linkset[0].license[0].href === 'https://creativecommons.org/licenses/by/4.0/', JSON.stringify(ls))
      } finally {
        await second.close()
      }
    })

    await check(CHECKS[33], async () => {
      const receiver = await startReceiver()
      try {
        const first = await listen({ engine, port: 0, insecureNoAuth: true, now: 4000, dir })
        let subscription
        let keyX
        try {
          const d = await (await fetch(`${first.origin}/.well-known/lws-storage`)).json()
          keyX = d.verificationMethod[0].publicKeyJwk.x
          const r = await fetch(`${first.origin}/.well-known/lws-subscriptions/`, {
            method: 'POST',
            headers: { 'content-type': 'application/lws+json' },
            body: JSON.stringify({ type: 'WebhookSubscription', topic: [`${first.origin}/kept/`], inbox: `${receiver.origin}/hook/p` })
          })
          subscription = (await r.json()).subscription
          assert(r.status === 201, `subscribe answered ${r.status}`)
        } finally {
          await first.close()
        }
        const second = await listen({ engine, port: 0, insecureNoAuth: true, dir, baseIri: `${first.origin}/` })
        try {
          const g = await fetch(`${second.origin}${new URL(subscription).pathname}`)
          await g.text()
          assert(g.status === 200, `the subscription after a restart answered ${g.status}`)
          const d = await (await fetch(`${second.origin}/.well-known/lws-storage`)).json()
          assert(d.verificationMethod[0].publicKeyJwk.x === keyX, 'the signing key changed on restart')
        } finally {
          await second.close()
        }
      } finally {
        await receiver.close()
      }
    })

    await check('Access Requests and Grants: grants and requests survive a restart', async () => {
      const first = await listen({ engine, port: 0, insecureNoAuth: true, now: 5000, dir })
      let grant
      let request
      try {
        const sid = `${first.origin}/.well-known/lws-storage`
        const doc = (type) => ({
          '@context': ['https://www.w3.org/ns/lws/v1'],
          type: [type],
          storage: sid,
          access: [{
            type: ['AccessPolicy'], action: ['read', 'create'], assignee: 'https://id.example/bob',
            target: { type: 'Container', value: [`${first.origin}/kept/`] }
          }]
        })
        for (const [path, type] of [['/.well-known/lws-access-grants/', 'AccessGrant'], ['/.well-known/lws-access-requests/', 'AccessRequest']]) {
          const r = await fetch(`${first.origin}${path}`, {
            method: 'POST', headers: { 'content-type': 'application/lws+json' }, body: JSON.stringify(doc(type))
          })
          await r.text()
          assert(r.status === 201, `${type} answered ${r.status}`)
          if (type === 'AccessGrant') grant = new URL(r.headers.get('location')).pathname
          else request = new URL(r.headers.get('location')).pathname
        }
      } finally {
        await first.close()
      }
      const second = await listen({ engine, port: 0, insecureNoAuth: true, dir, baseIri: `${first.origin}/` })
      try {
        for (const p of [grant, request]) {
          const g = await fetch(`${second.origin}${p}`)
          const j = await g.json()
          assert(g.status === 200 && j.access[0].action.includes('create'), `${p} after a restart: ${g.status} ${JSON.stringify(j)}`)
        }
      } finally {
        await second.close()
      }
    })

    await check(CHECKS[13], async () => {
      const s = await listen({ engine, port: 0, insecureNoAuth: true, dir })
      try {
        const before = readdirSync(dirname(dir)).length
        for (const t of ['/../outside', '/../../outside', '/x/../../outside']) {
          const r = await rawRequest(s.origin, 'PUT', t, { 'content-type': 'text/plain' }, 'x')
          assert(r.status === 400, `${t} answered ${r.status}`)
        }
        assert(!existsSync(join(dirname(dir), 'outside')), 'a file was written outside DIR')
        assert(readdirSync(dirname(dir)).length === before, 'the parent of DIR changed')
      } finally {
        await s.close()
      }
    })
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + xfailed + skipped
console.log(`lws-draft-binding node: ${passed} pass, ${failed} fail, ${xfailed} xfail, ` +
  `${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
