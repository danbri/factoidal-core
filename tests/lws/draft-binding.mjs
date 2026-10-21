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
  'Persistence: client links survive a restart'
]

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
      for (const rel of ['type', 'up', 'linkset', 'items', 'https://www.w3.org/ns/lws#storage']) {
        const r = await fetch(`${o}/lic.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain', prefer: 'set-linkset', link: `<https://example.org/x>; rel="${rel}"` }, body: 'changed' })
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

    await xfail('Notifications: the storage description advertises a NotificationService',
      'https://github.com/danbri/factoidal/issues/890', async () => {
        const d = await (await fetch(`${o}/.well-known/lws-storage`)).json()
        assert(d.service.some((s) => s.type === 'NotificationService'), JSON.stringify(d.service))
      })
  } finally {
    await running.close()
  }

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
