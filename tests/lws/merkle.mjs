// Host tests for the optional Merkle hashes of the LWS server.
// https://github.com/danbri/factoidal/issues/919
//
//   node tests/lws/merkle.mjs
//
// Owner, 2026-10-21: "After, yes. As an optional, probably default off until
// we settle on stronger motivating usecase but good to have the fundamentals
// there". Every decision is made in Lean: the hashes and their maintenance
// (formal/lean4/L4Factoidal/LWS/Merkle.lean), the fields and members and who
// sees a root (MerkleHttp.lean). The host passes `merkle: true` and routes.
//
// Checked: the Repr-Digest of a resource equals node:crypto's SHA-256 of the
// body (text, binary, a range, HEAD); a container's Factoidal-Merkle-Root
// field equals its listing member (JSON and Turtle); the storage description
// carries the root container's digest; a write deep in the tree, a move and
// a delete change the roots above them and no other; a restart rebuilds the
// same hashes and the snapshot holds none; off by default there is no field
// or member; entity tags are the same with the option on and off; under
// authorization only the storage controller sees roots; `lws-serve --merkle`.
//
// Score line: "N pass, M fail, X xfail, S skipped (out of T)". An xfail is a
// known shortfall with an open issue: it must FAIL today, and the run fails
// when one passes.

import { mkdtempSync, rmSync, readFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import http from 'node:http'
import { spawn } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { createHash, generateKeyPairSync, randomUUID, sign } from 'node:crypto'

const ROOT = fileURLToPath(new URL('../../', import.meta.url))
const CLI = join(ROOT, 'npm/factoidal/bin/factoidal.mjs')
const ROOT_MEMBER = 'https://github.com/danbri/factoidal/issues/919#merkleRoot'
const STORAGE_MEMBER = 'https://github.com/danbri/factoidal/issues/919#storageMerkleRoot'
const ALICE = 'https://id.example/alice'
const BOB = 'https://id.example/bob'

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

/** RFC 9530 `sha-256=:<base64>:` of some bytes, computed by node:crypto. */
function digestField (bytes) {
  return `sha-256=:${createHash('sha256').update(bytes).digest('base64')}:`
}

const CHECKS = [
  'Repr-Digest of a text resource is the SHA-256 of its bytes (node:crypto)',
  'Repr-Digest of a binary resource (every byte value) is the SHA-256 of its bytes',
  'Repr-Digest on a 206 range answer is the digest of the whole representation',
  'Repr-Digest on HEAD',
  'a container answers Factoidal-Merkle-Root, and its JSON listing carries the same value',
  'the Turtle listing states the same root',
  'the storage description carries the storage root container digest, naming issue 919',
  'a write deep in the tree changes the root of every container above it',
  'a write deep in the tree keeps the digest of a sibling subtree and of other resources',
  'a move changes the roots of both containers and of the storage root, and keeps the moved bytes digest',
  'a delete of a new resource gives back the roots before it was created',
  'a restart rebuilds the same hashes, and the snapshot holds none',
  'off by default: no Repr-Digest, no root field, no listing or storage description member',
  'entity tags are the same with the option on and off',
  'under authorization the storage controller sees roots',
  'under authorization a reader who is not the controller sees no root, but gets Repr-Digest',
  'under authorization the public storage description has no root member',
  'lws-serve --merkle answers Repr-Digest'
]

function b64url (bytes) {
  return Buffer.from(bytes).toString('base64url')
}

/** A local authorization server with one ES256 key. */
async function startIssuer () {
  const pair = generateKeyPairSync('ec', { namedCurve: 'P-256' })
  const jwk = { ...pair.publicKey.export({ format: 'jwk' }), kid: 'k1', alg: 'ES256', use: 'sig' }
  let origin = ''
  const server = http.createServer((req, res) => {
    const url = new URL(req.url, 'http://x')
    res.setHeader('content-type', 'application/json')
    if (url.pathname === '/.well-known/lws-configuration') {
      res.end(JSON.stringify({ issuer: origin, jwks_uri: `${origin}/jwks`, token_endpoint: `${origin}/token` }))
    } else if (url.pathname === '/jwks') {
      res.end(JSON.stringify({ keys: [jwk] }))
    } else { res.statusCode = 404; res.end() }
  })
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
  origin = `http://127.0.0.1:${server.address().port}`
  return {
    origin,
    token (audience, sub) {
      const now = Math.floor(Date.now() / 1000)
      const claims = { iss: origin, sub, aud: audience, client_id: 'https://app.example/id', jti: randomUUID(), iat: now, exp: now + 300 }
      const input = `${b64url(JSON.stringify({ alg: 'ES256', typ: 'at+jwt', kid: 'k1' }))}.${b64url(JSON.stringify(claims))}`
      const sig = sign('sha256', Buffer.from(input), { key: pair.privateKey, dsaEncoding: 'ieee-p1363' })
      return `${input}.${b64url(sig)}`
    },
    close () { return new Promise((resolve) => server.close(resolve)) }
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
  // A module built before issue 919 ignores the configuration member.
  {
    const s = await listen({ engine, port: 0, insecureNoAuth: true, merkle: true })
    try {
      await fetch(`${s.origin}/p.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'p' }).then((r) => r.text())
      const r = await fetch(`${s.origin}/p.txt`)
      await r.text()
      if (r.headers.get('repr-digest') === null) {
        for (const name of CHECKS) skip(name, 'the module ignores "merkle": true (rebuild the wasm)')
        return
      }
    } finally { await s.close() }
  }

  const put = (o, path, body, contentType = 'text/plain', headers = {}) =>
    fetch(`${o}${path}`, { method: 'PUT', headers: { 'content-type': contentType, ...headers }, body })
      .then(async (r) => { await r.arrayBuffer(); assert(r.status === 201 || r.status === 204, `PUT ${path} answered ${r.status}`); return r })
  const rootOf = async (o, path, headers = {}) => {
    const r = await fetch(`${o}${path}`, { headers: { accept: 'application/lws+json', ...headers } })
    await r.arrayBuffer()
    return r.headers.get('factoidal-merkle-root')
  }
  const reprOf = async (o, path) => {
    const r = await fetch(`${o}${path}`)
    await r.arrayBuffer()
    return r.headers.get('repr-digest')
  }
  // One sequence of writes, used on the servers with the option on and off.
  const TEXT = 'abcdefghij'
  const BINARY = Buffer.from(Array.from({ length: 256 }, (_, i) => i))
  const populate = async (o) => {
    await put(o, '/docs/a.txt', TEXT)
    await put(o, '/docs/bin', BINARY, 'application/octet-stream')
    await put(o, '/docs/deep/x/y.nt', '<http://example.org/s> <http://example.org/p> "1" .\n', 'application/n-triples')
    await put(o, '/other/z.txt', 'zed')
  }

  const dir = mkdtempSync(join(tmpdir(), 'lws919-merkle-'))
  let on = await listen({ engine, port: 0, insecureNoAuth: true, merkle: true, now: 1000, dir })
  const off = await listen({ engine, port: 0, insecureNoAuth: true, now: 1000 })
  let o = on.origin
  try {
    await populate(o)
    await populate(off.origin)

    await check(CHECKS[0], async () => {
      const r = await fetch(`${o}/docs/a.txt`)
      const body = Buffer.from(await r.arrayBuffer())
      assert(r.status === 200, `GET answered ${r.status}`)
      assert(r.headers.get('repr-digest') === digestField(body), `Repr-Digest ${r.headers.get('repr-digest')}, body digest ${digestField(body)}`)
      assert(r.headers.get('repr-digest') === digestField(Buffer.from(TEXT)), 'not the digest of the PUT body')
    })

    await check(CHECKS[1], async () => {
      const r = await fetch(`${o}/docs/bin`)
      const body = Buffer.from(await r.arrayBuffer())
      assert(body.equals(BINARY), 'GET did not return the bytes')
      assert(r.headers.get('repr-digest') === digestField(BINARY), `Repr-Digest ${r.headers.get('repr-digest')}`)
    })

    await check(CHECKS[2], async () => {
      const r = await fetch(`${o}/docs/a.txt`, { headers: { range: 'bytes=2-4' } })
      assert((await r.text()) === 'cde' && r.status === 206, `answered ${r.status}`)
      assert(r.headers.get('repr-digest') === digestField(Buffer.from(TEXT)), `Repr-Digest ${r.headers.get('repr-digest')}`)
    })

    await check(CHECKS[3], async () => {
      const r = await fetch(`${o}/docs/a.txt`, { method: 'HEAD' })
      await r.arrayBuffer()
      assert(r.headers.get('repr-digest') === digestField(Buffer.from(TEXT)), `Repr-Digest ${r.headers.get('repr-digest')}`)
    })

    await check(CHECKS[4], async () => {
      const r = await fetch(`${o}/docs/`, { headers: { accept: 'application/lws+json' } })
      const j = await r.json()
      const field = r.headers.get('factoidal-merkle-root')
      assert(/^sha-256=:[A-Za-z0-9+/]{43}=:$/.test(field || ''), `field ${field}`)
      assert(j[ROOT_MEMBER] === field, `member ${j[ROOT_MEMBER]}, field ${field}`)
      assert(j.type === 'Container' && j.totalItems === 4, JSON.stringify(j))
    })

    await check(CHECKS[5], async () => {
      const r = await fetch(`${o}/docs/`, { headers: { accept: 'text/turtle' } })
      const body = await r.text()
      const field = r.headers.get('factoidal-merkle-root')
      assert(body.indexOf(`<${o}/docs/> <${ROOT_MEMBER}> "${field}" .`) >= 0, body)
    })

    await check(CHECKS[6], async () => {
      const r = await fetch(`${o}/.well-known/lws-storage`)
      const d = await r.json()
      assert(d[STORAGE_MEMBER] === await rootOf(o, '/'), `member ${d[STORAGE_MEMBER]}`)
    })

    const watched = ['/', '/docs/', '/docs/deep/', '/docs/deep/x/', '/other/']
    const roots = async () => Object.fromEntries(await Promise.all(watched.map(async (p) => [p, await rootOf(o, p)])))
    const before = await roots()
    const otherDigest = await reprOf(o, '/other/z.txt')
    const aDigest = await reprOf(o, '/docs/a.txt')
    await put(o, '/docs/deep/x/y.nt', '<http://example.org/s> <http://example.org/p> "2" .\n', 'application/n-triples')
    const after = await roots()

    await check(CHECKS[7], async () => {
      for (const p of ['/', '/docs/', '/docs/deep/', '/docs/deep/x/']) {
        assert(after[p] !== null && after[p] !== before[p], `${p}: ${before[p]} then ${after[p]}`)
      }
    })

    await check(CHECKS[8], async () => {
      assert(after['/other/'] === before['/other/'], `/other/: ${before['/other/']} then ${after['/other/']}`)
      assert(await reprOf(o, '/other/z.txt') === otherDigest, 'the digest of /other/z.txt changed')
      assert(await reprOf(o, '/docs/a.txt') === aDigest, 'the digest of /docs/a.txt changed')
    })

    await check(CHECKS[9], async () => {
      const r0 = await roots()
      const moved = await fetch(`${o}/docs/a.txt?linkset`, {
        method: 'PATCH',
        headers: { 'content-type': 'application/json-patch+json' },
        body: JSON.stringify([{ op: 'replace', path: '/linkset/0/up/0/href', value: `${o}/other/` }])
      })
      await moved.text()
      assert(moved.status === 200, `move answered ${moved.status}`)
      const r1 = await roots()
      for (const p of ['/', '/docs/', '/other/']) assert(r1[p] !== r0[p], `${p} unchanged by the move`)
      assert(r1['/docs/deep/'] === r0['/docs/deep/'], 'the deep subtree changed')
      assert(await reprOf(o, '/other/a.txt') === aDigest, 'the moved bytes have another digest')
    })

    await check(CHECKS[10], async () => {
      const r0 = await roots()
      await put(o, '/docs/deep/new.txt', 'new')
      const r1 = await roots()
      assert(r1['/docs/deep/'] !== r0['/docs/deep/'] && r1['/'] !== r0['/'], 'the create changed nothing')
      const d = await fetch(`${o}/docs/deep/new.txt`, { method: 'DELETE' })
      await d.text()
      assert(d.status === 204, `DELETE answered ${d.status}`)
      const r2 = await roots()
      for (const p of watched) {
        // The parent's listing is stamped by the delete, but its members are
        // those before the create.
        assert(r2[p] === r0[p], `${p}: ${r0[p]} before, ${r2[p]} after create and delete`)
      }
    })

    await check(CHECKS[11], async () => {
      const r0 = await roots()
      const d0 = await reprOf(o, '/docs/bin')
      await on.close()
      const text = readFileSync(join(dir, 'lws-state.json'), 'utf8')
      for (const v of Object.values(r0)) {
        const b64 = v.slice('sha-256=:'.length, -1)
        assert(text.indexOf(b64) < 0, `the snapshot holds the root ${v}`)
      }
      on = await listen({ engine, port: 0, insecureNoAuth: true, merkle: true, dir, baseIri: `${o}/` })
      o = on.origin
      const sameBase = (await roots())
      for (const p of watched) assert(sameBase[p] === r0[p], `${p}: ${r0[p]} before the restart, ${sameBase[p]} after`)
      assert(await reprOf(o, '/docs/bin') === d0, 'the digest of /docs/bin changed across the restart')
    })

    await check(CHECKS[12], async () => {
      const p = off.origin
      const g = await fetch(`${p}/docs/a.txt`)
      await g.text()
      assert(g.headers.get('repr-digest') === null, 'Repr-Digest with the option off')
      const c = await fetch(`${p}/docs/`, { headers: { accept: 'application/lws+json' } })
      const j = await c.json()
      assert(c.headers.get('factoidal-merkle-root') === null, 'root field with the option off')
      assert(!(ROOT_MEMBER in j), 'listing member with the option off')
      const t = await (await fetch(`${p}/docs/`, { headers: { accept: 'text/turtle' } })).text()
      assert(t.indexOf(ROOT_MEMBER) < 0, 'Turtle listing statement with the option off')
      const d = await (await fetch(`${p}/.well-known/lws-storage`)).json()
      assert(!(STORAGE_MEMBER in d), 'storage description member with the option off')
    })

    await check(CHECKS[13], async () => {
      // Two fresh servers, the same clock and the same writes.
      const a = await listen({ engine, port: 0, insecureNoAuth: true, merkle: true, now: 5000, baseIri: 'http://tags.example/' })
      const b = await listen({ engine, port: 0, insecureNoAuth: true, now: 5000, baseIri: 'http://tags.example/' })
      try {
        await populate(a.origin)
        await populate(b.origin)
        for (const path of ['/docs/a.txt', '/docs/bin', '/docs/', '/docs/deep/', '/', '/.well-known/lws-storage']) {
          for (const accept of ['application/lws+json', 'text/turtle']) {
            const ra = await fetch(`${a.origin}${path}`, { headers: { accept } })
            const rb = await fetch(`${b.origin}${path}`, { headers: { accept } })
            await ra.arrayBuffer(); await rb.arrayBuffer()
            assert(ra.headers.get('etag') === rb.headers.get('etag'),
              `${path} (${accept}): ETag ${ra.headers.get('etag')} on, ${rb.headers.get('etag')} off`)
          }
        }
      } finally { await a.close(); await b.close() }
    })

    // Known shortfall of this step: entity tags do not change (owner's
    // coordinator, 2026-10-21), so a container listing whose root member
    // changed after a write deep below it keeps its strong ETag (RFC 9110
    // section 8.8.1 wants a strong validator to change with the
    // representation data).
    await xfail('the ETag of a container listing changes when its Merkle root changes (RFC 9110 section 8.8.1)',
      'https://github.com/danbri/factoidal/issues/919', async () => {
        const tag = async () => {
          const r = await fetch(`${o}/docs/`, { headers: { accept: 'application/lws+json' } })
          await r.text()
          return [r.headers.get('etag'), r.headers.get('factoidal-merkle-root')]
        }
        const [t0, m0] = await tag()
        await put(o, '/docs/deep/x/y.nt', '<http://example.org/s> <http://example.org/p> "3" .\n', 'application/n-triples')
        const [t1, m1] = await tag()
        assert(m0 !== m1, 'the root did not change')
        assert(t0 !== t1, `ETag ${t0} stayed while the root changed`)
      })
  } finally {
    await on.close()
    await off.close()
    rmSync(dir, { recursive: true, force: true })
  }

  // Authorization: roots to the storage controller only.
  const issuer = await startIssuer()
  const guarded = await listen({ engine, port: 0, owner: ALICE, realClock: true, merkle: true,
    auth: { issuers: [{ issuer: issuer.origin }], refreshInterval: 0 } })
  const g = guarded.origin
  const aud = `${g}/.well-known/lws-storage`
  const aliceT = issuer.token(aud, ALICE)
  const bobT = issuer.token(aud, BOB)
  const bearer = (t) => ({ authorization: `Bearer ${t}` })
  try {
    const acl = (target) => '@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n' +
      `<${g}${target}.acl#owner> a acl:Authorization ; acl:agent <${ALICE}> ; acl:accessTo <${g}${target}> ;` +
      ` acl:default <${g}${target}> ; acl:mode acl:Read, acl:Write, acl:Control .\n` +
      `<${g}${target}.acl#bob> a acl:Authorization ; acl:agent <${BOB}> ; acl:accessTo <${g}${target}> ;` +
      ` acl:default <${g}${target}> ; acl:mode acl:Read .\n`
    await put(g, '/shared/', '', 'text/turtle', bearer(aliceT))
    await put(g, '/shared/.acl', acl('/shared/'), 'text/turtle', bearer(aliceT))
    await put(g, '/shared/doc.txt', 'for bob', 'text/plain', bearer(aliceT))

    await check(CHECKS[14], async () => {
      const r = await fetch(`${g}/shared/`, { headers: { accept: 'application/lws+json', ...bearer(aliceT) } })
      const j = await r.json()
      assert(r.status === 200, `alice listing answered ${r.status}`)
      const field = r.headers.get('factoidal-merkle-root')
      assert(field !== null && j[ROOT_MEMBER] === field, `field ${field}, member ${j[ROOT_MEMBER]}`)
      const d = await (await fetch(`${g}/.well-known/lws-storage`, { headers: bearer(aliceT) })).json()
      assert(typeof d[STORAGE_MEMBER] === 'string', 'no storage root member for the controller')
    })

    await check(CHECKS[15], async () => {
      const r = await fetch(`${g}/shared/`, { headers: { accept: 'application/lws+json', ...bearer(bobT) } })
      const j = await r.json()
      assert(r.status === 200, `bob listing answered ${r.status}`)
      assert(r.headers.get('factoidal-merkle-root') === null, 'bob sees the root field')
      assert(!(ROOT_MEMBER in j), 'bob sees the root member')
      const t = await (await fetch(`${g}/shared/`, { headers: { accept: 'text/turtle', ...bearer(bobT) } })).text()
      assert(t.indexOf(ROOT_MEMBER) < 0, 'bob sees the Turtle root statement')
      const doc = await fetch(`${g}/shared/doc.txt`, { headers: bearer(bobT) })
      await doc.text()
      assert(doc.status === 200 && doc.headers.get('repr-digest') === digestField(Buffer.from('for bob')),
        `bob GET answered ${doc.status}, Repr-Digest ${doc.headers.get('repr-digest')}`)
    })

    await check(CHECKS[16], async () => {
      const r = await fetch(`${g}/.well-known/lws-storage`)
      const d = await r.json()
      assert(r.status === 200, `answered ${r.status}`)
      assert(!(STORAGE_MEMBER in d), 'the anonymous storage description carries a root')
      const b = await (await fetch(`${g}/.well-known/lws-storage`, { headers: bearer(bobT) })).json()
      assert(!(STORAGE_MEMBER in b), 'bob sees the storage root')
    })
  } finally {
    await guarded.close()
    await issuer.close()
  }

  // The CLI flag.
  await check(CHECKS[17], async () => {
    const cdir = mkdtempSync(join(tmpdir(), 'lws919-cli-'))
    const child = spawn(process.execPath, [CLI, 'lws-serve', cdir, '--insecure-no-auth', '--merkle',
      '--port', '0', '--quiet'], { stdio: ['ignore', 'pipe', 'pipe'] })
    try {
      const origin = await new Promise((resolve, reject) => {
        let out = ''
        const timer = setTimeout(() => reject(new Error(`no origin printed: ${out}`)), 30000)
        child.stdout.on('data', (c) => {
          out += c
          const m = /(http:\/\/[^\s]+)/.exec(out)
          if (m) { clearTimeout(timer); resolve(m[1]) }
        })
        child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`exited ${code}: ${out}`)) })
      })
      await put(origin, '/c.txt', 'cli')
      assert(await reprOf(origin, '/c.txt') === digestField(Buffer.from('cli')), 'no Repr-Digest from the CLI server')
    } finally {
      child.kill('SIGTERM')
      await new Promise((resolve) => child.on('close', resolve))
      rmSync(cdir, { recursive: true, force: true })
    }
  })
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + xfailed + skipped
console.log(`lws-merkle node: ${passed} pass, ${failed} fail, ${xfailed} xfail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
