// Host tests for CORS in the LWS HTTP binding, the authorization server and
// the Solid server's preflight. https://github.com/danbri/factoidal/issues/923
//
//   node tests/lws/cors.mjs
//
// Every decision is made in Lean: the policy, the preflight answer and the
// fields of every other answer (formal/lean4/L4Factoidal/HTTP/Cors.lean), the
// LWS profile (L4Factoidal/LWS/Cors.lean), the authorization server profile
// (L4Factoidal/Authz/Server.lean stepCors), the Solid preflight
// (L4Factoidal/Solid/Server/Methods.lean). The hosts pass `cors` unread.
// A browser check (Chromium) is tests/lws/cors-browser.mjs.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import { mkdtempSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import http from 'node:http'
import { spawn } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { generateKeyPairSync, randomUUID, sign } from 'node:crypto'

const ROOT = fileURLToPath(new URL('../../', import.meta.url))
const CLI = join(ROOT, 'npm/factoidal/bin/factoidal.mjs')
const PAGE = 'https://danbri.github.io'
const OTHER = 'https://evil.example'
const ALICE = 'https://id.example/alice'

// The fields as L4Factoidal/LWS/Cors.lean lists them.
const METHODS = ['GET', 'HEAD', 'OPTIONS', 'POST', 'PUT', 'PATCH', 'DELETE', 'QUERY']
const REQUEST_HEADERS = ['Accept', 'Authorization', 'Content-Type', 'DPoP', 'If-Match',
  'If-Modified-Since', 'If-None-Match', 'If-Unmodified-Since', 'Link', 'Prefer', 'Range', 'Slug']
const EXPOSED = ['Accept-Patch', 'Accept-Post', 'Accept-Put', 'Accept-Query', 'Accept-Ranges',
  'Allow', 'Content-Location', 'Content-Range', 'ETag', 'Factoidal-Merkle-Root', 'Last-Modified',
  'Link', 'Location', 'Preference-Applied', 'Repr-Digest', 'WWW-Authenticate']

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

const list = (v) => (v === null ? [] : v.split(',').map((x) => x.trim()).filter((x) => x !== ''))

const CHECKS = [
  'LWS preflight (open): 204, the page origin, methods with QUERY and PATCH, the request header fields, Max-Age, no credentials, Vary: Origin',
  'LWS preflight carries no Allow, no body: it is not the OPTIONS answer of the resource',
  'LWS GET with Origin: Allow-Origin, every exposed field, Vary: Origin',
  'LWS container listing: Vary lists Accept and Origin in one field',
  'LWS request without Origin: Vary: Origin and no other CORS field',
  'LWS OPTIONS without Access-Control-Request-Method: the resource answer as before, with the CORS fields',
  'LWS echo: Origin null and a malformed Origin are not echoed',
  'LWS cors list: a listed origin is echoed, another is not; a preflight from another gets no Allow-Origin',
  'LWS cors false: no CORS field; a preflight is the ordinary OPTIONS answer',
  'LWS a cors list with a path or a slash is refused at open',
  'LWS authorization on: a preflight with no token to a private resource is 204 with the fields, not 401',
  'LWS authorization on: 401 with no token carries Allow-Origin, and WWW-Authenticate is exposed',
  'LWS authorization on: with a token, write with If-Match and read back, Allow-Origin on each',
  'lws-serve --cors-origin twice: both origins answered, a third not',
  'lws-serve --no-cors: no CORS field',
  'lws-serve --cors-origin with a path: the start is refused',
  'authz-serve host: preflight to /token is 204 with POST allowed; GET /jwks with Origin has Allow-Origin',
  'authz-serve host with cors false: no CORS field',
  'solid-serve host, Web Access Control on: a preflight is 204 with Allow-Origin, while GET is refused'
]

/** One request with node:http, so that any header (Origin included) is sent as given. */
function raw (origin, method, path, headers = {}, body = null) {
  return new Promise((resolve, reject) => {
    const url = new URL(path, origin)
    const req = http.request({ host: url.hostname, port: url.port, path: url.pathname + url.search, method, headers }, (res) => {
      const chunks = []
      res.on('data', (c) => chunks.push(c))
      res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, rawHeaders: res.rawHeaders, body: Buffer.concat(chunks).toString('utf8') }))
      res.on('error', reject)
    })
    req.on('error', reject)
    if (body !== null) req.write(body)
    req.end()
  })
}

const preflightHeaders = (o, m = 'PUT') => ({
  origin: o,
  'access-control-request-method': m,
  'access-control-request-headers': 'authorization, content-type, if-match'
})

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

/** Start a CLI server and read the origin it prints, or its exit code and output. */
function startCli (args) {
  const child = spawn(process.execPath, [CLI, ...args], { stdio: ['ignore', 'pipe', 'pipe'] })
  let out = ''
  let errOut = ''
  child.stdout.on('data', (c) => { out += c })
  child.stderr.on('data', (c) => { errOut += c })
  const started = new Promise((resolve) => {
    const timer = setTimeout(() => resolve({ error: `no origin printed: ${out} ${errOut}` }), 30000)
    child.stdout.on('data', () => {
      const m = /(http:\/\/[^\s]+)/.exec(out)
      if (m) { clearTimeout(timer); resolve({ origin: m[1] }) }
    })
    child.on('exit', (code) => { clearTimeout(timer); resolve({ exit: code, out, errOut }) })
  })
  return {
    started,
    async stop () {
      if (child.exitCode === null) {
        child.kill('SIGTERM')
        await new Promise((resolve) => child.on('close', resolve))
      }
    }
  }
}

async function main () {
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  const { listen, lwsOpsAvailable, openLwsStorage } = await import('../../npm/factoidal/lws/server.mjs')
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
  // A module built before issue 923 sends no CORS field.
  {
    const s = await listen({ engine, port: 0, insecureNoAuth: true })
    try {
      const r = await raw(s.origin, 'GET', '/', { origin: PAGE })
      if (r.headers['access-control-allow-origin'] === undefined) {
        for (const name of CHECKS) skip(name, 'the module sends no CORS field (rebuild the wasm)')
        return
      }
    } finally { await s.close() }
  }

  const open = await listen({ engine, port: 0, insecureNoAuth: true })
  const o = open.origin
  try {
    await raw(o, 'PUT', '/notes/a.txt', { 'content-type': 'text/plain' }, 'hello')

    await check(CHECKS[0], async () => {
      const r = await raw(o, 'OPTIONS', '/notes/a.txt', preflightHeaders(PAGE))
      assert(r.status === 204, `status ${r.status}`)
      assert(r.headers['access-control-allow-origin'] === PAGE, `allow-origin ${r.headers['access-control-allow-origin']}`)
      const ms = list(r.headers['access-control-allow-methods'] || null)
      for (const m of METHODS) assert(ms.includes(m), `methods ${ms} lack ${m}`)
      const hs = list(r.headers['access-control-allow-headers'] || null)
      for (const h of REQUEST_HEADERS) assert(hs.includes(h), `allow-headers ${hs} lack ${h}`)
      assert(Number(r.headers['access-control-max-age']) > 0, `max-age ${r.headers['access-control-max-age']}`)
      assert(r.headers['access-control-allow-credentials'] === undefined, 'credentials sent')
      assert(list(r.headers.vary || null).includes('Origin'), `vary ${r.headers.vary}`)
    })

    await check(CHECKS[1], async () => {
      const r = await raw(o, 'OPTIONS', '/notes/a.txt', preflightHeaders(PAGE, 'DELETE'))
      assert(r.headers.allow === undefined, `allow ${r.headers.allow}`)
      assert(r.body === '', `body ${r.body}`)
    })

    await check(CHECKS[2], async () => {
      const r = await raw(o, 'GET', '/notes/a.txt', { origin: PAGE })
      assert(r.status === 200 && r.body === 'hello', `status ${r.status}`)
      assert(r.headers['access-control-allow-origin'] === PAGE, `allow-origin ${r.headers['access-control-allow-origin']}`)
      const ex = list(r.headers['access-control-expose-headers'] || null)
      for (const h of EXPOSED) assert(ex.includes(h), `expose ${ex} lacks ${h}`)
      assert(list(r.headers.vary || null).includes('Origin'), `vary ${r.headers.vary}`)
      assert(r.headers.etag !== undefined, 'no ETag')
    })

    await check(CHECKS[3], async () => {
      const r = await raw(o, 'GET', '/notes/', { origin: PAGE, accept: 'application/lws+json' })
      const varyFields = []
      for (let i = 0; i < r.rawHeaders.length; i += 2) {
        if (r.rawHeaders[i].toLowerCase() === 'vary') varyFields.push(r.rawHeaders[i + 1])
      }
      assert(varyFields.length === 1, `vary fields ${JSON.stringify(varyFields)}`)
      const v = list(varyFields[0]).map((x) => x.toLowerCase())
      assert(v.includes('accept') && v.includes('origin'), `vary ${varyFields[0]}`)
    })

    await check(CHECKS[4], async () => {
      const r = await raw(o, 'GET', '/notes/a.txt')
      assert(r.status === 200, `status ${r.status}`)
      assert(list(r.headers.vary || null).includes('Origin'), `vary ${r.headers.vary}`)
      assert(r.headers['access-control-allow-origin'] === undefined, 'allow-origin with no Origin')
      assert(r.headers['access-control-expose-headers'] === undefined, 'expose with no Origin')
    })

    await check(CHECKS[5], async () => {
      const r = await raw(o, 'OPTIONS', '/notes/a.txt', { origin: PAGE })
      assert(r.status === 204, `status ${r.status}`)
      assert(r.headers.allow !== undefined && r.headers.allow.includes('PUT'), `allow ${r.headers.allow}`)
      assert(r.headers['access-control-allow-origin'] === PAGE, `allow-origin ${r.headers['access-control-allow-origin']}`)
      assert(r.headers['access-control-allow-methods'] === undefined, 'a preflight answer')
    })

    await check(CHECKS[6], async () => {
      for (const bad of ['null', 'https://danbri.github.io/x', 'HTTPS://DANBRI.GITHUB.IO']) {
        const r = await raw(o, 'GET', '/notes/a.txt', { origin: bad })
        assert(r.headers['access-control-allow-origin'] === undefined, `${bad} echoed`)
        const p = await raw(o, 'OPTIONS', '/notes/a.txt', preflightHeaders(bad))
        assert(p.headers['access-control-allow-origin'] === undefined, `${bad} echoed in a preflight`)
      }
    })
  } finally {
    await open.close()
  }

  {
    const s = await listen({ engine, port: 0, insecureNoAuth: true, cors: [PAGE] })
    try {
      await check(CHECKS[7], async () => {
        const a = await raw(s.origin, 'GET', '/', { origin: PAGE })
        assert(a.headers['access-control-allow-origin'] === PAGE, `listed: ${a.headers['access-control-allow-origin']}`)
        const b = await raw(s.origin, 'GET', '/', { origin: OTHER })
        assert(b.headers['access-control-allow-origin'] === undefined, 'another origin echoed')
        assert(list(b.headers.vary || null).includes('Origin'), `vary ${b.headers.vary}`)
        const p = await raw(s.origin, 'OPTIONS', '/', preflightHeaders(OTHER))
        assert(p.status === 204 && p.headers['access-control-allow-origin'] === undefined,
          `preflight from another: ${p.status} ${p.headers['access-control-allow-origin']}`)
      })
    } finally { await s.close() }
  }

  {
    const s = await listen({ engine, port: 0, insecureNoAuth: true, cors: false })
    try {
      await check(CHECKS[8], async () => {
        const a = await raw(s.origin, 'GET', '/', { origin: PAGE })
        const names = Object.keys(a.headers)
        assert(!names.some((n) => n.startsWith('access-control-')), `fields ${names}`)
        assert(!list(a.headers.vary || null).includes('Origin'), `vary ${a.headers.vary}`)
        const p = await raw(s.origin, 'OPTIONS', '/', preflightHeaders(PAGE))
        assert(p.headers.allow !== undefined, `allow ${p.headers.allow}`)
        assert(!Object.keys(p.headers).some((n) => n.startsWith('access-control-')), 'CORS field on a preflight')
      })
    } finally { await s.close() }
  }

  await check(CHECKS[9], async () => {
    for (const bad of [['https://danbri.github.io/'], ['https://danbri.github.io/app'], [], ['*'], 'https://danbri.github.io']) {
      let refused = null
      try {
        const st = await openLwsStorage({ engine, insecureNoAuth: true, cors: bad })
        st.close()
      } catch (error) {
        refused = error
      }
      assert(refused !== null, `opened with cors ${JSON.stringify(bad)}`)
      const text = refused.envelope !== undefined ? refused.envelope.error : refused.message
      assert(/cors/.test(text), `message ${text}`)
    }
  })

  // Authorization on: the owner's root ACL, a local issuer.
  const issuer = await startIssuer()
  const guarded = await listen({ engine, port: 0, auth: { issuers: [{ issuer: issuer.origin }] }, owner: ALICE, realClock: true })
  const g = guarded.origin
  const aliceT = issuer.token(`${g}/.well-known/lws-storage`, ALICE)
  try {
    await check(CHECKS[10], async () => {
      const r = await raw(g, 'OPTIONS', '/private/x.txt', preflightHeaders(PAGE))
      assert(r.status === 204, `status ${r.status}`)
      assert(r.headers['access-control-allow-origin'] === PAGE, `allow-origin ${r.headers['access-control-allow-origin']}`)
      assert(r.headers['www-authenticate'] === undefined, 'challenge on a preflight')
    })

    await check(CHECKS[11], async () => {
      const r = await raw(g, 'GET', '/', { origin: PAGE })
      assert(r.status === 401, `status ${r.status}`)
      assert(r.headers['access-control-allow-origin'] === PAGE, `allow-origin ${r.headers['access-control-allow-origin']}`)
      assert(list(r.headers['access-control-expose-headers'] || null).includes('WWW-Authenticate'), 'WWW-Authenticate not exposed')
      assert(/^Bearer /.test(r.headers['www-authenticate'] || ''), `challenge ${r.headers['www-authenticate']}`)
    })

    await check(CHECKS[12], async () => {
      const auth = { authorization: `Bearer ${aliceT}`, origin: PAGE }
      const c = await raw(g, 'PUT', '/notes/b.txt', { ...auth, 'content-type': 'text/plain' }, 'one')
      assert(c.status === 201 && c.headers['access-control-allow-origin'] === PAGE, `PUT ${c.status}`)
      const r1 = await raw(g, 'GET', '/notes/b.txt', auth)
      assert(r1.status === 200 && r1.body === 'one', `GET ${r1.status}`)
      const tag = r1.headers.etag
      const stale = await raw(g, 'PUT', '/notes/b.txt', { ...auth, 'content-type': 'text/plain', 'if-match': '"stale"' }, 'two')
      assert(stale.status === 412 && stale.headers['access-control-allow-origin'] === PAGE, `stale If-Match ${stale.status}`)
      const w = await raw(g, 'PUT', '/notes/b.txt', { ...auth, 'content-type': 'text/plain', 'if-match': tag }, 'two')
      assert(w.status === 204 && w.headers['access-control-allow-origin'] === PAGE, `If-Match ${w.status}`)
      const r2 = await raw(g, 'GET', '/notes/b.txt', auth)
      assert(r2.body === 'two' && r2.headers['access-control-allow-origin'] === PAGE, `read back ${r2.body}`)
    })
  } finally {
    await guarded.close()
    await issuer.close()
  }

  // The CLI flags.
  {
    const dir = mkdtempSync(join(tmpdir(), 'cors923-cli-'))
    const run = startCli(['lws-serve', dir, '--insecure-no-auth', '--port', '0', '--quiet',
      '--cors-origin', PAGE, '--cors-origin', 'http://localhost:8080'])
    try {
      await check(CHECKS[13], async () => {
        const s = await run.started
        assert(s.origin !== undefined, JSON.stringify(s))
        for (const ok of [PAGE, 'http://localhost:8080']) {
          const r = await raw(s.origin, 'GET', '/', { origin: ok })
          assert(r.headers['access-control-allow-origin'] === ok, `${ok}: ${r.headers['access-control-allow-origin']}`)
        }
        const r = await raw(s.origin, 'GET', '/', { origin: OTHER })
        assert(r.headers['access-control-allow-origin'] === undefined, 'a third origin echoed')
      })
    } finally {
      await run.stop()
      rmSync(dir, { recursive: true, force: true })
    }
  }
  {
    const dir = mkdtempSync(join(tmpdir(), 'cors923-cli-'))
    const run = startCli(['lws-serve', dir, '--insecure-no-auth', '--port', '0', '--quiet', '--no-cors'])
    try {
      await check(CHECKS[14], async () => {
        const s = await run.started
        assert(s.origin !== undefined, JSON.stringify(s))
        const r = await raw(s.origin, 'GET', '/', { origin: PAGE })
        assert(!Object.keys(r.headers).some((n) => n.startsWith('access-control-')), 'CORS field sent')
      })
    } finally {
      await run.stop()
      rmSync(dir, { recursive: true, force: true })
    }
  }
  {
    const dir = mkdtempSync(join(tmpdir(), 'cors923-cli-'))
    const run = startCli(['lws-serve', dir, '--insecure-no-auth', '--port', '0', '--quiet',
      '--cors-origin', 'https://danbri.github.io/app'])
    try {
      await check(CHECKS[15], async () => {
        const s = await run.started
        assert(s.exit !== undefined && s.exit !== 0, `started: ${JSON.stringify(s)}`)
        assert(/cors/.test(s.errOut), `message ${s.errOut}`)
      })
    } finally {
      await run.stop()
      rmSync(dir, { recursive: true, force: true })
    }
  }

  // The authorization server.
  {
    const { listen: authzListen } = await import('../../npm/factoidal/authz/server.mjs')
    for (const [index, cors] of [[16, undefined], [17, false]]) {
      const dir = mkdtempSync(join(tmpdir(), 'cors923-authz-'))
      let s = null
      try {
        s = await authzListen({ engine, port: 0, dir, resources: ['http://127.0.0.1:1/.well-known/lws-storage'],
          storageKey: null, ...(cors === undefined ? {} : { cors }) })
        await check(CHECKS[index], async () => {
          const p = await raw(s.origin, 'OPTIONS', '/token', preflightHeaders(PAGE, 'POST'))
          const j = await raw(s.origin, 'GET', '/jwks', { origin: PAGE })
          assert(j.status === 200, `jwks ${j.status}`)
          if (cors === undefined) {
            assert(p.status === 204, `preflight ${p.status}`)
            assert(p.headers['access-control-allow-origin'] === PAGE, `preflight allow-origin ${p.headers['access-control-allow-origin']}`)
            assert(list(p.headers['access-control-allow-methods'] || null).includes('POST'), `methods ${p.headers['access-control-allow-methods']}`)
            assert(j.headers['access-control-allow-origin'] === PAGE, `jwks allow-origin ${j.headers['access-control-allow-origin']}`)
          } else {
            assert(!Object.keys(j.headers).some((n) => n.startsWith('access-control-')), 'CORS field sent')
            assert(!Object.keys(p.headers).some((n) => n.startsWith('access-control-')), 'CORS field on a preflight')
          }
        })
      } catch (error) {
        if (s === null) {
          failed += 1
          failures.push(`${CHECKS[index]}: the authorization server did not start: ${error.message}`)
          console.log(`  FAIL  ${CHECKS[index]}`)
        } else throw error
      } finally {
        if (s !== null) await s.close()
        rmSync(dir, { recursive: true, force: true })
      }
    }
  }

  // The Solid server: Web Access Control on, nobody authenticated.
  {
    const { listen: solidListen } = await import('../../npm/factoidal/solid/server/index.mjs')
    const s = await solidListen({ engine, port: 0, insecureNoAuth: true, enforceWac: true })
    try {
      await check(CHECKS[18], async () => {
        const get = await raw(s.origin, 'GET', '/', { origin: PAGE })
        assert(get.status === 401 || get.status === 403, `GET ${get.status}: Web Access Control is not on`)
        const p = await raw(s.origin, 'OPTIONS', '/', preflightHeaders(PAGE))
        assert(p.status === 204, `preflight ${p.status}`)
        assert(p.headers['access-control-allow-origin'] === PAGE, `allow-origin ${p.headers['access-control-allow-origin']}`)
      })
    } finally { await s.close() }
  }
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`lws-cors node: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
