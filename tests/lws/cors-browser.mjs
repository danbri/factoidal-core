// Browser check of CORS in the LWS HTTP binding (Chromium through Playwright).
// https://github.com/danbri/factoidal/issues/923
//
//   node tests/lws/cors-browser.mjs
//
// A page served from one origin (http://127.0.0.1:B) calls an lws-serve
// storage on another (http://127.0.0.1:A) under authorization, with fetch():
// it writes with a Bearer token, reads the ETag, writes again with If-Match
// (and is refused with 412 for a stale tag), reads the content back, and
// without a token gets 401 and reads its WWW-Authenticate. A storage started
// with `cors: false`, and one whose list does not name the page's origin, are
// refused by the browser (fetch rejects). Every CORS field comes from
// formal/lean4/L4Factoidal/LWS/Cors.lean.
//
// Needs Playwright with Chromium (PLAYWRIGHT_BROWSERS_PATH, default
// /opt/pw-browsers; never `playwright install`). Exit 0 pass, 1 fail, 2 could
// not run here (the reason is printed; never a pass).
//
// Score line: "N pass, M fail, S skipped (out of T)".

import http from 'node:http'
import { existsSync } from 'node:fs'
import { generateKeyPairSync, randomUUID, sign } from 'node:crypto'

const ALICE = 'https://id.example/alice'

let passed = 0
let failed = 0
let skipped = 0
const failures = []

const CHECKS = [
  'a page on another origin writes with a Bearer token (201) and reads the ETag',
  'the page writes again with If-Match of that ETag (204); a stale tag is 412 and readable',
  'the page reads the new content back',
  'the page gets 401 with no token and reads WWW-Authenticate and Link',
  'a storage with cors false: the browser refuses the answer (fetch rejects)',
  'a storage whose cors list does not name the page origin: the browser refuses the answer'
]

function record (name, ok, why) {
  if (ok) {
    passed += 1
    console.log(`  ok    ${name}`)
  } else {
    failed += 1
    failures.push(`${name}: ${why}`)
    console.log(`  FAIL  ${name}`)
  }
}

function notRun (reason) {
  for (const name of CHECKS) {
    skipped += 1
    console.log(`  skip  ${name} - ${reason}`)
  }
  console.log(`lws-cors browser: 0 pass, 0 fail, ${skipped} skipped (out of ${skipped}) - not run: ${reason}`)
  process.exit(2)
}

async function loadPlaywright () {
  const candidates = [process.env.PLAYWRIGHT_PKG, '/opt/node22/lib/node_modules/playwright',
    '/opt/node-tools/node_modules/playwright'].filter((p) => typeof p === 'string' && p !== '')
  for (const dir of candidates) {
    if (existsSync(`${dir}/index.mjs`)) return import(`${dir}/index.mjs`)
  }
  return import('playwright')
}

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

/** The page's own origin: one HTML page. */
async function startPageServer () {
  const server = http.createServer((req, res) => {
    res.setHeader('content-type', 'text/html; charset=utf-8')
    res.end('<!doctype html><html><head><meta charset="utf-8"><title>cors page</title></head><body>page</body></html>')
  })
  await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve))
  return {
    origin: `http://127.0.0.1:${server.address().port}`,
    close () { return new Promise((resolve) => server.close(resolve)) }
  }
}

async function main () {
  process.env.PLAYWRIGHT_BROWSERS_PATH = process.env.PLAYWRIGHT_BROWSERS_PATH || '/opt/pw-browsers'
  let chromium
  try {
    ({ chromium } = await loadPlaywright())
  } catch (error) {
    notRun(`no Playwright: ${error.message}`)
  }
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  const { listen, lwsOpsAvailable } = await import('../../npm/factoidal/lws/server.mjs')
  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    notRun(`the Lean engine did not load: ${error.message}`)
  }
  const probe = await lwsOpsAvailable(engine)
  if (!probe.available) notRun(probe.reason)

  let browser
  try {
    browser = await chromium.launch({ headless: true })
  } catch (error) {
    notRun(`Chromium did not start: ${error.message.split('\n')[0]}`)
  }

  const issuer = await startIssuer()
  const page0 = await startPageServer()
  const storage = await listen({ engine, port: 0, auth: { issuers: [{ issuer: issuer.origin }] }, owner: ALICE })
  const closed = await listen({ engine, port: 0, insecureNoAuth: true, cors: false })
  const listed = await listen({ engine, port: 0, insecureNoAuth: true, cors: ['https://danbri.github.io'] })
  try {
    if (storage.origin === page0.origin) throw new Error('one origin for the page and the storage')
    const token = issuer.token(`${storage.origin}/.well-known/lws-storage`, ALICE)
    const context = await browser.newContext()
    const page = await context.newPage()
    const pageErrors = []
    page.on('pageerror', (e) => pageErrors.push(String(e)))
    await page.goto(`${page0.origin}/`)

    const got = await page.evaluate(async ({ lws, token }) => {
      const out = {}
      const auth = { authorization: `Bearer ${token}` }
      try {
        const put1 = await fetch(`${lws}/notes/c.txt`, { method: 'PUT', headers: { ...auth, 'content-type': 'text/plain' }, body: 'one' })
        out.put1 = put1.status
        const get1 = await fetch(`${lws}/notes/c.txt`, { headers: auth })
        out.get1 = { status: get1.status, body: await get1.text(), etag: get1.headers.get('etag') }
        const stale = await fetch(`${lws}/notes/c.txt`, { method: 'PUT', headers: { ...auth, 'content-type': 'text/plain', 'if-match': '"stale"' }, body: 'x' })
        out.stale = stale.status
        const put2 = await fetch(`${lws}/notes/c.txt`, { method: 'PUT', headers: { ...auth, 'content-type': 'text/plain', 'if-match': out.get1.etag }, body: 'two' })
        out.put2 = { status: put2.status, etag: put2.headers.get('etag') }
        const get2 = await fetch(`${lws}/notes/c.txt`, { headers: auth })
        out.get2 = { status: get2.status, body: await get2.text() }
        const anon = await fetch(`${lws}/notes/c.txt`)
        out.anon = { status: anon.status, challenge: anon.headers.get('www-authenticate'), link: anon.headers.get('link') }
      } catch (error) {
        out.error = String(error)
      }
      return out
    }, { lws: storage.origin, token })

    record(CHECKS[0], got.error === undefined && got.put1 === 201 && got.get1 && got.get1.etag !== null,
      JSON.stringify(got))
    record(CHECKS[1], got.stale === 412 && got.put2 && got.put2.status === 204, JSON.stringify(got))
    record(CHECKS[2], got.get2 && got.get2.status === 200 && got.get2.body === 'two', JSON.stringify(got))
    record(CHECKS[3], got.anon && got.anon.status === 401 && /^Bearer /.test(got.anon.challenge || '') &&
      /lws#storage/.test(got.anon.link || ''), JSON.stringify(got.anon))

    const refused = async (lws) => page.evaluate(async (lws) => {
      try {
        const r = await fetch(`${lws}/`)
        return { status: r.status }
      } catch (error) {
        return { rejected: String(error) }
      }
    }, lws)
    const c = await refused(closed.origin)
    record(CHECKS[4], c.rejected !== undefined, JSON.stringify(c))
    const l = await refused(listed.origin)
    record(CHECKS[5], l.rejected !== undefined, JSON.stringify(l))
    if (pageErrors.length > 0) {
      failed += 1
      failures.push(`page errors: ${pageErrors.join('; ')}`)
    }
    await context.close()
  } finally {
    await browser.close()
    await storage.close()
    await closed.close()
    await listed.close()
    await page0.close()
    await issuer.close()
  }
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`lws-cors browser: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
