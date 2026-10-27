// `factoidal lws-serve DIR --authz ASDIR`: the storage and an authorization
// server whose issuer is the storage root, on one port
// (formal/lean4/L4Factoidal/Authz/Mount.lean).
//
//   node tests/authz/mounted.mjs
//
// Two deployments, each driven through the whole lws10-core "Authorization"
// flow (401, protected resource metadata, RFC 8414 metadata, token exchange
// with a did:key credential, the request with the token):
//
// 1. the server at an origin, base "http://127.0.0.1:P/";
// 2. the server behind a reverse proxy that serves it at /targets/f/ and
//    removes that prefix, as the router of Touchstone's targetservers does in
//    its "strip" mode. The proxy in this file is that router's rules, written
//    for the test: /targets/f/X to /X, /.well-known/lws-configuration/targets/f
//    to /.well-known/lws-configuration, and
//    /.well-known/oauth-protected-resource/targets/f/X to
//    /.well-known/oauth-protected-resource/X.
//
// Score line: "N pass, M fail, X xfail, S skipped (out of T)".

import { spawn } from 'node:child_process'
import http from 'node:http'
import { mkdtempSync, rmSync } from 'node:fs'
import { createServer } from 'node:net'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { TOKEN_EXCHANGE, JWT_TYPE, keyPair, didKeyOf, selfIssued, exchangeForm, postForm } from './fixtures.mjs'

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

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

const CLI = fileURLToPath(new URL('../../npm/factoidal/bin/factoidal.mjs', import.meta.url))

function freePort () {
  return new Promise((resolve) => {
    const s = createServer().listen(0, '127.0.0.1', () => { const p = s.address().port; s.close(() => resolve(p)) })
  })
}

function start (args) {
  const child = spawn(process.execPath, [CLI, ...args], { stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, FACTOIDAL_LWS_KEY: '' } })
  return new Promise((resolve, reject) => {
    let out = ''
    let errText = ''
    const timer = setTimeout(() => reject(new Error(`no origin printed: ${out} ${errText}`)), 60000)
    child.stdout.on('data', (c) => {
      out += c
      const m = /(http:\/\/[^\s]+)/.exec(out)
      if (m) { clearTimeout(timer); resolve({ child, origin: m[1] }) }
    })
    child.stderr.on('data', (c) => { errText += c })
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`exited ${code}: ${out} ${errText}`)) })
  })
}

async function stop (proc) {
  if (proc === null) return
  proc.child.kill('SIGTERM')
  await new Promise((resolve) => proc.child.on('close', resolve))
}

/** The strip-mode router rules of Touchstone's targetservers, for one target. */
function stripProxy (prefix, upstreamPort) {
  const server = http.createServer((req, res) => {
    let path = req.url
    const conf = '/.well-known/lws-configuration'
    const prm = '/.well-known/oauth-protected-resource'
    if (path === conf + prefix) path = conf
    else if (path.startsWith(prm + prefix + '/') || path === prm + prefix) path = prm + (path.slice((prm + prefix).length) || '/')
    else if (path.startsWith(prefix + '/')) path = path.slice(prefix.length)
    else { res.writeHead(404); res.end(); return }
    const up = http.request({ host: '127.0.0.1', port: upstreamPort, method: req.method, path, headers: req.headers }, (r) => {
      res.writeHead(r.statusCode, r.rawHeaders)
      r.pipe(res)
    })
    up.on('error', (e) => { res.writeHead(502); res.end(e.message) })
    req.pipe(up)
  })
  return new Promise((resolve) => server.listen(0, '127.0.0.1', () => resolve(server)))
}

/** The whole client flow against a storage root `base`. */
async function flow (label, base, agent, did) {
  const storageIri = `${base}.well-known/lws-storage`
  let meta = null
  let token = null
  await check(`${label}: 401 names the protected resource metadata; it names the issuer, which is the storage root`, async () => {
    const r = await fetch(`${base}private.txt`)
    assert(r.status === 401, `status ${r.status}`)
    const m = /resource_metadata="([^"]+)"/.exec(r.headers.get('www-authenticate') || '')
    assert(m !== null, 'no resource_metadata')
    const prmR = await fetch(m[1])
    assert(prmR.status === 200, `metadata ${prmR.status} at ${m[1]}`)
    const prm = await prmR.json()
    assert(prm.resource === `${base}private.txt`, `resource ${prm.resource}`)
    const issuer = base.replace(/\/$/, '')
    assert(prm.authorization_servers.includes(issuer), `authorization_servers ${JSON.stringify(prm.authorization_servers)}`)
    // RFC 8414 §3.1: the well-known segment between the host and the issuer's path.
    const u = new URL(issuer)
    const metaR = await fetch(`${u.origin}/.well-known/lws-configuration${u.pathname === '/' ? '' : u.pathname}`)
    assert(metaR.status === 200, `AS metadata ${metaR.status}`)
    meta = await metaR.json()
    assert(meta.issuer === issuer, `issuer ${meta.issuer}`)
    assert(meta.token_endpoint === `${base}.well-known/lws-token`, `token_endpoint ${meta.token_endpoint}`)
    assert(meta.jwks_uri === `${base}.well-known/lws-jwks`, `jwks_uri ${meta.jwks_uri}`)
  })
  await check(`${label}: token exchange at the advertised endpoint; the owner writes and reads`, async () => {
    assert(meta !== null, 'no metadata')
    const a = await postForm(meta.token_endpoint, exchangeForm({
      grant_type: TOKEN_EXCHANGE, resource: storageIri, subject_token_type: JWT_TYPE,
      subject_token: selfIssued(did, agent, { kid: did.slice(8), audience: meta.issuer })
    }))
    assert(a.status === 200, `${a.status} ${a.text}`)
    token = a.json.access_token
    const put = await fetch(`${base}private.txt`, { method: 'PUT', headers: { authorization: `Bearer ${token}`, 'content-type': 'text/plain' }, body: 'hello' })
    assert(put.status === 201, `PUT ${put.status}`)
    const get = await fetch(`${base}private.txt`, { headers: { authorization: `Bearer ${token}` } })
    assert(get.status === 200 && (await get.text()) === 'hello', `GET ${get.status}`)
  })
  await check(`${label}: the JWK Set is served; /token and /jwks are storage resources`, async () => {
    assert(token !== null, 'no token')
    const jwks = await (await fetch(meta.jwks_uri)).json()
    assert(Array.isArray(jwks.keys) && jwks.keys.length >= 1 && jwks.keys.every((k) => k.d === undefined), 'bad JWK Set')
    for (const name of ['token', 'jwks']) {
      const put = await fetch(`${base}${name}`, { method: 'PUT', headers: { authorization: `Bearer ${token}`, 'content-type': 'text/plain' }, body: name })
      assert(put.status === 201, `PUT /${name} ${put.status}`)
      const get = await fetch(`${base}${name}`, { headers: { authorization: `Bearer ${token}` } })
      assert(get.status === 200 && (await get.text()) === name, `GET /${name} ${get.status}`)
    }
  })
}

async function main () {
  const dir = mkdtempSync(join(process.env.AUTHZ_TEST_TMP || tmpdir(), 'factoidal-authz-mounted-'))
  const agent = keyPair('ES256')
  const did = didKeyOf(agent)
  let direct = null
  let behind = null
  let proxy = null
  try {
    try {
      direct = await start(['lws-serve', join(dir, 'a'), '--port', '0', '--authz', join(dir, 'a-as'), '--owner', did, '--quiet'])
    } catch (error) {
      if (/unknown op|not wired|exit(ed)? 3|authzOwns/.test(String(error.message))) {
        skipped += 1
        console.log(`  skip  every check - the wasm module carries no authzOwns op: ${error.message}`)
        return
      }
      throw error
    }
    await flow('at an origin', `${direct.origin}/`, agent, did)

    const port = await freePort()
    proxy = await stripProxy('/targets/f', port)
    const publicBase = `http://127.0.0.1:${proxy.address().port}/targets/f/`
    behind = await start(['lws-serve', join(dir, 'b'), '--port', String(port), '--base', publicBase,
      '--authz', join(dir, 'b-as'), '--owner', did, '--quiet'])
    await flow('behind a proxy that removes /targets/f', publicBase, agent, did)
  } finally {
    await stop(direct)
    await stop(behind)
    if (proxy !== null) await new Promise((resolve) => proxy.close(resolve))
    rmSync(dir, { recursive: true, force: true })
  }
}

await main()
console.log(`authz mounted: ${passed} pass, ${failed} fail, 0 xfail, ${skipped} skipped (out of ${passed + failed + skipped})`)
for (const f of failures) console.log(`  ${f}`)
process.exit(failed === 0 ? 0 : 1)
