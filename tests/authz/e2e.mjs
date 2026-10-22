// End-to-end test: `factoidal authz-serve` issues an access token and
// `factoidal lws-serve --issuer <it>` accepts it
// (https://github.com/danbri/factoidal/issues/916).
//
//   node tests/authz/e2e.mjs
//
// Three CLI processes and a client in this file. The client does what
// lws10-core "Authorization" describes: an unauthorized request, the 401's
// resource_metadata and storage Link, the protected resource metadata, the
// authorization server metadata, token exchange with a did:key credential
// (lws10-authn-ssi-cid), then the request with the Bearer token.
//
// solid-serve does not accept these tokens yet (Solid-OIDC expects a
// DPoP-bound token with aud "solid"): an expected failure naming
// https://github.com/danbri/factoidal/issues/928.
//
// Score line: "N pass, M fail, X xfail, S skipped (out of T)".

import { spawn } from 'node:child_process'
import { mkdtempSync, rmSync } from 'node:fs'
import { createServer } from 'node:net'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { TOKEN_EXCHANGE, JWT_TYPE, keyPair, didKeyOf, selfIssued, exchangeForm, postForm } from './fixtures.mjs'

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

function assert (condition, message) {
  if (!condition) throw new Error(message)
}

const CLI = fileURLToPath(new URL('../../npm/factoidal/bin/factoidal.mjs', import.meta.url))

function freePort () {
  return new Promise((resolve) => {
    const s = createServer().listen(0, '127.0.0.1', () => { const p = s.address().port; s.close(() => resolve(p)) })
  })
}

/** Start a CLI server and wait for the origin it prints. */
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

function run (args) {
  return new Promise((resolve) => {
    const child = spawn(process.execPath, [CLI, ...args], { stdio: ['ignore', 'pipe', 'pipe'], env: { ...process.env, FACTOIDAL_LWS_KEY: '' } })
    let out = ''
    let errText = ''
    child.stdout.on('data', (c) => { out += c })
    child.stderr.on('data', (c) => { errText += c })
    child.on('close', (code) => resolve({ code, out, err: errText }))
  })
}

async function stop (proc) {
  if (proc === null) return
  proc.child.kill('SIGTERM')
  await new Promise((resolve) => proc.child.on('close', resolve))
}

async function main () {
  const base = mkdtempSync(join(process.env.AUTHZ_TEST_TMP || tmpdir(), 'factoidal-authz-e2e-'))
  const lwsPort = await freePort()
  const solidPort = await freePort()
  const lwsBase = `http://127.0.0.1:${lwsPort}/`
  const storageIri = `${lwsBase}.well-known/lws-storage`
  const solidBase = `http://127.0.0.1:${solidPort}/`
  const agent = keyPair('ES256')
  const did = didKeyOf(agent)
  let authz = null
  let lws = null
  let solid = null
  try {
    try {
      authz = await start(['authz-serve', join(base, 'authz'), '--port', '0', '--resource', `${storageIri},${solidBase}`, '--quiet'])
    } catch (error) {
      if (/unknown op|not wired|exit(ed)? 3/.test(String(error.message))) {
        skipped += 1
        console.log(`  skip  every check - the wasm module carries no authz ops: ${error.message}`)
        return
      }
      throw error
    }
    lws = await start(['lws-serve', join(base, 'lws'), '--port', String(lwsPort), '--issuer', authz.origin, '--owner', did, '--quiet'])

    let token = null
    await check('Discovery: the storage answers 401 naming its protected resource metadata and storage; the metadata names authz-serve', async () => {
      const r = await fetch(lwsBase)
      assert(r.status === 401, `status ${r.status}`)
      const challenge = r.headers.get('www-authenticate') || ''
      const m = /resource_metadata="([^"]+)"/.exec(challenge)
      assert(m !== null, `challenge ${challenge}`)
      assert((r.headers.get('link') || '').indexOf(`<${storageIri}>`) >= 0, `link ${r.headers.get('link')}`)
      const prm = await (await fetch(m[1])).json()
      assert(prm.authorization_servers.includes(authz.origin), `authorization_servers ${JSON.stringify(prm.authorization_servers)}`)
    })
    await check('Token Exchange: authz-serve issues a token for the storage to a did:key agent', async () => {
      const meta = await (await fetch(`${authz.origin}/.well-known/lws-configuration`)).json()
      const a = await postForm(meta.token_endpoint, exchangeForm({
        grant_type: TOKEN_EXCHANGE, resource: storageIri, subject_token_type: JWT_TYPE,
        subject_token: selfIssued(did, agent, { kid: did.slice(8), audience: meta.issuer })
      }))
      assert(a.status === 200, `${a.status} ${a.text}`)
      token = a.json.access_token
    })
    await check('Validation: lws-serve accepts the token: the owner writes and reads', async () => {
      assert(token !== null, 'no token')
      const put = await fetch(`${lwsBase}e2e.txt`, { method: 'PUT', headers: { authorization: `Bearer ${token}`, 'content-type': 'text/plain' }, body: 'hello' })
      assert(put.status >= 200 && put.status < 300, `PUT ${put.status}`)
      const get = await fetch(`${lwsBase}e2e.txt`, { headers: { authorization: `Bearer ${token}` } })
      assert(get.status === 200 && (await get.text()) === 'hello', `GET ${get.status}`)
    })
    await check('Validation: a token for another resource is refused with 401 invalid_token', async () => {
      const a = await postForm(`${authz.origin}/token`, exchangeForm({
        grant_type: TOKEN_EXCHANGE, resource: solidBase, subject_token_type: JWT_TYPE,
        subject_token: selfIssued(did, agent, { kid: did.slice(8), audience: authz.origin })
      }))
      assert(a.status === 200, `exchange ${a.status}`)
      const r = await fetch(`${lwsBase}e2e.txt`, { headers: { authorization: `Bearer ${a.json.access_token}` } })
      assert(r.status === 401 && /invalid_token/.test(r.headers.get('www-authenticate') || ''), `status ${r.status}`)
    })
    await check('Validation: a changed token is refused with 401', async () => {
      const [h, , s] = token.split('.')
      const claims = JSON.parse(Buffer.from(token.split('.')[1], 'base64url').toString('utf8'))
      const forged = `${h}.${Buffer.from(JSON.stringify({ ...claims, sub: 'https://mallory.example/' })).toString('base64url')}.${s}`
      const r = await fetch(`${lwsBase}e2e.txt`, { headers: { authorization: `Bearer ${forged}` } })
      assert(r.status === 401, `status ${r.status}`)
    })
    await check('CLI: factoidal authz-keys prints the published JWK Set; --private adds d', async () => {
      const pub = await run(['authz-keys', join(base, 'authz')])
      assert(pub.code === 0, `exit ${pub.code} ${pub.err}`)
      const served = await (await fetch(`${authz.origin}/jwks`)).json()
      const printed = JSON.parse(pub.out)
      assert(JSON.stringify(printed.keys.map((k) => k.kid)) === JSON.stringify(served.keys.map((k) => k.kid)), 'kids differ')
      assert(printed.keys.every((k) => k.d === undefined), 'a private member in the public set')
      const priv = await run(['authz-keys', join(base, 'authz'), '--private'])
      assert(priv.code === 0 && JSON.parse(priv.out).keys.every((k) => typeof k.d === 'string'), 'no d in --private')
    })
    await check('CLI: authz-serve with no --resource refuses to start', async () => {
      const r = await run(['authz-serve', join(base, 'authz-none'), '--port', '0'])
      assert(r.code === 2, `exit ${r.code}`)
    })

    solid = await start(['solid-serve', join(base, 'solid'), '--port', String(solidPort), '--issuer', authz.origin, '--owner', did, '--quiet'])
    await xfail('solid-serve accepts an access token issued by authz-serve', 'https://github.com/danbri/factoidal/issues/928', async () => {
      const a = await postForm(`${authz.origin}/token`, exchangeForm({
        grant_type: TOKEN_EXCHANGE, resource: solidBase, subject_token_type: JWT_TYPE,
        subject_token: selfIssued(did, agent, { kid: did.slice(8), audience: authz.origin })
      }))
      assert(a.status === 200, `exchange ${a.status}`)
      const put = await fetch(`${solidBase}e2e.txt`, { method: 'PUT', headers: { authorization: `Bearer ${a.json.access_token}`, 'content-type': 'text/plain' }, body: 'hello' })
      assert(put.status >= 200 && put.status < 300, `PUT ${put.status}`)
    })
  } finally {
    await stop(solid)
    await stop(lws)
    await stop(authz)
    rmSync(base, { recursive: true, force: true })
  }
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + xfailed + skipped
console.log(`authz-e2e node: ${passed} pass, ${failed} fail, ${xfailed} xfail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
