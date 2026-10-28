// Browser reach to listeners without authentication
// (https://github.com/danbri/factoidal/issues/1124; row C7 and invariant I7
// of docs/designissues/2026-10-28-feature-combination-safety.md).
//
// Every decision is made in Lean (formal/lean4/L4Factoidal/HTTP/LocalGuard.lean,
// L4Factoidal/LWS/Cors.lean `policyFor`); this file sends requests with the
// Host and Origin fields a browser would send and reads the answers.
//
// Run: node --test test/local-guard-1124.test.mjs

import test from 'node:test'
import assert from 'node:assert/strict'
import http from 'node:http'
import { mkdtempSync, mkdirSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { execFileSync } from 'node:child_process'
import { serveStore } from '../index.mjs'
import { listen as lwsListen, openLwsStorage } from '../lws/server.mjs'
import { listen as webdavListen } from '../webdav/server.mjs'
import { listen as solidListen } from '../solid/server/index.mjs'

const ISSUE = 'https://github.com/danbri/factoidal/issues/1124'
const EVIL = 'https://evil.example'
const cli = join(dirname(fileURLToPath(import.meta.url)), '..', 'bin', 'factoidal.mjs')

/** One request with node:http, so that Host and Origin are sent as given. */
function raw (origin, method, path, headers = {}, body = null) {
  return new Promise((resolve, reject) => {
    const url = new URL(path, origin)
    const req = http.request({ host: url.hostname, port: url.port, path: url.pathname + url.search, method, headers }, (res) => {
      const chunks = []
      res.on('data', (c) => chunks.push(c))
      res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, body: Buffer.concat(chunks).toString('utf8') }))
      res.on('error', reject)
    })
    req.on('error', reject)
    if (body !== null) req.write(body)
    req.end()
  })
}

function xfail (name, issueUrl, fn) {
  test(`xfail: ${name} (${issueUrl})`, async (t) => {
    let failed = false
    try { await fn(t) } catch (error) { failed = true; t.diagnostic(`expected failure: ${String(error.message).slice(0, 160)}`) }
    assert.ok(failed, `unexpected pass: ${name} now works - flip this xfail to an assertion and close ${issueUrl}`)
  })
}

const hostOf = (origin) => new URL(origin).host

// ------------------------------------------------------------- lws-serve

test('lws-serve --insecure-no-auth: a foreign Origin gets no Access-Control-Allow-Origin', async () => {
  const s = await lwsListen({ port: 0, insecureNoAuth: true })
  try {
    const get = await raw(s.origin, 'GET', '/', { origin: EVIL })
    assert.equal(get.status, 200)
    assert.equal(get.headers['access-control-allow-origin'], undefined)
    const pre = await raw(s.origin, 'OPTIONS', '/', { origin: EVIL, 'access-control-request-method': 'PUT' })
    assert.equal(pre.headers['access-control-allow-origin'], undefined)
  } finally { await s.close() }
})

test('lws-serve --insecure-no-auth: a write from a foreign Origin is 403 and changes nothing; Host evil.example is 421', async () => {
  const s = await lwsListen({ port: 0, insecureNoAuth: true })
  try {
    const put = await raw(s.origin, 'PUT', '/a.txt', { origin: EVIL, 'content-type': 'text/plain' }, 'x')
    assert.equal(put.status, 403)
    assert.match(put.body, /1124/)
    assert.equal((await raw(s.origin, 'GET', '/a.txt')).status, 404)
    const rebound = await raw(s.origin, 'GET', '/', { host: `evil.example:${s.port}` })
    assert.equal(rebound.status, 421)
  } finally { await s.close() }
})

test('lws-serve --insecure-no-auth: curl-style and same-origin requests still work', async () => {
  const s = await lwsListen({ port: 0, insecureNoAuth: true })
  try {
    assert.equal((await raw(s.origin, 'PUT', '/a.txt', { 'content-type': 'text/plain' }, 'one')).status, 201)
    const same = await raw(s.origin, 'PUT', '/b.txt', { origin: s.origin, 'content-type': 'text/plain' }, 'two')
    assert.equal(same.status, 201)
    const local = await raw(s.origin, 'GET', '/a.txt', { host: `localhost:${s.port}` })
    assert.equal(local.status, 200)
    assert.equal(local.body, 'one')
  } finally { await s.close() }
})

test('lws-serve --insecure-no-auth: --allow-host, --allow-origin and --cors-origin are honoured', async () => {
  const page = 'https://app.example'
  const s = await lwsListen({ port: 0, insecureNoAuth: true, allowHosts: ['box.tail1234.ts.net'], cors: [page] })
  try {
    const viaProxy = await raw(s.origin, 'GET', '/', { host: 'box.tail1234.ts.net' })
    assert.equal(viaProxy.status, 200)
    const listed = await raw(s.origin, 'PUT', '/c.txt', { origin: page, 'content-type': 'text/plain' }, 'c')
    assert.equal(listed.status, 201)
    assert.equal(listed.headers['access-control-allow-origin'], page)
  } finally { await s.close() }
  const t = await lwsListen({ port: 0, insecureNoAuth: true, allowOrigins: [page] })
  try {
    const w = await raw(t.origin, 'PUT', '/d.txt', { origin: page, 'content-type': 'text/plain' }, 'd')
    assert.equal(w.status, 201)
    assert.equal(w.headers['access-control-allow-origin'], undefined)
  } finally { await t.close() }
})

test('lws: cors true (echo) with insecureNoAuth is refused at open; allowHosts under authorization is refused', async () => {
  await assert.rejects(openLwsStorage({ insecureNoAuth: true, cors: true, storageKey: null }), /1124|cors/)
  await assert.rejects(openLwsStorage({ auth: { issuers: [] }, allowHosts: ['a.example'], storageKey: null }), /allowHosts/)
  await assert.rejects(openLwsStorage({ insecureNoAuth: true, allowHosts: ['proxy.example:8080'], storageKey: null }), /allowHosts/)
})

test('lws-serve CLI: --insecure-no-auth prints why no CORS is sent', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'guard1124-lws-'))
  const { spawn } = await import('node:child_process')
  const child = spawn(process.execPath, [cli, 'lws-serve', dir, '--insecure-no-auth', '--port', '0'], { stdio: ['ignore', 'pipe', 'pipe'] })
  try {
    const errText = await new Promise((resolve, reject) => {
      let text = ''
      child.stderr.on('data', (d) => { text += d; if (/no CORS fields are sent/.test(text)) resolve(text) })
      child.on('exit', (code) => reject(new Error(`exited ${code}: ${text}`)))
    })
    assert.match(errText, /1124/)
  } finally { child.kill() }
})

// ---------------------------------------------------------- webdav-serve

test('webdav-serve without --users: Host evil.example is 421; a foreign-origin write is 403; PROPFIND works', async () => {
  const conf = mkdtempSync(join(tmpdir(), 'guard1124-dav-'))
  mkdirSync(join(conf, 'store'))
  writeFileSync(join(conf, 'notes.md'), '# Notes\n- kind: local\n- path: ./store\n')
  const s = await webdavListen({ configDir: conf, port: 0, onError: () => {} })
  try {
    const rebound = await raw(s.origin, 'PROPFIND', '/', { host: `evil.example:${s.port}`, depth: '1' })
    assert.equal(rebound.status, 421)
    const form = await raw(s.origin, 'PUT', '/notes/a.txt', { origin: EVIL, 'content-type': 'text/plain' }, 'x')
    assert.equal(form.status, 403)
    const list = await raw(s.origin, 'PROPFIND', '/', { depth: '1' })
    assert.equal(list.status, 207)
    const put = await raw(s.origin, 'PUT', '/notes/a.txt', { 'content-type': 'text/plain' }, 'hello')
    assert.ok(put.status === 201 || put.status === 204, `PUT ${put.status}`)
    const get = await raw(s.origin, 'GET', '/notes/a.txt', { host: `localhost:${s.port}` })
    assert.equal(get.body, 'hello')
  } finally { await s.close() }
})

test('webdav-serve: --allow-host adds a name', async () => {
  const conf = mkdtempSync(join(tmpdir(), 'guard1124-dav2-'))
  mkdirSync(join(conf, 'store'))
  writeFileSync(join(conf, 'notes.md'), '# Notes\n- kind: local\n- path: ./store\n')
  const s = await webdavListen({ configDir: conf, port: 0, allowHosts: ['nas.example'], onError: () => {} })
  try {
    const r = await raw(s.origin, 'PROPFIND', '/', { host: 'nas.example', depth: '0' })
    assert.equal(r.status, 207)
  } finally { await s.close() }
})

// --------------------------------------------------------- factoidal serve

const COUNT = 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }'

async function count (origin) {
  const r = await raw(origin, 'GET', `/sparql?query=${encodeURIComponent(COUNT)}`, { accept: 'application/sparql-results+json' })
  assert.equal(r.status, 200)
  return Number(JSON.parse(r.body).results.bindings[0].c.value)
}

test('factoidal serve: a urlencoded update POST with a foreign Origin is 403 and the store does not change', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'guard1124-serve-'))
  writeFileSync(join(dir, 'd.ttl'), '<http://ex/a> <http://ex/p> 1 .\n')
  const st = join(dir, 'st')
  execFileSync(process.execPath, [cli, 'pack', join(dir, 'd.ttl'), join(st, 'gen-1'), '--layout', 'ibk5', '--quiet'])
  execFileSync(process.execPath, [cli, 'activate', st, 'gen-1', '--quiet'])
  const s = await serveStore(st)
  const origin = new URL(s.url).origin
  try {
    assert.equal(await count(origin), 1)
    const form = 'update=' + encodeURIComponent('DROP ALL')
    const cross = await raw(origin, 'POST', '/sparql',
      { origin: EVIL, 'content-type': 'application/x-www-form-urlencoded' }, form)
    assert.equal(cross.status, 403)
    assert.equal(await count(origin), 1)
    const rebound = await raw(origin, 'GET', `/sparql?query=${encodeURIComponent(COUNT)}`,
      { host: `evil.example:${new URL(origin).port}` })
    assert.equal(rebound.status, 421)
    // curl, and a page of the endpoint itself.
    const ins = 'update=' + encodeURIComponent('INSERT DATA { <http://ex/b> <http://ex/p> 2 }')
    const plain = await raw(origin, 'POST', '/sparql', { 'content-type': 'application/x-www-form-urlencoded' }, ins)
    assert.ok(plain.status >= 200 && plain.status < 300, `update ${plain.status}`)
    assert.equal(await count(origin), 2)
    const same = await raw(origin, 'POST', '/sparql',
      { origin, 'content-type': 'application/x-www-form-urlencoded' }, form)
    assert.ok(same.status >= 200 && same.status < 300, `same-origin update ${same.status}`)
    assert.equal(await count(origin), 0)
  } finally { await s.close() }
})

// ----------------------------------------------------------- solid-serve

test('solid-serve --insecure-no-auth: Host evil.example is 421; a foreign-origin write is 403', async () => {
  const s = await solidListen({ port: 0, insecureNoAuth: true })
  try {
    assert.equal((await raw(s.origin, 'GET', '/', { host: `evil.example:${s.port}` })).status, 421)
    const put = await raw(s.origin, 'PUT', '/a.txt', { origin: EVIL, 'content-type': 'text/plain' }, 'x')
    assert.equal(put.status, 403)
    const ok = await raw(s.origin, 'PUT', '/a.txt', { 'content-type': 'text/plain', host: hostOf(s.origin) }, 'x')
    assert.ok(ok.status === 201 || ok.status === 204, `PUT ${ok.status}`)
  } finally { await s.close() }
})

// Solid Protocol section 8.1 requires the echo, so a page on another origin
// can still READ a solid-serve --insecure-no-auth storage. Writes are refused
// above; reads stay open until the Solid server takes a CORS policy.
xfail('solid-serve --insecure-no-auth: a foreign Origin gets no Access-Control-Allow-Origin', ISSUE, async () => {
  const s = await solidListen({ port: 0, insecureNoAuth: true })
  try {
    const get = await raw(s.origin, 'GET', '/', { origin: EVIL })
    assert.equal(get.headers['access-control-allow-origin'], undefined)
  } finally { await s.close() }
})

// Invariant I7: no CORS profile sends Access-Control-Allow-Credentials: true
// with an echoed origin. The LWS and authorization server profiles are
// proved (LWS.Cors.decorate_no_credentials); the Solid profile
// (L4Factoidal/Solid/Server/Cors.lean) still sends it.
xfail('solid-serve sends no Access-Control-Allow-Credentials with an echoed Origin', ISSUE, async () => {
  const s = await solidListen({ port: 0, insecureNoAuth: true })
  try {
    const get = await raw(s.origin, 'GET', '/', { origin: EVIL })
    assert.equal(get.headers['access-control-allow-credentials'], undefined)
  } finally { await s.close() }
})
