// test/lws-principal.test.mjs — a component principal (issue 1238): a storage a component
// opens in-process, with no token, where every request is the component's and Web Access
// Control still decides it (L4Factoidal/LWS/Authorization.lean, decide_principal_agents).

import { test } from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { randomBytes } from 'node:crypto'

const { openLwsStorage, createLwsServer } = await import('../lws/server.mjs')
const BASE = 'https://xmpp-state.invalid/'
const XMPP = 'urn:factoidal:component:xmpp-serve'
const OTHER = 'urn:factoidal:component:something-else'
// Relative references (`<#c>`, `<./>`) as Solid clients write them: an ACL document is parsed
// with its own IRI as the base (https://github.com/danbri/factoidal/issues/1241, fixed).
const acl = (agent) => `@prefix acl: <http://www.w3.org/ns/auth/acl#> .
<#c> a acl:Authorization ; acl:agent <${agent}> ; acl:accessTo <./> ; acl:default <./> ;
  acl:mode acl:Read, acl:Write, acl:Control .
`
const text = (s) => new TextEncoder().encode(s)

async function open (principal, grantee, dir = null) {
  return openLwsStorage({ baseIri: BASE, principal, rootAcl: acl(grantee), realClock: true,
    ...(dir ? { dir, storage: 'files', storageKey: randomBytes(32).toString('hex') } : {}) })
}

test('the principal writes and reads where WAC grants it', async () => {
  const s = await open(XMPP, XMPP)
  try {
    const put = await s.step({ method: 'PUT', target: '/xmpp/state.txt', headers: [['Content-Type', 'text/plain']], body: text('kept') })
    assert.ok(put.status === 201 || put.status === 204, `PUT ${put.status}`)
    const got = await s.step({ method: 'GET', target: '/xmpp/state.txt', headers: [], body: new Uint8Array(0) })
    assert.equal(got.status, 200)
    assert.equal(new TextDecoder().decode(got.body), 'kept')
  } finally { s.close() }
})

test('WAC still decides: a principal the ACL does not name is refused', async () => {
  const s = await open(XMPP, OTHER)
  try {
    const put = await s.step({ method: 'PUT', target: '/xmpp/state.txt', headers: [['Content-Type', 'text/plain']], body: text('x') })
    assert.equal(put.status, 403)
    const got = await s.step({ method: 'GET', target: '/', headers: [], body: new Uint8Array(0) })
    assert.equal(got.status, 403)
  } finally { s.close() }
})

test('a token in the request changes nothing: the agent is the principal', async () => {
  const s = await open(XMPP, OTHER)
  try {
    // A bearer token claiming to be OTHER: no issuer is trusted, and the principal decides.
    const put = await s.step({ method: 'PUT', target: '/xmpp/state.txt',
      headers: [['Content-Type', 'text/plain'], ['Authorization', 'Bearer eyJhbGciOiJub25lIn0.eyJzdWIiOiJ1cm46ZmFjdG9pZGFsOmNvbXBvbmVudDpzb21ldGhpbmctZWxzZSJ9.']],
      body: text('x') })
    assert.equal(put.status, 403)
  } finally { s.close() }
})

test('the HTTP listener refuses a principal storage', async () => {
  await assert.rejects(createLwsServer({ baseIri: BASE, principal: XMPP }), /in-process only/)
})

test('principal is exclusive with insecureNoAuth', async () => {
  await assert.rejects(openLwsStorage({ baseIri: BASE, principal: XMPP, insecureNoAuth: true }), /exclusive/)
})

test('a principal storage in files, sealed, survives a reopen', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'lws-principal-'))
  const key = randomBytes(32).toString('hex')
  try {
    const a = await openLwsStorage({ baseIri: BASE, principal: XMPP, rootAcl: acl(XMPP), realClock: true, dir, storage: 'files', storageKey: key })
    await a.step({ method: 'PUT', target: '/xmpp/state.txt', headers: [['Content-Type', 'text/plain']], body: text('after a restart') })
    a.close()
    const b = await openLwsStorage({ baseIri: BASE, principal: XMPP, realClock: true, dir, storage: 'files', storageKey: key })
    const got = await b.step({ method: 'GET', target: '/xmpp/state.txt', headers: [], body: new Uint8Array(0) })
    assert.equal(new TextDecoder().decode(got.body), 'after a restart')
    b.close()
    // The wrong key refuses to open; it does not start empty.
    await assert.rejects(openLwsStorage({ baseIri: BASE, principal: XMPP, realClock: true, dir, storage: 'files',
      storageKey: randomBytes(32).toString('hex') }))
  } finally { rmSync(dir, { recursive: true, force: true }) }
})
