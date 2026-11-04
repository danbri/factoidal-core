// test/lws-inpage.test.mjs — one Lean LWS storage with no network
// (lws/inpage.mjs): a fetch-shaped function over a component-principal
// storage, kept as a sealed snapshot the caller holds.

import { test } from 'node:test'
import assert from 'node:assert/strict'
import { randomBytes } from 'node:crypto'
import { loadEngine } from '../bin/engine.mjs'
import { openInPageLwsStorage } from '../lws/inpage.mjs'

const BASE = 'https://pod.foafos.local/'
const SHELL = 'urn:foafos:shell'
const OTHER = 'urn:foafos:other'
const acl = (agent) => `@prefix acl: <http://www.w3.org/ns/auth/acl#> .
<#c> a acl:Authorization ; acl:agent <${agent}> ; acl:accessTo <./> ; acl:default <./> ;
  acl:mode acl:Read, acl:Write, acl:Control .
`
const CONTAINER = '<https://www.w3.org/ns/lws#Container>; rel="type"'
const engine = await loadEngine()

test('fetch writes, reads, lists and deletes; ETags and If-Match hold', async () => {
  const pod = await openInPageLwsStorage({ engine, baseIri: BASE, principal: SHELL, rootAcl: acl(SHELL) })
  try {
    const dir = await pod.fetch(BASE + 'notes/', { method: 'PUT', headers: { Link: CONTAINER, 'Content-Type': 'text/turtle' } })
    assert.ok(dir.status === 201 || dir.status === 204, `container PUT ${dir.status}`)
    const put = await pod.fetch(BASE + 'notes/a.txt', { method: 'PUT', headers: { 'Content-Type': 'text/plain' }, body: 'first' })
    assert.ok(put.status === 201 || put.status === 204, `PUT ${put.status}`)
    const got = await pod.fetch(BASE + 'notes/a.txt')
    assert.equal(got.status, 200)
    assert.equal(await got.text(), 'first')
    const etag = got.headers.get('etag')
    assert.ok(etag, 'an ETag')
    const head = await pod.fetch(BASE + 'notes/a.txt', { method: 'HEAD' })
    assert.equal(head.status, 200)
    const list = await pod.fetch(BASE + 'notes/', { headers: { Accept: 'application/lws+json' } })
    assert.equal(list.status, 200)
    const ids = ((await list.json()).items || []).map((it) => it.id)
    assert.ok(ids.includes(BASE + 'notes/a.txt'), `listed: ${ids}`)
    const stale = await pod.fetch(BASE + 'notes/a.txt', { method: 'PUT', headers: { 'Content-Type': 'text/plain', 'If-Match': '"not-it"' }, body: 'x' })
    assert.equal(stale.status, 412)
    const del = await pod.fetch(BASE + 'notes/a.txt', { method: 'DELETE', headers: { 'If-Match': etag } })
    assert.ok(del.status === 200 || del.status === 204, `DELETE ${del.status}`)
    assert.equal((await pod.fetch(BASE + 'notes/a.txt')).status, 404)
    await assert.rejects(pod.fetch('https://elsewhere.example/x'), /not in this storage/)
  } finally { pod.close() }
})

test('WAC decides: a principal the ACL does not name is refused', async () => {
  const pod = await openInPageLwsStorage({ engine, baseIri: BASE, principal: OTHER, rootAcl: acl(SHELL) })
  try {
    assert.equal((await pod.fetch(BASE + 'x.txt', { method: 'PUT', body: 'x' })).status, 403)
  } finally { pod.close() }
})

test('a sealed snapshot reopens with its key and is refused with another', async () => {
  const key = randomBytes(32).toString('hex')
  let saved = null
  const a = await openInPageLwsStorage({ engine, baseIri: BASE, principal: SHELL, rootAcl: acl(SHELL), storageKey: key, onSnapshot: (s) => { saved = s } })
  await a.fetch(BASE + 'kept.txt', { method: 'PUT', headers: { 'Content-Type': 'text/plain' }, body: 'after a reload' })
  a.close()
  assert.ok(saved, 'onSnapshot was called')
  assert.ok(!JSON.stringify(saved).includes('after a reload'), 'the snapshot is sealed')
  const b = await openInPageLwsStorage({ engine, baseIri: BASE, principal: SHELL, storageKey: key, snapshot: saved })
  try {
    assert.equal(await (await b.fetch(BASE + 'kept.txt')).text(), 'after a reload')
  } finally { b.close() }
  await assert.rejects(openInPageLwsStorage({ engine, baseIri: BASE, principal: SHELL, storageKey: randomBytes(32).toString('hex'), snapshot: saved }))
})
