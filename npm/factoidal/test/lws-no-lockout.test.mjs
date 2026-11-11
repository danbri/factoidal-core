// No request leaves an LWS storage without an agent that has acl:Control on
// its root, and the offline operator recovery `factoidal lws-acl-reset`.
//
// The decisions are in Lean: formal/lean4/L4Factoidal/LWS/NoLockout.lean
// (lockout, reset; theorems accepted_keeps_control, guard_refused_unchanged,
// reset_has_control, reset_other_paths, reset_refuses) and
// NoLockoutTheorems.lean (step_keeps_root_control, lockoutGuard_refused).
// This file checks what the server and the command do with them.
//
// Run: node --test test/lws-no-lockout.test.mjs

import test from 'node:test'
import assert from 'node:assert/strict'
import { spawn, spawnSync } from 'node:child_process'
import { mkdtempSync, writeFileSync, rmSync, readdirSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { openLwsStorage } from '../lws/server.mjs'
import { createLwsClient, createDidKey } from '../lws/client.mjs'
import { loadEngine } from '../bin/engine.mjs'

const cli = join(dirname(fileURLToPath(import.meta.url)), '..', 'bin', 'factoidal.mjs')
const BASE = 'http://127.0.0.1:1/'
const OWNER = 'https://id.example/owner'
const OTHER = 'https://id.example/other'

const acl = '@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n'
const control = (who) => acl + `<#c> a acl:Authorization ; acl:agent <${who}> ;\n` +
  '  acl:accessTo <./> ; acl:default <./> ; acl:mode acl:Read, acl:Write, acl:Control .\n'
const noControl = (who) => acl + `<#rw> a acl:Authorization ; acl:agent <${who}> ;\n` +
  '  acl:accessTo <./> ; acl:default <./> ; acl:mode acl:Read, acl:Write .\n'
const enc = (s) => new TextEncoder().encode(s)
const dec = (b) => new TextDecoder().decode(b)
const req = (method, target, body = '', type = 'text/turtle') =>
  ({ method, target, headers: body === '' ? [] : [['content-type', type]], body: enc(body) })

/** A storage in DIR (files) with `rootAcl`, opened as the component principal `who`. */
async function seeded (engine, dir, rootAcl) {
  const s = await openLwsStorage({ engine, baseIri: BASE, dir, insecureNoAuth: true })
  assert.equal((await s.step(req('PUT', '/notes/a.txt', 'data a', 'text/plain'))).status, 201)
  assert.equal((await s.step(req('PUT', '/.acl', rootAcl))).status, 201)
  s.close()
}
const asPrincipal = (engine, dir, who) => openLwsStorage({ engine, baseIri: BASE, dir, principal: who })

test('a request that would leave no Control agent on the root is refused with 409 and changes nothing', async () => {
  const work = mkdtempSync(join(tmpdir(), 'lws-nolockout-'))
  const dir = join(work, 'storage')
  const engine = await loadEngine()
  try {
    await seeded(engine, dir, control(OWNER))
    const s = await asPrincipal(engine, dir, OWNER)
    try {
      // PUT /.acl without acl:Control: refused.
      const put = await s.step(req('PUT', '/.acl', noControl(OWNER)))
      assert.equal(put.status, 409)
      assert.match(dec(put.body), /no agent that has acl:Control on the storage root/)
      // DELETE /.acl: refused.
      assert.equal((await s.step(req('DELETE', '/.acl'))).status, 409)
      // PATCH /.acl that removes the mode: refused.
      const patch = await s.step({
        method: 'PATCH',
        target: '/.acl',
        headers: [['content-type', 'application/sparql-update']],
        body: enc('DELETE DATA { <http://127.0.0.1:1/.acl#c> <http://www.w3.org/ns/auth/acl#mode> <http://www.w3.org/ns/auth/acl#Control> }')
      })
      assert.ok([409, 415, 400].includes(patch.status), `PATCH: ${patch.status} ${dec(patch.body)}`)
      // Nothing changed: the root ACL is the one before.
      const got = await s.step(req('GET', '/.acl'))
      assert.equal(got.status, 200)
      assert.equal(dec(got.body), control(OWNER))
      // A write that keeps a Control agent is accepted.
      assert.equal((await s.step(req('PUT', '/.acl', control(OWNER) + '# kept\n'))).status, 204)
      // Other writes are not affected.
      assert.equal((await s.step(req('PUT', '/notes/b.txt', 'b', 'text/plain'))).status, 201)
      // A write that swaps the owner for another Control agent is accepted.
      assert.equal((await s.step(req('PUT', '/.acl', control(OTHER)))).status, 204)
      // The owner has lost control now, and OTHER has it.
      assert.equal((await s.step(req('GET', '/.acl'))).status, 403)
    } finally { s.close() }
    const t = await asPrincipal(engine, dir, OTHER)
    try {
      assert.equal(dec((await t.step(req('GET', '/.acl'))).body), control(OTHER))
      assert.equal((await t.step(req('DELETE', '/.acl'))).status, 409)
    } finally { t.close() }
  } finally { rmSync(work, { recursive: true, force: true }) }
})

test('with authorization off the guard does not apply (no behaviour change for --insecure-no-auth)', async () => {
  const work = mkdtempSync(join(tmpdir(), 'lws-nolockout-off-'))
  const dir = join(work, 'storage')
  const engine = await loadEngine()
  try {
    await seeded(engine, dir, control(OWNER))
    const s = await openLwsStorage({ engine, baseIri: BASE, dir, insecureNoAuth: true })
    try {
      assert.equal((await s.step(req('PUT', '/.acl', noControl(OWNER)))).status, 204)
      assert.equal((await s.step(req('DELETE', '/.acl'))).status, 204)
    } finally { s.close() }
  } finally { rmSync(work, { recursive: true, force: true }) }
})

test('over HTTP with a did:key agent: PUT /.acl with no Control is 409, the owner keeps control', async () => {
  const work = mkdtempSync(join(tmpdir(), 'lws-nolockout-http-'))
  const dir = join(work, 'storage')
  const engine = await loadEngine()
  const owner = await createDidKey({ engine })
  const aclFile = join(work, 'root.acl')
  writeFileSync(aclFile, control(owner.agent))
  const child = spawn(process.execPath, [cli, 'lws-serve', dir, '--authz', join(work, 'authz'), '--allow-http',
    '--root-acl', aclFile, '--storage', 'files', '--host', '127.0.0.1', '--port', '0'], { stdio: ['ignore', 'pipe', 'pipe'] })
  let out = ''
  let err = ''
  child.stderr.on('data', (b) => { err += b })
  try {
    const origin = await new Promise((resolve, reject) => {
      const timer = setTimeout(() => reject(new Error(`lws-serve did not start:\n${err}`)), 60000)
      child.stdout.on('data', (b) => {
        out += b
        const m = /^(http:\/\/127\.0\.0\.1:\d+)$/m.exec(out)
        if (m) { clearTimeout(timer); resolve(m[1]) }
      })
      child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`lws-serve exited ${code}:\n${err}`)) })
    })
    const client = await createLwsClient({ engine, selfIssued: owner.selfIssued })
    let status
    try {
      status = (await client.update(`${origin}/.acl`, { mediaType: 'text/turtle', body: noControl(owner.agent) })).status
    } catch (e) { status = e && e.detail ? e.detail.status : e }
    assert.equal(status, 409)
    const got = await client.read(`${origin}/.acl`)
    assert.equal(got.status, 200)
  } finally {
    await new Promise((resolve) => { if (child.exitCode !== null) resolve(); else { child.on('exit', resolve); child.kill('SIGTERM') } })
    rmSync(work, { recursive: true, force: true })
  }
})

const reset = (args) => spawnSync(process.execPath, [cli, 'lws-acl-reset', ...args], { encoding: 'utf8' })

test('lws-acl-reset: needs --operator, refuses a root ACL with no Control agent, replaces only /.acl', async () => {
  const work = mkdtempSync(join(tmpdir(), 'lws-acl-reset-'))
  const dir = join(work, 'storage')
  const engine = await loadEngine()
  try {
    // A storage whose root ACL gives control to nobody (made with authorization off).
    await seeded(engine, dir, noControl(OWNER))
    const good = join(work, 'good.acl')
    const bad = join(work, 'bad.acl')
    writeFileSync(good, control(OTHER))
    writeFileSync(bad, noControl(OTHER))

    const noFlag = reset([dir, good])
    assert.equal(noFlag.status, 2, noFlag.stderr)
    assert.match(noFlag.stderr, /--operator/)

    const refused = reset([dir, bad, '--operator'])
    assert.equal(refused.status, 1, refused.stderr)
    assert.match(refused.stderr, /gives no agent acl:Control on the storage root/)

    const none = reset([work, good, '--operator'])
    assert.equal(none.status, 1, none.stderr)
    assert.match(none.stderr, /holds no LWS storage/)
    assert.ok(!readdirSync(work).includes('lws-files.json'), 'nothing was made in a directory with no storage')

    const done = reset([dir, good, '--operator'])
    assert.equal(done.status, 0, done.stderr)
    assert.match(done.stderr, /the root ACL resource \(\/\.acl\) of this storage was replaced by the operator/)

    // The new controller has control; the data is as it was.
    const s = await asPrincipal(engine, dir, OTHER)
    try {
      assert.equal(dec((await s.step(req('GET', '/.acl'))).body), control(OTHER))
      const a = await s.step(req('GET', '/notes/a.txt'))
      assert.equal(a.status, 200)
      assert.equal(dec(a.body), 'data a')
    } finally { s.close() }
  } finally { rmSync(work, { recursive: true, force: true }) }
})

test('lws-acl-reset refuses while a server holds the storage directory lock', async () => {
  const work = mkdtempSync(join(tmpdir(), 'lws-acl-reset-lock-'))
  const dir = join(work, 'storage')
  const engine = await loadEngine()
  try {
    await seeded(engine, dir, control(OWNER))
    const good = join(work, 'good.acl')
    writeFileSync(good, control(OTHER))
    const held = await asPrincipal(engine, dir, OWNER)
    try {
      const r = reset([dir, good, '--operator'])
      assert.equal(r.status, 1, r.stderr)
      assert.match(r.stderr, /lws\.lock|in use|holds|running/i)
    } finally { held.close() }
    const s = await asPrincipal(engine, dir, OWNER)
    try {
      assert.equal(dec((await s.step(req('GET', '/.acl'))).body), control(OWNER), 'unchanged')
    } finally { s.close() }
  } finally { rmSync(work, { recursive: true, force: true }) }
})

test('an operator handle answers no request', async () => {
  const work = mkdtempSync(join(tmpdir(), 'lws-operator-'))
  const dir = join(work, 'storage')
  const engine = await loadEngine()
  try {
    await seeded(engine, dir, control(OWNER))
    const s = await openLwsStorage({ engine, baseIri: BASE, dir, operator: true })
    try {
      await assert.rejects(async () => s.step(req('GET', '/notes/a.txt')))
    } finally { s.close() }
  } finally { rmSync(work, { recursive: true, force: true }) }
})
