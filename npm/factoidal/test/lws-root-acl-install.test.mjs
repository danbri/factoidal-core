// The first root ACL of an EXISTING storage, installed at start with
// authorization on: no window with authorization off.
//
// A storage made with `lws-serve --insecure-no-auth` has no root ACL (/.acl).
// Started later with `--authz DIR --root-acl FILE`, it gets FILE as /.acl
// before the first request is answered; an existing /.acl is kept. The
// decision is in Lean (formal/lean4/L4Factoidal/LWS/RootAclInstall.lean,
// theorems install_only_when_absent, install_keeps_existing,
// install_has_root_acl, install_other_paths); this file checks what the
// command does with it.
//
// Run: node --test test/lws-root-acl-install.test.mjs

import test from 'node:test'
import assert from 'node:assert/strict'
import { spawn } from 'node:child_process'
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join, dirname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { openLwsStorage } from '../lws/server.mjs'
import { createLwsClient, createDidKey } from '../lws/client.mjs'
import { loadEngine } from '../bin/engine.mjs'

const cli = join(dirname(fileURLToPath(import.meta.url)), '..', 'bin', 'factoidal.mjs')
const INSTALLED = /root ACL: this storage had no root ACL resource/
const KEPT = /root ACL: this storage has a root ACL resource \(\/\.acl\); it is kept/

/** Start `factoidal lws-serve` with `args`; resolve with its origin and its output so far. */
function serve (args) {
  const child = spawn(process.execPath, [cli, 'lws-serve', ...args, '--host', '127.0.0.1', '--port', '0'],
    { stdio: ['ignore', 'pipe', 'pipe'] })
  let out = ''
  let err = ''
  const ready = new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error(`lws-serve did not start:\n${err}`)), 60000)
    child.stdout.on('data', (b) => {
      out += b
      const m = /^(http:\/\/127\.0\.0\.1:\d+)$/m.exec(out)
      if (m) { clearTimeout(timer); resolve(m[1]) }
    })
    child.stderr.on('data', (b) => { err += b })
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`lws-serve exited ${code}:\n${err}`)) })
  })
  return {
    ready,
    stderr: () => err,
    stop: () => new Promise((resolve) => {
      if (child.exitCode !== null) return resolve()
      child.on('exit', resolve)
      child.kill('SIGTERM')
    })
  }
}

const ownerAcl = (did) => '@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n' +
  `<#owner> a acl:Authorization ;\n  acl:agent <${did}> ;\n  acl:accessTo <./> ; acl:default <./> ;\n` +
  '  acl:mode acl:Read, acl:Write, acl:Control .\n'

const asAgent = (engine, made) => createLwsClient({ engine, selfIssued: made.selfIssued })
const statusOf = async (p) => { try { const r = await p; return r.status } catch (e) { return e && e.detail ? e.detail.status : e } }
const textOf = (r) => typeof r.body === 'string' ? r.body : Buffer.from(r.bodyBase64 || '', 'base64').toString('utf8')

test('an existing storage made with --insecure-no-auth gets its root ACL at the start with --authz, and keeps it', async () => {
  const work = mkdtempSync(join(tmpdir(), 'lws-root-acl-'))
  const dir = join(work, 'storage')
  const engine = await loadEngine()
  try {
    // The storage as an owner had it: data written with no authorization, no /.acl.
    const open = serve([dir, '--insecure-no-auth', '--storage', 'files'])
    const o1 = await open.ready
    try {
      assert.equal((await fetch(`${o1}/kept/old.txt`, { method: 'PUT', headers: { 'content-type': 'text/plain' }, body: 'old data' })).status, 201)
      assert.equal((await fetch(`${o1}/.acl`)).status, 404)
    } finally { await open.stop() }

    const owner = await createDidKey({ engine })
    const stranger = await createDidKey({ engine })
    const aclFile = join(work, 'root.acl')
    writeFileSync(aclFile, ownerAcl(owner.agent))

    // Started with authorization and a root ACL: installed before any answer.
    const authz = serve([dir, '--authz', join(work, 'authz'), '--allow-http', '--root-acl', aclFile, '--storage', 'files'])
    const o2 = await authz.ready
    try {
      assert.match(authz.stderr(), INSTALLED)
      assert.equal((await fetch(`${o2}/kept/old.txt`)).status, 401, 'no token: 401')
      const asOwner = await asAgent(engine, owner)
      const got = await asOwner.read(`${o2}/kept/old.txt`)
      assert.equal(got.status, 200)
      assert.equal(textOf(got), 'old data', 'the old data is as it was')
      assert.equal(textOf(await asOwner.read(`${o2}/.acl`)), ownerAcl(owner.agent))
      assert.equal(await statusOf((await asAgent(engine, stranger)).read(`${o2}/kept/old.txt`)), 403, 'a stranger: 403')
    } finally { await authz.stop() }

    // Started again with ANOTHER root ACL: the one in the storage is kept.
    const otherFile = join(work, 'other.acl')
    writeFileSync(otherFile, ownerAcl(stranger.agent))
    const again = serve([dir, '--authz', join(work, 'authz'), '--allow-http', '--root-acl', otherFile, '--storage', 'files'])
    const o3 = await again.ready
    try {
      assert.match(again.stderr(), KEPT)
      assert.doesNotMatch(again.stderr(), INSTALLED)
      const asOwner = await asAgent(engine, owner)
      assert.equal(textOf(await asOwner.read(`${o3}/.acl`)), ownerAcl(owner.agent), 'the existing root ACL is not replaced')
      assert.equal((await asOwner.read(`${o3}/kept/old.txt`)).status, 200)
      assert.equal(await statusOf((await asAgent(engine, stranger)).read(`${o3}/kept/old.txt`)), 403)
    } finally { await again.stop() }
  } finally { rmSync(work, { recursive: true, force: true }) }
})

test('a storage kept as a snapshot: the root ACL is installed once and persisted; with authorization off nothing changes', async () => {
  const work = mkdtempSync(join(tmpdir(), 'lws-root-acl-snap-'))
  const dir = join(work, 'storage')
  const engine = await loadEngine()
  const BASE = 'http://127.0.0.1:1/'
  const acl = ownerAcl('https://id.example/owner')
  const open = (extra) => openLwsStorage({ engine, baseIri: BASE, dir, storage: 'snapshot', ...extra })
  try {
    const s1 = await open({ insecureNoAuth: true })
    assert.equal((await s1.step({ method: 'PUT', target: '/a.txt', headers: [['content-type', 'text/plain']], body: new TextEncoder().encode('a') })).status, 201)
    await s1.close()
    // Authorization off, a root ACL given: no install, no notice.
    const s2 = await open({ insecureNoAuth: true, rootAcl: acl })
    assert.ok(!s2.notices.some((n) => /root ACL/.test(n)), s2.notices.join('\n'))
    assert.equal((await s2.step({ method: 'GET', target: '/.acl', headers: [], body: new Uint8Array(0) })).status, 404)
    await s2.close()
    // Authorization on: installed, and written to the snapshot.
    const s3 = await open({ rootAcl: acl })
    assert.ok(s3.notices.some((n) => INSTALLED.test(n)), s3.notices.join('\n'))
    await s3.close()
    const s4 = await open({ rootAcl: ownerAcl('https://id.example/someone-else') })
    assert.ok(s4.notices.some((n) => KEPT.test(n)), s4.notices.join('\n'))
    await s4.close()
    // Read back with authorization off: the first root ACL, unchanged; the data too.
    const s5 = await open({ insecureNoAuth: true })
    const got = await s5.step({ method: 'GET', target: '/.acl', headers: [], body: new Uint8Array(0) })
    assert.equal(got.status, 200)
    assert.equal(new TextDecoder().decode(got.body), acl)
    assert.equal((await s5.step({ method: 'GET', target: '/a.txt', headers: [], body: new Uint8Array(0) })).status, 200)
    await s5.close()
  } finally { rmSync(work, { recursive: true, force: true }) }
})
