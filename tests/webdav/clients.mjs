// Third-party WebDAV clients against `factoidal webdav-serve`
// (https://github.com/danbri/factoidal/issues/1079).
//
//   node tests/webdav/clients.mjs
//
// Runs two independent clients through the operations a file browser uses,
// over one local mount:
//   rclone (webdav backend, vendor other): copy a tree, list, move, mkdir,
//     read, purge;
//   cadaver: MKCOL, PUT, PROPFIND listing, PROPPATCH and PROPFIND of a dead
//     property, LOCK, lock discovery, UNLOCK, COPY, MOVE, GET, DELETE.
// A client that is not installed is a skip with the reason printed
// (Debian/Ubuntu: apt-get install rclone cadaver), never a pass. The desktop
// file browsers (Finder, Windows Explorer, GNOME Files, Dolphin) are not
// covered here; issue 1079 stays open for them.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import { spawn, spawnSync } from 'node:child_process'
import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { keyPair, didKeyOf } from '../authz/fixtures.mjs'

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

const CLI = fileURLToPath(new URL('../../npm/factoidal/bin/factoidal.mjs', import.meta.url))
const has = (cmd) => spawnSync('sh', ['-c', `command -v ${cmd}`]).status === 0

function start (dir, args) {
  const child = spawn(process.execPath, [CLI, ...(args || ['webdav-serve', 'dav', '--port', '0', '--guest', 'guest'])], { cwd: dir, stdio: ['ignore', 'pipe', 'pipe'] })
  return new Promise((resolve, reject) => {
    let out = ''
    let err = ''
    const timer = setTimeout(() => reject(new Error(`no origin printed: ${out} ${err}`)), 60000)
    child.stdout.on('data', (c) => {
      out += c
      const m = /^(http:\/\/127\.0\.0\.1:\d+)$/m.exec(out)
      if (m) { clearTimeout(timer); resolve({ child, origin: m[1] }) }
    })
    child.stderr.on('data', (c) => { err += c })
    child.on('exit', (code) => { clearTimeout(timer); reject(new Error(`exited ${code}: ${err}`)) })
  })
}

function run (cmd, args, opts = {}) {
  const r = spawnSync(cmd, args, { encoding: 'utf8', timeout: 120000, ...opts })
  if (r.status !== 0) throw new Error(`${cmd} ${args.join(' ')} exited ${r.status}: ${r.stderr || r.stdout}`)
  return r.stdout
}

async function main () {
  const dir = mkdtempSync(join(tmpdir(), 'factoidal-webdav-clients-'))
  let server = null
  let lws = null
  try {
    // Emergency mode (https://github.com/danbri/factoidal/issues/1147):
    // webdav-serve is read only and has no local mounts. The mount is an lws
    // mount of an `lws-serve --authz` storage, filled through the LWS client
    // as its owner; the clients read it, and their writes are refused.
    mkdirSync(join(dir, 'dav'), { recursive: true })
    const owner = keyPair('ES256')
    const did = didKeyOf(owner)
    const ownerJwk = owner.privateKey.export({ format: 'jwk' })
    writeFileSync(join(dir, 'dav', 'owner.jwk'), JSON.stringify(ownerJwk), { mode: 0o600 })
    lws = await start(dir, ['lws-serve', 'lws', '--port', '0', '--authz', 'lws-as', '--owner', did, '--quiet'])
    const { createLwsClient } = await import('../../npm/factoidal/lws/client.mjs')
    const ownerClient = await createLwsClient({ selfIssued: { subject: did, keyId: `${did}#${did.slice(8)}`, jwk: ownerJwk } })
    await ownerClient.update(`${lws.origin}/hello.txt`, { body: 'hello\n', mediaType: 'text/plain', precondition: 'none' })
    writeFileSync(join(dir, 'dav', 'notes.md'),
      `# Notes\n- kind: lws\n- url: ${lws.origin}/\n- auth: did-key\n- key-file: owner.jwk\n- users: guest\n`)
    writeFileSync(join(dir, 'up.txt'), 'hi\n')
    server = await start(dir)

    if (!has('rclone')) {
      skip('rclone', 'rclone is not installed')
    } else {
      const env = { ...process.env, RCLONE_CONFIG: join(dir, 'rclone.conf'),
        RCLONE_CONFIG_F_TYPE: 'webdav', RCLONE_CONFIG_F_URL: `${server.origin}/`, RCLONE_CONFIG_F_VENDOR: 'other' }
      writeFileSync(join(dir, 'rclone.conf'), '')
      const rc = (...args) => run('rclone', args, { env, cwd: dir })
      await check('rclone: list and read', async () => {
        const ls = rc('lsf', '-R', 'f:notes').split('\n').filter(Boolean).sort()
        assert(ls.includes('hello.txt'), `listing ${JSON.stringify(ls)}`)
        assert(rc('cat', 'f:notes/hello.txt') === 'hello\n', 'content')
      })
      await check('rclone: a copy in, a mkdir and a delete are refused (read only, issue 1147)', async () => {
        for (const args of [['copyto', 'up.txt', 'f:notes/up.txt'], ['mkdir', 'f:notes/empty'], ['deletefile', 'f:notes/hello.txt']]) {
          let refused = false
          try { rc(...args) } catch (_error) { refused = true }
          assert(refused, `rclone ${args.join(' ')} succeeded`)
        }
        assert(rc('cat', 'f:notes/hello.txt') === 'hello\n', 'content changed')
      })
    }

    if (!has('cadaver')) {
      skip('cadaver', 'cadaver is not installed')
    } else {
      const script = ['cd notes', 'ls', 'cat hello.txt', 'mkcol d1', 'put up.txt up.txt', 'lock hello.txt', 'quit', ''].join('\n')
      const r = spawnSync('cadaver', [`${server.origin}/`], { input: script, encoding: 'utf8', cwd: dir, timeout: 120000 })
      const out = `${r.stdout}${r.stderr}`
      const expect = (name, re) => check(`cadaver: ${name}`, async () => assert(re.test(out), `no match for ${re} in:\n${out}`))
      await expect('ls and cat', /hello\.txt[\s\S]*cat hello\.txt\nhello\n/)
      await expect('MKCOL refused', /Creating `d1': failed/)
      await expect('PUT refused', /Uploading up\.txt to `\/notes\/up\.txt': [^\n]*failed/)
      await expect('LOCK refused', /Locking `hello\.txt': failed/)
    }
  } finally {
    for (const p of [server, lws]) {
      if (p === null) continue
      p.child.kill('SIGTERM')
      await new Promise((resolve) => p.child.on('close', resolve))
    }
    rmSync(dir, { recursive: true, force: true })
  }
}

await main()
console.log(`webdav clients: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${passed + failed + skipped})`)
for (const f of failures) console.log(`  ${f}`)
process.exit(failed === 0 ? 0 : 1)
