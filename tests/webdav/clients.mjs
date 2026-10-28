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

function start (dir) {
  const child = spawn(process.execPath, [CLI, 'webdav-serve', 'dav', '--port', '0'], { cwd: dir, stdio: ['ignore', 'pipe', 'pipe'] })
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
  try {
    mkdirSync(join(dir, 'dav', 'notes'), { recursive: true })
    writeFileSync(join(dir, 'dav', 'notes.md'), '# Notes\n- kind: local\n- path: ./notes\n')
    mkdirSync(join(dir, 'src', 'sub'), { recursive: true })
    writeFileSync(join(dir, 'src', 'a.txt'), 'hello\n')
    writeFileSync(join(dir, 'src', 'sub', 'b.txt'), 'world\n')
    writeFileSync(join(dir, 'up.txt'), 'hi\n')
    server = await start(dir)

    if (!has('rclone')) {
      skip('rclone', 'rclone is not installed')
    } else {
      const env = { ...process.env, RCLONE_CONFIG: join(dir, 'rclone.conf'),
        RCLONE_CONFIG_F_TYPE: 'webdav', RCLONE_CONFIG_F_URL: `${server.origin}/`, RCLONE_CONFIG_F_VENDOR: 'other' }
      writeFileSync(join(dir, 'rclone.conf'), '')
      const rc = (...args) => run('rclone', args, { env, cwd: dir })
      await check('rclone: copy a tree, list it, and its bytes match', async () => {
        rc('copy', 'src', 'f:notes/proj')
        const ls = rc('lsf', '-R', 'f:notes/proj').split('\n').filter(Boolean).sort()
        assert(JSON.stringify(ls) === JSON.stringify(['a.txt', 'sub/', 'sub/b.txt']), `listing ${JSON.stringify(ls)}`)
        rc('check', 'src', 'f:notes/proj')
      })
      await check('rclone: move, mkdir, read', async () => {
        rc('moveto', 'f:notes/proj/a.txt', 'f:notes/proj/renamed.txt')
        rc('mkdir', 'f:notes/empty')
        const ls = rc('lsf', '-R', 'f:notes').split('\n').filter(Boolean).sort()
        assert(ls.includes('proj/renamed.txt') && !ls.includes('proj/a.txt') && ls.includes('empty/'), `listing ${JSON.stringify(ls)}`)
        assert(rc('cat', 'f:notes/proj/renamed.txt') === 'hello\n', 'content after move')
      })
      await check('rclone: purge a collection', async () => {
        rc('purge', 'f:notes/proj')
        const ls = rc('lsf', '-R', 'f:notes').split('\n').filter(Boolean)
        assert(!ls.some((l) => l.startsWith('proj')), `listing ${JSON.stringify(ls)}`)
      })
    }

    if (!has('cadaver')) {
      skip('cadaver', 'cadaver is not installed')
    } else {
      const script = ['cd notes', 'mkcol d1', 'put up.txt d1/up.txt', 'ls d1',
        'propset d1/up.txt color blue', 'propget d1/up.txt color',
        'lock d1/up.txt', 'discover d1/up.txt', 'unlock d1/up.txt',
        'copy d1/up.txt d1/copy.txt', 'move d1/copy.txt d1/moved.txt', 'ls d1',
        'cat d1/moved.txt', 'rm d1/moved.txt', 'rm d1/up.txt', 'rmcol d1', 'quit', ''].join('\n')
      const r = spawnSync('cadaver', [`${server.origin}/`], { input: script, encoding: 'utf8', cwd: dir, timeout: 120000 })
      const out = `${r.stdout}${r.stderr}`
      const expect = (name, re) => check(`cadaver: ${name}`, async () => assert(re.test(out), `no match for ${re} in:\n${out}`))
      await expect('MKCOL', /Creating `d1': succeeded/)
      await expect('PUT', /Uploading up\.txt to `\/notes\/d1\/up\.txt': .*succeeded/)
      await expect('PROPPATCH and PROPFIND of a dead property', /Value of color is: blue/)
      await expect('LOCK, discovery, UNLOCK', /Locking `d1\/up\.txt': succeeded[\s\S]*Lock token <urn:uuid:[0-9a-f-]+>[\s\S]*Unlocking `d1\/up\.txt': succeeded/)
      await expect('COPY and MOVE', /Copying[^\n]*succeeded[\s\S]*Moving[^\n]*succeeded/)
      await expect('GET after MOVE', /cat d1\/moved\.txt\nhi\n/)
      await expect('DELETE of a file and a collection', /Deleting `d1\/moved\.txt': succeeded[\s\S]*Deleting collection `d1': succeeded/)
      await check('cadaver: no failed command', async () => assert(!/failed/i.test(out), `a command failed:\n${out}`))
    }
  } finally {
    if (server !== null) {
      server.child.kill('SIGTERM')
      await new Promise((resolve) => server.child.on('close', resolve))
    }
    rmSync(dir, { recursive: true, force: true })
  }
}

await main()
console.log(`webdav clients: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${passed + failed + skipped})`)
for (const f of failures) console.log(`  ${f}`)
process.exit(failed === 0 ? 0 : 1)
