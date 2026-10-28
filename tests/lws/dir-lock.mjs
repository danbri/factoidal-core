// Host tests: one writing process per storage directory, and the start
// notice about encryption at rest.
// https://github.com/danbri/factoidal/issues/1135 (row C11, invariant I11 of
// docs/designissues/2026-10-28-feature-combination-safety.md)
//
//   node tests/lws/dir-lock.mjs
//
// The engine decides the lock file (DIR/lws.lock), its contents and every
// refusal (formal/lean4/L4Factoidal/LWS/DirLock.lean, op lwsDirLock); the
// host does the exclusive create, the liveness probe and the removal.
// Checked: a second lws-serve DIR is refused; solid-serve and a webdav-serve
// local mount of a held DIR are refused; a stale lock after a simulated crash
// is taken over with a warning; a clean exit (SIGINT, SIGTERM) removes the
// lock; a lock of another host, and a file that is not a lock, are refused;
// in one process, a second open of the same DIR is refused, a close releases
// it, and a lock with this process id and another token is taken over. Then
// the start notice: OFF (clear text, how to turn on encryption) with no key,
// ON with the key id with a key; `factoidal lws-keygen`.
//
// Score line: "N pass, M fail, S skipped (out of T)".

import { mkdtempSync, mkdirSync, rmSync, readFileSync, writeFileSync, existsSync } from 'node:fs'
import { tmpdir, hostname } from 'node:os'
import { join } from 'node:path'
import { createHash, randomBytes } from 'node:crypto'
import { spawn, spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'

// The snapshot mode; the lock does not depend on it.
delete process.env.FACTOIDAL_LWS_STORAGE
delete process.env.FACTOIDAL_LWS_KEY

const ROOT = fileURLToPath(new URL('../../', import.meta.url))
const CLI = join(ROOT, 'npm/factoidal/bin/factoidal.mjs')

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

/** Start a server command; resolve with the child and its origin, or with
 *  the exit code and standard error when it stops first. */
function start (args, env = {}) {
  return new Promise((resolve) => {
    const child = spawn(process.execPath, [CLI, ...args], {
      env: { ...process.env, ...env }, stdio: ['ignore', 'pipe', 'pipe']
    })
    let out = ''
    let errText = ''
    let done = false
    child.stdout.on('data', (d) => {
      out += d.toString()
      const line = out.split('\n')[0]
      if (!done && out.indexOf('\n') >= 0 && line.startsWith('http')) {
        done = true
        // Standard error before the origin line is complete: the notices
        // are written before it.
        setTimeout(() => resolve({ child, origin: line.trim(), stderr: () => errText }), 50)
      }
    })
    child.stderr.on('data', (d) => { errText += d.toString() })
    child.on('exit', (code) => {
      if (!done) { done = true; resolve({ code, stderr: () => errText }) }
    })
  })
}

function stop (child, signal = 'SIGINT') {
  return new Promise((resolve) => {
    child.on('exit', () => resolve())
    child.kill(signal)
  })
}

const LWS_ARGS = (dir) => ['lws-serve', dir, '--insecure-no-auth', '--port', '0', '--quiet']
const SOLID_ARGS = (dir) => ['solid-serve', dir, '--insecure-no-auth', '--port', '0', '--quiet']

/** A process id that does not run: a child that has exited. */
function deadPid () {
  const r = spawnSync(process.execPath, ['-e', 'process.stdout.write(String(process.pid))'])
  return Number(r.stdout.toString())
}

function lockText (fields) {
  return JSON.stringify({
    format: 'lws-lock-1', pid: 1, command: 'lws-serve', started: '2026-10-28T00:00:00.000Z',
    host: hostname(), token: 'AAAAAAAAAAAAAAAAAAAAAAAA', ...fields
  }) + '\n'
}

const KEY = randomBytes(32)
const KEY_HEX = KEY.toString('hex')
const KEY_ID = createHash('sha256').update(KEY).digest('hex').slice(0, 16)

const CLI_CHECKS = [
  'lws-serve: the lock file names this process while it runs',
  'lws-serve: a second lws-serve of the same DIR is refused (exit 1, names the lock file and the holder)',
  'solid-serve: a DIR that lws-serve holds is refused',
  'webdav-serve: a local mount of a DIR that lws-serve holds is refused',
  'lws-serve: a clean exit (SIGINT) removes the lock',
  'lws-serve: a clean exit (SIGTERM) removes the lock',
  'webdav-serve: a clean exit removes the lock of its local mount',
  'lws-serve: a stale lock (process not running) is taken over with a warning',
  'lws-serve: a lock of another host is refused',
  'lws-serve: a file that is not a lock is refused',
  'lws-serve: with no key, the start notice says clear text and how to turn on encryption',
  'lws-serve: with a key, the start notice says sealed and gives the key id',
  'solid-serve: the start notice says clear text with no key',
  'webdav-serve: the start notice of a local mount says clear text with no key',
  'lws-keygen: prints a key whose key id is SHA-256 of the key; lws-serve starts sealed with it'
]

const LIB_CHECKS = [
  'openLwsStorage: a second open of the same DIR in one process is refused; close releases it',
  'openLwsStorage: a lock with this process id and another token is taken over with a warning',
  'openLwsStorage: a refused open (wrong key) releases the lock'
]

async function runCli (root) {
  const dir = join(root, 'store')
  let first = null
  try {
    first = await start(LWS_ARGS(dir))
    await check(CLI_CHECKS[0], async () => {
      assert(first.child !== undefined, `lws-serve did not start: ${first.stderr()}`)
      const lock = JSON.parse(readFileSync(join(dir, 'lws.lock'), 'utf8'))
      assert(lock.format === 'lws-lock-1' && lock.pid === first.child.pid && lock.command === 'lws-serve' &&
        lock.host === hostname(), `lock ${JSON.stringify(lock)}`)
    })
    await check(CLI_CHECKS[1], async () => {
      const second = await start(LWS_ARGS(dir))
      if (second.child !== undefined) { await stop(second.child); throw new Error('the second lws-serve started') }
      assert(second.code === 1, `exit ${second.code}`)
      const text = second.stderr()
      assert(text.includes(join(dir, 'lws.lock')) && text.includes(`process ${first.child.pid}`) &&
        text.includes('issues/1135'), text)
    })
    await check(CLI_CHECKS[2], async () => {
      const solid = await start(SOLID_ARGS(dir))
      if (solid.child !== undefined) { await stop(solid.child); throw new Error('solid-serve started') }
      assert(solid.code === 1 && solid.stderr().includes(join(dir, 'lws.lock')), `exit ${solid.code} ${solid.stderr()}`)
    })
    await check(CLI_CHECKS[3], async () => {
      const conf = join(root, 'conf')
      mkdirSync(conf, { recursive: true })
      writeFileSync(join(conf, 'local.md'), `# Local storage\n- kind: local\n- path: ${dir}\n`)
      const web = await start(['webdav-serve', conf, '--port', '0', '--quiet'])
      if (web.child !== undefined) { await stop(web.child); throw new Error('webdav-serve started') }
      assert(web.code === 1 && web.stderr().includes(join(dir, 'lws.lock')) &&
        web.stderr().includes(`process ${first.child.pid}`), `exit ${web.code} ${web.stderr()}`)
    })
    await check(CLI_CHECKS[4], async () => {
      await stop(first.child, 'SIGINT')
      first = null
      assert(!existsSync(join(dir, 'lws.lock')), 'the lock is still there')
    })
    await check(CLI_CHECKS[5], async () => {
      const s = await start(LWS_ARGS(dir))
      assert(s.child !== undefined, `no start: ${s.stderr()}`)
      assert(existsSync(join(dir, 'lws.lock')), 'no lock while running')
      await stop(s.child, 'SIGTERM')
      assert(!existsSync(join(dir, 'lws.lock')), 'the lock is still there')
    })
    await check(CLI_CHECKS[6], async () => {
      const conf = join(root, 'conf')
      const web = await start(['webdav-serve', conf, '--port', '0', '--quiet'])
      assert(web.child !== undefined, `no start: ${web.stderr()}`)
      const lock = JSON.parse(readFileSync(join(dir, 'lws.lock'), 'utf8'))
      assert(lock.command === 'webdav-serve' && lock.pid === web.child.pid, JSON.stringify(lock))
      await stop(web.child)
      assert(!existsSync(join(dir, 'lws.lock')), 'the lock is still there')
    })
    await check(CLI_CHECKS[7], async () => {
      const pid = deadPid()
      writeFileSync(join(dir, 'lws.lock'), lockText({ pid }))
      const s = await start(LWS_ARGS(dir))
      assert(s.child !== undefined, `no start: ${s.stderr()}`)
      const lock = JSON.parse(readFileSync(join(dir, 'lws.lock'), 'utf8'))
      await stop(s.child)
      assert(lock.pid === s.child.pid, `lock not taken over: ${JSON.stringify(lock)}`)
      assert(s.stderr().includes('WARNING') && s.stderr().includes(`process ${pid}`) &&
        s.stderr().includes('stale lock'), s.stderr())
    })
    await check(CLI_CHECKS[8], async () => {
      writeFileSync(join(dir, 'lws.lock'), lockText({ pid: process.pid, host: 'another-host.invalid' }))
      const s = await start(LWS_ARGS(dir))
      if (s.child !== undefined) { await stop(s.child); throw new Error('lws-serve started') }
      assert(s.code === 1 && s.stderr().includes('another-host.invalid') && s.stderr().includes('cannot'), s.stderr())
    })
    await check(CLI_CHECKS[9], async () => {
      writeFileSync(join(dir, 'lws.lock'), 'some other text\n')
      const s = await start(LWS_ARGS(dir))
      if (s.child !== undefined) { await stop(s.child); throw new Error('lws-serve started') }
      assert(s.code === 1 && s.stderr().includes('not a lock file'), s.stderr())
      rmSync(join(dir, 'lws.lock'))
    })
    await check(CLI_CHECKS[10], async () => {
      const s = await start(LWS_ARGS(join(root, 'clear')))
      assert(s.child !== undefined, `no start: ${s.stderr()}`)
      await stop(s.child)
      const text = s.stderr()
      const warn = text.indexOf('EXPERIMENTAL UNREVIEWED CODE')
      const notice = text.indexOf('encryption at rest is OFF')
      assert(warn >= 0 && notice > warn, `order or text: ${text}`)
      assert(text.includes('clear text') && text.includes('factoidal lws-keygen') &&
        text.includes('FACTOIDAL_LWS_KEY') && text.includes('#encryption-at-rest'), text)
    })
    await check(CLI_CHECKS[11], async () => {
      const s = await start(LWS_ARGS(join(root, 'sealed')), { FACTOIDAL_LWS_KEY: KEY_HEX })
      assert(s.child !== undefined, `no start: ${s.stderr()}`)
      await stop(s.child)
      assert(s.stderr().includes('encryption at rest is ON') && s.stderr().includes(`key id ${KEY_ID}`), s.stderr())
    })
    await check(CLI_CHECKS[12], async () => {
      const s = await start(SOLID_ARGS(join(root, 'solid')))
      assert(s.child !== undefined, `no start: ${s.stderr()}`)
      await stop(s.child)
      assert(s.stderr().includes('solid-serve: encryption at rest is OFF'), s.stderr())
    })
    await check(CLI_CHECKS[13], async () => {
      const web = await start(['webdav-serve', join(root, 'conf'), '--port', '0', '--quiet'])
      assert(web.child !== undefined, `no start: ${web.stderr()}`)
      await stop(web.child)
      assert(web.stderr().includes('webdav-serve: mount local: encryption at rest is OFF'), web.stderr())
    })
    await check(CLI_CHECKS[14], async () => {
      const r = spawnSync(process.execPath, [CLI, 'lws-keygen'], { encoding: 'utf8' })
      assert(r.status === 0, `exit ${r.status} ${r.stderr}`)
      const key = r.stdout.trim()
      assert(/^[0-9a-f]{64}$/.test(key), `key text ${key}`)
      const kid = createHash('sha256').update(Buffer.from(key, 'hex')).digest('hex').slice(0, 16)
      assert(r.stderr.includes(`key id ${kid}`), r.stderr)
      const s = await start(LWS_ARGS(join(root, 'keygen')), { FACTOIDAL_LWS_KEY: key })
      assert(s.child !== undefined, `no start: ${s.stderr()}`)
      await stop(s.child)
      assert(s.stderr().includes(`key id ${kid}`), s.stderr())
    })
  } finally {
    if (first !== null && first.child !== undefined) await stop(first.child)
  }
}

async function runLibrary (root, engine) {
  const { openLwsStorage } = await import('../../npm/factoidal/lws/server.mjs')
  const dir = join(root, 'lib')
  await check(LIB_CHECKS[0], async () => {
    const a = await openLwsStorage({ engine, dir, insecureNoAuth: true })
    let refused = null
    try {
      const b = await openLwsStorage({ engine, dir, insecureNoAuth: true })
      b.close()
    } catch (error) {
      refused = error.message
    }
    assert(refused !== null && refused.includes('already open in this process'), `second open: ${refused}`)
    assert(a.lockFile === join(dir, 'lws.lock') && existsSync(a.lockFile), `lockFile ${a.lockFile}`)
    a.close()
    assert(!existsSync(join(dir, 'lws.lock')), 'close left the lock')
    const c = await openLwsStorage({ engine, dir, insecureNoAuth: true })
    c.close()
  })
  await check(LIB_CHECKS[1], async () => {
    writeFileSync(join(dir, 'lws.lock'), lockText({ pid: process.pid, token: 'an-earlier-process-token' }))
    const a = await openLwsStorage({ engine, dir, insecureNoAuth: true })
    try {
      assert(a.notices.some((n) => n.startsWith('WARNING') && n.includes(`process ${process.pid}`)), JSON.stringify(a.notices))
    } finally {
      a.close()
    }
  })
  await check(LIB_CHECKS[2], async () => {
    const sealed = join(root, 'lib-sealed')
    const a = await openLwsStorage({ engine, dir: sealed, insecureNoAuth: true, storageKey: KEY_HEX })
    await a.step({ method: 'PUT', target: '/x.txt', headers: [['content-type', 'text/plain']], body: 'x' })
    a.close()
    let refused = null
    try {
      const b = await openLwsStorage({ engine, dir: sealed, insecureNoAuth: true, storageKey: randomBytes(32).toString('hex') })
      b.close()
    } catch (error) {
      refused = error.message
    }
    assert(refused !== null && refused.includes('wrong key'), `open: ${refused}`)
    assert(!existsSync(join(sealed, 'lws.lock')), 'the refused open left the lock')
  })
}

async function main () {
  const { loadEngine } = await import('../../npm/factoidal/bin/engine.mjs')
  let engine
  try {
    engine = await loadEngine()
  } catch (error) {
    for (const n of [...CLI_CHECKS, ...LIB_CHECKS]) skip(n, `the Lean engine did not load: ${error.message}`)
    return
  }
  let carries = true
  try {
    engine.call('lwsDirLock', ['{}'])
  } catch (error) {
    carries = String(error.message).indexOf('unknown op') < 0
  }
  if (!carries) {
    for (const n of [...CLI_CHECKS, ...LIB_CHECKS]) skip(n, 'the module does not carry lwsDirLock (rebuild the wasm)')
    return
  }
  const root = mkdtempSync(join(tmpdir(), 'factoidal-dir-lock-'))
  try {
    await runLibrary(root, engine)
    await runCli(root)
  } finally {
    rmSync(root, { recursive: true, force: true })
  }
}

await main()

for (const failure of failures) console.log(`  FAIL ${failure}`)
const total = passed + failed + skipped
console.log(`lws-dir-lock node: ${passed} pass, ${failed} fail, ${skipped} skipped (out of ${total})`)
process.exitCode = failed === 0 ? 0 : 1
