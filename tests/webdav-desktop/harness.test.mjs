// Lifecycle checks use fake CLI children and no sockets or engine assets.
import test from 'node:test'
import assert from 'node:assert/strict'
import { mkdtempSync, writeFileSync, readFileSync, readdirSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { startProcess, stopServer, run } from './serve-labs.mjs'

function fixture (t, source) {
  const dir = mkdtempSync(join(tmpdir(), 'dav-harness-unit-'))
  t.after(() => rmSync(dir, { recursive: true, force: true }))
  const cli = join(dir, 'cli.mjs')
  writeFileSync(cli, source)
  return { dir, cli, cmd: [process.execPath, cli] }
}

test('startup exit reports both output streams', async (t) => {
  const { cmd } = fixture(t, "console.log('fixture stdout'); console.error('fixture stderr'); process.exitCode = 7")
  await assert.rejects(startProcess(['lws-serve'], cmd), (e) => {
    assert.match(e.message, /exited 7/)
    assert.match(e.message, /stdout:\nfixture stdout/)
    assert.match(e.message, /stderr:\nfixture stderr/)
    return true
  })
})

test('spawn error rejects immediately with command diagnostics', async () => {
  await assert.rejects(startProcess(['lws-serve'], ['/no/such/factoidal']), /lws-serve spawn failed:.*ENOENT/)
})

test('startup timeout terminates the child and retains stdout and stderr', async (t) => {
  const { dir, cli } = fixture(t, "import { writeFileSync } from 'node:fs'; writeFileSync(process.argv[2], String(process.pid)); console.log('waiting stdout'); console.error('waiting stderr'); setInterval(() => {}, 1000)")
  const pidFile = join(dir, 'pid')
  await assert.rejects(startProcess([], [process.execPath, cli, pidFile], { timeout: 500 }), (e) => {
    assert.match(e.message, /printed no origin/)
    assert.match(e.message, /waiting stdout/)
    assert.match(e.message, /waiting stderr/)
    return true
  })
  const pid = Number(readFileSync(pidFile, 'utf8'))
  assert.throws(() => process.kill(pid, 0), { code: 'ESRCH' })
})

test('a ready child can be stopped, including repeated stop', async (t) => {
  const { cmd } = fixture(t, "console.log('http://127.0.0.1:12345'); setInterval(() => {}, 1000)")
  const server = await startProcess(['webdav-serve'], cmd)
  assert.equal(server.origin, 'http://127.0.0.1:12345')
  await stopServer(server.child)
  await stopServer(server.child)
  assert.notEqual(server.child.signalCode, null)
})

test('run removes its owned temporary configuration after startup failure', async (t) => {
  const { dir, cli } = fixture(t, "console.error('fixture startup refusal'); process.exitCode = 9")
  const before = readdirSync(tmpdir()).filter((p) => p.startsWith('factoidal-labs-dav-')).sort()
  await assert.rejects(run({ trees: ['types'], out: join(dir, 'results'), cli, port: 0, quiet: true }), /fixture startup refusal/)
  const after = readdirSync(tmpdir()).filter((p) => p.startsWith('factoidal-labs-dav-')).sort()
  assert.deepEqual(after, before)
})
