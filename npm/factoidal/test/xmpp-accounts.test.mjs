// The accounts file: what stops the start, the warning on its mode, per-account salts and lines
// that hold no password.
import { test } from 'node:test'
import assert from 'node:assert/strict'
import net from 'node:net'
import { once } from 'node:events'
import { createHash, createHmac, pbkdf2Sync, randomBytes } from 'node:crypto'
import { mkdtempSync, rmSync, writeFileSync, chmodSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { setTimeout as sleep } from 'node:timers/promises'
import { createXmppServer, xmppServerOpsAvailable } from '../xmpp/server.mjs'
import { loadEngine } from '../bin/engine.mjs'

const engine = await loadEngine()
const { available } = await xmppServerOpsAvailable({ engine })
const skip = available ? false : 'the engine has no XMPP server ops'
const DOMAIN = 'localhost'
const HEADER = `<?xml version='1.0'?><stream:stream to='${DOMAIN}' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>`
const SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'

const start = async (options) => {
  const host = await createXmppServer({ domain: DOMAIN, pollMs: 0, onError: () => {}, engine, ...options })
  await new Promise((resolve) => host.server.listen(0, '127.0.0.1', resolve))
  return { host, port: host.server.address().port }
}

async function opened (port) {
  const socket = net.connect(port, '127.0.0.1')
  const c = { socket, text: '' }
  socket.setEncoding('utf8')
  socket.on('data', (d) => { c.text += d })
  socket.on('error', () => {})
  c.until = async (word, ms = 3000) => {
    const end = Date.now() + ms
    while (!c.text.includes(word) && Date.now() < end) await sleep(5)
    assert.ok(c.text.includes(word), `wanted ${word}, got ${c.text.slice(-300)}`)
  }
  await once(socket, 'connect')
  socket.write(HEADER)
  await c.until('</stream:features>'); c.text = ''
  return c
}

async function scramLogin (port, user, password) {
  const c = await opened(port)
  const nonce = randomBytes(12).toString('base64')
  const bare = `n=${user},r=${nonce}`
  c.socket.write(`<auth xmlns='${SASL}' mechanism='SCRAM-SHA-256'>${Buffer.from('n,,' + bare).toString('base64')}</auth>`)
  await c.until('</challenge>')
  const first = Buffer.from(/<challenge[^>]*>([^<]+)</.exec(c.text)[1], 'base64').toString()
  const f = Object.fromEntries(first.split(',').map((x) => [x[0], x.slice(2)]))
  const salted = pbkdf2Sync(password, Buffer.from(f.s, 'base64'), Number(f.i), 32, 'sha256')
  const clientKey = createHmac('sha256', salted).update('Client Key').digest()
  const stored = createHash('sha256').update(clientKey).digest()
  const final = `c=biws,r=${f.r}`
  const sig = createHmac('sha256', stored).update(`${bare},${first},${final}`).digest()
  const proof = Buffer.from(clientKey.map((b, i) => b ^ sig[i])).toString('base64')
  c.text = ''
  c.socket.write(`<response xmlns='${SASL}'>${Buffer.from(`${final},p=${proof}`).toString('base64')}</response>`)
  await c.until('</')
  const answer = c.text
  c.socket.destroy()
  return { answer, salt: f.s, iterations: f.i }
}

test('a line that makes no account stops the start, and the error does not quote the file', { skip }, async () => {
  for (const text of ['alice', 'alice:', ':secret-pw', 'alice:a\nalice:b']) {
    await assert.rejects(start({ accountsText: text }), (error) => !error.message.includes('secret-pw'))
  }
  await assert.rejects(start({ accounts: [{ username: 'alice', password: '' }] }))
  const { host } = await start({ accountsText: '# a comment\n\nalice:pw\n' })
  assert.equal(host.xmpp.accounts, 1)
  await host.close()
})

test('a file others can read gives a warning; a private file gives none', { skip }, async () => {
  const dir = mkdtempSync(join(tmpdir(), 'xmpp-accounts-'))
  try {
    writeFileSync(join(dir, 'accounts'), 'alice:pw\n')
    chmodSync(join(dir, 'accounts'), 0o644)
    let { host } = await start({ dir })
    assert.ok(host.xmpp.warnings.some((w) => w.includes('chmod 600')))
    await host.close()
    chmodSync(join(dir, 'accounts'), 0o600)
    ;({ host } = await start({ dir }))
    assert.ok(!host.xmpp.warnings.some((w) => w.includes('chmod 600')))
    await host.close()
  } finally { rmSync(dir, { recursive: true, force: true }) }
})

test('SCRAM: each account has its own salt, and the login works at the default count', { skip }, async () => {
  const { host, port } = await start({ accounts: [{ username: 'alice', password: 'a-pw' }, { username: 'bob', password: 'b-pw' }] })
  try {
    const a = await scramLogin(port, 'alice', 'a-pw')
    const b = await scramLogin(port, 'bob', 'b-pw')
    assert.match(a.answer, /<success/)
    assert.match(b.answer, /<success/)
    assert.notEqual(a.salt, b.salt)
    assert.equal(a.iterations, '10000')
  } finally { await host.close() }
})

test('a line with no password logs in by SCRAM, not by PLAIN', { skip }, async () => {
  const salt = randomBytes(16).toString('base64')
  const { line } = engine.call('xmppVerifier', ['alice', 'a-pw', salt, '4096'])
  assert.doesNotMatch(line, /a-pw/)
  const { host, port } = await start({ accountsText: line + '\n' })
  try {
    const ok = await scramLogin(port, 'alice', 'a-pw')
    assert.match(ok.answer, /<success/)
    assert.equal(ok.salt, salt)
    const bad = await scramLogin(port, 'alice', 'wrong')
    assert.match(bad.answer, /not-authorized/)
    const c = await opened(port)
    c.socket.write(`<auth xmlns='${SASL}' mechanism='PLAIN'>${Buffer.from('\0alice\0a-pw').toString('base64')}</auth>`)
    await c.until('</failure>')
    assert.doesNotMatch(c.text, /<success/)
    c.socket.destroy()
  } finally { await host.close() }
})
