// SASL on a stream: a stream closes after repeated failures, the address limit, and one exchange
// for every name.
import { test } from 'node:test'
import assert from 'node:assert/strict'
import net from 'node:net'
import { once } from 'node:events'
import { setTimeout as sleep } from 'node:timers/promises'
import { createXmppServer, xmppServerOpsAvailable } from '../xmpp/server.mjs'
import { loadEngine } from '../bin/engine.mjs'

const engine = await loadEngine()
const { available } = await xmppServerOpsAvailable({ engine })
const skip = available ? false : 'the engine has no XMPP server ops'
const DOMAIN = 'localhost'
const ACCOUNTS = [{ username: 'alice', password: 'alice-pw' }, { username: 'bob', password: 'bob-pw' }]
const HEADER = `<?xml version='1.0'?><stream:stream to='${DOMAIN}' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>`
const SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const plain = (user, pw) => `<auth xmlns='${SASL}' mechanism='PLAIN'>${Buffer.from(`\0${user}\0${pw}`).toString('base64')}</auth>`
const scramFirst = (user) => `<auth xmlns='${SASL}' mechanism='SCRAM-SHA-256'>${Buffer.from(`n,,n=${user},r=clientnonce`).toString('base64')}</auth>`

async function start (options) {
  const host = await createXmppServer({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, engine, ...options })
  await new Promise((resolve) => host.server.listen(0, '127.0.0.1', resolve))
  return { host, port: host.server.address().port }
}

async function opened (port) {
  const socket = net.connect(port, '127.0.0.1')
  const c = { socket, text: '', ended: false }
  socket.setEncoding('utf8')
  socket.on('data', (d) => { c.text += d })
  socket.on('close', () => { c.ended = true })
  socket.on('error', () => { c.ended = true })
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

test('a stream closes at the third failed attempt, and later attempts in the same read get no answer', { skip }, async () => {
  const { host, port } = await start({ disableRateLimits: true })
  try {
    const c = await opened(port)
    c.socket.write(plain('alice', 'x1') + plain('alice', 'x2') + plain('alice', 'x3') + plain('alice', 'x4') + plain('alice', 'x5'))
    await c.until('policy-violation')
    await sleep(100)
    assert.equal(c.text.split('<failure').length - 1, 3)
    assert.equal(c.ended, true)
  } finally { await host.close() }
})

test('two failed attempts leave the stream open for the right password', { skip }, async () => {
  const { host, port } = await start({ disableRateLimits: true })
  try {
    const c = await opened(port)
    c.socket.write(plain('alice', 'x1') + plain('alice', 'x2') + plain('alice', 'alice-pw'))
    await c.until('<success')
    c.socket.destroy()
  } finally { await host.close() }
})

test('SCRAM: the first answer has one form for a name with an account and for one without, and salts differ per name', { skip }, async () => {
  const { host, port } = await start({})
  const firstAnswer = async (user) => {
    const c = await opened(port)
    c.socket.write(scramFirst(user))
    await c.until('</challenge>')
    const m = /<challenge[^>]*>([^<]+)</.exec(c.text)
    c.socket.destroy()
    const fields = Object.fromEntries(Buffer.from(m[1], 'base64').toString().split(',').map((f) => [f[0], f.slice(2)]))
    return fields
  }
  try {
    const [a, b, none, none2] = [await firstAnswer('alice'), await firstAnswer('bob'), await firstAnswer('nobody'), await firstAnswer('nobody')]
    assert.notEqual(a.s, b.s)
    assert.equal(none.s, none2.s)
    assert.equal(none.s.length, a.s.length)
    assert.equal(none.i, a.i)
  } finally { await host.close() }
})

test('addressLimit false: failures from one address do not block another account', { skip }, async () => {
  const { host, port } = await start({ addressLimit: false })
  try {
    for (let i = 0; i < 3; i++) {
      const c = await opened(port)
      c.socket.write(plain(`n${2 * i}`, 'x') + plain(`n${2 * i + 1}`, 'x'))
      await c.until('not-authorized')
      c.socket.destroy()
    }
    const ok = await opened(port)
    ok.socket.write(plain('alice', 'alice-pw'))
    await ok.until('<success')
    ok.socket.destroy()
  } finally { await host.close() }
})

test('with the address limit on, one address is blocked after five failures', { skip }, async () => {
  const { host, port } = await start({})
  try {
    for (let i = 0; i < 3; i++) {
      const c = await opened(port)
      c.socket.write(plain(`n${2 * i}`, 'x') + plain(`n${2 * i + 1}`, 'x'))
      await sleep(30)
      c.socket.destroy()
    }
    const c = await opened(port)
    c.socket.write(plain('alice', 'alice-pw'))
    await c.until('temporary-auth-failure')
    c.socket.destroy()
  } finally { await host.close() }
})
