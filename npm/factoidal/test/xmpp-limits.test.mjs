// Transport limits of the XMPP host: connections, login time, and a client that stops reading.
import { test } from 'node:test'
import assert from 'node:assert/strict'
import net from 'node:net'
import { once } from 'node:events'
import { setTimeout as sleep } from 'node:timers/promises'
import { createXmppServer } from '../xmpp/server.mjs'

const DOMAIN = 'localhost'
const ACCOUNTS = [{ username: 'alice', password: 'alice-pw' }, { username: 'bob', password: 'bob-pw' }]
const HEADER = `<?xml version='1.0'?><stream:stream to='${DOMAIN}' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>`

async function start (options) {
  const host = await createXmppServer({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, ...options })
  await new Promise((resolve) => host.server.listen(0, '127.0.0.1', resolve))
  return { host, port: host.server.address().port }
}

function client (port) {
  const socket = net.connect(port, '127.0.0.1')
  const c = { socket, text: '', ended: false }
  socket.setEncoding('utf8')
  socket.on('data', (d) => { c.text += d })
  socket.on('close', () => { c.ended = true })
  socket.on('error', () => { c.ended = true })
  c.until = async (word, ms = 3000) => {
    const end = Date.now() + ms
    while (!c.text.includes(word) && Date.now() < end) await sleep(5)
    assert.ok(c.text.includes(word), `wanted ${word}, got ${c.text.slice(-200)}`)
    c.text = ''
  }
  c.closed = async (ms = 2000) => {
    const end = Date.now() + ms
    while (!c.ended && Date.now() < end) await sleep(5)
    return c.ended
  }
  return c
}

async function bound (port, user, password) {
  const c = client(port)
  await once(c.socket, 'connect')
  c.socket.write(HEADER)
  await c.until('</stream:features>')
  c.socket.write(`<auth xmlns='urn:ietf:params:xml:ns:xmpp-sasl' mechanism='PLAIN'>${Buffer.from(`\0${user}\0${password}`).toString('base64')}</auth>`)
  await c.until('<success')
  c.socket.write(HEADER)
  await c.until('</stream:features>')
  c.socket.write("<iq type='set' id='b'><bind xmlns='urn:ietf:params:xml:ns:xmpp-bind'><resource>r</resource></bind></iq>")
  await c.until('</iq>')
  return c
}

test('a connection over the limit is closed, and a place comes back', async () => {
  const { host, port } = await start({ maxConnections: 2, loginTimeoutMs: 0 })
  const a = client(port); const b = client(port)
  await Promise.all([once(a.socket, 'connect'), once(b.socket, 'connect')])
  await sleep(50)
  const c = client(port)
  assert.equal(await c.closed(), true)
  a.socket.destroy()
  await a.closed()
  await sleep(50)
  const d = client(port)
  await once(d.socket, 'connect')
  d.socket.write(HEADER)
  await d.until('</stream:features>')
  b.socket.destroy(); d.socket.destroy()
  await host.close()
})

test('a connection that does not log in is closed; one that does stays', async () => {
  const { host, port } = await start({ loginTimeoutMs: 150 })
  const idle = client(port)
  const partial = client(port)
  await once(partial.socket, 'connect')
  partial.socket.write(HEADER.slice(0, 20))
  const logged = await bound(port, 'alice', 'alice-pw')
  assert.equal(await idle.closed(), true)
  assert.equal(await partial.closed(), true)
  await sleep(250)
  assert.equal(logged.ended, false)
  logged.socket.destroy()
  await host.close()
})

test('a client that stops reading is closed, and its sender is not', async () => {
  const { host, port } = await start({ maxQueuedBytes: 64 * 1024 })
  const slow = await bound(port, 'bob', 'bob-pw')
  slow.socket.pause()
  const sender = await bound(port, 'alice', 'alice-pw')
  const body = 'x'.repeat(60000)
  for (let i = 0; i < 400 && host.sessions().length === 2; i++) {
    sender.socket.write(`<message to='bob@${DOMAIN}/r' type='chat'><body>${body}</body></message>`)
    await sleep(2)
  }
  assert.equal(host.sessions().length, 1)
  assert.equal(host.sessions()[0].bare, `alice@${DOMAIN}`)
  assert.equal(sender.ended, false)
  sender.socket.destroy(); slow.socket.destroy()
  await host.close()
})

test('a limit that is not a nonnegative integer is refused', async () => {
  for (const options of [{ maxConnections: -1 }, { loginTimeoutMs: 1.5 }, { maxQueuedBytes: -2 }]) {
    await assert.rejects(createXmppServer({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, ...options }), /nonnegative safe integer/)
  }
})
