// Stanzas held for offline accounts: the caps, the sender rate, and what is written to the state.
import { test } from 'node:test'
import assert from 'node:assert/strict'
import net from 'node:net'
import { once } from 'node:events'
import { mkdtempSync, rmSync, readdirSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { randomBytes } from 'node:crypto'
import { setTimeout as sleep } from 'node:timers/promises'
import { createXmppServer, xmppServerOpsAvailable } from '../xmpp/server.mjs'
import { loadEngine } from '../bin/engine.mjs'

const engine = await loadEngine()
const { available } = await xmppServerOpsAvailable({ engine })
const skip = available ? false : 'the engine has no XMPP server ops'
const DOMAIN = 'localhost'
const ACCOUNTS = [{ username: 'alice', password: 'alice-pw' }, { username: 'bob', password: 'bob-pw' }, { username: 'carol', password: 'carol-pw' }]
const HEADER = `<?xml version='1.0'?><stream:stream to='${DOMAIN}' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>`

async function start (options) {
  const host = await createXmppServer({ domain: DOMAIN, accounts: ACCOUNTS, pollMs: 0, onError: () => {}, engine, ...options })
  await new Promise((resolve) => host.server.listen(0, '127.0.0.1', resolve))
  return { host, port: host.server.address().port }
}

async function bound (port, user) {
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
  socket.write(`<auth xmlns='urn:ietf:params:xml:ns:xmpp-sasl' mechanism='PLAIN'>${Buffer.from(`\0${user}\0${user}-pw`).toString('base64')}</auth>`)
  await c.until('<success'); c.text = ''
  socket.write(HEADER)
  await c.until('</stream:features>'); c.text = ''
  socket.write("<iq type='set' id='b'><bind xmlns='urn:ietf:params:xml:ns:xmpp-bind'><resource>r</resource></bind></iq>")
  await c.until('</iq>')
  // What was held comes with the bind result: keep what follows it.
  c.text = c.text.slice(c.text.indexOf('</iq>') + 5)
  return c
}
const say = (c, to, body, id = 'm') => c.socket.write(`<message to='${to}@${DOMAIN}' type='chat' id='${id}'><body>${body}</body></message>`)
const count = (text, word) => text.split(word).length - 1

test('a cap on stanzas per recipient: past it the sender gets resource-constraint, and the recipient gets what was held', { skip }, async () => {
  const { host, port } = await start({ heldLimits: { perAccount: 3 } })
  try {
    const a = await bound(port, 'alice')
    for (let i = 0; i < 5; i++) say(a, 'bob', `n${i}`, `m${i}`)
    await a.until('resource-constraint')
    await sleep(100)
    assert.equal(count(a.text, 'resource-constraint'), 2)
    const b = await bound(port, 'bob')
    await b.until('n2')
    assert.doesNotMatch(b.text, /n3|n4/)
    a.socket.destroy()
    b.socket.destroy()
  } finally { await host.close() }
})

test('a cap on bytes per recipient', { skip }, async () => {
  const { host, port } = await start({ heldLimits: { perAccountBytes: 2000 } })
  try {
    const a = await bound(port, 'alice')
    say(a, 'bob', 'x'.repeat(1500), 'big1')
    say(a, 'bob', 'x'.repeat(1500), 'big2')
    await a.until('resource-constraint')
    assert.match(a.text, /id="big2"/)
    say(a, 'carol', 'x'.repeat(1500), 'other')
    await sleep(100)
    assert.doesNotMatch(a.text, /id="other"/)
    a.socket.destroy()
  } finally { await host.close() }
})

test('a sender rate on held stanzas; another sender is not affected', { skip }, async () => {
  const { host, port } = await start({ heldLimits: { senderPerWindow: 2, senderWindow: 60 } })
  try {
    const a = await bound(port, 'alice')
    const c = await bound(port, 'carol')
    for (let i = 0; i < 4; i++) say(a, 'bob', `n${i}`, `m${i}`)
    await a.until('resource-constraint')
    await sleep(100)
    assert.equal(count(a.text, 'resource-constraint'), 2)
    say(c, 'bob', 'mine', 'c1')
    await sleep(100)
    assert.doesNotMatch(c.text, /resource-constraint/)
    a.socket.destroy(); c.socket.destroy()
  } finally { await host.close() }
})

test('a held stanza is one write of that stanza: a restart gives every stanza back in order, and the release deletes them', { skip }, async () => {
  const dir = mkdtempSync(join(tmpdir(), 'xmpp-held-'))
  const stateKey = randomBytes(32).toString('hex')
  try {
    let { host, port } = await start({ dir, stateKey })
    const a = await bound(port, 'alice')
    for (let i = 0; i < 12; i++) say(a, 'bob', `n${i}.`, `m${i}`)
    await sleep(300)
    a.socket.destroy()
    await host.close()
    ;({ host, port } = await start({ dir, stateKey }))
    const b = await bound(port, 'bob')
    await b.until('n11.')
    const seen = [...b.text.matchAll(/<body>n(\d+)\.<\/body>/g)].map((m) => Number(m[1]))
    assert.deepEqual(seen, [...Array(12).keys()])
    b.socket.destroy()
    await host.close()
    ;({ host, port } = await start({ dir, stateKey }))
    const again = await bound(port, 'bob')
    await sleep(200)
    assert.doesNotMatch(again.text, /<body>/)
    again.socket.destroy()
    await host.close()
    assert.ok(readdirSync(dir).length > 0)
  } finally { rmSync(dir, { recursive: true, force: true }) }
})

test('only an account has a queue: another name gets service-unavailable, and nothing is held', { skip }, async () => {
  const { host, port } = await start({})
  try {
    const a = await bound(port, 'alice')
    say(a, 'nobody', 'x', 'g1')
    await a.until('service-unavailable')
    assert.match(a.text, /id="g1"/)
    a.text = ''
    a.socket.write("<message to='someone@other.example' type='chat' id='g2'><body>x</body></message>")
    await a.until('service-unavailable')
    a.text = ''
    a.socket.write("<presence to='nobody@localhost' type='subscribe'/>")
    say(a, 'bob', 'real', 'g3')
    await sleep(100)
    assert.doesNotMatch(a.text, /service-unavailable|resource-constraint/)
    a.socket.destroy()
    const b = await bound(port, 'bob')
    await b.until('real')
    b.socket.destroy()
  } finally { await host.close() }
})

test('presence that says who is online does not wait for an offline contact', { skip }, async () => {
  const { host, port } = await start({})
  try {
    const a = await bound(port, 'alice')
    a.socket.write("<presence to='bob@localhost'/>")
    say(a, 'bob', 'real', 'g1')
    await sleep(100)
    a.socket.destroy()
    const b = await bound(port, 'bob')
    await b.until('real')
    assert.doesNotMatch(b.text, /<presence/)
    b.socket.destroy()
  } finally { await host.close() }
})

test('roster writes have a rate; a read still works', { skip }, async () => {
  const { host, port } = await start({ heldLimits: { senderPerWindow: 3, senderWindow: 60 } })
  try {
    const a = await bound(port, 'alice')
    for (let i = 0; i < 5; i++) a.socket.write(`<iq type='set' id='r${i}'><query xmlns='jabber:iq:roster'><item jid='u${i}@localhost'/></query></iq>`)
    await a.until('resource-constraint')
    await sleep(100)
    assert.equal(count(a.text, 'resource-constraint'), 2)
    a.text = ''
    a.socket.write("<iq type='get' id='g'><query xmlns='jabber:iq:roster'/></iq>")
    await a.until('u2@localhost')
    assert.doesNotMatch(a.text, /u3@localhost/)
    a.socket.destroy()
  } finally { await host.close() }
})
