// The shape of a stanza: the limits on depth and on the number of elements.
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
const HEADER = "<?xml version='1.0'?><stream:stream to='localhost' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>"

async function bound (port, user) {
  const socket = net.connect(port, '127.0.0.1')
  const c = { socket, text: '', ended: false }
  socket.setEncoding('utf8')
  socket.on('data', (d) => { c.text += d })
  socket.on('close', () => { c.ended = true })
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
  await c.until('</iq>'); c.text = ''
  return c
}

test('a stanza within the limits goes through; one past a limit ends the stream; other clients go on', { skip }, async () => {
  const accounts = [{ username: 'alice', password: 'alice-pw' }, { username: 'bob', password: 'bob-pw' }]
  const host = await createXmppServer({ domain: 'localhost', accounts, pollMs: 0, onError: () => {}, engine })
  await new Promise((resolve) => host.server.listen(0, '127.0.0.1', resolve))
  const port = host.server.address().port
  const open = (n) => '<x>'.repeat(n); const close = (n) => '</x>'.repeat(n)
  try {
    const a = await bound(port, 'alice')
    const b = await bound(port, 'bob')
    a.socket.write(`<message to='bob@localhost' type='chat'><body>fine</body>${open(20)}${close(20)}</message>`)
    await b.until('fine')
    a.socket.write(`<message to='bob@localhost' type='chat'>${open(80)}${close(80)}</message>`)
    await a.until('not-well-formed')
    const c = await bound(port, 'alice')
    c.socket.write(`<message to='bob@localhost' type='chat'>${'<y/>'.repeat(9000)}</message>`)
    await c.until('not-well-formed')
    const d = await bound(port, 'alice')
    d.socket.write("<message to='bob@localhost' type='chat'><body>still here</body></message>")
    await b.until('still here')
    a.socket.destroy(); b.socket.destroy(); c.socket.destroy(); d.socket.destroy()
  } finally { await host.close() }
})
