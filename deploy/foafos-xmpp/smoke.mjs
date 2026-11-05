// Tests the public service from outside, with a third-party client library.
// Usage: npm install --no-save @xmpp/client ws
//        node smoke.mjs ~/.config/foafos-xmpp-fly/accounts [--idle SECONDS]
// It prints no password. Exit code 1 means a check failed.
import { readFileSync } from 'node:fs'
import net from 'node:net'
import tls from 'node:tls'
import { client, xml } from '@xmpp/client'
import WebSocket from 'ws'

const HOST = process.env.XMPP_HOST || 'foafos-xmpp.fly.dev'
const ROOM = `smoke-${process.pid}@rooms.${HOST}`
const [file, flag, idleArg] = process.argv.slice(2)
if (!file) throw new Error('usage: node smoke.mjs ACCOUNTS_FILE [--idle SECONDS]')
const idle = flag === '--idle' ? Number(idleArg) : 0
const pw = Object.fromEntries(readFileSync(file, 'utf8').trim().split('\n').map((l) => {
  const i = l.indexOf(':'); return [l.slice(0, i), l.slice(i + 1)]
}))

let failed = 0
async function check (name, fn) {
  try { const note = await fn(); console.log(`PASS ${name}${note ? ': ' + note : ''}`) } catch (e) {
    failed++; console.log(`FAIL ${name}: ${e.message}`)
  }
}
const timeout = (ms, what) => new Promise((_resolve, reject) => setTimeout(() => reject(new Error(`timed out: ${what}`)), ms).unref())

function login (service, username, password, resource) {
  const x = client({ service, domain: HOST, username, password, resource })
  x.on('error', () => {})
  return x
}
async function online (x) { await Promise.race([x.start(), timeout(20000, 'login')]); return x }

/** Raw bytes to a port: the transcript until `needle` or the close. */
function rawExchange (socket, send, until) {
  return new Promise((resolve) => {
    let got = ''
    const done = () => { socket.destroy(); resolve(got) }
    socket.setEncoding('utf8')
    socket.on('data', (d) => { got += d; if (until.test(got)) done() })
    socket.on('close', done)
    socket.on('error', done)
    setTimeout(done, 8000).unref()
    if (send) socket.write(send)
  })
}
const open = `<?xml version='1.0'?><stream:stream to='${HOST}' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>`

await check('direct TLS 5223: certificate valid for the name', () => new Promise((resolve, reject) => {
  const s = tls.connect({ host: HOST, port: 5223, servername: HOST })
  s.once('secureConnect', () => {
    const c = s.getPeerCertificate()
    resolve(`${s.getProtocol()}, issuer ${c.issuer.O} ${c.issuer.CN}, valid to ${c.valid_to}`)
    s.destroy()
  })
  s.once('error', reject)
}))

await check('login: direct TLS 5223', async () => {
  const x = await online(login(`xmpps://${HOST}:5223`, 'test1', pw.test1, 'smoke-direct'))
  const jid = String(x.jid); await x.stop(); return jid
})
await check('login: STARTTLS 5222', async () => {
  const x = await online(login(`xmpp://${HOST}:5222`, 'test1', pw.test1, 'smoke-starttls'))
  const jid = String(x.jid); await x.stop(); return jid
})
await check('wrong password refused', async () => {
  const x = login(`xmpps://${HOST}:5223`, 'test1', 'wrong-' + pw.test1, 'smoke-bad')
  let error = null
  try { await Promise.race([x.start(), timeout(20000, 'refusal')]) } catch (e) { error = e }
  try { await x.stop() } catch { /* gone */ }
  if (!error || !/not-authorized/.test(String(error.condition || error.message))) throw new Error(`no refusal: ${error}`)
  return error.condition
})
await check('unknown account refused', async () => {
  const x = login(`xmpps://${HOST}:5223`, 'nobody', pw.test1, 'smoke-bad')
  let error = null
  try { await Promise.race([x.start(), timeout(20000, 'refusal')]) } catch (e) { error = e }
  try { await x.stop() } catch { /* gone */ }
  if (!error || !/not-authorized/.test(String(error.condition || error.message))) throw new Error(`no refusal: ${error}`)
  return error.condition
})
await check('plaintext 5222: features offer no SASL mechanism', async () => {
  const got = await rawExchange(net.connect(5222, HOST), open, /<\/stream:features>/)
  if (!/<required\/>/.test(got) || /mechanism/.test(got)) throw new Error('STARTTLS is not required')
  return 'STARTTLS required'
})
// A made-up password: a real one must never cross in clear, even in a test.
await check('plaintext 5222: login in clear refused', async () => {
  const auth = `<auth xmlns='urn:ietf:params:xml:ns:xmpp-sasl' mechanism='PLAIN'>${Buffer.from('\0test1\0not-the-password').toString('base64')}</auth>`
  const got = await rawExchange(net.connect(5222, HOST), open + auth, /policy-violation|<success|<\/stream:stream>/)
  if (/<success/.test(got) || !/policy-violation/.test(got)) throw new Error('not refused')
  return 'policy-violation'
})
await check('plaintext 5223: no stream', async () => {
  const got = await rawExchange(net.connect(5223, HOST), open, /stream:features/)
  if (/stream:features/.test(got)) throw new Error('a stream opened in clear')
})
await check('plaintext 443: no stream', async () => {
  const got = await rawExchange(net.connect(443, HOST), 'GET /xmpp-websocket HTTP/1.1\r\nHost: x\r\n\r\n', /HTTP\/1|stream/)
  if (/HTTP\/1|stream/.test(got)) throw new Error('answered in clear')
})

await check('two clients exchange a message in a room', async () => {
  const a = await online(login(`xmpps://${HOST}:5223`, 'test1', pw.test1, 'smoke-a'))
  const b = await online(login(`xmpp://${HOST}:5222`, 'test2', pw.test2, 'smoke-b'))
  const joined = (x, nick) => new Promise((resolve) => {
    x.on('stanza', (s) => { if (s.is('presence') && s.attrs.from === `${ROOM}/${nick}`) resolve() })
    x.send(xml('presence', { to: `${ROOM}/${nick}` }, xml('x', { xmlns: 'http://jabber.org/protocol/muc' })))
  })
  await Promise.race([joined(a, 'alice'), timeout(10000, 'join a')])
  await Promise.race([joined(b, 'bob'), timeout(10000, 'join b')])
  const text = `hello ${Date.now()}`
  const heard = new Promise((resolve) => b.on('stanza', (s) => {
    if (s.is('message') && s.attrs.type === 'groupchat' && s.getChildText('body') === text) resolve(s.attrs.from)
  }))
  await a.send(xml('message', { to: ROOM, type: 'groupchat' }, xml('body', {}, text)))
  const from = await Promise.race([heard, timeout(10000, 'message')])
  if (idle > 0) {
    await new Promise((resolve) => setTimeout(resolve, idle * 1000))
    const later = `later ${Date.now()}`
    const again = new Promise((resolve) => b.on('stanza', (s) => { if (s.getChildText?.('body') === later) resolve() }))
    await a.send(xml('message', { to: ROOM, type: 'groupchat' }, xml('body', {}, later)))
    await Promise.race([again, timeout(10000, 'message after idle')])
  }
  await a.stop(); await b.stop()
  return `from ${from}${idle ? `, and again after ${idle} s idle` : ''}`
})

const wsOpen = (origin) => new Promise((resolve) => {
  const options = origin ? { origin } : {}
  const s = new WebSocket(`wss://${HOST}/xmpp-websocket`, 'xmpp', options)
  s.on('open', () => { resolve({ status: 101, socket: s }) })
  s.on('unexpected-response', (_q, res) => { resolve({ status: res.statusCode }); s.terminate() })
  s.on('error', (e) => resolve({ status: 0, error: e.message }))
})
for (const origin of ['https://danbri.github.io', 'http://localhost:8080']) {
  await check(`wss 443: Origin ${origin} accepted, SASL offered`, async () => {
    const r = await wsOpen(origin)
    if (r.status !== 101) throw new Error(`status ${r.status} ${r.error || ''}`)
    const text = await new Promise((resolve, reject) => {
      r.socket.on('message', (m) => { if (/mechanism/.test(String(m))) resolve(String(m)) })
      r.socket.on('close', () => reject(new Error('closed')))
      r.socket.send(`<open xmlns='urn:ietf:params:xml:ns:xmpp-framing' to='${HOST}' version='1.0'/>`)
    })
    r.socket.terminate()
    return text.match(/<mechanism>[^<]+/g).map((m) => m.slice(11)).join(' ')
  })
}
for (const origin of ['https://evil.example', 'https://danbri.github.io.evil.example', 'http://danbri.github.io', null]) {
  await check(`wss 443: Origin ${origin} refused`, async () => {
    const r = await wsOpen(origin)
    if (r.status === 101) { r.socket.terminate(); throw new Error('accepted') }
    return `status ${r.status}`
  })
}
console.log(failed === 0 ? 'ALL PASS' : `${failed} FAILED`)
process.exit(failed === 0 ? 0 : 1)
