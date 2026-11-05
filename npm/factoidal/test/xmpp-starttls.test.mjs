// test/xmpp-starttls.test.mjs — STARTTLS (RFC 6120 section 5) in the Node
// XMPP host (`xmpp/server.mjs`) against the Lean engine in wasm, over REAL
// sockets and a real TLS handshake.
//
// Every decision is `L4Factoidal.XMPP.Server.stepPreTls` and the drain of
// `Wasm/Ops/XmppSession.lean`; the theorems they carry are
// `steps_requiresStartTls`, `step_tlsPending`, `stepPreTls_startTls`,
// `tlsEstablished_spec`, `bufferAfter_startTls` and `drain_tlsPending`.
// These cases check the same properties through the host:
//
//   * the first features offer STARTTLS as required and no SASL mechanism;
//   * `<auth/>` in clear is `policy-violation` and the connection closes;
//   * bytes injected after `<starttls/>` in the same TCP write are
//     discarded, not read as part of the secured stream (CVE-2011-0411);
//   * after the handshake the new stream offers SASL, and PLAIN and bind
//     work over TLS;
//   * `xmppSessionTlsUp` is refused when no STARTTLS is pending.
//
// The certificate is a throwaway self-signed one made by `openssl` in a
// temporary directory. A missing `openssl` FAILS the cases, never skips
// them (https://github.com/danbri/factoidal/issues/1038, P2).

import { test } from 'node:test'
import assert from 'node:assert/strict'
import net from 'node:net'
import tls from 'node:tls'
import { execFileSync } from 'node:child_process'
import { mkdtemp, readFile, rm } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import { join } from 'node:path'

const DOMAIN = 'example.com'
const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_TLS = 'urn:ietf:params:xml:ns:xmpp-tls'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const ACCOUNTS = [{ username: 'juliet', password: 'r0m30' }]

const streamOpen = () =>
  `<?xml version='1.0'?><stream:stream to='${DOMAIN}' xmlns='jabber:client'` +
  ` xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>`
const plainAuth = (user, pw) =>
  `<auth xmlns='${NS_SASL}' mechanism='PLAIN'>` +
  Buffer.from(`\0${user}\0${pw}`, 'utf8').toString('base64') + '</auth>'

const serverModule = await import('../xmpp/server.mjs')

async function makeCert () {
  const dir = await mkdtemp(join(tmpdir(), 'l4xmpp-starttls-'))
  execFileSync('openssl', ['req', '-x509', '-newkey', 'rsa:2048', '-nodes', '-sha256',
    '-days', '1', '-subj', `/CN=${DOMAIN}`,
    '-keyout', join(dir, 'key.pem'), '-out', join(dir, 'cert.pem')], { stdio: 'ignore' })
  return {
    dir,
    cert: await readFile(join(dir, 'cert.pem')),
    key: await readFile(join(dir, 'key.pem'))
  }
}

/** A client over any duplex socket: write text, wait for a needle. */
function client (socket) {
  let buffer = ''
  const waiters = []
  socket.setEncoding('utf8')
  socket.on('data', (chunk) => { buffer += chunk; for (const w of waiters.splice(0)) w() })
  return {
    socket,
    get received () { return buffer },
    reset () { buffer = '' },
    write (text) { socket.write(text) },
    waitFor (needle, ms = 15000) {
      return new Promise((resolve, reject) => {
        const t0 = Date.now()
        const tick = () => {
          if (buffer.includes(needle)) return resolve(buffer)
          if (Date.now() - t0 > ms) return reject(new Error(`timed out waiting for ${needle}\ngot: ${buffer}`))
          waiters.push(tick)
          setTimeout(tick, 50)
        }
        tick()
      })
    },
    closed () {
      return new Promise((resolve) => {
        if (socket.destroyed) return resolve()
        socket.once('close', resolve)
      })
    }
  }
}

async function startServer (cert) {
  return serverModule.listen({
    domain: DOMAIN, accounts: ACCOUNTS, startTls: true, cert: cert.cert, key: cert.key,
    pollMs: 0, onError: () => {}
  })
}

test('starttls: engine refuses the handshake report when none is pending', async () => {
  const server = await serverModule.openXmppServer({ domain: DOMAIN, accounts: ACCOUNTS })
  try {
    const session = server.openSession({ startTls: true })
    assert.throws(() => session.tlsUp(), /no STARTTLS is pending/)
    const answer = session.feed(streamOpen() + `<starttls xmlns='${NS_TLS}'/>` + plainAuth('juliet', 'r0m30'))
    assert.equal(answer.startTls, true)
    assert.equal(answer.stage, 'tlsPending')
    // The injected <auth/> is gone: nothing buffered, no SASL answer.
    assert.equal(answer.bufferedBytes, 0)
    assert.ok(!answer.send.join('').includes('success'))
    // While the handshake runs, a feed reads nothing.
    const during = session.feed(plainAuth('juliet', 'r0m30'))
    assert.deepEqual(during.send, [])
    assert.equal(during.stage, 'tlsPending')
    session.close()
  } finally { server.close() }
})

test('starttls: first features are STARTTLS required, no SASL; auth in clear is refused', async () => {
  const cert = await makeCert()
  const server = await startServer(cert)
  try {
    const c = client(net.connect(server.port, '127.0.0.1'))
    c.write(streamOpen())
    const features = await c.waitFor('</stream:features>')
    assert.match(features, /<starttls xmlns="urn:ietf:params:xml:ns:xmpp-tls"><required\/><\/starttls>/)
    assert.ok(!features.includes('mechanism'), 'no SASL mechanism before TLS')
    c.reset()
    c.write(plainAuth('juliet', 'r0m30'))
    await c.waitFor('policy-violation')
    assert.ok(!c.received.includes('<success'))
    await c.closed()
  } finally {
    await server.close()
    await rm(cert.dir, { recursive: true, force: true })
  }
})

test('starttls: handshake, injected plaintext discarded, then SASL and bind over TLS', async () => {
  const cert = await makeCert()
  const server = await startServer(cert)
  try {
    const raw = net.connect(server.port, '127.0.0.1')
    const c = client(raw)
    c.write(streamOpen())
    await c.waitFor('</stream:features>')
    c.reset()
    // An attacker on the path appends an <auth/> to the client's
    // <starttls/>, in the same TCP segment.
    c.write(`<starttls xmlns='${NS_TLS}'/>` + plainAuth('juliet', 'r0m30'))
    await c.waitFor('<proceed')
    raw.removeAllListeners('data')

    const secure = tls.connect({ socket: raw, servername: DOMAIN, rejectUnauthorized: false })
    await new Promise((resolve, reject) => { secure.once('secureConnect', resolve); secure.once('error', reject) })
    const s = client(secure)
    s.write(streamOpen())
    const features = await s.waitFor('</stream:features>')
    // The injected <auth/> was not read: the new stream offers SASL and
    // nothing was authenticated.
    assert.ok(features.includes('SCRAM-SHA-256'), features)
    assert.ok(!features.includes('starttls'))
    assert.ok(!features.includes('<success'))
    s.reset()
    s.write(plainAuth('juliet', 'r0m30'))
    await s.waitFor('<success')
    s.reset()
    s.write(streamOpen())
    await s.waitFor('</stream:features>')
    s.reset()
    s.write(`<iq type='set' id='b1'><bind xmlns='${NS_BIND}'><resource>tls</resource></bind></iq>`)
    await s.waitFor('juliet@example.com/tls')
    secure.end()
  } finally {
    await server.close()
    await rm(cert.dir, { recursive: true, force: true })
  }
})

test('starttls: directTlsPort serves direct TLS in the same server', async () => {
  const cert = await makeCert()
  const server = await serverModule.listen({
    domain: DOMAIN, accounts: ACCOUNTS, startTls: true, directTlsPort: 0, cert: cert.cert, key: cert.key,
    pollMs: 0, onError: () => {}
  })
  try {
    const port = server.directServer.address().port
    assert.equal(server.directOrigin, `xmpps://127.0.0.1:${port}`)
    // In clear the first port still offers only STARTTLS.
    const clear = client(net.connect(server.port, '127.0.0.1'))
    clear.write(streamOpen())
    const first = await clear.waitFor('</stream:features>')
    assert.ok(!first.includes('mechanism'), 'no SASL mechanism before TLS')
    clear.socket.destroy()
    // The direct port offers SASL at once, with no STARTTLS, and logs in.
    const c = client(tls.connect({ port, host: '127.0.0.1', rejectUnauthorized: false }))
    c.write(streamOpen())
    const features = await c.waitFor('</stream:features>')
    assert.ok(!features.includes('starttls'), 'STARTTLS is not offered on direct TLS')
    assert.match(features, /PLAIN/)
    c.reset()
    c.write(plainAuth('juliet', 'r0m30'))
    await c.waitFor('<success')
    c.socket.destroy()
    // A raw client on the direct port never gets a stream.
    const raw = client(net.connect(port, '127.0.0.1'))
    raw.write(streamOpen())
    await raw.closed()
    assert.ok(!raw.received.includes('stream:features'))
  } finally {
    await server.close()
    await rm(cert.dir, { recursive: true, force: true })
  }
})

test('starttls: requires cert and key', async () => {
  await assert.rejects(serverModule.createXmppServer({ domain: DOMAIN, startTls: true }),
    /STARTTLS requires both cert and key/)
})
