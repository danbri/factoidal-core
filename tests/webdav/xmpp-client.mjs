// A minimal XMPP test client that sends HTTP over XMPP (XEP-0332) requests,
// shared by tests/webdav/xmpp.mjs and tests/hub/hub_webdav_test.mjs
// (https://github.com/danbri/factoidal/issues/1107). It is test code: it
// writes the stanza text by hand (SASL PLAIN over the test
// listener, then `req` iqs) and reads the `resp` iqs with regular
// expressions. It is not part of the package.

import net from 'node:net'
import tls from 'node:tls'

const NS_SASL = 'urn:ietf:params:xml:ns:xmpp-sasl'
const NS_BIND = 'urn:ietf:params:xml:ns:xmpp-bind'
const NS_HTTP = 'urn:xmpp:http'
const NS_SHIM = 'http://jabber.org/protocol/shim'

/** A minimal XMPP client for the test: one socket, a text buffer, and
 *  "wait until the buffer matches". */
export class TestClient {
  /** `ca`: PEM to trust for direct TLS (XEP-0368); without it, plain TCP. */
  constructor (port, domain, ca = null) {
    this.domain = domain
    this.buffer = ''
    this.waiters = []
    this.socket = ca === null
      ? net.connect({ host: '127.0.0.1', port })
      : tls.connect({ host: '127.0.0.1', port, servername: domain, ca })
    this.socket.setEncoding('utf8')
    this.socket.on('data', (t) => { this.buffer += t; this.poll() })
    this.socket.on('error', () => {})
  }

  poll () {
    for (const w of this.waiters.slice()) {
      const m = w.re.exec(this.buffer)
      if (m) {
        this.buffer = this.buffer.slice(m.index + m[0].length)
        this.waiters.splice(this.waiters.indexOf(w), 1)
        clearTimeout(w.timer)
        w.resolve(m)
      }
    }
  }

  wait (re, ms = 30000) {
    return new Promise((resolve, reject) => {
      const w = { re, resolve, timer: setTimeout(() => reject(new Error(`timeout waiting for ${re}; buffer: ${this.buffer.slice(0, 400)}`)), ms) }
      this.waiters.push(w)
      this.poll()
    })
  }

  send (text) { this.socket.write(text) }

  header () {
    this.send(`<?xml version='1.0'?><stream:stream xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' to='${this.domain}' version='1.0'>`)
  }

  async login (user, password) {
    this.header()
    await this.wait(/<\/stream:features>/)
    const plain = Buffer.from(`\u0000${user}\u0000${password}`).toString('base64')
    this.send(`<auth xmlns='${NS_SASL}' mechanism='PLAIN'>${plain}</auth>`)
    await this.wait(/<success[^>]*\/>|<success[\s\S]*?<\/success>/)
    this.buffer = ''
    this.header()
    await this.wait(/<\/stream:features>/)
    this.send(`<iq type='set' id='b1'><bind xmlns='${NS_BIND}'><resource>t</resource></bind></iq>`)
    await this.wait(/<iq[^>]*id="b1"[\s\S]*?<\/iq>/)
  }

  close () { this.socket.destroy() }
}

let serial = 0

/** One XEP-0332 request; resolves with `{status, iq, chunks}`. */
export async function request (c, target, method, resource, { headers = [], data = '', chunks = 0 } = {}) {
  serial += 1
  const id = `r${serial}`
  const hs = headers.map(([n, v]) => `<header name='${n}'>${v}</header>`).join('')
  c.send(`<iq type='set' id='${id}' to='${target}'><req xmlns='${NS_HTTP}' method='${method}' resource='${resource}' version='1.1'>` +
    `<headers xmlns='${NS_SHIM}'>${hs}</headers>${data}</req></iq>`)
  const m = await c.wait(new RegExp(`<iq[^>]*id="${id}"[^>]*?(?:/>|>[\\s\\S]*?</iq>)`))
  const iq = m[0]
  const status = /statusCode="(\d+)"/.exec(iq)
  const got = []
  for (let i = 0; i < chunks; i += 1) {
    const cm = await c.wait(/<message[\s\S]*?<\/message>/)
    got.push(cm[0])
  }
  return { status: status ? Number(status[1]) : null, iq, chunks: got }
}
