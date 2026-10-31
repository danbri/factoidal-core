import test from 'node:test'
import assert from 'node:assert/strict'
import { lwsSbm11Reader } from '../index.mjs'

function fixture (base = 'https://storage.invalid/container/', options = {}) {
  const calls = []
  const reader = lwsSbm11Reader(base, {
    auth: 'Bearer LOCAL_TEST_SENTINEL',
    transport (url, headers) {
      calls.push({ url, headers })
      return { status: 206, header: name => name === 'etag' ? '"test"' : name === 'content-range' ? 'bytes 0-0/1' : null, bytes: new Uint8Array([7]) }
    },
    ...options,
  })
  return { reader, calls }
}

test('resource names cannot move authority or escape the container before transport', () => {
  for (const file of [
    '//attacker.invalid/steal', '/private', 'https://attacker.invalid/steal',
    '../private', 'gen/../../private', '.', '..', 'gen/./CURRENT',
    'gen\\private', '\\attacker.invalid\\private', 'gen//CURRENT', '',
    '%2e%2e/private', 'gen/%2E%2e/private', '%252e%252e/private',
    'gen%2fprivate', 'gen%252fprivate', '%2f%2fattacker.invalid/steal',
    'gen%5cprivate', 'file?token=x', 'file#fragment', 'file%3ftoken=x', 'file%23fragment',
    'nul\0file', 'line\nfile', 'file%00', null, 1,
  ]) {
    const { reader, calls } = fixture()
    try {
      assert.equal(reader.size(file), null, `size ${JSON.stringify(file)}`)
      assert.equal(reader.readAt(file, 0, 1), null, `read ${JSON.stringify(file)}`)
      assert.equal(reader.readAt(file, 0, 0), null, `zero read ${JSON.stringify(file)}`)
      assert.deepEqual(calls, [], 'no credential-bearing transport call')
      assert.ok(reader.errors().length > 0)
    } finally { reader.close() }
  }
})

test('ordinary nested names and encoded filename bytes retain scoped authorization', () => {
  const { reader, calls } = fixture('https://storage.invalid/container')
  try {
    for (const file of ['CURRENT', 'gen/manifest.sbm11', 'a b/é.nt', '100%.bin', 'literal%20name.nt']) {
      assert.equal(reader.size(file), 1)
      const call = calls.at(-1), url = new URL(call.url)
      assert.equal(url.origin, 'https://storage.invalid')
      assert.ok(url.pathname.startsWith('/container/'))
      assert.equal(url.search, ''); assert.equal(url.hash, '')
      assert.equal(call.headers.authorization, 'Bearer LOCAL_TEST_SENTINEL')
      assert.equal(call.url, 'https://storage.invalid/container/' + file.split('/').map(encodeURIComponent).join('/'))
    }
  } finally { reader.close() }
})

test('ambiguous container credentials, query, fragment and non-HTTP schemes fail at construction', () => {
  for (const base of [
    'https://storage.invalid/container?token=secret',
    'https://storage.invalid/container/#fragment',
    'https://storage.invalid/container/?', 'https://storage.invalid/container/#',
    'https://user:secret@storage.invalid/container/',
    'file:///private/', 'data:text/plain,x', 'not an absolute URL',
  ]) assert.throws(() => fixture(base), TypeError, base)
})

test('default Node transport refuses same-origin and cross-origin redirects before following', async () => {
  const { Worker } = await import('node:worker_threads')
  const counts = new SharedArrayBuffer(12), hits = new Int32Array(counts)
  const server = new Worker(`
    const {parentPort,workerData}=require('node:worker_threads');
    const http=require('node:http'),hits=new Int32Array(workerData);
    const destination=http.createServer((_q,r)=>{Atomics.add(hits,2,1);r.end('secret');});
    destination.listen(0,'127.0.0.1',()=>{
      const source=http.createServer((q,r)=>{
        if(q.url==='/outside'){Atomics.add(hits,1,1);r.end('secret');return;}
        Atomics.add(hits,0,1);r.statusCode=302;
        r.setHeader('Location',q.url.startsWith('/cross/')?'http://127.0.0.1:'+destination.address().port+'/outside':'/outside');r.end();
      });
      source.listen(0,'127.0.0.1',()=>parentPort.postMessage(source.address().port));
    });
  `, { eval: true, workerData: counts })
  try {
    const port = await new Promise((resolve, reject) => { server.once('message', resolve); server.once('error', reject) })
    for (const route of ['same', 'cross']) {
      const reader = lwsSbm11Reader(`http://127.0.0.1:${port}/${route}/`, { auth: 'Bearer LOCAL_TEST_SENTINEL', headers: { 'X-Private-Test': 'LOCAL_TEST_SENTINEL' }, timeoutMs: 5000 })
      try { assert.equal(reader.size('CURRENT'), null); assert.ok(reader.errors().length > 0) } finally { reader.close() }
    }
    assert.equal(Atomics.load(hits, 0), 2)
    assert.equal(Atomics.load(hits, 1), 0, 'same-origin redirect target was not requested')
    assert.equal(Atomics.load(hits, 2), 0, 'cross-origin redirect target was not requested')
  } finally { await server.terminate() }
})

test('browser default refuses caller headers before XHR; redirect checking alone is post-request', async () => {
  const { lwsSbm11Reader: browserReader } = await import('../lib/sbm11-lws.mjs')
  const original = globalThis.XMLHttpRequest
  let created = 0, sent = 0
  globalThis.XMLHttpRequest = class {
    constructor () { created++ }
    open (_method, url) { this.url = url }
    setRequestHeader () {}
    send () { sent++; this.responseURL = 'https://elsewhere.invalid/redirected'; this.response = new ArrayBuffer(1); this.status = 200 }
    getResponseHeader () { return null }
  }
  try {
    for (const options of [{ auth: 'Bearer LOCAL_TEST_SENTINEL' }, { headers: { 'X-Private-Test': 'LOCAL_TEST_SENTINEL' } }]) {
      assert.throws(() => browserReader('https://storage.invalid/container/', options), TypeError)
    }
    assert.equal(created, 0, 'no credential-bearing XHR constructed')
    const reader = browserReader('https://storage.invalid/container/')
    try { assert.equal(reader.size('CURRENT'), null); assert.equal(sent, 1); assert.match(reader.errors()[0], /redirect/i) } finally { reader.close() }
  } finally {
    if (original === undefined) delete globalThis.XMLHttpRequest
    else globalThis.XMLHttpRequest = original
  }
})
