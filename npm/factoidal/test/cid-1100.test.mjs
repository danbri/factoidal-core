// Controlled Identifiers v1.0: cidValidate and cidRetrieveVerificationMethod
// (https://github.com/danbri/factoidal/issues/1100, items 7 and 9).
// The engine decides every answer (formal/lean4/L4Factoidal/CID/Validate.lean,
// CID/Fetch.lean); these are plain assertions against the wasm built from the
// same commit.
//
// Fixtures: the examples of the Recommendation (https://www.w3.org/TR/cid-1.0/)
// as the Lean tests hold them, read from formal/lean4/L4Factoidal/CID/Tests.lean
// (one copy of the text). The fetch is a local mock; no network is used.

import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import {
  ready, capabilities, FactoidalError, cidValidate, cidRetrieveVerificationMethod,
} from '../index.mjs';
import * as browser from '../browser.js';

const LEAN_TESTS = fileURLToPath(new URL('../../../formal/lean4/L4Factoidal/CID/Tests.lean', import.meta.url));

// `def NAME : String := r##"…"##` blocks of the Lean tests.
function examples() {
  const src = fs.readFileSync(LEAN_TESTS, 'utf8');
  const out = {};
  for (const m of src.matchAll(/^def (\w+) : String := r##"([\s\S]*?)"##/gm)) out[m[1]] = m[2];
  return out;
}
const EX = examples();

const ACCEPT = 'application/cid, application/cid+json, application/ld+json, application/json';
const PUBLIC = '203.0.113.7';

// A mock host: documents by URL, addresses by host name, and a log of calls.
function mockHost(docs, addresses = {}) {
  const calls = { fetch: [], resolve: [] };
  return {
    calls,
    resolve: async (host) => {
      calls.resolve.push(host);
      return host in addresses ? addresses[host] : [PUBLIC];
    },
    fetch: async (url, init) => {
      calls.fetch.push({ url, accept: init.headers.accept, address: init.address, redirect: init.redirect });
      const d = docs[url];
      if (!d) return new Response('not found', { status: 404 });
      const headers = d.contentType === null ? {} : { 'content-type': d.contentType || 'application/cid' };
      return new Response(d.body, { status: d.status || 200, headers });
    },
  };
}

function retrieve(vm, rel, host, extra = {}) {
  return cidRetrieveVerificationMethod(vm, rel, { fetch: host.fetch, resolve: host.resolve, ...extra });
}

await ready();

test('the engine has the CID ops', async () => {
  assert.equal((await capabilities()).cid, true);
  assert.ok(Object.keys(EX).length >= 25, `examples read from ${LEAN_TESTS}`);
});

test('cidValidate: the examples of the Recommendation', async () => {
  const valid = ['ex1', 'ex2', 'ex4', 'ex5', 'ex6', 'ex7', 'ex12', 'ex13', 'ex14', 'ex15', 'ex16',
    'ex17', 'ex20', 'ex21', 'ex22', 'ex29', 'external789'];
  for (const name of valid) {
    assert.deepEqual(await cidValidate(EX[name]), { valid: true, errors: [] }, name);
  }
  // As printed, Examples 12, 13 and 29 are not JSON (comments, a missing comma).
  for (const name of ['ex12AsPrinted', 'ex13AsPrinted', 'ex29AsPrinted']) {
    const r = await cidValidate(EX[name]);
    assert.equal(r.valid, false, name);
    assert.deepEqual(r.errors.map((e) => [e.code, e.path]), [['notJson', '']], name);
  }
  // A value is written as JSON first.
  assert.equal((await cidValidate(JSON.parse(EX.ex20))).valid, true);
});

test('cidValidate: every failed MUST, with its code and JSON Pointer', async () => {
  const doc = {
    id: 'not a url',
    verificationMethod: [
      { id: 'https://controller.example#k', type: 'Multikey', controller: 'https://controller.example',
        publicKeyMultibase: 'z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu' },
      { id: 'https://controller.example#j', type: 'JsonWebKey', controller: 'https://controller.example',
        publicKeyJwk: { kty: 'OKP', d: 'x' } },
      { id: 'https://controller.example#s', type: 'Multikey', controller: 'https://controller.example',
        secretKeyMultibase: 'z3u2en7t5LR2WtQH5PfsqMDPFSLwhwPvAcp8f5ZH4ZDxM9nT' },
    ],
    service: [{ type: 1, serviceEndpoint: 'https://e.example' }],
    assertionMethod: ['#k', 3],
    keyAgreement: [],
  };
  const r = await cidValidate(doc);
  assert.equal(r.valid, false);
  assert.deepEqual(r.errors.map((e) => [e.code, e.path]), [
    ['idNotUrl', '/id'],
    ['serviceTypeInvalid', '/service/0/type'],
    ['jwkPrivateMember', '/verificationMethod/1/publicKeyJwk/d'],
    ['secretMaterial', '/verificationMethod/2/secretKeyMultibase'],
    ['relationshipEntryInvalid', '/assertionMethod/1'],
    ['relationshipEmpty', '/keyAgreement'],
  ]);
  for (const e of r.errors) assert.equal(typeof e.message, 'string');
  assert.deepEqual((await cidValidate('[1]')).errors.map((e) => e.code), ['notMap']);
  assert.deepEqual((await cidValidate('{}')).errors.map((e) => [e.code, e.path]), [['idMissing', '/id']]);
});

test('cidRetrieveVerificationMethod: the examples, through a mock fetch', async () => {
  const host = mockHost({
    'https://controller.example': { body: EX.ex1 },
    'https://controller.example/101': { body: EX.ex2, contentType: 'application/cid+json' },
    'https://controller.example/123': { body: EX.ex20, contentType: 'application/ld+json' },
    'https://controller.example/123456789abcdefghi': { body: EX.ex13, contentType: 'application/json; charset=utf-8' },
    'https://external.example/xyz': { body: EX.external789 },
  });
  const ok = [
    ['https://controller.example#authn-key-123', 'authentication'],
    ['https://controller.example/101#key-20240828', 'authentication'],
    ['https://controller.example/123#key-456', 'authentication'],
    ['https://controller.example/123456789abcdefghi#keys-2', 'authentication'],
    ['https://external.example/xyz#key-789', 'capabilityInvocation'],
  ];
  for (const [vm, rel] of ok) {
    const r = await retrieve(vm, rel, host);
    assert.equal(r.ok, true, `${vm} ${JSON.stringify(r)}`);
    assert.equal(r.verificationMethod.id.endsWith(vm.slice(vm.indexOf('#'))), true);
    assert.equal(r.controllerDocument, vm.slice(0, vm.indexOf('#')));
  }
  const r20 = await retrieve('https://controller.example/123#key-456', 'authentication', host);
  assert.deepEqual(r20.verificationMethod, JSON.parse(EX.ex20).verificationMethod[0]);
  // The engine named every request: the Accept header, the resolved address, no redirect.
  for (const c of host.calls.fetch) {
    assert.equal(c.accept, ACCEPT);
    assert.equal(c.address, PUBLIC);
    assert.equal(c.redirect, 'manual');
  }
  assert.ok(host.calls.resolve.includes('controller.example'));
});

test('cidRetrieveVerificationMethod: §3.5 processing errors as RFC 9457 objects', async () => {
  const host = mockHost({
    'https://controller.example': { body: EX.ex1 },
    'https://controller.example/123': { body: EX.ex29 },
    'https://controller.example/999': { body: EX.ex20 },
    'https://bad.example': { body: '{' },
  });
  const cases = [
    ['https://controller.example#authn-key-123', 'assertionMethod', 'INVALID_RELATIONSHIP_FOR_VERIFICATION_METHOD'],
    ['https://controller.example/123#key-1', 'authentication', 'INVALID_VERIFICATION_METHOD'],
    ['https://controller.example/999#key-456', 'authentication', 'INVALID_CONTROLLED_IDENTIFIER_DOCUMENT_ID'],
    ['https://bad.example#k', 'authentication', 'INVALID_CONTROLLED_IDENTIFIER_DOCUMENT'],
    ['key-456', 'authentication', 'INVALID_VERIFICATION_METHOD_URL'],
  ];
  for (const [vm, rel, code] of cases) {
    const r = await retrieve(vm, rel, host);
    assert.equal(r.ok, false, vm);
    assert.equal(r.code, code, vm);
    assert.equal(r.problem.type, `https://w3id.org/security#${code}`);
    assert.equal(typeof r.problem.title, 'string');
    assert.equal(typeof r.problem.detail, 'string');
  }
  await assert.rejects(retrieve('https://controller.example#k', 'proofOfWork', host), FactoidalError);
});

test('cidRetrieveVerificationMethod: the Content-Type of the answer (item 7)', async () => {
  const vm = 'https://controller.example/123#key-456';
  for (const ct of ['application/cid', 'application/cid+json', 'application/ld+json', 'application/json',
    'Application/CID; charset=utf-8']) {
    const r = await retrieve(vm, 'authentication', mockHost({ 'https://controller.example/123': { body: EX.ex20, contentType: ct } }));
    assert.equal(r.ok, true, ct);
  }
  for (const ct of ['text/html', 'application/did+json', null]) {
    const r = await retrieve(vm, 'authentication', mockHost({ 'https://controller.example/123': { body: EX.ex20, contentType: ct } }));
    assert.equal(r.code, 'UNSUPPORTED_MEDIA_TYPE', String(ct));
    assert.equal(r.problem.type, 'tag:danbri.github.io,2026:factoidal/cid#UNSUPPORTED_MEDIA_TYPE');
  }
});

test('cidRetrieveVerificationMethod: the private-address guard and the scheme', async () => {
  const vm = 'https://controller.example/123#key-456';
  const docs = { 'https://controller.example/123': { body: EX.ex20 } };
  for (const addrs of [['10.0.0.5'], ['127.0.0.1'], ['169.254.169.254'], ['192.168.1.1'], ['fd00::1'], ['::1'],
    [PUBLIC, '172.16.0.1'], []]) {
    const host = mockHost(docs, { 'controller.example': addrs });
    const r = await retrieve(vm, 'authentication', host);
    assert.equal(r.code, 'FETCH_REFUSED', JSON.stringify(addrs));
    assert.equal(host.calls.fetch.length, 0, 'nothing is fetched');
  }
  // Literals and localhost names, whatever the resolver says.
  for (const u of ['https://127.0.0.1/123#key-456', 'https://[::1]/123#key-456', 'https://10.1.2.3/x#k',
    'https://localhost:8443/123#key-456', 'https://a.localhost/x#k']) {
    const host = mockHost({});
    const r = await retrieve(u, 'authentication', host);
    assert.equal(r.code, 'FETCH_REFUSED', u);
    assert.equal(host.calls.fetch.length, 0);
  }
  // https only, unless allowHttp.
  const httpHost = mockHost({ 'http://controller.example/123': { body: EX.ex20.replaceAll('https://', 'http://') } });
  assert.equal((await retrieve('http://controller.example/123#key-456', 'authentication', httpHost)).code, 'FETCH_REFUSED');
  assert.equal(httpHost.calls.fetch.length, 0);
  assert.equal((await retrieve('http://controller.example/123#key-456', 'authentication', httpHost, { allowHttp: true })).ok, true);
  // A private address only with allowPrivateFetch.
  const priv = mockHost(docs, { 'controller.example': ['10.0.0.5'] });
  const r = await retrieve(vm, 'authentication', priv, { allowPrivateFetch: true });
  assert.equal(r.ok, true);
  assert.equal(priv.calls.fetch[0].address, '10.0.0.5');
});

test('cidRetrieveVerificationMethod: a host with no resolver (a browser page)', async () => {
  const host = mockHost({ 'https://controller.example/123': { body: EX.ex20 } });
  const r = await cidRetrieveVerificationMethod('https://controller.example/123#key-456', 'authentication',
    { fetch: host.fetch, resolve: null });
  assert.equal(r.ok, true);
  assert.equal(host.calls.fetch[0].address, undefined, 'the page connects by name');
  const lit = await cidRetrieveVerificationMethod('https://192.168.0.9/123#k', 'authentication',
    { fetch: host.fetch, resolve: null });
  assert.equal(lit.code, 'FETCH_REFUSED');
});

test('cidRetrieveVerificationMethod: status, a failed fetch, and now (§2.2)', async () => {
  const vm = 'https://controller.example/123#key-456';
  const notFound = await retrieve(vm, 'authentication', mockHost({}));
  assert.equal(notFound.code, 'FETCH_FAILED');
  assert.match(notFound.problem.detail, /404/);
  const redirect = await retrieve(vm, 'authentication', mockHost({ 'https://controller.example/123': { body: '', status: 302 } }));
  assert.equal(redirect.code, 'FETCH_FAILED');
  const thrown = await cidRetrieveVerificationMethod(vm, 'authentication',
    { resolve: async () => [PUBLIC], fetch: async () => { throw new Error('ECONNREFUSED'); } });
  assert.equal(thrown.code, 'FETCH_FAILED');
  // Example 7's expiry, on a method that authentication names.
  const doc = JSON.parse(EX.ex20);
  doc.verificationMethod[0].expires = '2025-12-01T00:00:00Z';
  const host = mockHost({ 'https://controller.example/123': { body: JSON.stringify(doc) } });
  assert.equal((await retrieve(vm, 'authentication', host)).ok, true);
  assert.equal((await retrieve(vm, 'authentication', host, { now: new Date('2025-11-30T23:59:59Z') })).ok, true);
  const late = await retrieve(vm, 'authentication', host, { now: Date.parse('2025-12-01T00:00:00Z') / 1000 });
  assert.equal(late.code, 'VERIFICATION_METHOD_NOT_IN_FORCE');
});

test('the browser entry has the same two functions', async () => {
  assert.equal(typeof browser.cidValidate, 'function');
  assert.equal(typeof browser.cidRetrieveVerificationMethod, 'function');
});
