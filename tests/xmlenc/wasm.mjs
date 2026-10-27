// XML Encryption 1.1 through the Lean wasm (ops xmlDecrypt and xmlEncrypt,
// formal/lean4/Wasm/Ops/XmlEnc.lean), with WebCrypto answering every AES
// request (npm/factoidal/lib/cipher-host.mjs, runWithCipher).
// https://github.com/danbri/factoidal/issues/1084
//
// The host loop only answers requests: every decision (structure, algorithm
// allowlist, keys, RSA-OAEP, ECDH, Concat KDF, padding, parsing) is in Lean.
// The fixtures are Apache Santuario's (tests/xmlenc/MakeFixtures.java); the
// expected documents are Santuario's own decryptions.
//
//   node --test tests/xmlenc/wasm.mjs
//
// The engine is docs/web/hub/assets/l4/l4factoidal.js (written by
// formal/lean4/Wasm/build-wasm.sh), or $XMLENC_L4_ASSETS/l4factoidal.js.
// XMLENC_DUMP=<file>: write the documents Lean encrypted, with the keys, for
// tests/xmlenc/CheckLeanOutput.java (Santuario decrypts them).
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { runWithCipher } from '../../npm/factoidal/lib/cipher-host.mjs';

const root = join(dirname(fileURLToPath(import.meta.url)), '..', '..');
const assets = process.env.XMLENC_L4_ASSETS ?? join(root, 'docs', 'web', 'hub', 'assets', 'l4');
const fixtures = JSON.parse(readFileSync(join(root, 'tests', 'xmlenc', 'fixtures.json'), 'utf8'));
const { loadL4 } = await import(pathToFileURL(join(assets, 'l4factoidal.js')).href);
const l4 = await loadL4();

const keys = fixtures.keys;
const DECRYPTION_ERROR = 'XML decryption failed';

/** One call of an op; an {ok:false} envelope is returned, not thrown. */
function op(name) {
  return (args) => {
    try {
      return l4.call(name, [JSON.stringify(args)]);
    } catch (e) {
      if (e.envelope) return e.envelope;
      throw e;
    }
  };
}
const decrypt = (args) => runWithCipher(op('xmlDecrypt'), args);
const encrypt = (args) => runWithCipher(op('xmlEncrypt'), args);

/** The canonical form of a document with no encrypted part, by the engine. */
function canonical(doc) {
  const r = op('xmlDecrypt')({ document: doc, keys: [] });
  assert.equal(r.ok, true, r.error);
  return r.canonical;
}

/** Count the requests of one run. */
async function counted(name, args) {
  let n = 0;
  const call = op(name);
  const res = await runWithCipher((a) => { n = a.answers.length; return call(a); }, args);
  return { res, requests: n };
}

for (const c of fixtures.cases) {
  if (c.outcome === 'ok') {
    test(`Santuario ${c.name}: decrypted through WebCrypto`, async () => {
      const { res, requests } = await counted('xmlDecrypt', { document: c.document, keys });
      assert.equal(res.ok, true, res.error);
      assert.equal(res.canonical, canonical(c.expected));
      // GCM content, plus one AES Key Wrap unwrap where the key is wrapped.
      assert.equal(requests, c.native ? 1 : 2);
    });
  } else if (c.outcome === 'refused') {
    test(`Santuario ${c.name}: refused before any key is used`, async () => {
      const res = await decrypt({ document: c.document, keys });
      assert.equal(res.ok, false);
      assert.match(res.error, /rsa-1_5/);
    });
  } else if (c.outcome === 'needsAllowCbc') {
    test(`Santuario ${c.name}: refused without allowCbc, decrypted with it`, async () => {
      const no = await decrypt({ document: c.document, keys });
      assert.equal(no.ok, false);
      assert.match(no.error, /allowCbc/);
      // Two CBC requests: the PKCS #7 padding block, then the decryption;
      // the XML Encryption padding (ISO 10126, random octets) is removed in Lean.
      const { res, requests } = await counted('xmlDecrypt', { document: c.document, keys, allowCbc: true });
      assert.equal(res.ok, true, res.error);
      assert.equal(res.canonical, canonical(c.expected));
      assert.equal(requests, 2);
    });
  }
}

// The W3C XML Encryption 1.1 test cases (tests/xmlenc/w3c/PROVENANCE.md).
const w3cDir = join(root, 'tests', 'xmlenc', 'w3c');
const w3c = JSON.parse(readFileSync(join(w3cDir, 'cases.json'), 'utf8'));
const w3cKeys = JSON.parse(readFileSync(join(w3cDir, 'keys.json'), 'utf8'));
for (const c of w3c.cases) {
  test(`W3C ${c.id}: ${c.outcome}`, async () => {
    const res = await decrypt({ document: readFileSync(join(w3cDir, c.file), 'utf8'), keys: w3cKeys });
    if (c.outcome === 'ok') {
      assert.equal(res.ok, true, res.error);
      assert.equal(res.canonical, canonical(readFileSync(join(w3cDir, c.expected), 'utf8')));
    } else {
      assert.equal(res.ok, false);
      assert.ok(res.error.includes(c.reason), res.error);
      assert.notEqual(res.error, DECRYPTION_ERROR);
    }
  });
}

test('an altered ciphertext and a wrong key give the one decryption error', async () => {
  const c = fixtures.cases.find((x) => x.name === 'gcm128-kek-kw128');
  const parts = c.document.split('<xenc:CipherValue>');
  const last = parts.pop();
  const altered = [...parts, (last[0] === 'A' ? 'B' : 'A') + last.slice(1)].join('<xenc:CipherValue>');
  const r1 = await decrypt({ document: altered, keys });
  assert.deepEqual([r1.ok, r1.error], [false, DECRYPTION_ERROR]);
  const wrongKek = keys.map((k) => (k.kid === 'kek128' ? { ...k, k: Buffer.alloc(16, 7).toString('base64url') } : k));
  const r2 = await decrypt({ document: c.document, keys: wrongKek });
  assert.deepEqual([r2.ok, r2.error], [false, DECRYPTION_ERROR]);
});

test('a need is a request object of the CipherCall format', () => {
  const c = fixtures.cases.find((x) => x.name === 'gcm128-ecdh-p256-kw128');
  const r = op('xmlDecrypt')({ document: c.document, keys, answers: [] });
  assert.equal(r.ok, true);
  assert.equal(r.need.op, 'aes-kw-unwrap');
  assert.equal(Buffer.from(r.need.key, 'base64').length, 16);
  assert.equal(r.need.iv, '');
});

const publicOf = (k) => { const { d, ...rest } = k; return rest; };
const byKid = (kid) => keys.find((k) => k.kid === kid);
const PLAIN = '<inv:invoice xmlns:inv="urn:example:invoice" no="7"><inv:line>tea &amp; cake</inv:line>' +
  '<inv:card><!-- c --><inv:number>4019 2445</inv:number><inv:holder>Zoë</inv:holder></inv:card></inv:invoice>';

const RECIPIENTS = [
  ['RSA-OAEP mgf1p, AES-128-GCM', { recipient: publicOf(byKid('rsa-1')), algorithm: 'aes128-gcm' }],
  ['RSA-OAEP SHA-256, AES-256-GCM', { recipient: publicOf(byKid('rsa-1')), algorithm: 'aes256-gcm', keyTransport: 'rsa-oaep-sha256' }],
  ['ECDH-ES P-256, kw-aes128, AES-128-GCM', { recipient: publicOf(byKid('ec-1')), algorithm: 'aes128-gcm' }],
  ['X25519, kw-aes256, AES-256-GCM', { recipient: publicOf(byKid('x-1')), algorithm: 'aes256-gcm' }],
  ['kw-aes256 under a named key, Content', { recipient: byKid('kek256'), algorithm: 'aes128-gcm', content: true }],
];

const dump = [];
for (const [label, opts] of RECIPIENTS) {
  test(`Lean encrypts (${label}) and decrypts`, async () => {
    const random = Buffer.from(crypto.getRandomValues(new Uint8Array(96))).toString('base64');
    const enc = await encrypt({ document: PLAIN, random, ...opts });
    assert.equal(enc.ok, true, enc.error);
    assert.equal(enc.document.includes('4019'), false);
    const dec = await decrypt({ document: enc.document, keys });
    assert.equal(dec.ok, true, dec.error);
    assert.equal(dec.canonical, canonical(PLAIN));
    dump.push({ name: label, document: enc.document, expected: PLAIN });
  });
}

test('Lean encrypts a SAML EncryptedAssertion', async () => {
  const assertion = '<saml:Assertion xmlns:saml="urn:oasis:names:tc:SAML:2.0:assertion" ID="_1" Version="2.0"/>';
  const random = Buffer.from(crypto.getRandomValues(new Uint8Array(96))).toString('base64');
  const enc = await encrypt({ document: assertion, random, saml: true, recipient: publicOf(byKid('rsa-1')) });
  assert.equal(enc.ok, true, enc.error);
  assert.match(enc.document, /^<saml:EncryptedAssertion xmlns:saml="urn:oasis:names:tc:SAML:2.0:assertion"><xenc:EncryptedData /);
});

test.after(() => {
  // One line per key ("key" and its string members as name=value) and per
  // document ("doc" and the base64 of the name, the document, the plaintext).
  if (process.env.XMLENC_DUMP) {
    const b = (s) => Buffer.from(s, 'utf8').toString('base64');
    const lines = keys.map((k) => ['key', ...Object.entries(k).map(([n, v]) => `${n}=${v}`)].join(' '))
      .concat(dump.map((d) => ['doc', b(d.name), b(d.document), b(d.expected)].join(' ')));
    writeFileSync(process.env.XMLENC_DUMP, lines.join('\n') + '\n');
  }
});
