// Stage 2 of https://github.com/danbri/factoidal/issues/713: the functions
// the F* engine serves through index.js that the Lean 4 engine now serves
// through factoidal/l4-core, with the same signatures and result shapes
// (index.d.ts):
//
//   1. maths:        matrix*, sigmoid*
//   2. VC and DID:   vc* (Ed25519 through the HACL* build linked into the
//                    wasm module), didKeyResolve
//   3. envelope parity (https://github.com/danbri/factoidal/issues/685):
//                    positioned parse errors, prefixes, serializeTurtleWith,
//                    bare Turtle literals
//   4. blank-node scope per document when documents are merged
//
// Every case runs through require('../l4-core.js'). Two kinds of cross-check
// keep the Lean answers from agreeing only with themselves:
//   * node:crypto (an independent SHA-256 and Ed25519) for the VC primitives,
//     and Math.exp for the sigmoid;
//   * the F* engine (require('../index.js')) for the maths and the VC checks,
//     when its bundle is present. That cross-check skips when it is not.
//
// Skips wholesale when the Lean wasm assets are not resolvable; a case for an
// op that an older resolved wasm lacks skips with the op's name.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const fs = require('node:fs');
const path = require('node:path');

const AVAILABLE = require('../l4.js').available();
const l4core = require('../l4-core.js');

const REPO = path.join(__dirname, '..', '..', '..');

function skipUnlessAvailable(t) {
  if (AVAILABLE) return false;
  t.skip('Lean wasm assets not resolvable (l4.js available() is false)');
  return true;
}

let leanOpsPromise = null;
function leanOps() {
  if (!leanOpsPromise) {
    leanOpsPromise = require('../l4.js')
      .loadL4()
      .then((eng) => (typeof eng.call === 'function' ? eng.call('ops', []).ops : []))
      .catch(() => []);
  }
  return leanOpsPromise;
}

async function skipUnlessOps(t, ...ops) {
  if (skipUnlessAvailable(t)) return true;
  const have = await leanOps();
  const missing = ops.filter((op) => !have.includes(op));
  if (missing.length > 0) {
    t.skip(`resolved Lean wasm lacks ${missing.join(', ')} (ops reflection); rebuild formal/lean4/Wasm/build-wasm.sh`);
    return true;
  }
  return false;
}

// The F* engine, when its bundle is present.
async function fstarWith(capability) {
  try {
    const fstar = require('../index.js');
    const caps = await fstar.capabilities();
    return caps[capability] ? fstar : null;
  } catch (_) {
    return null;
  }
}

// ---------------------------------------------------------------------
// 1. Maths
// ---------------------------------------------------------------------

const MATRIX_OPS = ['matrixDeterminant', 'matrixScalarProduct', 'matrixVectorProduct', 'matrixOuterProduct'];

test('l4-core matrixDeterminant: exact values', async (t) => {
  if (await skipUnlessOps(t, ...MATRIX_OPS)) return;
  assert.deepEqual(await l4core.matrixDeterminant([[1, 2], [3, 4]]), { result: '-2', reason: '' });
  // 2*(3*1-2*1) - 0*(1*1-2*1) + 1*(1*1-3*1) = 2 - 0 - 2 = 0
  assert.deepEqual(await l4core.matrixDeterminant([[2, 0, 1], [1, 3, 2], [1, 1, 1]]), { result: '0', reason: '' });
  // 1*(5*10-6*8) - 2*(4*10-6*7) + 3*(4*8-5*7) = 2 + 4 - 9 = -3
  assert.equal((await l4core.matrixDeterminant([[1, 2, 3], [4, 5, 6], [7, 8, 10]])).result, '-3');
  // The 0 x 0 matrix has determinant 1 by convention.
  assert.equal((await l4core.matrixDeterminant([])).result, '1');
  // Exact rational entries: [[1/2, 0], [0, 1/2]] has determinant 1/4.
  assert.equal((await l4core.matrixDeterminant([[[1, 2], 0], [0, [1, 2]]])).result, '1/4');
  // Entries reduce to lowest terms with a positive denominator.
  assert.equal((await l4core.matrixDeterminant([[[2, 4], 0], [0, [-3, -6]]])).result, '1/4');
});

test('l4-core matrixDeterminant: undefined results carry a reason', async (t) => {
  if (await skipUnlessOps(t, ...MATRIX_OPS)) return;
  let r = await l4core.matrixDeterminant([[1, 2, 3], [4, 5, 6]]);
  assert.equal(r.result, 'undef');
  assert.match(r.reason, /square/);
  r = await l4core.matrixDeterminant([[1, 2], [3]]);
  assert.equal(r.result, 'undef');
  assert.match(r.reason, /non-rectangular/);
  // A zero denominator is an undefined entry, never an exception or a number.
  r = await l4core.matrixDeterminant([[1, [1, 0]], [3, 4]]);
  assert.equal(r.result, 'undef');
  assert.equal(r.reason, 'division-by-zero');
});

test('l4-core matrix vector operations', async (t) => {
  if (await skipUnlessOps(t, ...MATRIX_OPS)) return;
  assert.equal((await l4core.matrixScalarProduct([1, 2, 3], [4, 5, 6])).result, '32');
  assert.equal((await l4core.matrixScalarProduct([[1, 2], 1], [2, [1, 3]])).result, '4/3');
  let r = await l4core.matrixScalarProduct([1, 2, 3], [4, 5]);
  assert.equal(r.result, 'undef');
  assert.match(r.reason, /length/);
  // e_x x e_y = e_z, and the cross product is anti-commutative.
  assert.equal((await l4core.matrixVectorProduct([1, 0, 0], [0, 1, 0])).result, '[0,0,1]');
  assert.equal((await l4core.matrixVectorProduct([0, 1, 0], [1, 0, 0])).result, '[0,0,-1]');
  assert.equal((await l4core.matrixVectorProduct([1, 2, 3], [4, 5, 6])).result, '[-3,6,-3]');
  r = await l4core.matrixVectorProduct([1, 0], [0, 1]);
  assert.equal(r.result, 'undef');
  assert.match(r.reason, /3-vectors/);
  assert.equal((await l4core.matrixOuterProduct([1, 2], [3, 4])).result, '[[3,4],[6,8]]');
  assert.equal((await l4core.matrixOuterProduct([1, 2, 3], [[1, 2]])).result, '[[1/2],[1],[3/2]]');
});

test('l4-core matrix wrappers reject non-array arguments before any engine call', async () => {
  await assert.rejects(() => l4core.matrixDeterminant('x'), TypeError);
  await assert.rejects(() => l4core.matrixScalarProduct([1], 2), TypeError);
  await assert.rejects(() => l4core.matrixVectorProduct(1, [1]), TypeError);
  await assert.rejects(() => l4core.matrixOuterProduct(null, [1]), TypeError);
});

test('l4-core matrix: a cell that is not an integer or a [num,den] pair rejects', async (t) => {
  if (await skipUnlessOps(t, ...MATRIX_OPS)) return;
  await assert.rejects(() => l4core.matrixDeterminant([[1.5, 2], [3, 4]]), /each cell/);
  await assert.rejects(() => l4core.matrixDeterminant([['x', 2], [3, 4]]), /each cell/);
  await assert.rejects(() => l4core.matrixScalarProduct([[1, 2, 3]], [1]), /each cell/);
});

test('l4-core matrix vs F* engine: same results on the same inputs', async (t) => {
  if (await skipUnlessOps(t, ...MATRIX_OPS)) return;
  const fstar = await fstarWith('matrix');
  if (!fstar) { t.skip('F* npm-entry bundle not present'); return; }
  const matrices = [[[1, 2], [3, 4]], [[1, 2, 3], [4, 5, 6]], [[[1, 2], 0], [0, [1, 2]]],
    [[2, 0, 1], [1, 3, 2], [1, 1, 1]], [[1, [1, 0]], [3, 4]], [[1, 2], [3]], []];
  for (const m of matrices) {
    assert.deepEqual(await l4core.matrixDeterminant(m), await fstar.matrixDeterminant(m),
      `matrixDeterminant ${JSON.stringify(m)}`);
  }
  const pairs = [[[1, 2, 3], [4, 5, 6]], [[1, 0, 0], [0, 1, 0]], [[1, 2], [3, 4]], [[1, 2, 3], [4, 5]],
    [[[1, 2], 1], [2, [1, 3]]], [[1, [1, 0]], [2, 3]]];
  for (const [a, b] of pairs) {
    for (const fn of ['matrixScalarProduct', 'matrixVectorProduct', 'matrixOuterProduct']) {
      assert.deepEqual(await l4core[fn](a, b), await fstar[fn](a, b),
        `${fn} ${JSON.stringify([a, b])}`);
    }
  }
});

const SIGMOID_OPS = ['sigmoidPoints', 'sigmoidFormulaMathml'];

test('l4-core sigmoidPoints: n+1 samples, exact midpoint, monotone, close to Math.exp', async (t) => {
  if (await skipUnlessOps(t, ...SIGMOID_OPS)) return;
  const pts = await l4core.sigmoidPoints({ k: '1', x0: '0', l: '1', xmin: '-6', xmax: '6', n: 24 });
  assert.equal(pts.length, 25);
  for (const p of pts) {
    for (const v of [p.x, p.y]) {
      assert.deepEqual(Object.keys(v), ['mantissa', 'scale', 'decimal']);
      assert.equal(typeof v.mantissa, 'string');
      assert.equal(v.scale, '9');
    }
  }
  // x = x0 = 0 is sample 12; k*(x-x0) = 0 exactly, so y = 1 / (1 + 1) with no rounding.
  assert.equal(pts[12].x.decimal, '0.000000000');
  assert.equal(pts[12].y.decimal, '0.500000000');
  assert.equal(pts[12].y.mantissa, '500000000');
  assert.equal(pts[0].x.decimal, '-6.000000000');
  assert.equal(pts[24].x.decimal, '6.000000000');
  for (let i = 1; i < pts.length; i++) {
    assert.ok(Number(pts[i].x.decimal) > Number(pts[i - 1].x.decimal));
    assert.ok(Number(pts[i].y.decimal) > Number(pts[i - 1].y.decimal));
  }
  // The documented bound is 1e-9 over the practical range; Math.exp is the independent witness.
  for (const p of pts) {
    const x = Number(p.x.decimal);
    const want = 1 / (1 + Math.exp(-x));
    assert.ok(Math.abs(Number(p.y.decimal) - want) < 2e-9, `sigmoid(${x})`);
  }
  // Symmetry: sigmoid(x) + sigmoid(-x) = 1.
  for (let i = 0; i < 12; i++) {
    const sum = BigInt(pts[i].y.mantissa) + BigInt(pts[24 - i].y.mantissa);
    assert.ok(sum >= 999999998n && sum <= 1000000002n, `symmetry at ${i}`);
  }
});

test('l4-core sigmoidPoints: parameters, n = 0, and refusals', async (t) => {
  if (await skipUnlessOps(t, ...SIGMOID_OPS)) return;
  // Numbers and strings are both accepted; L scales the curve.
  const pts = await l4core.sigmoidPoints({ k: 2, x0: '1.5', l: 10, xmin: 0, xmax: 3, n: 2 });
  assert.equal(pts.length, 3);
  assert.equal(pts[1].x.decimal, '1.500000000');
  assert.equal(pts[1].y.decimal, '5.000000000');
  // n = 0 is the single sample at xmin.
  const one = await l4core.sigmoidPoints({ k: 1, x0: 0, l: 1, xmin: -2, xmax: 2, n: 0 });
  assert.equal(one.length, 1);
  assert.equal(one[0].x.decimal, '-2.000000000');
  await assert.rejects(() => l4core.sigmoidPoints({ k: 1, x0: 0, l: 1, xmin: -2, xmax: 2, n: -1 }), /negative/);
  await assert.rejects(() => l4core.sigmoidPoints({ k: 'one', x0: 0, l: 1, xmin: -2, xmax: 2, n: 1 }), /not a decimal/);
  // The wrapper sends every parameter as text, so an absent one reaches the engine as "undefined".
  await assert.rejects(() => l4core.sigmoidPoints({ k: 1 }), /not a decimal literal: undefined/);
  await assert.rejects(() => l4core.sigmoidPoints(null), TypeError);
});

test('l4-core sigmoidPoints vs F* engine: identical digits', async (t) => {
  if (await skipUnlessOps(t, ...SIGMOID_OPS)) return;
  const fstar = await fstarWith('sigmoid');
  if (!fstar) { t.skip('F* npm-entry bundle not present'); return; }
  for (const params of [
    { k: '1', x0: '0', l: '1', xmin: '-6', xmax: '6', n: 24 },
    { k: '2.5', x0: '-1.25', l: '3', xmin: '-4', xmax: '4', n: 16 },
    { k: '0.5', x0: '3', l: '1', xmin: '0', xmax: '10', n: 10 },
  ]) {
    assert.deepEqual(await l4core.sigmoidPoints(params), await fstar.sigmoidPoints(params),
      JSON.stringify(params));
  }
  assert.equal(await l4core.sigmoidFormulaMathml(), await fstar.sigmoidFormulaMathml());
});

test('l4-core sigmoidFormulaMathml: Presentation MathML of L / (1 + e^(-k(x - x0)))', async (t) => {
  if (await skipUnlessOps(t, ...SIGMOID_OPS)) return;
  const mathml = await l4core.sigmoidFormulaMathml();
  assert.match(mathml, /^<math xmlns="http:\/\/www\.w3\.org\/1998\/Math\/MathML">/);
  assert.match(mathml, /<mfrac>/);
  assert.match(mathml, /<msup><mi>e<\/mi>/);
  assert.match(mathml, /<mi>L<\/mi>/);
  assert.match(mathml, /<mi>x0<\/mi>/);
  assert.match(mathml, /<\/math>$/);
});

// ---------------------------------------------------------------------
// 2. VC and DID
// ---------------------------------------------------------------------

const VC_PRIMITIVES = ['vcSha256Hex', 'vcEd25519SecretToPublic', 'vcEd25519Sign', 'vcEd25519Verify'];

// RFC 8032 section 7.1 test vectors.
const RFC8032 = [
  { name: 'TEST 1', sk: '9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60',
    pk: 'd75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a', msg: '',
    sig: 'e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b' },
  { name: 'TEST 2', sk: '4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb',
    pk: '3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c', msg: '72',
    sig: '92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00' },
  { name: 'TEST 3', sk: 'c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7',
    pk: 'fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025', msg: 'af82',
    sig: '6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a' },
];

function flipHexByte(hex, byteIndex) {
  const bytes = Buffer.from(hex, 'hex');
  bytes[byteIndex] ^= 1;
  return bytes.toString('hex');
}

test('l4-core vcSha256Hex: FIPS 180-4 vectors and node:crypto on arbitrary text', async (t) => {
  if (await skipUnlessOps(t, ...VC_PRIMITIVES)) return;
  assert.equal(await l4core.vcSha256Hex('abc'),
    'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad');
  assert.equal(await l4core.vcSha256Hex(''),
    'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855');
  assert.equal(await l4core.vcSha256Hex('abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq'),
    '248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1');
  // The text is hashed as UTF-8.
  for (const text of ['é', 'café ☃ 😀', 'x'.repeat(55), 'x'.repeat(56), 'x'.repeat(64), 'x'.repeat(65), 'line\nbreak\r\n']) {
    assert.equal(await l4core.vcSha256Hex(text),
      crypto.createHash('sha256').update(text, 'utf8').digest('hex'), JSON.stringify(text));
  }
});

test('l4-core Ed25519: RFC 8032 vectors, derive + sign + verify', async (t) => {
  if (await skipUnlessOps(t, ...VC_PRIMITIVES)) return;
  for (const v of RFC8032) {
    assert.equal(await l4core.vcEd25519SecretToPublic(v.sk), v.pk, `${v.name}: public key`);
    assert.equal(await l4core.vcEd25519Sign(v.sk, v.msg), v.sig, `${v.name}: signature`);
    assert.equal(await l4core.vcEd25519Verify(v.pk, v.msg, v.sig), true, `${v.name}: verify`);
  }
});

test('l4-core Ed25519: wrong key, tampered signature and tampered message verify false', async (t) => {
  if (await skipUnlessOps(t, ...VC_PRIMITIVES)) return;
  const [v1, v2] = RFC8032;
  assert.equal(await l4core.vcEd25519Verify(v2.pk, v1.msg, v1.sig), false, 'wrong public key');
  assert.equal(await l4core.vcEd25519Verify(v1.pk, v2.msg, v1.sig), false, 'different message');
  assert.equal(await l4core.vcEd25519Verify(v1.pk, v1.msg + '00', v1.sig), false, 'message with a byte appended');
  for (const i of [0, 31, 32, 63]) {
    assert.equal(await l4core.vcEd25519Verify(v1.pk, v1.msg, flipHexByte(v1.sig, i)), false,
      `signature byte ${i} flipped`);
  }
  // A signature made by another key does not verify under this one.
  assert.equal(await l4core.vcEd25519Verify(v1.pk, v1.msg, v2.sig), false, 'signature of another key');
  // Public key with a flipped byte.
  assert.equal(await l4core.vcEd25519Verify(flipHexByte(v1.pk, 5), v1.msg, v1.sig), false, 'public key byte flipped');
});

test('l4-core Ed25519: malformed input never verifies true and never throws', async (t) => {
  if (await skipUnlessOps(t, ...VC_PRIMITIVES)) return;
  const v = RFC8032[0];
  assert.equal(await l4core.vcEd25519Verify('ab', v.msg, v.sig), false, '1-byte public key');
  assert.equal(await l4core.vcEd25519Verify(v.pk, v.msg, v.sig.slice(0, -2)), false, '63-byte signature');
  assert.equal(await l4core.vcEd25519Verify(v.pk, v.msg, v.sig + '00'), false, '65-byte signature');
  assert.equal(await l4core.vcEd25519Verify('zz', v.msg, v.sig), false, 'non-hex public key');
  assert.equal(await l4core.vcEd25519Verify(v.pk, 'zz', v.sig), false, 'non-hex message');
  assert.equal(await l4core.vcEd25519Verify(v.pk, '7', v.sig), false, 'odd-length message');
  assert.equal(await l4core.vcEd25519Verify('', '', ''), false, 'all empty');
  await assert.rejects(() => l4core.vcEd25519SecretToPublic('ab'), /malformed secret key/);
  await assert.rejects(() => l4core.vcEd25519SecretToPublic('zz'), /malformed secret key/);
  await assert.rejects(() => l4core.vcEd25519Sign(v.sk, 'zz'), /malformed input/);
  await assert.rejects(() => l4core.vcEd25519Sign('ab', ''), /malformed input/);
  // Argument types are checked before any engine call.
  await assert.rejects(() => l4core.vcSha256Hex(42), TypeError);
  await assert.rejects(() => l4core.vcEd25519Verify('aa', 'bb', 5), TypeError);
});

test('l4-core Ed25519 vs node:crypto: same signature, each verifies the other', async (t) => {
  if (await skipUnlessOps(t, ...VC_PRIMITIVES)) return;
  // PKCS#8 wrapper of a raw 32-byte Ed25519 seed.
  const pkcs8Prefix = Buffer.from('302e020100300506032b657004220420', 'hex');
  const seeds = [RFC8032[0].sk, RFC8032[1].sk, crypto.createHash('sha256').update('seed-3').digest('hex')];
  const messages = ['', '00', 'ff'.repeat(100), Buffer.from('café', 'utf8').toString('hex')];
  for (const seed of seeds) {
    const priv = crypto.createPrivateKey({ key: Buffer.concat([pkcs8Prefix, Buffer.from(seed, 'hex')]), format: 'der', type: 'pkcs8' });
    const pub = crypto.createPublicKey(priv);
    const rawPub = pub.export({ format: 'der', type: 'spki' }).subarray(-32).toString('hex');
    assert.equal(await l4core.vcEd25519SecretToPublic(seed), rawPub, 'public key');
    for (const msgHex of messages) {
      const msg = Buffer.from(msgHex, 'hex');
      const theirs = crypto.sign(null, msg, priv).toString('hex');
      const ours = await l4core.vcEd25519Sign(seed, msgHex);
      assert.equal(ours, theirs, 'Ed25519 is deterministic: the two signatures are equal');
      assert.equal(crypto.verify(null, msg, pub, Buffer.from(ours, 'hex')), true, 'node verifies ours');
      assert.equal(await l4core.vcEd25519Verify(rawPub, msgHex, theirs), true, 'we verify theirs');
    }
  }
});

// The W3C vc-di-eddsa section 3.4 test vectors, canonical forms.
const SPEC = {
  sk: 'c96ef9ea10c5e414c471723aff9de72c35fa5b70fae97e8832ecac7d2e2b8ed6',
  pk: 'b00d8d938e7f773d51565aad36a623f5344f7f5d1960f9cf3e8e12620ea2810f',
  vm: 'did:key:z6MkrJVnaZkeFzdQyMZu1cgjg7k1pZZ6pvBQ7XJPt4swbTQ2#z6MkrJVnaZkeFzdQyMZu1cgjg7k1pZZ6pvBQ7XJPt4swbTQ2',
  proofValue: 'z2YwC8z3ap7yx1nZYCg4L3j3ApHsF8kgPdSb5xoS1VR7vPG3F561B52hYnQF9iseabecm3ijx4K1FBTQsCZahKZme',
  doc:
    '<did:example:abcdefgh> <https://www.w3.org/ns/credentials/examples#alumniOf> "The School of Examples" .\n' +
    '<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/2018/credentials#VerifiableCredential> .\n' +
    '<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/ns/credentials/examples#AlumniCredential> .\n' +
    '<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/description> "A minimum viable example of an Alumni Credential." .\n' +
    '<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/name> "Alumni Credential" .\n' +
    '<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#credentialSubject> <did:example:abcdefgh> .\n' +
    '<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#issuer> <https://vc.example/issuers/5678> .\n' +
    '<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#validFrom> "2023-01-01T00:00:00Z"^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n',
};
SPEC.cfg =
  '_:c14n0 <http://purl.org/dc/terms/created> "2023-02-24T23:36:38Z"^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n' +
  '_:c14n0 <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://w3id.org/security#DataIntegrityProof> .\n' +
  '_:c14n0 <https://w3id.org/security#cryptosuite> "eddsa-rdfc-2022"^^<https://w3id.org/security#cryptosuiteString> .\n' +
  '_:c14n0 <https://w3id.org/security#proofPurpose> <https://w3id.org/security#assertionMethod> .\n' +
  `_:c14n0 <https://w3id.org/security#verificationMethod> <${SPEC.vm}> .\n`;

const EDDSA_OPS = ['vcEddsaCreateFromCanonical', 'vcEddsaVerifyFromCanonical'];

test('l4-core eddsa-rdfc-2022: reproduces the W3C section 3.4 proofValue and verifies it', async (t) => {
  if (await skipUnlessOps(t, ...EDDSA_OPS, ...VC_PRIMITIVES)) return;
  assert.equal(await l4core.vcEd25519SecretToPublic(SPEC.sk), SPEC.pk);
  const created = await l4core.vcEddsaCreateFromCanonical(SPEC.sk, SPEC.doc, SPEC.cfg);
  assert.equal(created, SPEC.proofValue);
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(SPEC.pk, SPEC.doc, SPEC.cfg, SPEC.proofValue), true);
});

test('l4-core eddsa-rdfc-2022: wrong key, tampered document, config or proofValue verify false', async (t) => {
  if (await skipUnlessOps(t, ...EDDSA_OPS, ...VC_PRIMITIVES)) return;
  const wrongPk = RFC8032[0].pk;
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(wrongPk, SPEC.doc, SPEC.cfg, SPEC.proofValue), false, 'wrong key');
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(SPEC.pk,
    SPEC.doc.replace('Alumni Credential', 'Alumni CredentiaL'), SPEC.cfg, SPEC.proofValue), false, 'tampered document');
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(SPEC.pk, SPEC.doc,
    SPEC.cfg.replace('2023-02-24', '2023-02-25'), SPEC.proofValue), false, 'tampered proof config');
  // Two characters of the proofValue swapped.
  const pv = SPEC.proofValue;
  const swapped = pv.slice(0, 5) + pv[6] + pv[5] + pv.slice(7);
  assert.notEqual(swapped, pv);
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(SPEC.pk, SPEC.doc, SPEC.cfg, swapped), false, 'swapped characters');
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(SPEC.pk, SPEC.doc, SPEC.cfg, pv.slice(0, -1)), false, 'truncated proofValue');
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(SPEC.pk, SPEC.doc, SPEC.cfg, pv.slice(1)), false, 'no multibase prefix');
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(SPEC.pk, SPEC.doc, SPEC.cfg, ''), false, 'empty proofValue');
  assert.equal(await l4core.vcEddsaVerifyFromCanonical('ab', SPEC.doc, SPEC.cfg, pv), false, 'malformed key');
  // Swapping the roles of the document and the config changes the hash data.
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(SPEC.pk, SPEC.cfg, SPEC.doc, pv), false, 'document and config swapped');
  await assert.rejects(() => l4core.vcEddsaCreateFromCanonical('ab', SPEC.doc, SPEC.cfg), /malformed key/);
  await assert.rejects(() => l4core.vcEddsaCreateFromCanonical(SPEC.sk, 1, SPEC.cfg), TypeError);
});

test('l4-core eddsa-rdfc-2022 round trip over fresh text, create then verify', async (t) => {
  if (await skipUnlessOps(t, ...EDDSA_OPS, ...VC_PRIMITIVES)) return;
  const sk = RFC8032[0].sk;
  const pk = await l4core.vcEd25519SecretToPublic(sk);
  const pkOther = await l4core.vcEd25519SecretToPublic(RFC8032[1].sk);
  const doc = '<http://example.org/s> <http://example.org/p> "canonical value" .\n';
  const doc2 = '<http://example.org/s> <http://example.org/p> "TAMPERED value" .\n';
  const cfg = '_:pc <http://www.w3.org/ns/data-integrity#cryptosuite> "eddsa-rdfc-2022" .\n';
  const pv = await l4core.vcEddsaCreateFromCanonical(sk, doc, cfg);
  assert.equal(pv[0], 'z');
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(pk, doc, cfg, pv), true);
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(pkOther, doc, cfg, pv), false);
  assert.equal(await l4core.vcEddsaVerifyFromCanonical(pk, doc2, cfg, pv), false);
});

test('l4-core didKeyResolve: the tests/did vectors, as sorted N-Triples lines', async (t) => {
  if (await skipUnlessOps(t, 'didKeyResolve')) return;
  const dir = path.join(REPO, 'tests', 'did');
  if (!fs.existsSync(dir)) { t.skip('tests/did vectors not present'); return; }
  const dids = fs.readdirSync(dir).filter((f) => f.endsWith('.did')).sort();
  assert.ok(dids.length >= 3, 'the three did:key vectors');
  const lines = (s) => s.split('\n').map((l) => l.trim()).filter((l) => l && !l.startsWith('#')).sort();
  for (const f of dids) {
    const did = fs.readFileSync(path.join(dir, f), 'utf8').trim();
    const expected = lines(fs.readFileSync(path.join(dir, f.replace(/\.did$/, '.nt')), 'utf8'));
    const ds = await l4core.didKeyResolve(did);
    assert.equal(ds.constructor.name, 'Dataset');
    const got = lines(await l4core.serialize(ds, { format: 'nquads' }));
    assert.deepEqual(got, expected, f);
  }
});

test('l4-core didKeyResolve: anything that is not an Ed25519 did:key rejects', async (t) => {
  if (await skipUnlessOps(t, 'didKeyResolve')) return;
  for (const bad of [
    'did:example:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK',
    '', 'did:key:', 'did:key:mAbCdEfGhIjKlMnOpQrStUvWxYz',
    'did:key:zQ3shokFTS3brHcDQrn82RUDfCZESWL1ZdCEJwekUDPQiYBme',
  ]) {
    await assert.rejects(() => l4core.didKeyResolve(bad), /not a resolvable did:key/, JSON.stringify(bad));
  }
  await assert.rejects(() => l4core.didKeyResolve(7), TypeError);
});

// ---- the VCDM 2.0 data-model checks ----------------------------------

const VC_CHECKS = ['vcCheckCredential', 'vcCheckCredentialSubject', 'vcCheckNoDataLoss', 'vcCheckRelatedResourceDigests'];
const V2_CONTEXT_PATH = path.join(REPO, 'third_party', 'contexts', 'credentials-v2.jsonld');
const VC_FIXTURES = path.join(REPO, 'third_party', 'testing', 'vc', 'tests', 'input');

function fixtureFiles(dir) {
  const out = [];
  for (const name of fs.readdirSync(dir).sort()) {
    const full = path.join(dir, name);
    if (fs.statSync(full).isDirectory()) out.push(...fixtureFiles(full));
    else if (name.endsWith('.json')) out.push(full);
  }
  return out;
}

// The three unsigned fixtures the upstream suite withdrew (vc_runner.ml).
const WITHDRAWN = new Set([
  'presentation-self-asserted-vc-no-holder.json',
  'presentation-self-asserted-vc-holder-mismatch.json',
  'presentation-self-asserted-vc-issuer-mismatch.json',
]);

test('l4-core vcCheckCredential over the vendored VCDM 2.0 fixtures: 117 pass, 0 fail', async (t) => {
  if (await skipUnlessOps(t, 'vcCheckCredential')) return;
  if (!fs.existsSync(VC_FIXTURES) || !fs.existsSync(V2_CONTEXT_PATH)) {
    t.skip('third_party/testing/vc fixtures or third_party/contexts not present');
    return;
  }
  const v2ctx = fs.readFileSync(V2_CONTEXT_PATH, 'utf8');
  const files = fixtureFiles(VC_FIXTURES);
  assert.equal(files.length, 120, 'the corpus has 120 files');
  let pass = 0;
  const failures = [];
  for (const file of files) {
    const name = path.basename(file);
    if (WITHDRAWN.has(name)) continue;
    const base = name.replace(/\.json$/, '');
    const wantPass = base.endsWith('-ok');
    assert.ok(wantPass || base.endsWith('-fail') || base.endsWith('-fail-or-inject'), name);
    const text = fs.readFileSync(file, 'utf8')
      .replace(/PAST DATE/g, '2020-01-01T00:00:00Z').replace(/FUTURE DATE/g, '2099-01-01T00:00:00Z');
    const r = await l4core.vcCheckCredential(v2ctx, text);
    if (r.valid === wantPass) pass++;
    else failures.push(`${name}: expected ${wantPass ? 'pass' : 'fail'}, got ${r.valid ? 'pass' : 'fail: ' + r.reason}`);
  }
  assert.deepEqual(failures, []);
  assert.equal(pass, 117, `${pass} pass, ${failures.length} fail (out of 117)`);
});

test('l4-core vcCheckCredential vs F* engine: the same verdict on every fixture', async (t) => {
  if (await skipUnlessOps(t, 'vcCheckCredential')) return;
  const fstar = await fstarWith('entry');
  if (!fstar || typeof fstar.vcCheckCredential !== 'function') { t.skip('F* npm-entry bundle not present'); return; }
  if (!fs.existsSync(VC_FIXTURES) || !fs.existsSync(V2_CONTEXT_PATH)) { t.skip('fixtures not present'); return; }
  const v2ctx = fs.readFileSync(V2_CONTEXT_PATH, 'utf8');
  const disagreements = [];
  for (const file of fixtureFiles(VC_FIXTURES)) {
    const text = fs.readFileSync(file, 'utf8')
      .replace(/PAST DATE/g, '2020-01-01T00:00:00Z').replace(/FUTURE DATE/g, '2099-01-01T00:00:00Z');
    const a = await l4core.vcCheckCredential(v2ctx, text);
    const b = await fstar.vcCheckCredential(v2ctx, text);
    if (a.valid !== b.valid) disagreements.push(`${path.basename(file)}: Lean ${a.valid}, F* ${b.valid}`);
  }
  assert.deepEqual(disagreements, []);
});

const V2 = '"@context":["https://www.w3.org/ns/credentials/v2"]';

test('l4-core vcCheckCredential: verdicts with reasons, and an unreadable context rejects', async (t) => {
  if (await skipUnlessOps(t, ...VC_CHECKS)) return;
  const ctx = '{"@context":{"@protected":true}}';
  const ok = `{${V2},"type":["VerifiableCredential"],"credentialSubject":{"id":"did:example:s"}}`;
  assert.deepEqual(await l4core.vcCheckCredential(ctx, ok), { valid: true });
  const noSubject = `{${V2},"type":["VerifiableCredential"]}`;
  assert.deepEqual(await l4core.vcCheckCredential(ctx, noSubject), { valid: false, reason: 'missing credentialSubject' });
  const wrongFirst = '{"@context":["https://ex.org/c","https://www.w3.org/ns/credentials/v2"],"type":["VerifiableCredential"],"credentialSubject":{"a":1}}';
  const r = await l4core.vcCheckCredential(ctx, wrongFirst);
  assert.equal(r.valid, false);
  assert.match(r.reason, /FIRST/);
  assert.equal((await l4core.vcCheckCredential(ctx, '{')).valid, false);
  assert.equal((await l4core.vcCheckCredential(ctx, '[]')).valid, false);
  await assert.rejects(() => l4core.vcCheckCredential('not json', ok), /v2ctx/);
  await assert.rejects(() => l4core.vcCheckCredential(ctx, 5), TypeError);
});

test('l4-core vcCheckCredentialSubject: no @context gate', async (t) => {
  if (await skipUnlessOps(t, ...VC_CHECKS)) return;
  assert.deepEqual(await l4core.vcCheckCredentialSubject(
    '{"@context":"https://www.w3.org/2018/credentials/v1","type":["VerifiableCredential"],"credentialSubject":{"a":1}}'),
  { valid: true });
  const noSubject = await l4core.vcCheckCredentialSubject('{"type":["VerifiableCredential"]}');
  assert.equal(noSubject.valid, false);
  assert.equal(noSubject.reason, 'missing credentialSubject');
  assert.equal((await l4core.vcCheckCredentialSubject('{"type":["VerifiableCredential"],"credentialSubject":{}}')).valid, false);
  assert.equal((await l4core.vcCheckCredentialSubject('{"type":["VerifiablePresentation"]}')).valid, true);
});

test('l4-core vcCheckNoDataLoss: undefined terms are refused, defined ones pass', async (t) => {
  if (await skipUnlessOps(t, ...VC_CHECKS)) return;
  const ctx = '{"Known":"https://ex.org/Known","name":"https://schema.org/name"}';
  const doc = (types, subject, context = ctx) =>
    `{"@context":${context},"type":${types},"credentialSubject":${subject}}`;
  assert.deepEqual(await l4core.vcCheckNoDataLoss(doc('["Known"]', '{"name":"x"}')), { valid: true });
  let r = await l4core.vcCheckNoDataLoss(doc('["Unknown"]', '{"name":"x"}'));
  assert.equal(r.valid, false);
  assert.match(r.reason, /DATA_LOSS_DETECTION_ERROR/);
  r = await l4core.vcCheckNoDataLoss(doc('["Known"]', '{"nick":"x"}'));
  assert.equal(r.valid, false);
  assert.match(r.reason, /credentialSubject/);
  assert.equal((await l4core.vcCheckNoDataLoss(doc('["Known"]', '{"id":"did:example:s","@id":"did:example:s","name":"x"}'))).valid, true);
  assert.equal((await l4core.vcCheckNoDataLoss(doc('["Known"]', '[{"name":"x"},{"nick":"y"}]'))).valid, false);
  assert.equal((await l4core.vcCheckNoDataLoss(doc('["Anything"]', '{"anything":1}', '{"@vocab":"https://ex.org/"}'))).valid, true);
  // A bare remote context IRI cannot be fetched: refused, never silently skipped.
  r = await l4core.vcCheckNoDataLoss(doc('["VerifiableCredential"]', '{"a":1}', '"https://www.w3.org/ns/credentials/v2"'));
  assert.equal(r.valid, false);
  assert.match(r.reason, /could not process @context/);
  assert.match((await l4core.vcCheckNoDataLoss('{"type":["T"]}')).reason, /missing @context/);
});

test('l4-core vcCheckRelatedResourceDigests: match, mismatch, and the offline policy', async (t) => {
  if (await skipUnlessOps(t, ...VC_CHECKS)) return;
  // The registry the host computes from vendored copies: here the SHA-256 of the
  // 2024-07-20 VCDM 2.0 context, and its base64url form is the test suite's own value.
  const bytes = fs.readFileSync(path.join(REPO, 'third_party', 'contexts', 'credentials-v2-20240720-8d0ee107.jsonld'));
  const sha256 = crypto.createHash('sha256').update(bytes).digest();
  const sha384 = crypto.createHash('sha384').update(bytes).digest();
  const id = 'https://www.w3.org/ns/credentials/v2';
  const registry = JSON.stringify([{ id, digestsHex: [sha256.toString('hex'), sha384.toString('hex')] }]);
  const withResource = (rr) =>
    JSON.stringify({ '@context': ['https://www.w3.org/ns/credentials/v2'], type: ['VerifiableCredential'],
      credentialSubject: { a: 1 }, relatedResource: [rr] });
  const u = (buf) => 'u' + buf.toString('base64url');
  assert.deepEqual(await l4core.vcCheckRelatedResourceDigests(registry,
    withResource({ id, digestMultibase: u(sha256) })), { valid: true });
  assert.equal(u(sha256), 'uJKGMkOmFbVJhEfKTduMC2XCyvRAYLjOVmZWwIH1wQ7k');
  assert.deepEqual(await l4core.vcCheckRelatedResourceDigests(registry,
    withResource({ id, digestSRI: 'sha384-' + sha384.toString('base64') })), { valid: true });
  assert.deepEqual(await l4core.vcCheckRelatedResourceDigests(registry,
    withResource({ id, digestSRI: 'sha256-' + sha256.toString('base64') })), { valid: true });
  const altered = Buffer.from(sha256); altered[0] ^= 1;
  let r = await l4core.vcCheckRelatedResourceDigests(registry, withResource({ id, digestMultibase: u(altered) }));
  assert.equal(r.valid, false);
  assert.match(r.reason, /digestMultibase does not match/);
  r = await l4core.vcCheckRelatedResourceDigests(registry, withResource({ id, digestSRI: 'sha384-' + altered.toString('base64') }));
  assert.equal(r.valid, false);
  assert.match(r.reason, /digestSRI does not match/);
  // Offline policy: unknown resource and uncovered algorithm are unverifiable, so they pass.
  assert.equal((await l4core.vcCheckRelatedResourceDigests(registry,
    withResource({ id: 'https://ex.org/unknown', digestMultibase: u(altered) }))).valid, true);
  assert.equal((await l4core.vcCheckRelatedResourceDigests(registry,
    withResource({ id, digestSRI: 'sha512-AAAA' }))).valid, true);
  // Malformed registry or document.
  assert.match((await l4core.vcCheckRelatedResourceDigests('[', '{}')).reason, /digest registry is not well-formed JSON/);
  assert.match((await l4core.vcCheckRelatedResourceDigests('[]', '[]')).reason, /top-level JSON value must be an object/);
});

// ---------------------------------------------------------------------
// 3. Envelope parity (https://github.com/danbri/factoidal/issues/685)
// ---------------------------------------------------------------------

const X = 'http://x/';
const XSD_INT = 'http://www.w3.org/2001/XMLSchema#integer';

function assertParseError(err, who) {
  assert.equal(err.name, 'ParseError', `${who}: err.name`);
  assert.ok(err instanceof l4core.ParseError, `${who}: instanceof the exported ParseError`);
  assert.equal(typeof err.line, 'number', `${who}: err.line`);
  assert.equal(typeof err.column, 'number', `${who}: err.column`);
  assert.equal(typeof err.offset, 'number', `${who}: err.offset`);
}

test('l4-core parse errors carry line, column, offset and format (Turtle, TriG, N-Triples, N-Quads)', async (t) => {
  if (await skipUnlessOps(t, 'parseToDatasetJson')) return;
  await assert.rejects(l4core.parse('this is not turtle', { format: 'turtle' }),
    (err) => { assertParseError(err, 'turtle'); assert.equal(err.line, 1); assert.equal(err.column, 5); assert.equal(err.format, 'turtle'); return true; });
  await assert.rejects(l4core.parse('<http://x/s> <http://x/p> .', { format: 'ntriples' }),
    (err) => { assertParseError(err, 'ntriples'); assert.equal(err.line, 1); return true; });
  await assert.rejects(l4core.parse('<http://x/s> <http://x/p> .', { format: 'nquads' }),
    (err) => { assertParseError(err, 'nquads'); return true; });
  await assert.rejects(l4core.parse('@prefix ex: <http://x/> . GRAPH ex:g { ex:s ex:p', { format: 'trig' }),
    (err) => { assertParseError(err, 'trig'); return true; });
});

test('l4-core parse error: a Turtle statement missing its dot is reported on the FOLLOWING line', async (t) => {
  if (await skipUnlessOps(t, 'parseToDatasetJson')) return;
  const text = '@prefix ex: <http://example.org/> .\nex:a ex:p ex:o\nex:b ex:p ex:o2 .\n';
  await assert.rejects(l4core.parse(text, { format: 'turtle' }),
    (err) => { assertParseError(err, 'missing-dot'); assert.equal(err.line, 3); return true; });
});

test('l4-core parse error: the column counts Unicode scalar values, the line counts newlines', async (t) => {
  if (await skipUnlessOps(t, 'parseToDatasetJson')) return;
  const ascii = '# \n<http://x/s> <http://x/p> .';
  const wide = '# ééé\n<http://x/s> <http://x/p> .';
  let a, w;
  await assert.rejects(l4core.parse(ascii, { format: 'ttl' }), (err) => { a = err; return true; });
  await assert.rejects(l4core.parse(wide, { format: 'ttl' }), (err) => { w = err; return true; });
  assert.equal(a.line, 2);
  assert.equal(w.line, 2);
  assert.equal(a.column, w.column, 'non-ASCII text on a previous line does not move the column');
  // On the same line, three two-byte characters are three columns.
  await assert.rejects(l4core.parse('ééé .', { format: 'ttl' }),
    (err) => { assert.equal(err.line, 1); assert.ok(err.column <= 4, `column ${err.column}`); return true; });
});

test('l4-core parse error: an RDF/XML failure is a message only, a plain Error', async (t) => {
  if (await skipUnlessOps(t, 'parseToDatasetJson')) return;
  const bad = '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">' +
    '<rdf:Description rdf:nodeID="333-555-666" /></rdf:RDF>';
  await assert.rejects(l4core.parse(bad, { format: 'rdfxml' }),
    (err) => { assert.notEqual(err.name, 'ParseError'); assert.match(err.message, /nodeID/); return true; });
});

test('l4-core parse error: a relative IRI with no baseIRI names the IRI', async (t) => {
  if (await skipUnlessOps(t, 'parseToDatasetJson')) return;
  await assert.rejects(l4core.parse('<a> <b> <c> .', { format: 'turtle' }), /IRI/i);
  await assert.rejects(l4core.query('this is not turtle', 'SELECT * WHERE { ?s ?p ?o }', { format: 'turtle' }),
    (err) => { assertParseError(err, 'query'); return true; });
});

test('l4-core parse() records the prefixes of a Turtle and a TriG document', async (t) => {
  if (await skipUnlessOps(t, 'parseToDatasetJson')) return;
  const ttl = '@prefix ex: <http://example.org/> .\n@prefix a: <http://a.org/> .\n@prefix ex: <http://other.org/> .\nex:s a:p 1 .\n';
  const ds = await l4core.parse(ttl, { format: 'turtle' });
  assert.deepEqual(Object.entries(ds.prefixes), [['a', 'http://a.org/'], ['ex', 'http://other.org/']],
    'each label once, its latest binding, in declaration order');
  const trig = await l4core.parse('@prefix ex: <http://x/> . <http://x/g> { ex:s ex:p ex:o }', { format: 'trig' });
  assert.deepEqual({ ...trig.prefixes }, { ex: 'http://x/' });
  assert.deepEqual({ ...(await l4core.parse('<http://x/s> <http://x/p> <http://x/o> .', { format: 'nquads' })).prefixes }, {});
  // The prefixes survive into Turtle output of the parsed dataset.
  const out = await l4core.serialize(await l4core.parse(
    '@prefix ex: <http://example.org/> .\nex:s ex:p ex:o .\n', { format: 'turtle' }), { format: 'turtle' });
  assert.match(out, /@prefix ex: <http:\/\/example\.org\/> \./);
  assert.match(out, /ex:s ex:p ex:o \./);
});

test('l4-core openDataset: prefixes at open, handle prefixes in Turtle output, options', async (t) => {
  if (await skipUnlessOps(t, 'datasetOpen', 'datasetSerializeWith')) return;
  const h = await l4core.openDataset(
    `@prefix ex: <http://example.org/> .\nex:s ex:p 1, true, 1.5, "x", "5."^^<http://www.w3.org/2001/XMLSchema#decimal> .\n`,
    { format: 'turtle' });
  try {
    assert.deepEqual({ ...h.prefixes }, { ex: 'http://example.org/' });
    assert.equal(h.size, 5);
    const ttl = await h.serialize({ format: 'turtle' });
    assert.match(ttl, /@prefix ex: <http:\/\/example\.org\/> \./);
    assert.match(ttl, /ex:s ex:p 1 , 1\.5 , /);
    assert.match(ttl, / true /);
    assert.equal(ttl.split('^^').length - 1, 1, 'only the "5." decimal keeps its datatype');
    const quoted = await h.serialize({ format: 'turtle', literalShorthand: false });
    assert.equal(quoted.split('^^').length - 1, 4);
    assert.doesNotMatch(quoted, / 1 ,/);
    // The handle's prefixes and the caller's are merged, handle first. A caller label
    // for a namespace that is already named keeps the first label (the F* rule); a
    // caller label for a new namespace is used.
    const sameNs = await h.serialize({ format: 'turtle', prefixes: { e: 'http://example.org/' } });
    assert.match(sameNs, /@prefix ex: <http:\/\/example\.org\/> \./);
    assert.doesNotMatch(sameNs, /\be:/);
    const extra = await h.serialize({ format: 'turtle', prefixes: { xs: 'http://www.w3.org/2001/XMLSchema#' } });
    assert.match(extra, /@prefix ex: <http:\/\/example\.org\/> \./);
    assert.match(extra, /@prefix xs: <http:\/\/www\.w3\.org\/2001\/XMLSchema#> \./);
    assert.match(extra, /"5\."\^\^xs:decimal/);
    assert.doesNotMatch(extra, /xsd:/);
  } finally {
    await h.close();
  }
  await assert.rejects(l4core.openDataset('this is not turtle', { format: 'turtle' }),
    (err) => { assertParseError(err, 'openDataset'); assert.equal(err.line, 1); return true; });
});

test('l4-core serialize({format:"turtle"}): bare literals by default, quoted with literalShorthand:false', async (t) => {
  if (await skipUnlessOps(t, 'serializeTurtleWith')) return;
  const nt = `<${X}s> <${X}p> "42"^^<${XSD_INT}> .\n` +
    `<${X}s> <${X}p> "1.5"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n` +
    `<${X}s> <${X}p> "1e3"^^<http://www.w3.org/2001/XMLSchema#double> .\n` +
    `<${X}s> <${X}p> "false"^^<http://www.w3.org/2001/XMLSchema#boolean> .\n` +
    `<${X}s> <${X}p> "5."^^<http://www.w3.org/2001/XMLSchema#decimal> .\n` +
    `<${X}s> <${X}p> " 7"^^<${XSD_INT}> .\n`;
  const bare = await l4core.serialize(nt, { format: 'turtle', inputFormat: 'ntriples' });
  assert.match(bare, / 42 /);
  assert.match(bare, / 1\.5 /);
  assert.match(bare, / 1e3 /);
  assert.match(bare, / false /);
  assert.match(bare, /"5\."\^\^xsd:decimal/, 'a lexical form that is not the terminal stays quoted');
  assert.match(bare, /" 7"\^\^xsd:integer/);
  const quoted = await l4core.serialize(nt, { format: 'turtle', inputFormat: 'ntriples', literalShorthand: false });
  assert.equal(quoted.split('^^').length - 1, 6);
  // Both read back to the same graph.
  for (const ttl of [bare, quoted]) {
    const again = await l4core.serialize(await l4core.parse(ttl, { format: 'turtle' }), { format: 'nquads' });
    assert.deepEqual(again.split('\n').filter(Boolean).sort(),
      (await l4core.serialize(nt, { format: 'nquads', inputFormat: 'ntriples' })).split('\n').filter(Boolean).sort());
  }
  // Caller prefixes win and are emitted only when used.
  const withPrefixes = await l4core.serialize(nt, { format: 'turtle', inputFormat: 'ntriples',
    prefixes: { ex: X, unused: 'http://unused.example/' } });
  assert.match(withPrefixes, /@prefix ex: <http:\/\/x\/> \./);
  assert.doesNotMatch(withPrefixes, /unused:/);
  assert.match(withPrefixes, /ex:s ex:p/);
});

// ---------------------------------------------------------------------
// 4. Blank-node scope per document
// ---------------------------------------------------------------------

test('l4-core multi-document merge keeps blank-node labels document-scoped', async (t) => {
  if (await skipUnlessOps(t, 'parseToDatasetJson')) return;
  const d1 = `_:b0 <${X}p> "one" .`;
  const d2 = `_:b0 <${X}p> "two" .`;
  const rows = await l4core.query([d1, d2], `SELECT DISTINCT ?s WHERE { ?s <${X}p> ?o }`, { format: 'turtle' });
  assert.equal(rows.length, 2, 'two documents each with _:b0 contribute two distinct nodes');
  // The same text twice is still two documents: a merge, not a union.
  const twice = await l4core.query([d1, d1], `SELECT DISTINCT ?s WHERE { ?s <${X}p> ?o }`, { format: 'turtle' });
  assert.equal(twice.length, 2);
  // Inside ONE document the label is one node.
  const inOne = await l4core.query(`_:b0 <${X}p> "one", "two" .`,
    `SELECT DISTINCT ?s WHERE { ?s <${X}p> ?o }`, { format: 'turtle' });
  assert.equal(inOne.length, 1);
  // update() and canonicalize() merge documents the same way.
  const updated = await l4core.update([d1, d2], `INSERT DATA { <${X}a> <${X}b> <${X}c> }`, { format: 'turtle' });
  assert.equal(updated.size, 3);
  const canon = await l4core.canonicalize([d1, d2], { format: 'turtle' });
  assert.equal(canon.split('\n').filter(Boolean).length, 2);
  assert.notEqual(canon.split('\n')[0].split(' ')[0], canon.split('\n')[1].split(' ')[0],
    'two different canonical labels for the two nodes');
});
