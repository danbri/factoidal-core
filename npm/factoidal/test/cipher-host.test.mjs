// Unit tests of lib/cipher-host.mjs, the host side of the AES call-out
// (https://github.com/danbri/factoidal/issues/1081, issue 677). Published
// vectors only; the random differential run is tests/crypto/aes-diff.mjs.
import test from 'node:test';
import assert from 'node:assert/strict';
import { answerCipherRequest, runWithCipher, MAX_CIPHER_REQUESTS } from '../lib/cipher-host.mjs';

const b64 = (hex) => Buffer.from(hex, 'hex').toString('base64');
const hex = (s) => Buffer.from(s, 'base64').toString('hex');
const ask = (op, key, iv, aad, data) => answerCipherRequest({ op, key: b64(key), iv: b64(iv), aad: b64(aad), data: b64(data) });

// McGrew and Viega, GCM revised 2005, Appendix B, test cases 2 and 4.
const MV2 = { key: '00000000000000000000000000000000', iv: '000000000000000000000000', aad: '',
  pt: '00000000000000000000000000000000', ct: '0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf' };
const MV4 = { key: 'feffe9928665731c6d6a8f9467308308', iv: 'cafebabefacedbaddecaf888', aad: 'feedfacedeadbeeffeedfacedeadbeefabaddad2',
  pt: 'd9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39',
  ct: '42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091' +
      '5bc94fbc3221a5db94fae95ae7121a47' };

test('AES-GCM: McGrew-Viega cases 2 and 4, encrypt and decrypt', async () => {
  for (const v of [MV2, MV4]) {
    assert.equal(hex((await ask('aes-gcm-encrypt', v.key, v.iv, v.aad, v.pt)).ok), v.ct);
    assert.equal(hex((await ask('aes-gcm-decrypt', v.key, v.iv, v.aad, v.ct)).ok), v.pt);
  }
});

test('AES-GCM: a flipped tag bit and a changed AAD are refused with no message', async () => {
  const bad = MV4.ct.slice(0, -2) + (parseInt(MV4.ct.slice(-2), 16) ^ 1).toString(16).padStart(2, '0');
  assert.deepEqual(await ask('aes-gcm-decrypt', MV4.key, MV4.iv, MV4.aad, bad), { refused: true });
  assert.deepEqual(await ask('aes-gcm-decrypt', MV4.key, MV4.iv, '00', MV4.ct), { refused: true });
});

// RFC 3394 section 4.1 (128-bit KEK, 128-bit key) and 4.6 (256-bit KEK, 256-bit key).
const KEK128 = '000102030405060708090a0b0c0d0e0f';
const KEK256 = '000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f';
const RFC3394 = [
  [KEK128, '00112233445566778899aabbccddeeff', '1fa68b0a8112b447aef34bd8fb5a7b829d3e862371d2cfe5'],
  [KEK256, '00112233445566778899aabbccddeeff000102030405060708090a0b0c0d0e0f',
    '28c9f404c4b810f4cbccb35cfb87f8263f5786e2d80ed326cbc7f0e71a99f43bfb988b9b7a02dd21'],
];

test('AES Key Wrap: RFC 3394 sections 4.1 and 4.6, wrap and unwrap', async () => {
  for (const [kek, k, w] of RFC3394) {
    assert.equal(hex((await ask('aes-kw-wrap', kek, '', '', k)).ok), w);
    assert.equal(hex((await ask('aes-kw-unwrap', kek, '', '', w)).ok), k);
  }
});

test('AES Key Wrap: a changed wrapped key is refused', async () => {
  const [kek, , w] = RFC3394[0];
  assert.deepEqual(await ask('aes-kw-unwrap', kek, '', '', 'ff' + w.slice(2)), { refused: true });
});

// NIST SP 800-38A F.2.1, CBC-AES128, first block; PKCS #7 adds one block.
test('AES-CBC: SP 800-38A F.2.1 first block, PKCS #7 round trip', async () => {
  const key = '2b7e151628aed2a6abf7158809cf4f3c';
  const iv = '000102030405060708090a0b0c0d0e0f';
  const pt = '6bc1bee22e409f96e93d7e117393172a';
  const ct = hex((await ask('aes-cbc-encrypt', key, iv, '', pt)).ok);
  assert.equal(ct.length, 64);
  assert.equal(ct.slice(0, 32), '7649abac8119b246cee98e9b12e9197d');
  assert.equal(hex((await ask('aes-cbc-decrypt', key, iv, '', ct)).ok), pt);
  // Without the padding block the last block does not end in valid padding.
  assert.deepEqual(await ask('aes-cbc-decrypt', key, iv, '', ct.slice(0, 32)), { refused: true });
});

test('an unknown op or a malformed request is refused with no message', async () => {
  assert.deepEqual(await answerCipherRequest({ op: 'aes-ecb-encrypt', key: '', data: '' }), { refused: true });
  assert.deepEqual(await answerCipherRequest({ op: 'toString', key: '', data: '' }), { refused: true });
  assert.deepEqual(await answerCipherRequest(null), { refused: true });
  assert.deepEqual(await answerCipherRequest({ op: 'aes-gcm-encrypt', key: '%%%', iv: '', data: '' }), { refused: true });
});

test('runWithCipher: answers each need, calls again with the list extended', async () => {
  const need = { op: 'aes-gcm-encrypt', key: b64(MV2.key), iv: b64(MV2.iv), aad: '', data: b64(MV2.pt) };
  const seen = [];
  const op = (args) => {
    seen.push(args.answers.length);
    if (args.answers.length < 2) return { need };
    return { ok: true, input: args.input, answers: args.answers };
  };
  const res = await runWithCipher(op, { input: 'x' });
  assert.deepEqual(seen, [0, 1, 2]);
  assert.equal(res.input, 'x');
  assert.equal(hex(res.answers[1].answer.ok), MV2.ct);
  assert.deepEqual(res.answers[0].request, need);
});

test('runWithCipher: stops after the request bound', async () => {
  let calls = 0;
  const op = () => { calls++; return { need: { op: 'aes-ecb-encrypt' } }; };
  await assert.rejects(runWithCipher(op, {}), /more than 64/);
  assert.equal(calls, MAX_CIPHER_REQUESTS + 1);
});
