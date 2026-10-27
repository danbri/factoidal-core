// cipher-host.mjs — the JavaScript host side of the AES call-out
// (https://github.com/danbri/factoidal/issues/1081,
// https://github.com/danbri/factoidal/issues/677; design record
// docs/designissues/2026-10-27-xml-encryption-and-jwe.md, section "The AES
// call-out on JavaScript hosts"; request format
// formal/lean4/L4Factoidal/Crypto/CipherCall.lean).
//
// The engine (Lean, in the wasm) makes every decision: the algorithm, the key,
// the IV, the lengths (`Req.wellFormed`), the document structure. When it needs
// AES it answers `{need: {op, key, iv, aad, data}}` (bytes as base64). This
// module runs exactly that one WebCrypto operation and gives back
// `{ok: base64}` or `{refused: true}`. It reads no document, chooses no
// algorithm and checks no length. Every failure becomes the same refusal with
// no message, so no error text of the host's crypto library reaches the caller
// (padding oracle, Jager and Somorovsky 2011).
//
// Only `globalThis.crypto.subtle` is used, so the same code runs in Node 22,
// Deno and browsers (Node: OpenSSL; Chromium: BoringSSL; Firefox: NSS).
//
// Key Wrap: WebCrypto wraps a CryptoKey, not bytes. The bytes to wrap are
// imported as an extractable raw HMAC key (any byte length), wrapped with
// `wrapKey('raw', ...)`; an unwrap gives an HMAC key whose raw export is the
// unwrapped bytes.

const subtle = () => globalThis.crypto.subtle;

/** The most requests one engine operation may make (CipherCall.maxRequests). */
export const MAX_CIPHER_REQUESTS = 64;

function fromBase64(s) {
  const bin = atob(s ?? '');
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}

function toBase64(buf) {
  const b = new Uint8Array(buf);
  let bin = '';
  for (let i = 0; i < b.length; i += 0x8000) {
    bin += String.fromCharCode.apply(null, b.subarray(i, i + 0x8000));
  }
  return btoa(bin);
}

const HMAC = { name: 'HMAC', hash: 'SHA-256' };

// One entry per op name of CipherCall.Op.name: the WebCrypto call, nothing more.
const OPS = {
  'aes-gcm-encrypt': async (k, iv, aad, d) => {
    const key = await subtle().importKey('raw', k, 'AES-GCM', false, ['encrypt']);
    return subtle().encrypt({ name: 'AES-GCM', iv, additionalData: aad, tagLength: 128 }, key, d);
  },
  'aes-gcm-decrypt': async (k, iv, aad, d) => {
    const key = await subtle().importKey('raw', k, 'AES-GCM', false, ['decrypt']);
    return subtle().decrypt({ name: 'AES-GCM', iv, additionalData: aad, tagLength: 128 }, key, d);
  },
  'aes-kw-wrap': async (k, _iv, _aad, d) => {
    const kek = await subtle().importKey('raw', k, 'AES-KW', false, ['wrapKey']);
    const inner = await subtle().importKey('raw', d, HMAC, true, ['sign']);
    return subtle().wrapKey('raw', inner, kek, 'AES-KW');
  },
  'aes-kw-unwrap': async (k, _iv, _aad, d) => {
    const kek = await subtle().importKey('raw', k, 'AES-KW', false, ['unwrapKey']);
    const inner = await subtle().unwrapKey('raw', d, kek, 'AES-KW', HMAC, true, ['sign']);
    return subtle().exportKey('raw', inner);
  },
  'aes-cbc-encrypt': async (k, iv, _aad, d) => {
    const key = await subtle().importKey('raw', k, 'AES-CBC', false, ['encrypt']);
    return subtle().encrypt({ name: 'AES-CBC', iv }, key, d);
  },
  'aes-cbc-decrypt': async (k, iv, _aad, d) => {
    const key = await subtle().importKey('raw', k, 'AES-CBC', false, ['decrypt']);
    return subtle().decrypt({ name: 'AES-CBC', iv }, key, d);
  },
};

/**
 * Answer one cipher request of the engine.
 * @param {{op: string, key: string, iv?: string, aad?: string, data: string}} req  bytes as base64
 * @returns {Promise<{ok: string} | {refused: true}>}
 */
export async function answerCipherRequest(req) {
  try {
    const run = Object.prototype.hasOwnProperty.call(OPS, req?.op) ? OPS[req.op] : null;
    if (!run) return { refused: true };
    const out = await run(fromBase64(req.key), fromBase64(req.iv), fromBase64(req.aad), fromBase64(req.data));
    return { ok: toBase64(out) };
  } catch {
    return { refused: true };
  }
}

/**
 * Run an engine operation that may ask for AES. `callOp(args)` calls the wasm
 * op (sync or async) with `args` plus `answers`; while its result has `need`,
 * the request is answered and the op is called again with the same inputs and
 * the answer list extended by `{request, answer}`. The engine's format code is
 * deterministic, so each call gets one request further.
 * @param {(args: object) => any} callOp
 * @param {object} args
 */
export async function runWithCipher(callOp, args) {
  const answers = [];
  for (let asked = 0; ; asked++) {
    const res = await callOp({ ...args, answers: answers.slice() });
    if (!res || res.need === undefined) return res;
    // The request bound is the one check the host makes (design record step 4).
    if (asked === MAX_CIPHER_REQUESTS) {
      throw new Error(`runWithCipher: more than ${MAX_CIPHER_REQUESTS} cipher requests`);
    }
    answers.push({ request: res.need, answer: await answerCipherRequest(res.need) });
  }
}
