// Pure functions over engine ops that had no JavaScript function before
// 0.10.0. Each one takes values and returns a value: no handle, no hidden
// state. Every decision is made by the Lean op it calls
// (formal/lean4/Wasm/Ops/Crypto.lean, Wasm/Ops/Proof.lean,
// Wasm/CoreDispatch.lean). This file converts bytes to hex and back.
// No Node built-ins: the browser imports it as it is.

function hexOf(bytes) {
  if (!(bytes instanceof Uint8Array)) throw new TypeError('expected a Uint8Array');
  let s = '';
  for (const b of bytes) s += b.toString(16).padStart(2, '0');
  return s;
}

function bytesOf(hex) {
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.substr(2 * i, 2), 16);
  return out;
}

function optHex(v) {
  return v === undefined ? undefined : hexOf(v);
}

function str(name, v) {
  if (typeof v !== 'string') throw new TypeError(`${name}: argument must be a string`);
  return v;
}

/**
 * @param {() => Promise<object>} loadEngine resolves to an engine handle
 *   with `call(op, args)` (bin/engine.mjs, lib/browser-engine.mjs).
 */
export function buildPure(loadEngine) {
  const call = async (op, args) => (await loadEngine()).call(op, args);

  /** ChaCha20-Poly1305 seal (RFC 8439). key 32 bytes, nonce 12 bytes. */
  async function aeadSeal({ key, nonce, plaintext, aad }) {
    const r = await call('aeadSeal', [JSON.stringify({
      alg: 'chacha20-poly1305', key: hexOf(key), nonce: hexOf(nonce),
      aad: optHex(aad), plaintext: optHex(plaintext),
    })]);
    return bytesOf(r.ciphertext);
  }

  /** ChaCha20-Poly1305 open. Rejects when the tag does not authenticate. */
  async function aeadOpen({ key, nonce, ciphertext, aad }) {
    const r = await call('aeadOpen', [JSON.stringify({
      alg: 'chacha20-poly1305', key: hexOf(key), nonce: hexOf(nonce),
      aad: optHex(aad), ciphertext: hexOf(ciphertext),
    })]);
    return bytesOf(r.plaintext);
  }

  /** HPKE base mode seal, RFC 9180 DHKEM(X25519)/HKDF-SHA256/ChaCha20-Poly1305. */
  async function hpkeSeal({ skE, pkR, plaintext, info, aad }) {
    const r = await call('hpkeSeal', [JSON.stringify({
      skE: hexOf(skE), pkR: hexOf(pkR), info: optHex(info),
      aad: optHex(aad), plaintext: optHex(plaintext),
    })]);
    return { message: bytesOf(r.message), enc: bytesOf(r.enc), ciphertext: bytesOf(r.ciphertext) };
  }

  /** HPKE base mode open over the `message` that hpkeSeal returned. */
  async function hpkeOpen({ skR, message, info, aad }) {
    const r = await call('hpkeOpen', [JSON.stringify({
      skR: hexOf(skR), info: optHex(info), aad: optHex(aad), message: hexOf(message),
    })]);
    return bytesOf(r.plaintext);
  }

  /** Check an FPP0 proof bundle (JSON text). Returns the engine's report. */
  async function proofCheck(bundleJson) {
    const { ok, ...rest } = await call('proofCheck', [str('proofCheck', bundleJson)]);
    return rest;
  }

  /** Describe the shape of an FPP0 proof bundle without checking it. */
  async function proofInspect(bundleJson) {
    const { ok, ...rest } = await call('proofInspect', [str('proofInspect', bundleJson)]);
    return rest;
  }

  /** RDFC-1.0 over N-Quads text, N-Quads text out. */
  async function canonicalizeNQuads(nquads) {
    return (await call('canonicalizeToNQuads', [str('canonicalizeNQuads', nquads)])).nquads;
  }

  /** Parse N-Quads (or N-Triples) text and write it back as N-Quads. */
  async function normalizeNQuads(nquads) {
    return (await call('serializeNQuads', [str('normalizeNQuads', nquads)])).nquads;
  }

  return {
    aeadSeal, aeadOpen, hpkeSeal, hpkeOpen,
    proofCheck, proofInspect, canonicalizeNQuads, normalizeNQuads,
  };
}
