// jwe-engine.mjs — load the Lean wasm engine and call its JWE ops with the
// AES call-out answered by WebCrypto (npm/factoidal/lib/cipher-host.mjs).
// Shared by tests/jose/jwe-wasm.mjs and tests/jose/jwe-diff.mjs
// (https://github.com/danbri/factoidal/issues/1085).
//
// No JWE decision is made here: it passes JSON to the op and answers each
// `need` with exactly the WebCrypto call named.

import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runWithCipher } from '../../npm/factoidal/lib/cipher-host.mjs';

const here = dirname(fileURLToPath(import.meta.url));
export const repoRoot = resolve(here, '..', '..');

let enginePromise = null;

/** The loaded engine, or null with the reason printed when the assets are
 *  absent (the caller exits 77). */
export async function engine() {
  if (enginePromise === null) {
    enginePromise = (async () => {
      const mod = await import(resolve(repoRoot, 'npm/factoidal/bin/engine.mjs'));
      try {
        return await mod.loadEngine();
      } catch (e) {
        console.log(`SKIP: the Lean wasm engine is not available: ${e.message}`);
        return null;
      }
    })();
  }
  return enginePromise;
}

/** Call one op once; `{ok:false, error}` instead of a throw. */
export async function callOnce(op, args) {
  const e = await engine();
  try {
    return e.call(op, [JSON.stringify(args)]);
  } catch (err) {
    return { ok: false, error: String(err?.message ?? err) };
  }
}

/** Call a JWE op to completion, answering every `need` with WebCrypto.
 *  `seen`, when given, receives each request the op made. */
export async function callJwe(op, args, seen = null) {
  return runWithCipher(async (a) => {
    const r = await callOnce(op, a);
    if (seen && r && r.need) seen.push(r.need);
    return r;
  }, args);
}

export const b64 = (u8) => Buffer.from(u8).toString('base64');
export const unb64 = (s) => new Uint8Array(Buffer.from(s, 'base64'));
export const b64u = (u8) => Buffer.from(u8).toString('base64url');
export const unb64u = (s) => new Uint8Array(Buffer.from(s, 'base64url'));
