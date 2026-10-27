// The load-time check of the engine against its release stamp
// (https://github.com/danbri/factoidal/issues/1106, layer 1).
//
// A release stamps l4-assets/version.json with the SHA-256 and the size of
// l4factoidal.wasm (tools/stamp-l4-version.mjs). Before an engine is
// instantiated, its bytes are hashed and compared with the stamp: a stamped
// copy whose bytes differ does not load. An unstamped copy (a source
// checkout, a local build that did not stamp) loads as before.
//
// This catches accidents (a stale wasm next to a new loader, a partial
// upgrade, a hand edit). It is not a defence against someone who can edit
// the package: they can edit this file too. See issue 1106 for the checks
// made from outside the package.
//
// ES module, no Node built-ins: Node, Deno and the browser load it as it is.
// The digest is Web Crypto's SHA-256 (globalThis.crypto.subtle).

/** Lowercase hex SHA-256 of `bytes` (a Uint8Array or an ArrayBuffer). */
export async function sha256Hex(bytes) {
  const subtle = globalThis.crypto && globalThis.crypto.subtle;
  if (!subtle) throw new Error('factoidal: no Web Crypto SHA-256 to check the engine with');
  const digest = new Uint8Array(await subtle.digest('SHA-256', bytes));
  let hex = '';
  for (const b of digest) hex += b.toString(16).padStart(2, '0');
  return hex;
}

/**
 * Check engine bytes against a version.json stamp.
 * @param {Uint8Array|ArrayBuffer} bytes the wasm
 * @param {object|null} stamp the parsed version.json, or null when absent
 * @param {{where?: string, allowModified?: boolean, warn?: (msg: string) => void}} [opts]
 * @returns {Promise<{checked: boolean, sha256?: string}>} `checked` false for
 *   an absent or unstamped version.json
 */
export async function checkEngineStamp(bytes, stamp, opts = {}) {
  if (!stamp || stamp.stamped !== true || typeof stamp.wasmSha256 !== 'string') {
    return { checked: false };
  }
  const size = bytes.byteLength;
  const sha256 = await sha256Hex(bytes);
  const sizeOk = !Number.isInteger(stamp.wasmBytes) || stamp.wasmBytes === size;
  if (sha256 === stamp.wasmSha256.toLowerCase() && sizeOk) return { checked: true, sha256 };
  const where = opts.where || 'l4factoidal.wasm';
  const msg = `factoidal: ${where} is not the engine of this release: version.json ` +
    `(build ${stamp.release ?? stamp.gitSha ?? '?'}) says sha256 ${stamp.wasmSha256}, ${stamp.wasmBytes ?? '?'} bytes; ` +
    `the file has sha256 ${sha256}, ${size} bytes. Reinstall @factoidal/core, ` +
    'or set FACTOIDAL_ALLOW_MODIFIED_ENGINE=1 to load a changed engine on purpose.';
  if (opts.allowModified) {
    (opts.warn || (() => {}))(`${msg} Loading it because FACTOIDAL_ALLOW_MODIFIED_ENGINE is set.`);
    return { checked: false, sha256 };
  }
  const err = new Error(msg);
  err.code = 'engine.modified';
  throw err;
}
