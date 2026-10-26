// Host plumbing for the Lean persisted store (Shardborough IBK3/IBK4/IBK5
// generations), shared by Node and the browser.
//
// A store is read through a READER: a function from a path relative to the
// collection root ('CURRENT', 'gen-1/manifest.sbm2',
// 'gen-1/predicate-0.ibk3', ...) to the bytes of that file (a Uint8Array or
// an ArrayBuffer, or a Promise of either). index.mjs builds one over the
// file system; a browser page builds one over fetch().
//
// WHAT THIS FILE IS ALLOWED TO DO
// Read CURRENT, read a manifest by name, read the artifact files the
// engine named, concatenate their bytes and say where each one starts.
// It never parses a manifest, verifies a digest, decodes a block or
// chooses an artifact: the ops storeManifestInspect, storeQueryPlan and
// storeOpen (formal/lean4/Wasm/Ops/Store.lean, StoreHandles.lean) decide
// all of that. bin/store.mjs is the same plumbing over store-host/ for the
// `factoidal` command.

import { requireChildName } from '../store-host/paths.mjs';
import { hostError } from './errors.mjs';

/** The manifest file names a generation directory can carry, in the order
 *  the native tools try them. */
export const MANIFEST_NAMES = ['manifest.sbm2', 'manifest.sbm1'];

async function readBytes(reader, path) {
  const out = await reader(path);
  if (out instanceof Uint8Array) return out;
  if (out instanceof ArrayBuffer) return new Uint8Array(out);
  if (ArrayBuffer.isView(out)) return new Uint8Array(out.buffer, out.byteOffset, out.byteLength);
  throw new TypeError(
    `store reader: '${path}' answered ${out === null ? 'null' : typeof out}, ` +
    'expected a Uint8Array or an ArrayBuffer');
}

/**
 * The generation to open and its manifest bytes. With no `generation`,
 * CURRENT names it (an activated collection); with one, that generation is
 * opened directly, activated or not.
 */
export async function openGeneration(reader, generation) {
  let name = generation;
  if (name == null) {
    let pointer;
    try {
      pointer = await readBytes(reader, 'CURRENT');
    } catch (cause) {
      throw hostError(
        `openStore: the collection root has no readable CURRENT pointer (${cause && cause.message})`, cause);
    }
    // CURRENT holds a UTF-8 generation name (docs/shardborough-storage-spec.md
    // section 6.4); trailing ASCII whitespace is tolerated, as in
    // store-host/index.mjs.
    name = new TextDecoder('utf-8', { fatal: true }).decode(pointer).replace(/[\r\n\t ]+$/, '');
    requireChildName(name, 'CURRENT');
  } else {
    requireChildName(String(name), 'generation');
    name = String(name);
  }
  for (const manifestName of MANIFEST_NAMES) {
    let manifest;
    try {
      manifest = await readBytes(reader, `${name}/${manifestName}`);
    } catch (_err) {
      continue;
    }
    return { generation: name, manifestName, manifest, activated: generation == null };
  }
  throw hostError(`openStore: generation '${name}' has none of ${MANIFEST_NAMES.join(', ')}`);
}

/** Read the named artifacts of one generation into one region, with a
 *  {key, offset, len} window per artifact. */
export async function readRegion(reader, generation, keys) {
  const chunks = [];
  for (const key of keys) chunks.push(await readBytes(reader, `${generation}/${key}`));
  let total = 0;
  for (const c of chunks) total += c.length;
  const blob = new Uint8Array(total);
  const artifacts = [];
  let offset = 0;
  for (let i = 0; i < chunks.length; i += 1) {
    blob.set(chunks[i], offset);
    artifacts.push({ key: keys[i], offset, len: chunks[i].length });
    offset += chunks[i].length;
  }
  return { blob, artifacts, total };
}

/** The artifact keys a manifest declares, as storeManifestInspect lists
 *  them: every block, every index sidecar, every out-of-line literal. */
export function manifestKeys(inspectEnvelope) {
  const keys = [];
  for (const entry of inspectEnvelope.entries || []) {
    keys.push(entry.key);
    for (const key of Object.values(entry.sidecars || {})) keys.push(key);
  }
  for (const blob of inspectEnvelope.blobs || []) keys.push(blob.key);
  return keys;
}

const HEX_DIGIT = Uint8Array.from('0123456789abcdef', (c) => c.charCodeAt(0));
const HEX_DECODER = new TextDecoder();

/** Lowercase hexadecimal: the transport the manifest argument of the store
 *  ops takes. Artifact bytes never take this path. */
export function hexOfBytes(bytes) {
  // One byte buffer of ASCII digits, decoded once (issue 1039; see
  // bin/engine.mjs hexOfBytes).
  const out = new Uint8Array(bytes.length * 2);
  for (let i = 0, at = 0; i < bytes.length; i += 1, at += 2) {
    out[at] = HEX_DIGIT[bytes[i] >> 4];
    out[at + 1] = HEX_DIGIT[bytes[i] & 15];
  }
  return HEX_DECODER.decode(out);
}
