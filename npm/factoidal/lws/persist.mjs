// Durable storage for `factoidal lws-serve DIR` and `solid-serve DIR`.
// https://github.com/danbri/factoidal/issues/659
//
// WHAT THIS FILE IS ALLOWED TO DO
// Move bytes between one file and the engine. The engine decides what
// the bytes are (`L4Factoidal/LWS/Snapshot.lean`): the snapshot document,
// which paths it may hold (no `..`, no absolute or encoded traversal), and
// when the storage changed (the `changed` member of the step envelope).
// This file decides only where the one file lives and how it is written:
//
//   DIR/lws-state.json      the snapshot, replaced atomically
//
// No request target ever becomes a file name here, so a request cannot
// address a file outside DIR.
//
// ENCRYPTION AT REST (https://github.com/danbri/factoidal/issues/921)
// This file also reads the environment variable FACTOIDAL_LWS_KEY and
// draws 12 random bytes for every write. Both go to the engine unread: the
// key text as the open configuration's `storageKey`, the bytes as the
// `nonce` of the snapshot call. The engine decides everything else
// (`L4Factoidal/LWS/SnapshotSeal.lean`): whether the key is valid, whether
// the file in DIR is sealed, whether it authenticates, and the bytes of
// the sealed document. This file never inspects the document it writes. The write is: a temporary file in DIR,
// fsync, rename over the state file, fsync of DIR. A crash leaves the old
// snapshot or the new one, never a torn one.

import { closeSync, fsyncSync, mkdirSync, openSync, readFileSync, renameSync, writeSync, existsSync } from 'node:fs'
import { join, resolve } from 'node:path'

export const STATE_FILE = 'lws-state.json'

/** The environment variable that holds the storage key. */
export const STORAGE_KEY_VARIABLE = 'FACTOIDAL_LWS_KEY'

/**
 * The text of the storage key: `explicit` when the caller gave a string,
 * none when the caller gave `null`, and otherwise the environment variable
 * (Node `process.env`, or `Deno.env` when only Deno's API is present). An
 * empty value is no key. The engine checks the text.
 */
export function storageKeyText (explicit) {
  if (typeof explicit === 'string') return explicit
  if (explicit === null) return undefined
  let value
  try {
    if (globalThis.process !== undefined && globalThis.process.env !== undefined) {
      value = globalThis.process.env[STORAGE_KEY_VARIABLE]
    } else if (globalThis.Deno !== undefined) {
      value = globalThis.Deno.env.get(STORAGE_KEY_VARIABLE)
    }
  } catch (_error) {
    value = undefined
  }
  return typeof value === 'string' && value !== '' ? value : undefined
}

/** 12 bytes from the platform's random source, base64: the nonce of one
 *  snapshot write. Pure I/O. */
function nonceBase64 () {
  const bytes = new Uint8Array(12)
  globalThis.crypto.getRandomValues(bytes)
  let text = ''
  for (const b of bytes) text += String.fromCharCode(b)
  return btoa(text)
}

/** The absolute path of the state file of a storage directory. */
export function stateFileOf (dir) {
  return join(resolve(dir), STATE_FILE)
}

/**
 * The parsed snapshot in DIR, or `null` when DIR holds none yet. The
 * engine checks the document; a file that does not parse as JSON is an
 * error of this host, reported as such.
 */
export function readSnapshot (dir) {
  const file = stateFileOf(dir)
  if (!existsSync(file)) return null
  const text = readFileSync(file, 'utf8')
  try {
    return JSON.parse(text)
  } catch (error) {
    throw new Error(`${file} is not JSON: ${error.message}`)
  }
}

/** Write a snapshot document to DIR, atomically. */
export function writeSnapshot (dir, snapshot) {
  const root = resolve(dir)
  mkdirSync(root, { recursive: true })
  const file = stateFileOf(root)
  const temporary = join(root, `.${STATE_FILE}.${process.pid}.tmp`)
  const fd = openSync(temporary, 'w', 0o600)
  try {
    writeSync(fd, JSON.stringify(snapshot))
    fsyncSync(fd)
  } finally {
    closeSync(fd)
  }
  renameSync(temporary, file)
  try {
    const dirFd = openSync(root, 'r')
    try { fsyncSync(dirFd) } finally { closeSync(dirFd) }
  } catch (_error) {
    // Some platforms cannot fsync a directory; the rename stands.
  }
}

/**
 * After one step: when the engine says the storage changed, ask it for
 * the snapshot (`snapshotOp`) and write it. The call carries a fresh random
 * nonce; the engine uses it when the storage is sealed under a key.
 */
export function persistIfChanged (engine, snapshotOp, handle, envelope, dir) {
  if (typeof dir !== 'string' || envelope === null || typeof envelope !== 'object') return
  if (envelope.changed !== true) return
  const answer = engine.call(snapshotOp, [handle, JSON.stringify({ nonce: nonceBase64() })])
  if (answer === null || typeof answer !== 'object' || answer.snapshot === undefined) {
    throw new Error(`${snapshotOp} answered with no snapshot`)
  }
  writeSnapshot(dir, answer.snapshot)
}
