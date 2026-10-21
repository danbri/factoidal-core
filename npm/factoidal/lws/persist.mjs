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
// address a file outside DIR. The write is: a temporary file in DIR,
// fsync, rename over the state file, fsync of DIR. A crash leaves the old
// snapshot or the new one, never a torn one.

import { closeSync, fsyncSync, mkdirSync, openSync, readFileSync, renameSync, writeSync, existsSync } from 'node:fs'
import { join, resolve } from 'node:path'

export const STATE_FILE = 'lws-state.json'

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
 * the snapshot (`snapshotOp`) and write it.
 */
export function persistIfChanged (engine, snapshotOp, handle, envelope, dir) {
  if (typeof dir !== 'string' || envelope === null || typeof envelope !== 'object') return
  if (envelope.changed !== true) return
  const answer = engine.call(snapshotOp, [handle])
  if (answer === null || typeof answer !== 'object' || answer.snapshot === undefined) {
    throw new Error(`${snapshotOp} answered with no snapshot`)
  }
  writeSnapshot(dir, answer.snapshot)
}
