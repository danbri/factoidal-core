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
//   DIR/lws.lock            the lock of the one writing process (named by
//                           the engine, issue 1135; see the end of this file)
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

import { closeSync, fsyncSync, mkdirSync, openSync, readFileSync, renameSync, unlinkSync, writeSync, existsSync } from 'node:fs'
import { dirname, join, resolve, sep } from 'node:path'
import { hostname } from 'node:os'

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

/** The environment variable that sets where `lws-serve DIR` keeps the
 *  storage when the caller names no `storage` (issue 918). */
export const STORAGE_MODE_VARIABLE = 'FACTOIDAL_LWS_STORAGE'

/**
 * The text of the storage mode: `explicit` when the caller gave a string,
 * and otherwise the environment variable, passed unread; the engine checks
 * it. An empty value is none (the engine's default, the snapshot).
 */
export function storageModeText (explicit) {
  if (typeof explicit === 'string') return explicit
  let value
  try {
    if (globalThis.process !== undefined && globalThis.process.env !== undefined) {
      value = globalThis.process.env[STORAGE_MODE_VARIABLE]
    } else if (globalThis.Deno !== undefined) {
      value = globalThis.Deno.env.get(STORAGE_MODE_VARIABLE)
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
    throw Object.assign(new Error(`${file} is not JSON: ${error.message}`), { stateFile: true })
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

// ---------------------------------------------------------------------------
// A STORAGE KEPT IN FILES (https://github.com/danbri/factoidal/issues/918)
//
// With the open configuration `storage: "files"` the engine decides the
// directory layout and every byte (formal/lean4/L4Factoidal/LWS/FileLayout.lean,
// design record docs/designissues/2026-10-22-lws-storage-on-disk.md). This
// part of the file only performs what the engine names:
//
//   * reads: the engine names files (paths relative to DIR); each is read
//     whole, or reported absent. At start (`lwsLoad`) and before a step that
//     needs the bytes of a resource (a `read` answer of `lwsStep`, given to
//     `lwsRead`, stage 2 of issue 918);
//   * a plan of file operations, in order, with their bytes in one region:
//       write  {path, temp, offset, length}  parent directory, temp file,
//                                            fsync, rename, fsync directory
//       append {path, offset, length}        append, fsync
//       remove {path}                        remove; a missing file is no error
//       rename {from, to}                    rename, fsync directory; a missing
//                                            file is no error
//
// A name that leaves DIR is refused as a failure of this host; the engine
// never names one.

/** The absolute path of a name the engine gave, inside DIR. */
function insideDir (root, name) {
  if (typeof name !== 'string' || name === '') throw new Error('lws files: the engine named no file')
  const abs = resolve(root, name)
  if (!abs.startsWith(root + sep)) throw new Error(`lws files: ${name} is outside the storage directory`)
  return abs
}

/** fsync a directory; some platforms cannot, and the rename stands. */
function fsyncDir (dir) {
  try {
    const fd = openSync(dir, 'r')
    try { fsyncSync(fd) } finally { closeSync(fd) }
  } catch (_error) {
    // Some platforms cannot fsync a directory.
  }
}

/** `seed` for one engine call: 32 random bytes, base64. Pure I/O. */
function seedBase64 () {
  const bytes = new Uint8Array(32)
  globalThis.crypto.getRandomValues(bytes)
  let text = ''
  for (const b of bytes) text += String.fromCharCode(b)
  return btoa(text)
}

/**
 * Read the files the engine named. Returns the `files` member of the load
 * document and the bytes of the present files, one after the other.
 */
export function readNamedFiles (dir, names) {
  const root = resolve(dir)
  const files = []
  const parts = []
  let total = 0
  for (const name of names) {
    const abs = insideDir(root, name)
    if (!existsSync(abs)) {
      files.push({ path: name, present: false })
      continue
    }
    const bytes = readFileSync(abs)
    files.push({ path: name, present: true, length: bytes.length })
    parts.push(bytes)
    total += bytes.length
  }
  const region = new Uint8Array(total)
  let at = 0
  for (const part of parts) { region.set(part, at); at += part.length }
  return { files, region }
}

/** Perform a plan of file operations exactly as the engine gave it. */
export function performPlan (dir, plan, bytes) {
  const root = resolve(dir)
  mkdirSync(root, { recursive: true })
  const slice = (op) => bytes.subarray(op.offset, op.offset + op.length)
  for (const op of Array.isArray(plan) ? plan : []) {
    switch (op.op) {
      case 'write': {
        const path = insideDir(root, op.path)
        const temp = insideDir(root, op.temp)
        mkdirSync(dirname(path), { recursive: true })
        const fd = openSync(temp, 'w', 0o600)
        try {
          writeSync(fd, slice(op))
          fsyncSync(fd)
        } finally {
          closeSync(fd)
        }
        renameSync(temp, path)
        fsyncDir(dirname(path))
        break
      }
      case 'append': {
        const path = insideDir(root, op.path)
        mkdirSync(dirname(path), { recursive: true })
        const fd = openSync(path, 'a', 0o600)
        try {
          writeSync(fd, slice(op))
          fsyncSync(fd)
        } finally {
          closeSync(fd)
        }
        break
      }
      case 'remove': {
        try { unlinkSync(insideDir(root, op.path)) } catch (error) {
          if (error.code !== 'ENOENT') throw error
        }
        break
      }
      case 'rename': {
        const to = insideDir(root, op.to)
        try { renameSync(insideDir(root, op.from), to) } catch (error) {
          if (error.code !== 'ENOENT') throw error
        }
        fsyncDir(dirname(to))
        break
      }
      default:
        throw new Error(`lws files: the engine named an unknown file operation ${String(op.op)}`)
    }
  }
}

/**
 * Open a storage kept in files: read what `lwsOpen` named, give it to
 * `lwsLoad`, read what that names, until the engine is ready; then perform
 * the plan of the start. An engine refusal is thrown as the engine's error.
 */
export function loadFiles (engine, handle, opened, dir) {
  let want = opened.load
  for (let round = 0; round < 8; round += 1) {
    const { files, region } = readNamedFiles(dir, Array.isArray(want.read) ? want.read : [])
    const answered = engine.callBlobIO('lwsLoad', [handle, JSON.stringify({ files, seed: seedBase64() })], region)
    const envelope = answered.envelope
    if (envelope.ready === true) {
      performPlan(dir, envelope.plan, answered.bytes)
      return envelope
    }
    if (envelope.load === undefined || envelope.load === null) {
      throw new Error('lwsLoad answered neither load nor ready')
    }
    want = envelope.load
  }
  throw new Error('lwsLoad asked for more reads than one start may make')
}

/**
 * Before one step of a storage kept in files (stage 2): read the body files
 * the engine named in a `read` answer and give them to `lwsRead`. The engine
 * checks each one (seal, length, digests); a refusal is thrown as its error.
 */
export function readStepBodies (engine, handle, names, dir) {
  const { files, region } = readNamedFiles(dir, Array.isArray(names) ? names : [])
  const answered = engine.callBlobIO('lwsRead', [handle, JSON.stringify({ files })], region)
  const envelope = answered.envelope
  if (envelope === null || typeof envelope !== 'object' || envelope.ok !== true) {
    throw new Error(`lwsRead: ${envelope !== null && typeof envelope === 'object' ? envelope.error : 'no answer'}`)
  }
}

/**
 * After one step of a storage kept in files: when the engine says the
 * storage changed, ask it for the write plan (`lwsPersist`) and perform it.
 */
export function persistFilesIfChanged (engine, handle, envelope, dir) {
  if (typeof dir !== 'string' || envelope === null || typeof envelope !== 'object') return
  if (envelope.changed !== true) return
  const answered = engine.callBlobIO('lwsPersist', [handle, JSON.stringify({ seed: seedBase64() })], new Uint8Array(0))
  performPlan(dir, answered.envelope.plan, answered.bytes)
}

// ---------------------------------------------------------------------------
// ONE WRITING PROCESS PER STORAGE DIRECTORY
// (https://github.com/danbri/factoidal/issues/1135)
//
// The engine decides the lock file name, its contents and what a start does
// (`lwsDirLock`, formal/lean4/L4Factoidal/LWS/DirLock.lean). This host does
// three things only: the exclusive create of the file it names (flag `wx`,
// O_EXCL), the liveness probe of a process id it names (`kill(pid, 0)`), and
// the removal of the file at a clean exit. Each result goes back to the
// engine as data.

/** Random text of this process, drawn once: it tells a lock this process
 *  wrote from the lock of an earlier process with the same process id. */
let processToken = null
function processTokenText () {
  if (processToken === null) {
    const bytes = new Uint8Array(18)
    globalThis.crypto.getRandomValues(bytes)
    let text = ''
    for (const b of bytes) text += String.fromCharCode(b)
    processToken = btoa(text)
  }
  return processToken
}

/** The lock files this process holds: absolute path -> contents. */
const heldLocks = new Map()
let exitHookSet = false

/** Remove a lock file this process holds, when it still holds this
 *  process's contents. Pure I/O. */
function removeHeldLock (file) {
  if (!heldLocks.has(file)) return
  const contents = heldLocks.get(file)
  heldLocks.delete(file)
  try {
    if (readFileSync(file, 'utf8') === contents) unlinkSync(file)
  } catch (_error) {
    // Already gone, or not readable: nothing to remove.
  }
}

/** At process exit (normal end, `process.exit`, and after a SIGINT or
 *  SIGTERM handler ends the process), remove every lock still held. */
function ensureExitHook () {
  if (exitHookSet || globalThis.process === undefined || typeof globalThis.process.on !== 'function') return
  exitHookSet = true
  globalThis.process.on('exit', () => {
    for (const file of [...heldLocks.keys()]) removeHeldLock(file)
  })
}

/** Is process `pid` alive on this host? Pure I/O: `kill(pid, 0)`; EPERM
 *  means it exists under another user. */
function processAlive (pid) {
  try {
    globalThis.process.kill(pid, 0)
    return true
  } catch (error) {
    return error !== null && typeof error === 'object' && error.code === 'EPERM'
  }
}

/** Create `file` with O_EXCL and write `contents`; false when it exists. */
function createExclusive (file, contents) {
  let fd
  try {
    fd = openSync(file, 'wx', 0o600)
  } catch (error) {
    if (error.code === 'EEXIST') return false
    throw error
  }
  try {
    writeSync(fd, contents)
    fsyncSync(fd)
  } finally {
    closeSync(fd)
  }
  return true
}

/** An error that stops a start because another process holds the storage
 *  directory. `envelope` carries the engine's message, as for every other
 *  refusal of a start. */
export class StorageLockedError extends Error {
  constructor (message) {
    super(message)
    this.name = 'StorageLockedError'
    this.envelope = { ok: false, error: message }
  }
}

/**
 * Take the lock of storage directory `dir` for `command` (`lws-serve`,
 * `solid-serve`, `webdav-serve`). Returns `{ file, warning, release }`:
 * `warning` is the engine's text when it took over a stale lock, else null;
 * `release()` removes the lock. Throws `StorageLockedError` with the
 * engine's message when the engine refuses.
 */
export function acquireDirLock (engine, dir, command) {
  const root = resolve(dir)
  mkdirSync(root, { recursive: true })
  const base = {
    dir: root,
    pid: globalThis.process.pid,
    command,
    started: new Date().toISOString(),
    host: hostname(),
    token: processTokenText()
  }
  let request = { ...base }
  // Each round is one engine answer; a create that loses to another start
  // reads the file again and asks again.
  for (let round = 0; round < 8; round += 1) {
    const told = engine.call('lwsDirLock', [JSON.stringify(request)])
    if (told === null || typeof told !== 'object' || told.ok === false) {
      throw Object.assign(new Error(`lwsDirLock: ${told && told.error ? told.error : 'no answer'}`), { envelope: told })
    }
    switch (told.action) {
      case 'create':
      case 'replace': {
        const file = insideDir(root, told.file)
        if (told.action === 'replace') {
          try { unlinkSync(file) } catch (error) { if (error.code !== 'ENOENT') throw error }
        }
        if (createExclusive(file, told.contents)) {
          heldLocks.set(file, told.contents)
          ensureExitHook()
          return {
            file,
            warning: told.action === 'replace' ? told.warning : null,
            release: () => removeHeldLock(file)
          }
        }
        let present = null
        try { present = readFileSync(file, 'utf8') } catch (error) { if (error.code !== 'ENOENT') throw error }
        request = present === null ? { ...base } : { ...base, present }
        break
      }
      case 'probe':
        request = { ...request, alive: processAlive(Number(told.pid)) }
        break
      case 'refuse':
        throw new StorageLockedError(told.message)
      default:
        throw new Error(`lwsDirLock answered an unknown action ${String(told.action)}`)
    }
  }
  throw new Error('lwsDirLock: the lock file changed on every attempt')
}

/**
 * The start notice about encryption at rest of the storage in `dir`
 * (`lwsAtRestNotice`): `{ sealed, keyId?, notice }`. The key text is passed
 * unread; the engine checks it.
 */
export function atRestNotice (engine, dir, storageKey) {
  const request = { dir: resolve(dir) }
  if (typeof storageKey === 'string') request.storageKey = storageKey
  const told = engine.call('lwsAtRestNotice', [JSON.stringify(request)])
  if (told === null || typeof told !== 'object' || told.ok === false) {
    throw Object.assign(new Error(`lwsAtRestNotice: ${told && told.error ? told.error : 'no answer'}`), { envelope: told })
  }
  return told
}
