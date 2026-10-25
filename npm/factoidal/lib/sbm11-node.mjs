// The Node reader of an SBM11 generation directory for lib/sbm11.mjs: the
// source is a directory path, and a file of the generation is read with
// fs.readSync at an offset (https://github.com/danbri/factoidal/issues/1009
// KR1). It moves bytes only (iron rule 7); the engine checks every length.
//
// One open file descriptor per file, kept while the reader lives: a query
// makes many small reads of the same few files.

import { closeSync, fstatSync, openSync, readSync, statSync } from 'node:fs'
import { join } from 'node:path'

export function nodeDirectoryReader (dir) {
  const fds = new Map()
  function fdOf (file) {
    let fd = fds.get(file)
    if (fd === undefined) {
      fd = openSync(join(dir, file), 'r')
      fds.set(file, fd)
    }
    return fd
  }
  return {
    readAt (file, offset, length) {
      const out = new Uint8Array(length)
      const fd = fdOf(file)
      let done = 0
      while (done < length) {
        const n = readSync(fd, out, done, length - done, offset + done)
        if (n === 0) break
        done += n
      }
      return done === length ? out : null
    },
    size (file) {
      try {
        const fd = fds.get(file)
        const st = fd === undefined ? statSync(join(dir, file)) : fstatSync(fd)
        return st.isFile() ? st.size : null
      } catch {
        return null
      }
    },
    close () {
      for (const fd of fds.values()) closeSync(fd)
      fds.clear()
    }
  }
}

/** A default-reader factory: one reader per directory, kept. */
export function nodeDefaultReaderFactory () {
  const byDir = new Map()
  return (source) => {
    let r = byDir.get(source)
    if (!r) {
      r = nodeDirectoryReader(source)
      byDir.set(source, r)
    }
    return r
  }
}
