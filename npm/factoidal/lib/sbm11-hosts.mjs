// Storage-medium hosts for the Sbm11 store ops (sbm11Open, sbm11Query,
// sbm11Close; formal/lean4/Wasm/Ops/Sbm11.lean).
// https://github.com/danbri/factoidal/issues/1009 KR1 and
// https://github.com/danbri/factoidal/issues/1010 KR1.
//
// The engine asks for byte ranges of named objects through two globals
// (formal/lean4/ffi/l4_medium.c):
//
//   globalThis.__factoidalMediumRead(root, name, off, len) -> Uint8Array | null
//   globalThis.__factoidalMediumSize(root, name)           -> number (-1: absent)
//
// `root` is the string the caller gave to openSbm11Store; `name` is an object
// name the engine built from the manifest it decoded. A host maps the pair to
// bytes and decides nothing else: no file name, no format, no digest (CLAUDE.md
// iron rule 7; tools/host-purity-lint.sh checks this file).
//
// A host is an object { read(root, name, off, len), size(root, name),
// close?(root) }. installMediumBridge() keeps one host per root, so stores
// with different hosts (Node fs now; OPFS and HTTP Range in issue 1010 KR2)
// can be open at once.

const hostsByRoot = new Map();

function bridgeRead(root, name, off, len) {
  const host = hostsByRoot.get(String(root));
  if (!host) return null;
  return host.read(String(root), String(name), Number(off), Number(len));
}

function bridgeSize(root, name) {
  const host = hostsByRoot.get(String(root));
  if (!host) return -1;
  return host.size(String(root), String(name));
}

/**
 * Register `host` for store root `root` and install the two globals the
 * engine calls.
 * @param {string} root
 * @param {{read: Function, size: Function, close?: Function}} host
 */
export function installMediumBridge(root, host) {
  if (!host || typeof host.read !== 'function' || typeof host.size !== 'function') {
    throw new TypeError('openSbm11Store: a medium host has read(root, name, off, len) and size(root, name)');
  }
  hostsByRoot.set(String(root), host);
  globalThis.__factoidalMediumRead = bridgeRead;
  globalThis.__factoidalMediumSize = bridgeSize;
}

/**
 * Drop the host of `root` when no open store uses it.
 * @param {string} root
 */
export function releaseMediumBridge(root) {
  const host = hostsByRoot.get(String(root));
  hostsByRoot.delete(String(root));
  if (host && typeof host.close === 'function') host.close(String(root));
}

/**
 * The Node host: object `name` of root `root` is the file `root/name`, read
 * with positioned reads (fs.readSync at an offset; no shared file cursor).
 * A name with an empty, `.` or `..` segment, or an absolute name, is refused
 * (the engine never builds one; the check keeps a host from reading outside
 * the root).
 * @param {{fs: object, path: object}} mods node:fs and node:path
 */
export function nodeMediumHost({ fs, path }) {
  const fds = new Map();
  const fileOf = (root, name) => {
    const segs = String(name).split('/');
    if (name.startsWith('/') || segs.some((s) => s === '' || s === '.' || s === '..' || s.includes('\\'))) {
      return null;
    }
    return path.join(root, ...segs);
  };
  const fdOf = (file) => {
    let fd = fds.get(file);
    if (fd === undefined) {
      fd = fs.openSync(file, 'r');
      fds.set(file, fd);
    }
    return fd;
  };
  return {
    read(root, name, off, len) {
      const file = fileOf(root, name);
      if (file === null) return null;
      try {
        const buf = new Uint8Array(len);
        let done = 0;
        while (done < len) {
          const n = fs.readSync(fdOf(file), buf, done, len - done, off + done);
          if (n <= 0) return null;
          done += n;
        }
        return buf;
      } catch (_err) {
        return null;
      }
    },
    size(root, name) {
      const file = fileOf(root, name);
      if (file === null) return -1;
      try {
        const st = fs.statSync(file);
        return st.isFile() ? st.size : -1;
      } catch (_err) {
        return -1;
      }
    },
    close(root) {
      const prefix = path.join(root, '');
      for (const [file, fd] of fds) {
        if (file.startsWith(prefix)) {
          try { fs.closeSync(fd); } catch (_err) { /* already closed */ }
          fds.delete(file);
        }
      }
    },
  };
}
