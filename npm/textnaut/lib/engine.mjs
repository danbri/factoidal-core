// Finding and fetching the Wasm engine. The only network use in this package is one download of
// a pinned release asset, checked against a sha256 recorded in engine-pin.json, on the first
// run that needs the engine. Nothing is sent but the request for that file.
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, renameSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { homedir, platform } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { gunzipSync } from 'node:zlib';

export const pin = JSON.parse(readFileSync(join(dirname(fileURLToPath(import.meta.url)), '..', 'engine-pin.json'), 'utf8'));
export const sha256 = (bytes) => createHash('sha256').update(bytes).digest('hex');
const RUNTIME = Object.values(pin.files);

/** The cache directory for this pin: $TEXTNAUT_CACHE, else $XDG_CACHE_HOME/textnaut, else ~/.cache/textnaut; keyed by commit. */
export function cacheDir(env = process.env, home = homedir()) {
  const base = env.TEXTNAUT_CACHE || join(env.XDG_CACHE_HOME || join(home, '.cache'), 'textnaut');
  return join(base, `engine-${pin.commit.slice(0, 12)}`);
}

/** True when both runtime files are in `dir` with the pinned size and sha256. */
export function cacheValid(dir) {
  return RUNTIME.every((f) => {
    try {
      const path = join(dir, f.name);
      return statSync(path).size === f.bytes && sha256(readFileSync(path)) === f.sha256;
    } catch { return false; }
  });
}

/** The entries of a tar archive (ustar and pax long names): [{name, data}] for regular files. */
export function untar(buffer) {
  const out = [];
  let offset = 0, longName = null;
  while (offset + 512 <= buffer.length) {
    const header = buffer.subarray(offset, offset + 512);
    if (header.every((b) => b === 0)) break;
    const text = (a, b) => header.toString('utf8', a, b).replace(/\0.*$/s, '');
    let name = text(0, 100);
    const prefix = text(345, 500);
    if (prefix) name = `${prefix}/${name}`;
    const size = parseInt(text(124, 136).trim() || '0', 8);
    const type = String.fromCharCode(header[156] || 48);
    const data = buffer.subarray(offset + 512, offset + 512 + size);
    offset += 512 + Math.ceil(size / 512) * 512;
    if (type === 'x') { const m = /\d+ path=([^\n]*)\n/.exec(data.toString('utf8')); if (m) longName = m[1]; continue; }
    if (type === 'L') { longName = data.toString('utf8').replace(/\0.*$/s, ''); continue; }
    if (type === '0' || type === '\0') out.push({ name: (longName ?? name).replace(/^\.\//, ''), data });
    longName = null;
  }
  return out;
}

/**
 * Checks a downloaded asset against the pin and returns the two runtime files. Throws, and
 * returns nothing, when the size or the sha256 of the download, or of either file, is wrong.
 */
export function checkTarball(bytes, thePin = pin) {
  if (bytes.length !== thePin.tarball.bytes) throw new Error(`the download is ${bytes.length} bytes; ${thePin.tarball.bytes} expected`);
  const got = sha256(bytes);
  if (got !== thePin.tarball.sha256) throw new Error(`the download has sha256 ${got}; the pinned release has ${thePin.tarball.sha256}`);
  const entries = untar(gunzipSync(bytes));
  const files = [];
  for (const [path, f] of Object.entries(thePin.files)) {
    const entry = entries.find((e) => e.name === path);
    if (!entry) throw new Error(`${path} is not in the download`);
    if (sha256(entry.data) !== f.sha256 || entry.data.length !== f.bytes) throw new Error(`${f.name} does not match the pinned sha256`);
    files.push({ name: f.name, data: Buffer.from(entry.data) });
  }
  return files;
}

const mb = (n) => (n / 1e6).toFixed(1);

/**
 * The directory holding web-render.mjs and web-render.wasm, fetching them once when they are not
 * cached. `fetchImpl` is for tests. Errors are plain messages for the person at the terminal.
 */
export async function ensureEngine({ env = process.env, fetchImpl = globalThis.fetch, log = (s) => process.stderr.write(s + '\n') } = {}) {
  const dir = cacheDir(env);
  if (cacheValid(dir)) return dir;
  const diskBytes = RUNTIME.reduce((n, f) => n + f.bytes, 0);
  log(`textnaut: fetching the Wasm engine, once: ${mb(pin.tarball.bytes)} MB from github.com/${pin.repository}\n` +
      `          release ${pin.release} (${mb(diskBytes)} MB kept in ${dir}).\n` +
      `          It is checked against sha256 ${pin.tarball.sha256.slice(0, 16)}... before use. Nothing else is downloaded or sent.`);
  let bytes;
  try {
    const response = await fetchImpl(pin.url, { redirect: 'follow' });
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    bytes = Buffer.from(await response.arrayBuffer());
  } catch (error) {
    throw new Error(`could not fetch the Wasm engine (${error.cause?.code ?? error.message}). ` +
      `You may be offline. Screensavers need no engine: textnaut --screensaver. ` +
      `To use a page, connect once, or set TEXTNAUT_WASM_DIR to a directory with web-render.mjs and web-render.wasm, ` +
      `or TEXTNAUT_NATIVE to a libweb-render library.`);
  }
  let files;
  try { files = checkTarball(bytes); } catch (error) {
    throw new Error(`the downloaded engine was refused: ${error.message}. Nothing was kept.`);
  }
  const temp = `${dir}.tmp-${process.pid}`;
  rmSync(temp, { recursive: true, force: true });
  mkdirSync(temp, { recursive: true });
  for (const f of files) writeFileSync(join(temp, f.name), f.data);
  writeFileSync(join(temp, 'PIN.json'), JSON.stringify({ commit: pin.commit, release: pin.release, runtimeFormat: pin.runtimeFormat }) + '\n');
  rmSync(dir, { recursive: true, force: true });
  renameSync(temp, dir);
  return dir;
}

/** The library of an installed foafnaut (FOAFNAUT_HOME or ~/.foafnaut), or undefined. */
export function installedLibrary(env = process.env, home = homedir(), os = platform()) {
  const lib = os === 'darwin' ? 'libweb-render.dylib' : 'libweb-render.so';
  const path = join(env.FOAFNAUT_HOME || join(home, '.foafnaut'), 'current', 'foafnaut', lib);
  return existsSync(path) ? path : undefined;
}

/**
 * Which engine to use, in order: --engine FILE (textnaut takes it as it is); TEXTNAUT_NATIVE;
 * TEXTNAUT_WASM_DIR; an installed foafnaut's library; the pinned Wasm engine.
 * Returns {env} to add and {fetch: true} when the Wasm engine is needed.
 */
export function chooseEngine(args, env = process.env, home = homedir(), os = platform()) {
  if (args.includes('--engine')) return { how: '--engine', env: {} };
  const wasm = args.includes('--wasm');
  if (!wasm && env.TEXTNAUT_NATIVE) return { how: 'TEXTNAUT_NATIVE', env: {} };
  if (env.TEXTNAUT_WASM_DIR) return { how: 'TEXTNAUT_WASM_DIR', env: {} };
  const lib = wasm ? undefined : installedLibrary(env, home, os);
  if (lib) return { how: 'installed foafnaut', env: { TEXTNAUT_NATIVE: lib } };
  return { how: 'pinned Wasm engine', env: {}, fetch: true };
}
