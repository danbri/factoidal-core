// Installing the native Linux engine (libweb-render.so) into $FOAFNAUT_HOME (default ~/.foafnaut),
// where chooseEngine finds it: versions/<commit>/foafnaut/libweb-render.so, and current -> versions/<commit>.
// The library is self-contained (the Lean runtime is linked in), so no Lean toolchain is needed.
// The download is checked by SHA-256 before anything is kept: against engine-pin.json's `native`
// entry when it has one for this platform, else (with `latest`) against the release's build-info.json.
import { chmodSync, lstatSync, mkdirSync, renameSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { arch as osArch, homedir, platform } from 'node:os';
import { join } from 'node:path';
import { gunzipSync } from 'node:zlib';
import { pin, sha256, untar } from './engine.mjs';

const LIBRARY = 'foafnaut/libweb-render.so';
const KEEP = [LIBRARY, 'foafnaut/README-linux.txt', 'foafnaut/engine-build.txt'];

/** linux-x86_64 or linux-arm64 on Linux; undefined elsewhere. */
export function nativePlatform(os = platform(), cpu = osArch()) {
  if (os !== 'linux') return undefined;
  return cpu === 'x64' ? 'linux-x86_64' : cpu === 'arm64' ? 'linux-arm64' : undefined;
}

/** The release to install: {release, url, commit, tarball: {bytes, sha256}, file: {bytes, sha256}, pinned}. */
export async function nativeChoice(target, { channel = 'pinned', fetchImpl = globalThis.fetch, thePin = pin } = {}) {
  const pinned = thePin.native?.[target];
  if (channel === 'pinned' && pinned) return { ...pinned, pinned: true };
  const headers = { accept: 'application/vnd.github+json', 'user-agent': 'textnaut' };
  const list = await fetchImpl(`https://api.github.com/repos/${thePin.repository}/releases?per_page=100`, { headers });
  if (!list.ok) throw new Error(`the release list: HTTP ${list.status}`);
  const tag = new RegExp(`^build-[0-9a-f]{12}-foafnaut-${target}$`);
  const releases = (await list.json()).filter((r) => tag.test(r.tag_name) && r.published_at)
    .sort((a, b) => b.published_at.localeCompare(a.published_at));
  const asset = `foafnaut-${target}.tar.gz`;
  for (const r of releases) {
    const infoUrl = r.assets.find((a) => a.name === 'build-info.json')?.browser_download_url;
    const url = r.assets.find((a) => a.name === asset)?.browser_download_url;
    if (!infoUrl || !url) continue;
    const reply = await fetchImpl(infoUrl, { headers: { 'user-agent': 'textnaut' }, redirect: 'follow' });
    if (!reply.ok) continue;
    const info = await reply.json();
    // Older Linux releases link Lean's shared runtime and need the toolchain: not these.
    if (info.library?.self_contained !== true) continue;
    const art = info.artifacts?.[asset];
    const file = art?.files?.[LIBRARY];
    if (!art?.sha256 || !file?.sha256) continue;
    return { release: r.tag_name, url, commit: info.source_commit, tarball: { bytes: art.size, sha256: art.sha256 },
      file: { bytes: file.size, sha256: file.sha256 }, pinned: false };
  }
  throw new Error(`no self-contained ${target} engine release in ${thePin.repository} yet`);
}

/** Checks the download against the choice and returns the files to keep: [{name, data}]. */
export function checkNativeTarball(bytes, choice) {
  if (choice.tarball.bytes && bytes.length !== choice.tarball.bytes) throw new Error(`the download is ${bytes.length} bytes; ${choice.tarball.bytes} expected`);
  const got = sha256(bytes);
  if (got !== choice.tarball.sha256) throw new Error(`the download has sha256 ${got}; ${choice.tarball.sha256} expected`);
  const entries = untar(gunzipSync(bytes));
  const lib = entries.find((e) => e.name === LIBRARY);
  if (!lib) throw new Error(`${LIBRARY} is not in the download`);
  if (sha256(lib.data) !== choice.file.sha256) throw new Error(`${LIBRARY} does not match its sha256`);
  return entries.filter((e) => KEEP.includes(e.name));
}

const mb = (n) => (n / 1e6).toFixed(1);

/**
 * Downloads, checks and installs the native engine; returns the library's path.
 * `channel`: 'pinned' (engine-pin.json's entry, else the newest self-contained release) or 'latest'.
 */
export async function installNative({ channel = 'pinned', env = process.env, home = homedir(), os = platform(), cpu = osArch(),
  fetchImpl = globalThis.fetch, log = (s) => process.stderr.write(s + '\n'), thePin = pin } = {}) {
  const target = nativePlatform(os, cpu);
  if (!target) {
    throw new Error(os === 'darwin'
      ? 'the native engine for macOS comes with the foafnaut app (npx -p @factoidal/core foafnaut --install-latest); Textnaut finds it there.'
      : `there is no native engine for ${os} ${cpu}; Textnaut uses the Wasm engine.`);
  }
  const choice = await nativeChoice(target, { channel, fetchImpl, thePin });
  log(`textnaut: installing the native engine ${choice.release}${choice.tarball.bytes ? ` (${mb(choice.tarball.bytes)} MB)` : ''}\n` +
      `          checked against sha256 ${choice.tarball.sha256.slice(0, 16)}... ` +
      (choice.pinned ? '(pinned in this package)' : '(from the release\'s build-info.json; not pinned in this package)'));
  const reply = await fetchImpl(choice.url, { redirect: 'follow', headers: { 'user-agent': 'textnaut' } });
  if (!reply.ok) throw new Error(`${choice.url}: HTTP ${reply.status}`);
  const files = checkNativeTarball(Buffer.from(await reply.arrayBuffer()), choice);
  const base = env.FOAFNAUT_HOME || join(home, '.foafnaut');
  const id = (choice.commit || choice.release).slice(0, 12);
  const dir = join(base, 'versions', id);
  const temp = `${dir}.tmp-${process.pid}`;
  rmSync(temp, { recursive: true, force: true });
  for (const f of files) {
    mkdirSync(join(temp, 'foafnaut'), { recursive: true });
    writeFileSync(join(temp, f.name), f.data);
  }
  chmodSync(join(temp, LIBRARY), 0o755);
  writeFileSync(join(temp, 'build-info.json'), JSON.stringify({ release: choice.release, commit: choice.commit, url: choice.url,
    tarball: choice.tarball, library: choice.file, pinned: choice.pinned }, null, 1) + '\n');
  rmSync(dir, { recursive: true, force: true });
  mkdirSync(join(base, 'versions'), { recursive: true });
  renameSync(temp, dir);
  const link = join(base, 'current');
  let old;
  try { old = lstatSync(link); } catch { old = undefined; }
  if (old && !old.isSymbolicLink()) throw new Error(`${link} is not a symbolic link; it was left alone (the engine is in ${dir})`);
  if (old) rmSync(link);
  symlinkSync(join('versions', id), link);
  const path = join(link, LIBRARY);
  log(`textnaut: native engine installed: ${path}`);
  return path;
}
