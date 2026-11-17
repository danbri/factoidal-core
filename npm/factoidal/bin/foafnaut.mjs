#!/usr/bin/env node
// foafnaut: start the Foafnaut web browser (macOS) in its own window.
// This launcher only chooses, installs and starts a macOS app. All page work is in that app.
// Layout: $FOAFNAUT_HOME (default ~/.foafnaut), versions/<12 hex>/, current -> versions/<12 hex>,
// config.json {"bleedingEdge":"/path/to/App.app"}.
//
// Modes (owner, 2026-11-16: the old ones were confusing):
//   foafnaut                 the installed build (current), with no network use
//   foafnaut --update        install the newest build of main and make it current (--install-latest)
//   foafnaut --latest        --update, then run it
//   foafnaut --bleeding-edge your local build
//   foafnaut --which/--list  what runs, what is installed, what is newest
import { spawn, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, lstatSync, mkdirSync, readFileSync, readdirSync, realpathSync, renameSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { ReleaseError, assetUrl, mainReleases } from './foafnaut-releases.mjs';

const HELP = `foafnaut: the Foafnaut web browser (macOS, Apple silicon)

  foafnaut [PAGE]                  open PAGE in the installed build (no network check)
  foafnaut --update                install the newest build of main and make it the one
                                   that runs; prints what it replaced
  foafnaut --latest [PAGE]         --update, then open PAGE
  foafnaut --bleeding-edge [PAGE]  open PAGE in your local build (config.json "bleedingEdge",
                                   else ~/Applications/foafnaut.app)
  foafnaut --which                 which build runs, the newest build of main, your local build
  foafnaut --list                  installed builds (* is the one that runs)
  foafnaut --version               commit and build time, as the app reports them

PAGE is an http(s) or file: URL or an HTML file (or --url URL, --html FILE); none opens the
start page. --verbose prints the choice and follows the trace; --detach returns at once.

App options, passed to the app: --perf-summary, --check-pixels, --wasm-engine,
--native-engine PATH, --font FILE, --bitmap-font, --follow-links,
--be-liberal-in-what-we-accept (draw pages that use features the browser skips, listing them
in the console, Option-Command-J); more after --, and in --dev-help.

Environment: FOAFNAUT_APP runs that app outright; FOAFNAUT_HOME (default ~/.foafnaut);
GITHUB_TOKEN is used by --update if set. Trace: ~/Library/Logs/foafnaut/trace.jsonl.
Old names still work: --install-latest (now --update), foafnaut-latest, foafnaut-bleedingedge.

EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.
`;
const DEV_HELP = `foafnaut --dev-help: tools for developing and testing the browser

More app options (passed to the app as they are)
  --offscreen            no window: draw into a GPU texture (for tests and captures)
  --shot FILE            write a PNG of the page (with --offscreen)
  --print-pdf FILE       print the page to a PDF file
  --no-scripts           run no page scripts
  --strict               refuse pages with features the browser skips (the default)
  --no-state             no saved state: no history, bookmarks or session
  --state-dir DIR        keep the saved state in DIR
  --restore-session      reopen the tabs of the last run
  --no-splash            no splash at start (off already offscreen and in checks)
  --single-frame         draw the page as one layer (no partial frames)
  --gpu-frames-in-flight N  GPU frames queued at most (default: 1 for heavy work, 3 for light)
  --trace-input          log every input event and edge drag to stderr
  --check-engine         run the engine on the main thread and check its render plan (CPU)
  --quickjs-wasm FILE    run page scripts on QuickJS-NG in BubblePopWASM from FILE
                         (BubblePopJS, the built-in JavaScript engine, is the default)
  --*-sweep              scripted checks used by the tests (scroll, resize, find, ...);
                         see labs/demos/foafnaut/sweeps.sh

Inside the browser
  Option-Command-J       the console: page script output, refusals, skipped features
  about:foafnaut         version, commit, build time and the specifications implemented,
                         written by the engine; facts from the desktop program are marked
  foafnaut:console, foafnaut:sparql, foafnaut:wasm   developer pages
  Command-F              find in page

Through a proxy (developer proxy: tools/devproxy/README.md, in the source repository)
  The app uses HTTP_PROXY, HTTPS_PROXY and DENO_CERT from its environment, so it can run
  through a local proxy with no change. tools/devproxy/devproxy.mjs records real pages once
  to WARC and replays them offline, and can simplify pages as it serves them:
    full             no change
    no-scripts       scripts and on* attributes removed
    text-css-links   structure, text, links and stylesheets kept; scripts, frames, media,
                     images, canvas and svg removed
  Run it with tools/devproxy/foafnaut-through-proxy.sh (--record NAME, --replay NAME, or
  devproxy.mjs --passthrough --default-service LEVEL). It listens on 127.0.0.1 only, with a
  private CA for this process only. A test tool, not a sanitiser and not a security
  boundary. Page scripts' XMLHttpRequest and fetch() may not go through the proxy yet.

Not yet: a debugging protocol (Chrome DevTools Protocol, WebDriver BiDi), an MCP server,
breakpoints, console input. Plan: https://github.com/danbri/factoidal-core/issues/372

Logs: ~/Library/Logs/foafnaut/trace.jsonl. Source and issues:
https://github.com/danbri/factoidal-core (labs/demos/foafnaut/).
`;
const APP = 'foafnaut.app';
const ARCHIVE = 'foafnaut-darwin-arm64.tar.gz';
const TARGET = 'darwin-arm64';

/** A message for the terminal; main() prints it and exits 1. */
class LaunchError extends Error {}
const fail = (message) => { throw new LaunchError(message); };

const home = (env = process.env) => env.FOAFNAUT_HOME || join(homedir(), '.foafnaut');
function config(env) {
  const path = join(home(env), 'config.json');
  if (!existsSync(path)) return {};
  try { return JSON.parse(readFileSync(path, 'utf8')); } catch (error) { fail(`${path}: ${error.message}`); }
}
export const bleedingEdgeApp = (env = process.env) => config(env).bleedingEdge || join(homedir(), 'Applications', APP);
function versionApp(dir) {
  const app = join(dir, 'foafnaut', APP);
  return existsSync(app) ? app : undefined;
}
/** The 12-hex name of the current version, or undefined. */
export function currentName(env = process.env) {
  try { return basename(realpathSync(join(home(env), 'current'))); } catch { return undefined; }
}
const currentApp = (env) => { const n = currentName(env); return n ? versionApp(join(home(env), 'versions', n)) : undefined; };

const readJson = (path) => { try { return JSON.parse(readFileSync(path, 'utf8')); } catch { return undefined; } };
/** What is known of an installed version: {name, commit, committedAt, builtAt, tag}. */
export function versionInfo(env, name) {
  const dir = join(home(env), 'versions', name);
  const installed = readJson(join(dir, 'installed.json')) ?? {};
  const release = readJson(join(dir, 'build-info.json')) ?? {};
  const inner = readJson(join(dir, 'foafnaut', 'BUILD-INFO.json')) ?? {};
  return { name, commit: installed.commit ?? release.source_commit ?? inner.commitFull ?? name, committedAt: installed.committedAt,
    builtAt: release.built_at ?? inner.builtAt, tag: installed.tag ?? `build-${name}-foafnaut-${TARGET}`, installedAt: installed.installedAt };
}
const when = (iso) => (iso ? iso.replace('T', ' ').replace(/:\d\d(\.\d+)?Z$/, 'Z') : 'unknown');
const short = (sha) => (sha ?? '').slice(0, 12);
const describe = (v) => {
  const facts = [v.committedAt && `committed ${when(v.committedAt)}`, v.builtAt && `built ${when(v.builtAt)}`].filter(Boolean);
  return `${short(v.commit)}${facts.length ? ` (${facts.join(', ')})` : ''}`;
};
/** The local build: {app, commit, builtAt, dirty, hours} from BUILD-INFO.json beside it. */
function localInfo(app) {
  const info = readJson(join(dirname(app), 'BUILD-INFO.json'));
  if (!info) return { app, text: `${app} (no BUILD-INFO.json, so its commit is not known)` };
  const hours = (Date.now() - Date.parse(info.builtAt)) / 3.6e6;
  return { app, text: `${app}\n    built from ${info.commit}${info.dirty ? ' with uncommitted changes' : ''} at ${when(info.builtAt)} (${hours.toFixed(1)} h ago)` +
    (hours > 6 ? '; it may lack newer work on main' : '') };
}

async function download(fetchImpl, url) {
  let reply;
  try { reply = await fetchImpl(url, { headers: { 'user-agent': 'foafnaut' }, redirect: 'follow' }); } catch (error) {
    fail(`can not download ${url} (${error.cause?.code ?? error.message}); check the network connection`);
  }
  if (!reply.ok) fail(`${url}: HTTP ${reply.status}`);
  return Buffer.from(await reply.arrayBuffer());
}

/** Downloads a release into versions/<12 hex>, checking the archive against its build-info.json. */
async function installRelease(env, release, fetchImpl, log) {
  const dir = join(home(env), 'versions', release.sha12);
  if (versionApp(dir)) return dir;
  const info = JSON.parse((await download(fetchImpl, assetUrl(release.tag, 'build-info.json'))).toString('utf8'));
  const expected = info.artifacts?.[ARCHIVE]?.sha256;
  if (!expected) fail(`${release.tag}: its build-info.json has no digest for ${ARCHIVE}; nothing was changed`);
  const size = info.artifacts[ARCHIVE].size;
  log(`foafnaut: downloading ${release.tag}${size ? ` (${(size / 1e6).toFixed(0)} MB)` : ''}`);
  const archive = await download(fetchImpl, assetUrl(release.tag, ARCHIVE));
  const actual = createHash('sha256').update(archive).digest('hex');
  if (expected !== actual) fail(`${release.tag}: the download does not match its published digest (sha256 ${actual}, expected ${expected}); nothing was changed`);
  const staging = `${dir}.tmp`;
  rmSync(staging, { recursive: true, force: true });
  mkdirSync(staging, { recursive: true });
  writeFileSync(join(staging, 'archive.tar.gz'), archive);
  const unpack = spawnSync('tar', ['-xzf', 'archive.tar.gz'], { cwd: staging, stdio: 'inherit' });
  if (unpack.status !== 0) { rmSync(staging, { recursive: true, force: true }); fail(`${release.tag}: tar could not unpack the archive; nothing was changed`); }
  rmSync(join(staging, 'archive.tar.gz'));
  writeFileSync(join(staging, 'build-info.json'), JSON.stringify(info, null, 2));
  if (!versionApp(staging)) {
    rmSync(staging, { recursive: true, force: true });
    fail(`${release.tag} has no ${APP}; it predates the native window. Use --bleeding-edge.`);
  }
  rmSync(dir, { recursive: true, force: true });
  renameSync(staging, dir);
  return dir;
}

function makeCurrent(env, name) {
  const link = join(home(env), 'current');
  let old;
  try { old = lstatSync(link); } catch { old = undefined; }
  if (old && !old.isSymbolicLink()) fail(`${link} is not a symbolic link; it was left alone`);
  if (old) rmSync(link);
  symlinkSync(join('versions', name), link);
}

/**
 * --update: installs the newest build of main and makes it current. Never replaces a current build that
 * is newer on main than every release found. Returns the app path.
 */
export async function update({ env = process.env, fetchImpl = globalThis.fetch, log = (s) => console.error(s), verbose = false } = {}) {
  const before = currentName(env);
  log('foafnaut: looking for the newest macOS build of main ...');
  let found;
  try { found = await mainReleases({ target: TARGET, currentSha: before, fetchImpl, env }); } catch (error) {
    if (error instanceof ReleaseError) fail(`${error.message}. Nothing was changed.`);
    throw error;
  }
  if (verbose) for (const n of found.notes) log(`foafnaut: ${n}`);
  else for (const n of found.notes.filter((n) => !/skipped$/.test(n))) log(`foafnaut: note: ${n}`);
  const newest = found.releases[0];
  if (!newest) fail('no macOS build of main has been published yet. Nothing was changed.');
  const was = before ? versionInfo(env, before) : undefined;
  if (was && found.current) was.committedAt ??= found.current.committedAt;
  if (before === newest.sha12 && versionApp(join(home(env), 'versions', before))) {
    log(`foafnaut: already up to date: ${describe({ ...was, committedAt: newest.committedAt ?? was.committedAt })}`);
    return currentApp(env);
  }
  if (found.current?.onBranch && newest.aheadBy !== undefined && found.current.aheadBy <= newest.aheadBy) {
    log(`foafnaut: the installed build ${describe(was)} is as new as or newer than the newest release (${newest.tag}); kept it`);
    return currentApp(env);
  }
  const dir = await installRelease(env, newest, fetchImpl, log);
  writeFileSync(join(dir, 'installed.json'), JSON.stringify({ tag: newest.tag, commit: newest.commit, committedAt: newest.committedAt,
    publishedAt: newest.publishedAt, installedAt: new Date().toISOString() }, null, 1) + '\n');
  makeCurrent(env, newest.sha12);
  const now = versionInfo(env, newest.sha12);
  log(`foafnaut: was ${was ? describe(was) : 'nothing installed'}`);
  log(`foafnaut: now ${describe(now)}, from ${newest.tag}` +
    (newest.aheadBy ? `; main has ${newest.aheadBy} newer commits with no macOS build yet` : '; the head of main'));
  return versionApp(dir);
}

/** --which: the build that runs, the newest build of main, and the local build. */
export async function which({ env = process.env, fetchImpl = globalThis.fetch, out = (s) => console.log(s), channel = 'current' } = {}) {
  const name = currentName(env), local = bleedingEdgeApp(env);
  const runs = env.FOAFNAUT_APP ? `${env.FOAFNAUT_APP} (from FOAFNAUT_APP)` : channel === 'bleeding-edge' ? local : currentApp(env) ?? (existsSync(local) ? `${local} (your local build: no release is installed)` : 'nothing: run foafnaut --update');
  out(`runs:           ${runs}`);
  const cur = name ? versionInfo(env, name) : undefined;
  let found;
  try { found = await mainReleases({ target: TARGET, currentSha: name, fetchImpl, env }); } catch (error) {
    found = { error: error instanceof ReleaseError ? error.message : String(error) };
  }
  if (cur && found.current?.committedAt) cur.committedAt ??= found.current.committedAt;
  out(`installed:      ${cur ? describe(cur) : 'none'}`);
  const newest = found.releases?.[0];
  if (found.error) out(`newest on main: could not check: ${found.error}`);
  else if (!newest) out('newest on main: no macOS build of main is published yet');
  else {
    const gap = found.current?.onBranch && newest.aheadBy !== undefined ? found.current.aheadBy - newest.aheadBy : undefined;
    const state = name === newest.sha12 ? 'installed; up to date'
      : gap === undefined ? 'not installed; foafnaut --update installs it'
      : gap > 0 ? `${gap} commits newer than the installed build; foafnaut --update installs it`
      : 'the installed build is as new or newer';
    out(`newest on main: ${describe(newest)}, published ${when(newest.publishedAt)}\n    ${state}` +
      (newest.aheadBy ? `; main has ${newest.aheadBy} later commits with no macOS build yet` : ''));
  }
  out(`bleeding edge:  ${existsSync(local) ? localInfo(local).text : `${local} (not found)`}`);
}

/** --list: installed versions, newest build first, with * on the current one. */
export function list({ env = process.env, out = (s) => console.log(s) } = {}) {
  const versions = join(home(env), 'versions'), current = currentName(env);
  const names = existsSync(versions) ? readdirSync(versions).filter((n) => !n.includes('.tmp') && versionApp(join(versions, n))) : [];
  const infos = names.map((n) => versionInfo(env, n)).sort((a, b) => (b.builtAt ?? '').localeCompare(a.builtAt ?? ''));
  if (infos.length === 0) out('no builds installed (foafnaut --update installs one)');
  for (const v of infos) out(`${v.name === current ? '*' : ' '} ${describe(v)}`);
  const local = bleedingEdgeApp(env);
  out(`  bleeding edge: ${local}${existsSync(local) ? '' : ' (not found)'}`);
}

// App options that take no value, and those that take one.
const APP_FLAGS = ['--perf-summary', '--check-pixels', '--wasm-engine', '--bitmap-font', '--follow-links', '--idle-checks-only', '--trace-input', '--be-liberal-in-what-we-accept'];
const APP_VALUES = ['--native-engine', '--font'];

function pageArgs(page) {
  if (page === undefined) return [];
  if (/^https?:\/\//i.test(page)) return ['--url', page];
  // file:///abs/path is a URL; file:name.html has no // and is relative to here.
  if (/^file:\/\//i.test(page)) page = fileURLToPath(page);
  else if (/^file:/i.test(page)) page = decodeURIComponent(page.slice(5));
  const path = resolve(page);
  if (!existsSync(path)) fail(`no such file: ${page}`);
  return ['--html', path];
}

/** Reads the command line: {channel, action, page, verbose, detach, app_, notes}. Throws LaunchError. */
export function parseArgs(argv, channel = 'current') {
  const split = argv.indexOf('--');
  const options = split < 0 ? argv : argv.slice(0, split);
  const r = { channel, action: 'run', page: undefined, verbose: false, detach: false, app_: [], extra: split < 0 ? [] : argv.slice(split + 1), notes: [] };
  const setPage = (value) => { if (r.page !== undefined) fail('give one page'); if (value === undefined) fail('a page option needs a value'); r.page = value; };
  // Each of these picks the build or the action; two of them together have no one meaning.
  const picks = options.filter((a) => ['--latest', '--bleeding-edge', '--update', '--install-latest', '--list'].includes(a));
  if (new Set(picks).size > 1) fail(`${picks.join(' and ')} can not be used together; see --help`);
  for (let i = 0; i < options.length; i++) {
    const arg = options[i];
    if (arg === '--help' || arg === '-h') return { ...r, action: 'help' };
    if (arg === '--dev-help') return { ...r, action: 'dev-help' };
    if (arg === '--latest') r.channel = 'latest';
    else if (arg === '--bleeding-edge') r.channel = 'bleeding-edge';
    else if (arg === '--update') r.action = 'update';
    else if (arg === '--install-latest') { r.action = 'update'; r.notes.push('--install-latest is now called --update; it does the same'); }
    else if (arg === '--list') r.action = 'list';
    else if (arg === '--which') r.action = 'which';
    else if (arg === '--version') r.action = 'version';
    else if (arg === '--verbose' || arg === '-v') r.verbose = true;
    else if (arg === '--detach') r.detach = true;
    else if (arg === '--url' || arg === '--html') setPage(options[++i]);
    else if (arg.startsWith('--url=') || arg.startsWith('--html=')) setPage(arg.slice(arg.indexOf('=') + 1));
    else if (APP_FLAGS.includes(arg)) r.app_.push(arg);
    else if (APP_VALUES.includes(arg)) { if (options[i + 1] === undefined) fail(`${arg} needs a value`); r.app_.push(arg, options[++i]); }
    else if (arg.startsWith('-')) fail(`unknown option ${arg}; see --help`);
    else setPage(arg);
  }
  return r;
}

/** The app to run, and a line saying which it is. */
async function chooseApp(r, env) {
  if (env.FOAFNAUT_APP) return { app: env.FOAFNAUT_APP, say: `foafnaut: running ${env.FOAFNAUT_APP} (from FOAFNAUT_APP)` };
  const local = bleedingEdgeApp(env);
  if (r.channel === 'bleeding-edge') {
    if (!existsSync(local)) fail(`no local build at ${local}. Set "bleedingEdge" in ${join(home(env), 'config.json')}, or run foafnaut --update for a release.`);
    return { app: local, say: `foafnaut: running your local build ${localInfo(local).text}` };
  }
  if (r.channel === 'latest') {
    try { await update({ env, verbose: r.verbose }); } catch (error) {
      if (!(error instanceof LaunchError) || !currentApp(env)) throw error;
      console.error(`foafnaut: could not update: ${error.message}\nfoafnaut: starting the installed build instead`);
    }
  }
  const app = currentApp(env);
  if (app) {
    const v = versionInfo(env, currentName(env));
    const newerLocal = existsSync(local) && statSync(local).mtimeMs > statSync(app).mtimeMs;
    return { app, say: `foafnaut: running ${describe(v)}` + (newerLocal ? '\nfoafnaut: your local build is newer; foafnaut --bleeding-edge runs it' : '') };
  }
  if (existsSync(local)) return { app: local, say: `foafnaut: no release is installed (foafnaut --update installs one); running your local build ${localInfo(local).text}` };
  fail('Foafnaut is not installed yet. Run: foafnaut --update');
}

export async function main(argv, channel = 'current', env = process.env) {
  try {
    const r = parseArgs(argv, channel);
    if (r.action === 'help') { process.stdout.write(HELP); return; }
    if (r.action === 'dev-help') { process.stdout.write(DEV_HELP); return; }
    for (const n of r.notes) console.error(`foafnaut: ${n}`);
    if (r.action === 'list') { list({ env }); return; }
    if (r.action === 'which') { await which({ env, channel: r.channel }); return; }
    if (process.platform !== 'darwin') fail('the Foafnaut app is for macOS only; elsewhere use the Hub page in a WebGPU browser');
    if (r.action === 'update') { await update({ env, verbose: r.verbose }); return; }
    const { app, say } = await chooseApp(r, env);
    if (!existsSync(app)) fail(`no app at ${app}. Run foafnaut --update.`);
    // The app answers for itself. `open` shows no output, so run its program directly.
    if (r.action === 'version') {
      const run = spawnSync(join(dirname(app), 'native-webgpu-html-darwin-arm64'), ['--version'], { encoding: 'utf8' });
      if (run.status === 0) process.stdout.write(run.stdout);
      else console.log(`foafnaut: this build is too old to answer --version (${app})`);
      return;
    }
    console.error(say);
    const args = ['-n', ...(r.detach ? [] : ['-W']), app, '--args', ...pageArgs(r.page), ...(r.verbose ? ['--trace-input'] : []), ...r.app_, ...r.extra];
    const log = join(homedir(), 'Library', 'Logs', 'foafnaut', 'trace.jsonl');
    if (r.verbose) console.error(`foafnaut: open ${args.join(' ')}\nfoafnaut: trace ${log}`);
    // Follow only what this run appends.
    const follow = r.verbose ? spawn('tail', ['-n', '0', '-F', log], { stdio: ['ignore', 'inherit', 'ignore'] }) : undefined;
    const run = spawnSync('open', args, { stdio: 'inherit' });
    follow?.kill();
    process.exitCode = run.status ?? 1;
  } catch (error) {
    if (!(error instanceof LaunchError || error instanceof ReleaseError)) throw error;
    console.error(`foafnaut: ${error.message}`);
    process.exitCode = 1;
  }
}

if (import.meta.url === pathToFileURL(realpathSync(process.argv[1])).href) await main(process.argv.slice(2));
