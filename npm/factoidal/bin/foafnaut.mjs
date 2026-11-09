#!/usr/bin/env node
// foafnaut: start foafnaut2525, the Lean web rendering engine, in its own window.
// This launcher only chooses and starts an installed macOS app. All page work is
// in that app. Layout: $FOAFNAUT_HOME (default ~/.foafnaut), versions/<commit>/,
// current -> versions/<commit>, config.json {"bleedingEdge":"/path/to/App.app"}.
import { spawn, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readFileSync, readdirSync, realpathSync, renameSync, rmSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { homedir } from 'node:os';
import { basename, dirname, join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const HELP = `foafnaut [--latest|--bleeding-edge] [PAGE | --url URL | --html FILE] [APP_OPTIONS] [-- APP_ARGS]

  PAGE              an http(s) or file: URL, or an HTML file; none opens the default page
  --url URL         the page as a URL (http, https or file)
  --html FILE       the page as a local HTML file
  --latest          install the newest published macOS build, then use it
  --bleeding-edge   use the local build (config.json "bleedingEdge", or
                    ~/Applications/foafnaut.app)
  --verbose         print the choice of app, follow the trace, and log input
  --detach          do not wait for the window to close
  --install-latest  install the newest published build and stop
  --list            list installed versions
  --which           print the app that would run
  --help            this text

App options, passed to the app as they are:
  --perf-summary    print frame and input latency figures when the window closes
  --check-pixels    read back and check every frame (slow)
  --wasm-engine     use the Wasm engine, not the native library
  --native-engine PATH  use this native engine library
  --font FILE       load this font file
  --bitmap-font     use the baked-in ASCII font only
  --follow-links    open links that a page asks for at load
  --be-liberal-in-what-we-accept  draw a page without the features this browser may skip
                    (module scripts, unreadable media conditions, stylesheets that did not
                    load) and list them in the console (Option-Command-J); the default refuses

Also: foafnaut-latest, foafnaut-bleedingedge. Environment: FOAFNAUT_HOME, and
FOAFNAUT_APP, which chooses the app outright. Page data goes to the app. Its trace
is in ~/Library/Logs/foafnaut/trace.jsonl. The command stays open until the window
closes; --detach returns at once.

EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.
`;
const RELEASES = 'https://api.github.com/repos/danbri/factoidal-builds/releases?per_page=60';
const APP = 'foafnaut.app';
const home = () => process.env.FOAFNAUT_HOME || join(homedir(), '.foafnaut');
const fail = (message) => { console.error(`foafnaut: ${message}`); process.exit(1); };

function config() {
  const path = join(home(), 'config.json');
  if (!existsSync(path)) return {};
  try { return JSON.parse(readFileSync(path, 'utf8')); } catch (error) { fail(`${path}: ${error.message}`); }
}
const bleedingEdgeApp = () => config().bleedingEdge || join(homedir(), 'Applications', APP);
function versionApp(dir) {
  const app = join(dir, 'foafnaut', APP);
  return existsSync(app) ? app : undefined;
}
function currentApp() {
  const current = join(home(), 'current');
  return existsSync(current) ? versionApp(current) : undefined;
}

async function installLatest() {
  const response = await fetch(RELEASES, { headers: { accept: 'application/vnd.github+json', 'user-agent': 'foafnaut' } });
  if (!response.ok) fail(`release list: HTTP ${response.status}`);
  // The release list is not in publication order.
  const release = (await response.json())
    .filter((r) => /^build-[0-9a-f]{12}-foafnaut-darwin-arm64$/.test(r.tag_name) && r.published_at)
    .sort((a, b) => b.published_at.localeCompare(a.published_at))[0];
  if (!release) fail('no published macOS build');
  const commit = release.tag_name.split('-')[1];
  const dir = join(home(), 'versions', commit);
  if (!versionApp(dir)) {
    const asset = (name) => release.assets.find((a) => a.name === name)?.browser_download_url ?? fail(`${release.tag_name}: no ${name}`);
    const download = async (url) => {
      const reply = await fetch(url, { headers: { 'user-agent': 'foafnaut' } });
      if (!reply.ok) fail(`${url}: HTTP ${reply.status}`);
      return Buffer.from(await reply.arrayBuffer());
    };
    console.error(`foafnaut: downloading ${release.tag_name}`);
    const info = JSON.parse((await download(asset('build-info.json'))).toString('utf8'));
    const archive = await download(asset('foafnaut-darwin-arm64.tar.gz'));
    const expected = info.artifacts?.['foafnaut-darwin-arm64.tar.gz']?.sha256;
    const actual = createHash('sha256').update(archive).digest('hex');
    if (!expected) fail(`${release.tag_name}: build-info.json has no archive digest`);
    if (expected !== actual) fail(`${release.tag_name}: archive digest ${actual} is not ${expected}`);
    const staging = `${dir}.tmp`;
    rmSync(staging, { recursive: true, force: true });
    mkdirSync(staging, { recursive: true });
    writeFileSync(join(staging, 'archive.tar.gz'), archive);
    const unpack = spawnSync('tar', ['-xzf', 'archive.tar.gz'], { cwd: staging, stdio: 'inherit' });
    if (unpack.status !== 0) fail('tar failed');
    rmSync(join(staging, 'archive.tar.gz'));
    writeFileSync(join(staging, 'build-info.json'), JSON.stringify(info, null, 2));
    if (!versionApp(staging)) {
      rmSync(staging, { recursive: true, force: true });
      fail(`${release.tag_name} has no ${APP}; it predates the native window. Use --bleeding-edge.`);
    }
    rmSync(dir, { recursive: true, force: true });
    renameSync(staging, dir);
  }
  const link = join(home(), 'current');
  rmSync(link, { force: true });
  symlinkSync(join('versions', commit), link);
  console.error(`foafnaut: current is ${commit}`);
  return versionApp(dir);
}

// App options that take no value, and those that take one.
const APP_FLAGS = ['--perf-summary', '--check-pixels', '--wasm-engine', '--bitmap-font', '--follow-links', '--idle-checks-only', '--trace-input', '--be-liberal-in-what-we-accept'];
const APP_VALUES = ['--native-engine', '--font'];

function pageArgs(page) {
  if (page === undefined) return [];
  if (/^https?:\/\//i.test(page)) return ['--url', page];
  if (/^file:/i.test(page)) page = new URL(page).pathname;
  const path = resolve(page);
  if (!existsSync(path)) fail(`no such file: ${page}`);
  return ['--html', path];
}

export async function main(argv, channel = 'current') {
  const split = argv.indexOf('--');
  const options = split < 0 ? argv : argv.slice(0, split);
  const extra = split < 0 ? [] : argv.slice(split + 1);
  let page, which = false, verbose = false, detach = false;
  const app_ = [];
  const setPage = (value) => { if (page !== undefined) fail('give one page'); if (value === undefined) fail('a page option needs a value'); page = value; };
  // Each of these picks the app or the action. Two of them have no one meaning.
  const exclusive = options.filter((arg) => ['--latest', '--bleeding-edge', '--install-latest', '--list'].includes(arg));
  if (new Set(exclusive).size > 1) fail(`${exclusive.join(' and ')} can not be used together; see --help`);
  for (let i = 0; i < options.length; i++) {
    const arg = options[i];
    if (arg === '--help' || arg === '-h') { process.stdout.write(HELP); return; }
    else if (arg === '--latest') channel = 'latest';
    else if (arg === '--bleeding-edge') channel = 'bleeding-edge';
    else if (arg === '--which') which = true;
    else if (arg === '--verbose' || arg === '-v') verbose = true;
    else if (arg === '--detach') detach = true;
    else if (arg === '--install-latest') { await installLatest(); return; }
    else if (arg === '--list') {
      const versions = join(home(), 'versions');
      const current = existsSync(join(home(), 'current')) ? basename(realpathSync(join(home(), 'current'))) : '';
      for (const name of existsSync(versions) ? readdirSync(versions).filter((n) => !n.endsWith('.tmp')) : [])
        console.log(`${name === current ? '*' : ' '} ${name}`);
      console.log(`  bleeding edge: ${bleedingEdgeApp()}${existsSync(bleedingEdgeApp()) ? '' : ' (not found)'}`);
      return;
    } else if (arg === '--url' || arg === '--html') setPage(options[++i]);
    else if (arg.startsWith('--url=') || arg.startsWith('--html=')) setPage(arg.slice(arg.indexOf('=') + 1));
    else if (APP_FLAGS.includes(arg)) app_.push(arg);
    else if (APP_VALUES.includes(arg)) { if (options[i + 1] === undefined) fail(`${arg} needs a value`); app_.push(arg, options[++i]); }
    else if (arg.startsWith('-')) fail(`unknown option ${arg}; see --help`);
    else setPage(arg);
  }
  if (process.platform !== 'darwin') fail('the native window is macOS only; use the Hub page in a WebGPU browser');
  let app = process.env.FOAFNAUT_APP;
  if (!app && channel === 'latest') app = await installLatest();
  if (!app && channel === 'bleeding-edge') app = bleedingEdgeApp();
  // With no channel named: the newer of the installed release and the bleeding-edge build
  // (owner, 2026-11-09: plain foafnaut started a release of 6 November, older than the
  // local build, with nothing to say so). Each is dated by its files on disk.
  if (!app) {
    const release = currentApp(), local = existsSync(bleedingEdgeApp()) ? bleedingEdgeApp() : undefined;
    const age = (path) => statSync(path).mtimeMs;
    app = release && local ? (age(local) >= age(release) ? local : release) : (release ?? local ?? bleedingEdgeApp());
    if (release && app === release)
      console.error(`foafnaut: the installed release ${basename(realpathSync(join(home(), 'current')))} (newer than the bleeding-edge build)`);
    else if (release) console.error('foafnaut: the bleeding-edge build (newer than the installed release; --latest for the release)');
  }
  if (!existsSync(app)) fail(`no app at ${app}. Run foafnaut --install-latest.`);
  // The bleeding-edge build says what it was built from (BUILD-INFO.json beside the app,
  // written when the build is swapped in); an old build is named, so it is not taken for main.
  if (app === bleedingEdgeApp()) {
    try {
      const info = JSON.parse(readFileSync(join(dirname(app), 'BUILD-INFO.json'), 'utf8'));
      const hours = (Date.now() - Date.parse(info.builtAt)) / 3.6e6;
      console.error(`foafnaut: bleeding edge built from ${info.commit}${info.dirty ? " with uncommitted changes" : ""} at ${info.builtAt} (${hours.toFixed(1)} h ago)` +
        (hours > 6 ? '; it may lack newer work on main' : ''));
    } catch { console.error('foafnaut: bleeding edge has no BUILD-INFO.json; its commit is not known'); }
  }
  if (which) { console.log(app); return; }
  const args = ['-n', ...(detach ? [] : ['-W']), app, '--args', ...pageArgs(page), ...(verbose ? ['--trace-input'] : []), ...app_, ...extra];
  const log = join(homedir(), 'Library', 'Logs', 'foafnaut', 'trace.jsonl');
  if (verbose) console.error(`foafnaut: app ${app}\nfoafnaut: open ${args.join(' ')}\nfoafnaut: trace ${log}`);
  // Follow only what this run appends.
  const follow = verbose ? spawn('tail', ['-n', '0', '-F', log], { stdio: ['ignore', 'inherit', 'ignore'] }) : undefined;
  const run = spawnSync('open', args, { stdio: 'inherit' });
  follow?.kill();
  process.exit(run.status ?? 1);
}

if (import.meta.url === pathToFileURL(realpathSync(process.argv[1])).href) await main(process.argv.slice(2));
