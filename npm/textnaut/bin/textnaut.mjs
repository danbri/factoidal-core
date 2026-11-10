#!/usr/bin/env node
// textnaut: a text-mode web browser on the Foafnaut engine (experimental). This launcher checks for
// Deno, chooses an engine, and runs app/textnaut/textnaut.ts with the permissions it needs.
import { spawn, spawnSync } from 'node:child_process';
import { createRequire } from 'node:module';
import { existsSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { chooseEngine, denoDir, ensureEngine } from '../lib/engine.mjs';

const DENO_VERSION = '2.9.6';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const MIN_DENO = [2, 0, 0];
const args = process.argv.slice(2);

const HELP = `textnaut [OPTIONS] URL_OR_FILE      a text-mode web browser (experimental)
textnaut --screensaver [NAME]      screensavers; no page and no engine

Keys: arrows, j, k, Page Up/Down, Space scroll; [n] Enter follows link n; Tab next link; b back;
? or h help; q quit.

Options: --width COLS (with --dump), --dump, --colour none|16|256|24bit, --big-headings=auto|on|off,
--strict, --no-scripts, --timing, --verbose, --wasm, --engine FILE, --font FILE, --version.

Engine, in order: --engine FILE or TEXTNAUT_NATIVE; TEXTNAUT_WASM_DIR; the library of an installed
foafnaut (FOAFNAUT_HOME or ~/.foafnaut); else the pinned Wasm engine, downloaded once on first use
into $TEXTNAUT_CACHE, $XDG_CACHE_HOME/textnaut or ~/.cache/textnaut.
Uses your Deno if it is ${MIN_DENO.join('.')} or later; otherwise fetches Deno once.`;

if (args.includes('--help') || args.includes('-h')) { console.log(HELP); process.exit(0); }
if (args.includes('--version')) { console.log(JSON.parse((await import('node:fs')).readFileSync(join(root, 'package.json'), 'utf8')).version); process.exit(0); }

function denoVersion(command) {
  const run = spawnSync(command, ["--version"], { encoding: "utf8" });
  if (run.error || run.status !== 0) return null;
  const m = /deno (\d+)\.(\d+)\.(\d+)/.exec(run.stdout);
  return m ? [Number(m[1]), Number(m[2]), Number(m[3])] : null;
}
/** A Deno fetched once from npm into the cache. Only used when there is no usable Deno. */
function fetchedDeno() {
  const dir = denoDir(DENO_VERSION), exe = join(dir, "node_modules", "deno", process.platform === "win32" ? "deno.exe" : "deno");
  if (!existsSync(exe)) {
    console.error(`textnaut: no Deno found; fetching Deno ${DENO_VERSION} from npm, once (about 96 MB, kept in ${dir}).`);
    const run = spawnSync("npm", ["install", "--prefix", dir, "--no-audit", "--no-fund", "--loglevel=error", `deno@${DENO_VERSION}`],
      { stdio: ["ignore", "ignore", "inherit"], shell: process.platform === "win32" });
    if (run.status !== 0 || !existsSync(exe)) return undefined;
  }
  return exe;
}
const isNew = (v) => v && v[0] >= MIN_DENO[0];
// $DENO if set; else a Deno on the PATH that is new enough; else one fetched once.
let deno = process.env.DENO || "deno", version = denoVersion(deno);
if (!process.env.DENO && !isNew(version)) {
  const fetched = fetchedDeno();
  if (fetched) { deno = fetched; version = denoVersion(deno); }
}
const need = `Deno ${MIN_DENO.join(".")} or later`;
if (!version) {
  console.error(`textnaut: Deno was not found, and it could not be fetched. Textnaut runs on Deno (${need}).\n` +
    `  Install it: curl -fsSL https://deno.land/install.sh | sh   (or: brew install deno)\n` +
    `  then run textnaut again. See https://docs.deno.com/runtime/getting_started/installation/`);
  process.exit(127);
}
if (version[0] < MIN_DENO[0]) {
  console.error(`textnaut: this Deno is ${version.join('.')}; ${need} is needed. Upgrade: deno upgrade`);
  process.exit(127);
}
if (!existsSync(join(root, 'app', 'textnaut', 'textnaut.ts'))) {
  console.error('textnaut: the package is incomplete (app/ is missing). Reinstall it, or run `node scripts/sync.mjs` in a checkout.');
  process.exit(1);
}

const needsEngine = !args.includes('--screensaver');
const env = { ...process.env };
if (needsEngine) {
  const choice = chooseEngine(args, process.env);
  Object.assign(env, choice.env);
  if (choice.fetch) {
    try { env.TEXTNAUT_WASM_DIR = await ensureEngine(); } catch (error) { console.error(`textnaut: ${error.message}`); process.exit(1); }
  }
}

const child = spawn(deno, [
  'run', '--no-check', '--no-config', '--no-prompt',
  `--import-map=${join(root, 'app', 'textnaut', 'import_map.json')}`,
  '--allow-read', '--allow-ffi', '--allow-net', '--allow-env',
  join(root, 'app', 'textnaut', 'textnaut.ts'), ...args,
], { stdio: 'inherit', env });
for (const signal of ['SIGTERM', 'SIGHUP']) process.on(signal, () => child.kill(signal));
child.on('exit', (code, signal) => process.exit(code ?? (signal ? 130 : 1)));
