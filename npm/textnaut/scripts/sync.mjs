#!/usr/bin/env node
// Copies the files Textnaut needs into app/, keeping their relative paths (textnaut.ts imports
// ../native_html_engine.ts, and so on). Run by `prepack`. test/package.test.mjs checks the list
// against what Deno says textnaut.ts imports.
import { cpSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { dirname, join, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const source = join(here, '..', '..', '..', 'labs', 'demos', 'foafnaut');
const target = join(here, '..', 'app');

/** Files of labs/demos/foafnaut that the program uses, relative to it. */
export const SHARED = ['finite_floats.ts', 'native_console.ts', 'native_html_document.ts', 'native_html_engine.ts', 'native_html_layout.ts', 'native_net.ts'];
/** Files outside labs/demos/foafnaut that the program imports: [import path relative to it, path in app/].
 * The import lines of the copied files are rewritten to the copy, so the package holds no path above app/. */
export const OUTSIDE = [['../../../docs/web/hub/foafnaut/page-load.mjs', 'hub/page-load.mjs'], ['../../../docs/web/hub/foafnaut/log-gate.mjs', 'hub/log-gate.mjs'],
  ['../../../docs/web/hub/foafnaut/host-trace.mjs', 'hub/host-trace.mjs']];
const TEXTNAUT_EXCLUDE = /(\.test\.ts|\.py|\.md)$|^textnaut$|^__pycache__$/;

export function appFiles() {
  const own = readdirSync(join(source, 'textnaut')).filter((f) => !TEXTNAUT_EXCLUDE.test(f)).map((f) => `textnaut/${f}`);
  return [...SHARED, ...own, ...OUTSIDE.map(([, to]) => to)].sort();
}

/** The app/ path of a file imported by the given path relative to labs/demos/foafnaut. */
export const appPath = (f) => (OUTSIDE.find(([from]) => from === f) ?? [f, f])[1];

export function sync() {
  rmSync(target, { recursive: true, force: true });
  for (const f of appFiles()) {
    const from = (OUTSIDE.find(([, to]) => to === f) ?? [f])[0];
    mkdirSync(dirname(join(target, f)), { recursive: true });
    cpSync(join(source, from), join(target, f));
    if (!/\.(ts|mjs)$/.test(f)) continue;
    let text = readFileSync(join(target, f), 'utf8');
    for (const [imp, to] of OUTSIDE) {
      const now = relative(dirname(join(source, f)), join(source, imp));
      const rel = relative(dirname(join(target, f)), join(target, to));
      text = text.split(`"${now}"`).join(`"${rel.startsWith('.') ? rel : './' + rel}"`).split(`'${now}'`).join(`'${rel.startsWith('.') ? rel : './' + rel}'`);
    }
    writeFileSync(join(target, f), text);
  }
  return appFiles();
}

if (process.argv[1] === fileURLToPath(import.meta.url)) console.error(`copied ${sync().length} files into app/`);
