#!/usr/bin/env node
// Copies the files Textnaut needs into app/, keeping their relative paths (textnaut.ts imports
// ../native_html_engine.ts, and so on). Run by `prepack`. test/package.test.mjs checks the list
// against what Deno says textnaut.ts imports.
import { cpSync, mkdirSync, readdirSync, rmSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const source = join(here, '..', '..', '..', 'labs', 'demos', 'foafnaut');
const target = join(here, '..', 'app');

/** Files of labs/demos/foafnaut that the program uses, relative to it. */
export const SHARED = ['native_console.ts', 'native_html_document.ts', 'native_html_engine.ts'];
const TEXTNAUT_EXCLUDE = /(\.test\.ts|\.py|\.md)$|^textnaut$/;

export function appFiles() {
  const own = readdirSync(join(source, 'textnaut')).filter((f) => !TEXTNAUT_EXCLUDE.test(f)).map((f) => `textnaut/${f}`);
  return [...SHARED, ...own].sort();
}

export function sync() {
  rmSync(target, { recursive: true, force: true });
  for (const f of appFiles()) {
    mkdirSync(dirname(join(target, f)), { recursive: true });
    cpSync(join(source, f), join(target, f));
  }
  return appFiles();
}

if (process.argv[1] === fileURLToPath(import.meta.url)) console.error(`copied ${sync().length} files into app/`);
