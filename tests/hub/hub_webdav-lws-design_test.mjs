// docs/web/hub/webdav-lws-design.md is a design note with no live cells.
// This file keeps its claims checkable: every theorem it names in its table is
// declared in the Lean sources, in the file the table gives, and the CLI help
// shows the 0.21.0 WebDAV options the page describes.

import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const PAGE = fs.readFileSync(path.join(ROOT, 'docs', 'web', 'hub', 'webdav-lws-design.md'), 'utf8');
const LEAN = path.join(ROOT, 'formal', 'lean4');

/** Rows of the theorem table: [names, file]. */
function theoremRows() {
  const table = PAGE.split('## The theorems')[1].split('\n## ')[0];
  const rows = [];
  for (const line of table.split('\n')) {
    const cells = line.split('|').map((c) => c.trim());
    if (cells.length < 4 || !cells[2].startsWith('`')) continue;
    const names = [...cells[1].matchAll(/`([A-Za-z_][A-Za-z0-9_]*)`/g)].map((m) => m[1]);
    const file = cells[2].replace(/`/g, '');
    if (names.length) rows.push([names, file]);
  }
  return rows;
}

test('the page names at least the two release theorems', () => {
  const names = theoremRows().flatMap(([n]) => n);
  assert.ok(names.includes('webdav_within_lws'));
  assert.ok(names.includes('lws_data_only_through_authorized_step'));
  assert.ok(names.length >= 10, `${names.length} theorems in the table`);
});

test('every theorem in the table is declared in the file the table gives', () => {
  for (const [names, file] of theoremRows()) {
    const src = fs.readFileSync(path.join(LEAN, file), 'utf8');
    for (const n of names) {
      assert.match(src, new RegExp(`\\btheorem ${n}\\b`), `${n} in ${file}`);
    }
  }
});

test('no file named by the table uses sorry', () => {
  for (const file of new Set(theoremRows().map(([, f]) => f))) {
    const src = fs.readFileSync(path.join(LEAN, file), 'utf8').replace(/--.*$/gm, '').replace(/\/-[\s\S]*?-\//g, '');
    assert.doesNotMatch(src, /\bsorry\b/, file);
  }
});

test('the CLI help shows the 0.21.0 WebDAV options the page describes', () => {
  const r = spawnSync(process.execPath, [path.join(ROOT, 'npm', 'factoidal', 'bin', 'factoidal.mjs'), 'webdav-serve', '--help'],
    { encoding: 'utf8', timeout: 60000 });
  const help = r.stdout + r.stderr;
  assert.match(help, /--guest/);
  assert.match(help, /users:/);
});
