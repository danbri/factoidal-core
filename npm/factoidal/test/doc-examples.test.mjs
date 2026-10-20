// Every ```js example in README.md and API.md is executed here, as an ES
// module that imports the package by its published name. A fence written
// ```js browser needs a page (fetch of a page-relative URL, IndexedDB); it
// is compiled with `node --check` only. Real-browser runs of those
// examples are https://github.com/danbri/factoidal/issues/882 item 7.

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, mkdtempSync, mkdirSync, symlinkSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const pkg = dirname(dirname(fileURLToPath(import.meta.url)));
const work = mkdtempSync(join(tmpdir(), 'factoidal-doc-examples-'));
mkdirSync(join(work, 'node_modules', '@factoidal'), { recursive: true });
symlinkSync(pkg, join(work, 'node_modules', '@factoidal', 'core'), 'dir');
test.after(() => rmSync(work, { recursive: true, force: true }));

function blocks(file) {
  const text = readFileSync(join(pkg, file), 'utf8');
  const out = [];
  const re = /^```js( browser)?\n([\s\S]*?)^```$/gm;
  let m;
  while ((m = re.exec(text)) !== null) {
    const line = text.slice(0, m.index).split('\n').length;
    out.push({ file, line, browser: !!m[1], code: m[2] });
  }
  return out;
}

const all = [...blocks('README.md'), ...blocks('API.md')];

test('the documents have examples', () => {
  assert.ok(all.length >= 15, `found ${all.length}`);
});

for (const b of all) {
  test(`${b.file}:${b.line}${b.browser ? ' (browser: syntax only)' : ''}`, () => {
    const path = join(work, `${b.file.replace('.', '_')}_${b.line}.mjs`);
    writeFileSync(path, b.code);
    const args = b.browser ? ['--check', path] : ['--stack-size=4000', path];
    const r = spawnSync(process.execPath, args, { cwd: work, encoding: 'utf8', timeout: 120000 });
    assert.equal(r.status, 0, `${b.file}:${b.line} exited ${r.status}\n${r.stderr}`);
  });
}
