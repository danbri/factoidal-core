// tools/npm-release-check.mjs (danbri/factoidal issue 1038, P5): the version
// agrees in package.json, package-lock.json (two places) and lib/version.mjs,
// and CHANGELOG.md has a dated heading for it. The first test checks this
// package as it is; the others check that each defect is found.

import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { checkRelease } from '../../../tools/npm-release-check.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const pkgDir = resolve(here, '..');
const tool = resolve(here, '../../../tools/npm-release-check.mjs');

function fixture({ pkg = '1.2.3', lock = '1.2.3', lockRoot = '1.2.3', lib = '1.2.3',
  changelog = '# Changelog\n\n## Unreleased\n\n## 1.2.3 (2026-10-26)\n\n- x\n\n## 1.2.2 (2026-10-01)\n' } = {}) {
  const d = mkdtempSync(join(tmpdir(), 'release-check-'));
  mkdirSync(join(d, 'lib'));
  writeFileSync(join(d, 'package.json'), JSON.stringify({ name: '@factoidal/core', version: pkg }));
  writeFileSync(join(d, 'package-lock.json'), JSON.stringify({ name: '@factoidal/core', version: lock,
    lockfileVersion: 3, packages: { '': { name: '@factoidal/core', version: lockRoot } } }));
  writeFileSync(join(d, 'lib/version.mjs'), `export const version = '${lib}';\n`);
  writeFileSync(join(d, 'CHANGELOG.md'), changelog);
  return d;
}

function errorsOf(opts, check = {}) {
  const d = fixture(opts);
  try {
    return checkRelease(d, check).errors;
  } finally {
    rmSync(d, { recursive: true, force: true });
  }
}

test('release check: this package passes', () => {
  const { version, errors } = checkRelease(pkgDir);
  assert.deepEqual(errors, [], errors.join('\n'));
  assert.match(version, /^\d+\.\d+\.\d+/);
});

test('release check: a consistent fixture passes', () => {
  assert.deepEqual(errorsOf({}), []);
  assert.deepEqual(errorsOf({}, { expect: '1.2.3' }), []);
});

test('release check: --expect names a different version', () => {
  const e = errorsOf({}, { expect: '1.2.4' });
  assert.equal(e.length, 1);
  assert.match(e[0], /expected 1\.2\.4/);
});

test('release check: package-lock.json version, both places', () => {
  assert.match(errorsOf({ lock: '1.2.2' }).join('\n'), /package-lock\.json: "version" is 1\.2\.2/);
  assert.match(errorsOf({ lockRoot: '1.2.2' }).join('\n'), /packages\[""\]\.version is 1\.2\.2/);
});

test('release check: lib/version.mjs', () => {
  assert.match(errorsOf({ lib: '1.2.2' }).join('\n'), /lib\/version\.mjs: version is 1\.2\.2/);
});

test('release check: CHANGELOG.md heading', () => {
  const head = (h) => errorsOf({ changelog: `# Changelog\n\n${h}\n\n- x\n` }).join('\n');
  assert.match(head('## 1.2.2 (2026-10-01)'), /no heading "## 1\.2\.3 \(YYYY-MM-DD\)"/);
  assert.match(head('## 1.2.3 (unreleased)'), /is not "## 1\.2\.3 \(YYYY-MM-DD\)"/);
  assert.match(head('## 1.2.3'), /is not "## 1\.2\.3 \(YYYY-MM-DD\)"/);
  assert.match(head('## 1.2.3 — 2026-10-22'), /is not "## 1\.2\.3 \(YYYY-MM-DD\)"/);
  assert.match(head('## 1.2.3 (2026-02-30)'), /not a calendar date/);
  assert.match(head('## 1.2.3 (2026-10-01)\n\n## 1.2.3 (2026-10-02)'), /2 headings for 1\.2\.3/);
  // A longer version that starts with the same digits is not this version.
  assert.match(head('## 1.2.30 (2026-10-01)'), /no heading/);
  assert.equal(head('## 1.2.3 (2026-10-01)'), '');
});

test('release check: the command exits 1 with a message, 0 when consistent', () => {
  const bad = fixture({ lib: '1.2.2' });
  const good = fixture({});
  try {
    const r1 = spawnSync(process.execPath, [tool, '--dir', bad], { encoding: 'utf8' });
    assert.equal(r1.status, 1);
    assert.match(r1.stderr, /FAIL/);
    assert.match(r1.stderr, /lib\/version\.mjs: version is 1\.2\.2; package\.json has 1\.2\.3/);
    const r0 = spawnSync(process.execPath, [tool, '--dir', good, '--expect', '1.2.3'], { encoding: 'utf8' });
    assert.equal(r0.status, 0, r0.stderr);
    assert.match(r0.stdout, /OK, 1\.2\.3/);
    const r2 = spawnSync(process.execPath, [tool, '--bogus'], { encoding: 'utf8' });
    assert.equal(r2.status, 2);
  } finally {
    rmSync(bad, { recursive: true, force: true });
    rmSync(good, { recursive: true, force: true });
  }
});
