#!/usr/bin/env node
// npm release check for @factoidal/core (danbri/factoidal issue 1038, P5).
//
// The version is a manual edit in four places, and nothing checked them or
// the changelog cut: 0.11.0 shipped with package-lock.json at 0.10.0, 0.10.0
// shipped with "## 0.10.0 (unreleased)", and 0.13.0 to 0.15.0 have no date.
// This tool checks, for the package directory (default npm/factoidal):
//
//   1. package.json "version" is a semver version;
//   2. package-lock.json "version" and packages[""].version equal it;
//   3. lib/version.mjs exports `version = '<it>'`;
//   4. CHANGELOG.md has exactly one heading "## <version> (YYYY-MM-DD)"
//      with a real calendar date.
//
// Usage:
//   node tools/npm-release-check.mjs [--dir npm/factoidal] [--expect VERSION]
//   --expect: also require the version to be VERSION (the publish
//             workflow passes its `confirm` input).
// Exit 0: all checks pass. Exit 1: a check failed (each failure is printed).
// Exit 2: bad arguments.
//
// The danbri/factoidal-builds publish workflow runs it before the pack
// step; npm/factoidal/test/release-check.test.mjs runs it in `npm test`.

import { readFileSync } from 'node:fs';
import { join, resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const SEMVER = /^\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?$/;

function escapeRe(s) {
  return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function readText(dir, name, errors) {
  try {
    return readFileSync(join(dir, name), 'utf8');
  } catch (e) {
    errors.push(`${name}: cannot read (${e.code || e.message})`);
    return null;
  }
}

function readJson(dir, name, errors) {
  const t = readText(dir, name, errors);
  if (t === null) return null;
  try {
    return JSON.parse(t);
  } catch (e) {
    errors.push(`${name}: not JSON (${e.message})`);
    return null;
  }
}

function validDate(s) {
  const m = /^(\d{4})-(\d{2})-(\d{2})$/.exec(s);
  if (!m) return false;
  const d = new Date(Date.UTC(+m[1], +m[2] - 1, +m[3]));
  return d.getUTCFullYear() === +m[1] && d.getUTCMonth() === +m[2] - 1 && d.getUTCDate() === +m[3];
}

/**
 * Check the package directory. Returns { version, errors }; errors is empty
 * when every check passes.
 */
export function checkRelease(dir, { expect } = {}) {
  const errors = [];
  const pkg = readJson(dir, 'package.json', errors);
  const version = pkg && pkg.version;
  if (pkg && (typeof version !== 'string' || !SEMVER.test(version))) {
    errors.push(`package.json: version ${JSON.stringify(version)} is not a semver version`);
  }
  if (expect !== undefined && version !== expect) {
    errors.push(`package.json: version is ${version}; expected ${expect}`);
  }

  const lock = readJson(dir, 'package-lock.json', errors);
  if (lock) {
    if (lock.version !== version) {
      errors.push(`package-lock.json: "version" is ${lock.version}; package.json has ${version}`);
    }
    const root = lock.packages && lock.packages[''];
    if (!root || root.version !== version) {
      errors.push(`package-lock.json: packages[""].version is ${root && root.version}; package.json has ${version}`);
    }
  }

  const lib = readText(dir, 'lib/version.mjs', errors);
  if (lib !== null) {
    const m = /export\s+const\s+version\s*=\s*['"]([^'"]*)['"]/.exec(lib);
    if (!m) errors.push('lib/version.mjs: no `export const version = \'...\'`');
    else if (m[1] !== version) errors.push(`lib/version.mjs: version is ${m[1]}; package.json has ${version}`);
  }

  const log = readText(dir, 'CHANGELOG.md', errors);
  if (log !== null && typeof version === 'string') {
    const v = escapeRe(version);
    const any = log.split('\n').filter((l) => new RegExp(`^##\\s+${v}(?![0-9A-Za-z.-])`).test(l));
    const good = any.filter((l) => /^## \S+ \((\d{4}-\d{2}-\d{2})\)\s*$/.test(l));
    if (any.length === 0) {
      errors.push(`CHANGELOG.md: no heading "## ${version} (YYYY-MM-DD)"`);
    } else if (any.length > 1) {
      errors.push(`CHANGELOG.md: ${any.length} headings for ${version}: ${any.map((l) => JSON.stringify(l)).join(', ')}`);
    } else if (good.length !== 1) {
      errors.push(`CHANGELOG.md: heading ${JSON.stringify(any[0])} is not "## ${version} (YYYY-MM-DD)"`);
    } else {
      const date = /\((\d{4}-\d{2}-\d{2})\)/.exec(good[0])[1];
      if (!validDate(date)) errors.push(`CHANGELOG.md: heading ${JSON.stringify(good[0])}: ${date} is not a calendar date`);
    }
  }
  return { version, errors };
}

function main(argv) {
  const here = dirname(fileURLToPath(import.meta.url));
  let dir = resolve(here, '..', 'npm', 'factoidal');
  let expect;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--dir' && i + 1 < argv.length) dir = resolve(argv[++i]);
    else if (a === '--expect' && i + 1 < argv.length) expect = argv[++i];
    else if (a === '-h' || a === '--help') {
      console.log('usage: node tools/npm-release-check.mjs [--dir DIR] [--expect VERSION]');
      return 0;
    } else {
      console.error(`npm-release-check: unknown argument ${a}`);
      return 2;
    }
  }
  const { version, errors } = checkRelease(dir, { expect });
  if (errors.length) {
    console.error(`npm-release-check: FAIL for ${dir} (version ${version}):`);
    for (const e of errors) console.error(`  - ${e}`);
    console.error('Bump the version in package.json, package-lock.json (two places) and lib/version.mjs, and give CHANGELOG.md the heading "## <version> (YYYY-MM-DD)".');
    return 1;
  }
  console.log(`npm-release-check: OK, ${version} in package.json, package-lock.json (2), lib/version.mjs and a dated CHANGELOG.md heading`);
  return 0;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  process.exitCode = main(process.argv.slice(2));
}
