#!/usr/bin/env node
// Fetch VerifiedJS at one pinned commit into the ignored .build/ directory.
// LICENCE: the upstream repository has no licence file. Nothing it contains,
// and nothing built from it, may be committed here. See
// docs/designissues/2026-11-07-verifiedjs-page-scripts.md.
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readdirSync, readFileSync, statSync } from 'node:fs';
import { join, relative } from 'node:path';
import { fileURLToPath } from 'node:url';

import { VERIFIEDJS_REPOSITORY, VERIFIEDJS_COMMIT, VERIFIEDJS_SHA256 } from './pin.mjs';
export { VERIFIEDJS_REPOSITORY, VERIFIEDJS_COMMIT, VERIFIEDJS_SHA256 };
const CHECKED_PATHS = ['VerifiedJS', 'VerifiedJS.lean', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'scripts', 'tests/e2e', 'tests/unit', 'tools'];

const walk = path => statSync(path).isDirectory()
  ? readdirSync(path).flatMap(name => walk(join(path, name)))
  : [path];

export function treeDigest(root) {
  const lines = CHECKED_PATHS.flatMap(path => walk(join(root, path)))
    .map(path => relative(root, path)).sort()
    .map(path => `${createHash('sha256').update(readFileSync(join(root, path))).digest('hex')}  ${path}`);
  return createHash('sha256').update(lines.join('\n')).digest('hex');
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const target = fileURLToPath(new URL('../../../.build/verifiedjs/', import.meta.url));
  const git = (...args) => execFileSync('git', ['-C', target, ...args], { stdio: ['ignore', 'pipe', 'inherit'] }).toString().trim();
  mkdirSync(target, { recursive: true });
  if (!existsSync(join(target, '.git'))) {
    git('init', '-q');
    git('remote', 'add', 'origin', VERIFIEDJS_REPOSITORY);
  }
  // The upstream tree holds 2 GB of agent logs. No build or test reads them.
  git('sparse-checkout', 'set', '--no-cone', '/*', '!/logs/', '!/agent_logs/');
  git('fetch', '-q', '--depth', '1', 'origin', VERIFIEDJS_COMMIT);
  git('-c', 'advice.detachedHead=false', 'checkout', '-q', VERIFIEDJS_COMMIT);
  if (git('rev-parse', 'HEAD') !== VERIFIEDJS_COMMIT) throw Error('VerifiedJS commit mismatch');
  const digest = treeDigest(target);
  if (digest !== VERIFIEDJS_SHA256) throw Error(`VerifiedJS tree checksum mismatch: ${digest}`);
  console.log(`VerifiedJS ${VERIFIEDJS_COMMIT}; tree sha256 ${digest}; ${target}`);
}
