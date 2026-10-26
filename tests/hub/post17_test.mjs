// Pins the live cells in docs/web/historical-fstar-notebooks/17-mutating-and-serving-data.md.
//
// node:test, requiring the committed npm/factoidal bundles (no F*
// toolchain needed). Both live cells go through the typed `fn` adapter
// now (`fn.parse`/`fn.update`/`fn.query`) -- `fn` here is the real
// npm/factoidal typed API, which already has `update()`; the adapter
// gap this post used to document (`docs/_includes/hub.njk`'s `fn` had
// no `update` method) is closed.

import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, pretty, resolvePreSplitCommit } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);
const POST_FILE = '17-mutating-and-serving-data.md';
const REPO_ROOT = path.join(__dirname, '..', '..');

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;

const cells = extractObservableCells(POST_FILE);

test('post17: post has at least 2 live cells', () => {
  assert.ok(cells.length >= 2, `expected >= 2 live cells, found ${cells.length}`);
});

test('post17 cell 1 (INSERT DATA): Bob appears alongside Alice after the update', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.deepEqual(result.namesBeforeInsertData, ['Alice']);
  assert.deepEqual(result.namesAfterInsertData, ['Alice', 'Bob']);
});

test('post17 cell 1 degrades gracefully when the npm-entry bundle is unavailable', async () => {
  const brokenFn = {
    parse: factoidal.parse,
    async update() {
      throw new Error('update needs the factoidal-npm-entry bundle, which is not present');
    },
    query: factoidal.query,
  };
  const result = await runObservableCell(cells[0], { fn: brokenFn, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /npm-entry bundle/);
});

test('post17 cell 2 (DELETE/INSERT WHERE): Bob becomes Bobby, Alice untouched', async () => {
  const result = await runObservableCell(cells[1], { fn: factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.deepEqual(result.namesAfterDeleteInsertWhere, ['Alice', 'Bobby']);
});

test('post17 cell 2 degrades gracefully when the npm-entry bundle is unavailable', async () => {
  const brokenFn = {
    parse: factoidal.parse,
    async update() {
      throw new Error('update needs the factoidal-npm-entry bundle, which is not present');
    },
    query: factoidal.query,
  };
  const result = await runObservableCell(cells[1], { fn: brokenFn, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /npm-entry bundle/);
});

// ---------------------------------------------------------------------
// Direct checks on the prose claims: scores, commits, and the "not
// wired" honesty claims are read from the real tree, not typed from
// memory.
// ---------------------------------------------------------------------

test('post17: the page\'s fn carries update() (grounds this post\'s fn.update cells)', async () => {
  // hub.njk builds fn from the package's browser entry
  // (Object.assign({}, Factoidal.default, hubHelpers)), so update is the
  // package's own function.
  const hubNjk = fs.readFileSync(path.join(REPO_ROOT, 'docs', '_includes', 'hub.njk'), 'utf8');
  assert.match(hubNjk, /const fn = Object\.assign\(\{\}, Factoidal\.default, hubHelpers\);/);
  const browser = await import(path.join(REPO_ROOT, 'npm', 'factoidal', 'browser.js'));
  assert.equal(typeof browser.default.update, 'function');
  assert.equal(typeof browser.update, 'function');
});

// The hub runs the Lean engine (issue 726). The checkout's record of its
// SPARQL 1.1 score is the committed Lean conformance baseline; the F*
// dashboard file docs/test-results/latest.json is a build artifact of
// danbri/factoidal-builds and is not in a checkout.
test('post17: the committed Lean conformance baseline has SPARQL 1.1 manifest-all, which includes the 13 Update manifests, at 0 fail', () => {
  const baseline = fs.readFileSync(path.join(REPO_ROOT, 'docs', 'designissues',
    '2026-10-09-lean-conformance-baseline.md'), 'utf8');
  const row = baseline.split('\n').find((l) => l.startsWith('SPARQL 1.1 (query+update+protocol, manifest-all)'));
  assert.ok(row, 'expected the SPARQL 1.1 manifest-all row in the Lean conformance baseline');
  const cols = row.split('|').map((c) => c.trim());
  assert.equal(cols[1], 'l4w3c');
  assert.deepEqual(cols.slice(2, 6).map(Number), [631, 0, 0, 631],
    'expected 631 pass, 0 fail, 0 other (out of 631)');
  const manifestAll = fs.readFileSync(path.join(REPO_ROOT, 'third_party', 'testing', 'w3c',
    'sparql', 'sparql11', 'manifest-all.ttl'), 'utf8');
  for (const name of [
    'add', 'basic-update', 'clear', 'copy', 'delete', 'delete-data',
    'delete-insert', 'delete-where', 'drop', 'move', 'syntax-update-1',
    'syntax-update-2', 'update-silent',
  ]) {
    assert.ok(manifestAll.includes(`<${name}/manifest.ttl>`), `manifest-all includes ${name}`);
  }
});

test('post17: the three durable-UPDATE commits cited exist (danbri/factoidal ids, mapped into factoidal-core)', () => {
  const { execFileSync } = require('node:child_process');
  for (const sha of ['868a20b', '1f27320', '5e8399a']) {
    const m = resolvePreSplitCommit(REPO_ROOT, sha);
    assert.ok(m, `expected ${sha} in tools/repo-split/commit-map.tsv`);
    assert.equal(m.kind, 'rewritten', `expected ${sha} to have a rewritten core commit`);
    const out = execFileSync('git', ['cat-file', '-t', m.core], { cwd: REPO_ROOT }).toString().trim();
    assert.equal(out, 'commit', `expected core commit ${m.core} (from ${sha}) to be reachable in this repo`);
  }
});

test('post17: the delta-log F* modules this post cites exist and verify without assume vals (DeltaLog/DeltaMerge)', () => {
  for (const mod of ['RDF.Store.Columnar.DeltaLog.fst', 'RDF.Store.Columnar.DeltaMerge.fst']) {
    const p = path.join(REPO_ROOT, 'formal', 'fstar', mod);
    assert.ok(fs.existsSync(p), `expected ${mod} to exist`);
  }
  const deltaMerge = fs.readFileSync(
    path.join(REPO_ROOT, 'formal', 'fstar', 'RDF.Store.Columnar.DeltaMerge.fst'), 'utf8');
  assert.match(deltaMerge, /lemma_merge_on_read_matches_apply_entries/,
    'expected the proved merge-on-read correspondence lemma to be present');
});

test('post17: the CLI --delta-log flag this post cites is real', () => {
  const cli = fs.readFileSync(
    path.join(REPO_ROOT, 'bin', 'factoidal-cli', 'factoidal_cli.ml'), 'utf8');
  assert.match(cli, /"--delta-log"/);
});

test('post17: SPARQL.GraphStore.fst is verified F* with no assume vals (grounds "specified and proven")', () => {
  const gsp = fs.readFileSync(
    path.join(REPO_ROOT, 'formal', 'fstar', 'SPARQL.GraphStore.fst'), 'utf8');
  assert.doesNotMatch(gsp, /^assume val/m, 'SPARQL.GraphStore.fst should have zero assume vals');
  for (const fn of ['gsp_get', 'gsp_head', 'gsp_put', 'gsp_post', 'gsp_delete']) {
    assert.match(gsp, new RegExp(`let ${fn}\\b`), `expected ${fn} to be defined`);
  }
});

test('post17: factoidal-http now routes the Graph Store Protocol (grounds the "landed, routed" update)', () => {
  const http = fs.readFileSync(
    path.join(REPO_ROOT, 'bin', 'factoidal-http', 'factoidal_http.ml'), 'utf8');
  assert.match(http, /GraphStore/, 'factoidal_http.ml should reference the GraphStore module now that stage 8 has landed');
  assert.match(http, /POST \/update/, 'expected the whole-dataset /update route to still be documented');
});

test('post17: the stage-8 HTTP-wiring commit cited exists on this branch', () => {
  const { execFileSync } = require('node:child_process');
  const m = resolvePreSplitCommit(REPO_ROOT, 'e8085da');
  assert.ok(m && m.kind === 'rewritten', 'expected e8085da to have a rewritten core commit');
  const out = execFileSync('git', ['cat-file', '-t', m.core], { cwd: REPO_ROOT }).toString().trim();
  assert.equal(out, 'commit', `expected core commit ${m.core} (from e8085da) to be reachable in this repo`);
});
