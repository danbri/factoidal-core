// Pins the live cells in docs/web/historical-fstar-notebooks/18-the-durable-log-live.md.
//
// The hub runs the Lean engine of @factoidal/core (issue 726); `fn` and
// `Factoidal` here are npm/factoidal, the same typed API the page binds.
// Cell 1 (parse + in-memory UPDATE) and cells 2-4 (the durable update log:
// deltaLogOpen, deltaLogAppend, deltaLogReadAllHex, deltaLogMerge,
// deltaLogDestroy, _deltaLogCorruptLastForTest) run on it. The log's bytes,
// checksums and merge are Lean (formal/lean4/L4Factoidal/Storage/
// BrowserLog.lean, ops deltaLogEncode/deltaLogMerge); under Node the host
// store keeps the records in memory, in the browser in IndexedDB
// (https://github.com/danbri/factoidal/issues/728). The real-IndexedDB
// check is tests/web-demos/hub_browser_all.sh.

import fs from 'node:fs';
import { createRequire } from 'node:module';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { NPM_FACTOIDAL_INDEX, extractObservableCells, runObservableCell, pretty, resolvePreSplitCommit } from './_helpers.mjs';

import test from 'node:test';
import assert from 'node:assert/strict';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);
const POST_FILE = '18-the-durable-log-live.md';
const REPO_ROOT = path.join(__dirname, '..', '..');

const factoidal = (await import(NPM_FACTOIDAL_INDEX)).default;

const Factoidal = factoidal;

const cells = extractObservableCells(POST_FILE);

test('post18: post has at least 5 live cells (4 lifecycle steps + the runtimes table)', () => {
  assert.ok(cells.length >= 5, `expected >= 5 live cells, found ${cells.length}`);
});

test('post18 cell 1 (parse + in-memory UPDATE): Carol appears alongside Alice/Bob', async () => {
  const result = await runObservableCell(cells[0], { fn: factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.deepEqual(result.namesAfterInsert, ['Alice', 'Bob', 'Carol']);
});

test('post18 cell 1 degrades gracefully when the npm-entry bundle is unavailable', async () => {
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

test('post18 cell 2 degrades gracefully when loadNpmEntry throws', async () => {
  const brokenFactoidal = {
    async loadNpmEntry() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
    async deltaLogOpen(dbName) {
      return { dbName };
    },
    async deltaLogAppend() {
      // deltaLogAppend calls loadNpmEntry() itself in the real
      // implementation; the stub used elsewhere in this file does
      // too (via `abi`), so a broken loadNpmEntry should surface here.
      const e = new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
      throw e;
    },
  };
  const result = await runObservableCell(cells[1], { Factoidal: brokenFactoidal, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /fetch failed/);
});

test('post18 cell 3 degrades gracefully when loadNpmEntry throws', async () => {
  const brokenFactoidal = {
    async deltaLogOpen(dbName) {
      return { dbName };
    },
    async deltaLogReadAllHex() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
    async deltaLogMerge() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
  };
  const result = await runObservableCell(cells[2], { Factoidal: brokenFactoidal, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /fetch failed/);
});

test('post18 cell 4 degrades gracefully when loadNpmEntry throws', async () => {
  const brokenFactoidal = {
    async deltaLogDestroy() {},
    async deltaLogOpen(dbName) {
      return { dbName };
    },
    async deltaLogAppend() {
      throw new Error('factoidal-npm-entry.js fetch failed: 404 Not Found');
    },
  };
  const result = await runObservableCell(cells[3], { Factoidal: brokenFactoidal, pretty });
  assert.equal(result.available, false);
  assert.match(result.note, /fetch failed/);
});

test('post18 cell 5 (the runtimes pretty() table): four rows, native/js/C/wasm in that order, wasm now proven too', async () => {
  const result = await runObservableCell(cells[4], { Factoidal, pretty });
  assert.equal(result.kind, 'table');
  assert.deepEqual(result.columns, ['runtime', 'proves', 'evidence', 'landed']);
  assert.equal(result.rows.length, 4);
  const runtimes = result.rows.map((r) => r[0]);
  assert.deepEqual(runtimes, [
    'Native (OCaml)', 'JavaScript (js_of_ocaml)', 'C (KaRaMeL)', 'WebAssembly (wasm_of_ocaml)',
  ]);
  const wasmRow = result.rows[3];
  assert.doesNotMatch(wasmRow[1], /nothing yet/i,
    'the wasm row was rebuilt to include DeltaLog/DeltaMerge -- update this assertion, not revert the rebuild, if it fails');
});

// ---------------------------------------------------------------------
// Direct checks on the prose claims: the five assume vals, the four
// realisations, the C demo transcript's provenance, the BaseWriter
// honesty section, and the cited commits/files all read from the real
// tree rather than typed from memory.
// ---------------------------------------------------------------------

test('post18: RDF.Store.Columnar.DeltaLog.fst declares exactly five ML-effect I/O assume vals', () => {
  const src = fs.readFileSync(
    path.join(REPO_ROOT, 'formal', 'fstar', 'RDF.Store.Columnar.DeltaLog.fst'), 'utf8');
  const assumeVals = [...src.matchAll(/^assume val (\w+)/gm)].map((m) => m[1]);
  assert.deepEqual(
    assumeVals.sort(),
    ['atomic_rename', 'delta_log_append', 'delta_log_fsync', 'delta_log_read_all', 'fsync_dir'].sort(),
  );
});

test('post18: the native realisation of the five delta-log I/O assume vals exists (issue #282 patch)', () => {
  const p = path.join(
    REPO_ROOT, 'formal', 'fstar', 'minimal_regrettable_glue_code_each_with_an_open_issue',
    '282_delta_log_io.sh');
  assert.ok(fs.existsSync(p), 'expected the #282 delta-log I/O patch to exist');
});

test('post18: npm/factoidal/browser.js exports the durable update log this post\'s cells call', () => {
  const browserJs = fs.readFileSync(
    path.join(REPO_ROOT, 'npm', 'factoidal', 'browser.js'), 'utf8');
  for (const name of [
    'deltaLogOpen', 'deltaLogAppend', 'deltaLogReadAllHex', 'deltaLogMerge',
    'deltaLogDestroy', '_deltaLogCorruptLastForTest',
  ]) {
    assert.match(browserJs, new RegExp(`export const ${name} = `), `expected browser.js to export ${name}`);
  }
});

test('post18 cell 2 (deltaLogAppend) runs on the Lean package: seq 0, opCount 1', async () => {
  const result = await runObservableCell(cells[1], { Factoidal, fn: factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.equal(result.seq, 0);
  assert.equal(result.opCount, 1);
});

test('post18 cell 3 (deltaLogMerge) runs on the Lean package: the log read back holds Dana', async () => {
  const result = await runObservableCell(cells[2], { Factoidal, fn: factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.ok(result.batchesInLog >= 1, `batchesInLog ${result.batchesInLog}`);
  assert.equal(result.containsDana, true);
  assert.ok(result.mergedPreview.some((line) => line.includes('"Dana"')), result.mergedPreview.join('\n'));
});

test('post18 cell 4 (torn write) runs on the Lean package: Eve survives, Frank is lost', async () => {
  const result = await runObservableCell(cells[3], { Factoidal, fn: factoidal, pretty });
  assert.equal(result.available, true, result.note);
  assert.equal(result.eveSurvivesCorruption, true);
  assert.equal(result.frankWasLostToCorruption, true);
});

test('post18: the Lean engine reports the torn record, and a fresh log after it is clean', async () => {
  const handle = await Factoidal.deltaLogOpen('post18-test-inspect');
  await Factoidal.deltaLogDestroy(handle);
  await Factoidal.deltaLogOpen('post18-test-inspect');
  const a = await Factoidal.deltaLogAppend(handle,
    'INSERT DATA { <http://example.org/a> <http://example.org/p> "1" . }');
  const b = await Factoidal.deltaLogAppend(handle,
    'INSERT DATA { <http://example.org/b> <http://example.org/p> "2" . }');
  assert.deepEqual([a.seq, b.seq], [0, 1]);
  const hex = await Factoidal.deltaLogReadAllHex(handle);
  const records = hex.split('\n');
  assert.equal(records.length, 2);
  // Each record is the engine's DLB1 frame ('DLB1' little-endian first).
  for (const r of records) assert.match(r, /^444c4231[0-9a-f]+$/);
  let info = await Factoidal.deltaLogInspect(handle);
  assert.equal(info.batches, 2);
  assert.equal(info.torn, false);
  assert.deepEqual(info.records.map((r) => r.seq), [0, 1]);
  assert.equal(await Factoidal._deltaLogCorruptLastForTest(handle), true);
  info = await Factoidal.deltaLogInspect(handle);
  assert.equal(info.batches, 1);
  assert.equal(info.torn, true);
  assert.equal(info.tornBytes, records[1].length / 2 - 4);
  const merged = await Factoidal.deltaLogMerge(handle, '<http://example.org/base> <http://example.org/p> "0" .\n');
  assert.match(merged, /"0"/);
  assert.match(merged, /"1"/);
  assert.doesNotMatch(merged, /"2"/);
  await Factoidal.deltaLogDestroy(handle);
  info = await Factoidal.deltaLogInspect(handle);
  assert.equal(info.batches, 0);
  assert.equal(info.torn, false);
});

test('post18: deltaLogAppend refuses an update form the log does not admit, and writes nothing', async () => {
  const handle = await Factoidal.deltaLogOpen('post18-test-refuse');
  await Factoidal.deltaLogDestroy(handle);
  await assert.rejects(
    Factoidal.deltaLogAppend(handle, 'DELETE WHERE { ?s ?p ?o }'),
    /admits INSERT DATA/);
  assert.equal(await Factoidal.deltaLogReadAllHex(handle), '');
  await assert.rejects(Factoidal.deltaLogAppend({}, 'INSERT DATA {}'), TypeError);
  await assert.rejects(Factoidal.deltaLogMerge(handle, 42), TypeError);
});

test('post18: entry_jsoo.ml exports the delta-log ABI AND the toCottas BaseWriter write path (grounds the "base-store write path reaches the browser too" section)', () => {
  const entry = fs.readFileSync(
    path.join(REPO_ROOT, 'bin', 'npm-entry', 'entry_jsoo.ml'), 'utf8');
  assert.match(entry, /"deltaBatchToHex"/);
  assert.match(entry, /"deltaMergeApplyBrowser"/);
  // toCottas was added since an earlier version of this post claimed
  // no BaseWriter existed in the browser. It now does: the export wraps
  // the same pure-Tot serializer the native CLI uses. Since
  // https://github.com/danbri/factoidal/issues/684's module split, the
  // export TABLE ("toCottas" the key) lives in entry_jsoo.ml, but the
  // implementation calling the BaseWriter serializer moved to
  // entry_extras.ml (the full bundle links both, so the grounding claim
  // "the code path exists and reaches the browser" still holds).
  assert.match(entry, /"toCottas"/);
  const extras = fs.readFileSync(
    path.join(REPO_ROOT, 'bin', 'npm-entry', 'entry_extras.ml'), 'utf8');
  assert.match(extras, /RDF_CottasStore_BaseWriter\.serialize_cottas_v2/);
});

test('post18: RDF.CottasStore.BaseWriter.fst exists and is the module the zero-Python claim cites', () => {
  const p = path.join(REPO_ROOT, 'formal', 'fstar', 'RDF.CottasStore.BaseWriter.fst');
  assert.ok(fs.existsSync(p), 'expected RDF.CottasStore.BaseWriter.fst to exist');
});

// The demo binary is an F* native build product (the factoidal-builds
// linux-x86_64 release), which a hub checkout does not have since the hub
// moved to the Lean engine (issue 726). The checkout has the committed
// KaRaMeL C the binary is built from, so the transcript lines the post
// quotes are checked against that source: each check label and the final
// line are strings the demo prints.
test('post18: the C demo transcript quoted in this post is printed by the committed delta_log_demo.c', () => {
  const demoSrc = fs.readFileSync(path.join(
    REPO_ROOT, 'formal', 'fstar', 'c-output', 'deltalog', 'demo', 'delta_log_demo.c'), 'utf8');
  assert.ok(demoSrc.includes('"parse_delta_batch(corrupted bytes) = None (checksum rejects it)"'));
  assert.ok(demoSrc.includes('All checks passed'));
  const post = fs.readFileSync(path.join(REPO_ROOT, 'docs', 'web', 'historical-fstar-notebooks', POST_FILE), 'utf8');
  assert.match(post, /parse_delta_batch\(corrupted bytes\) = None \(checksum rejects it\)\s+OK/);
  assert.match(post, /All checks passed/);
});
test('post18: the KaRaMeL C output directory this post links to exists', () => {
  const dir = path.join(REPO_ROOT, 'formal', 'fstar', 'c-output', 'deltalog');
  assert.ok(fs.existsSync(path.join(dir, 'Factoidal_DeltaLog.c')));
  assert.ok(fs.existsSync(path.join(dir, 'Factoidal_DeltaLog.h')));
});

test('post18: the delta-log merge correspondence lemma this post cites is present (same lemma post17 cites)', () => {
  const deltaMerge = fs.readFileSync(
    path.join(REPO_ROOT, 'formal', 'fstar', 'RDF.Store.Columnar.DeltaMerge.fst'), 'utf8');
  assert.match(deltaMerge, /lemma_merge_on_read_matches_apply_entries/);
});

test('post18: the commits cited in this post are real, reachable commits', () => {
  const { execFileSync } = require('node:child_process');
  // Ids are danbri/factoidal commits; resolve them through the split map.
  // 8ff60eb (browser persistence) changed no formal/ file, so it exists only
  // in danbri/factoidal: the map must say so, and the post links there.
  for (const sha of ['8ff60eb', 'bd9e5be', '4f8fc95', 'e8085da']) {
    const m = resolvePreSplitCommit(REPO_ROOT, sha);
    assert.ok(m, `expected ${sha} in tools/repo-split/commit-map.tsv`);
    if (sha === '8ff60eb') { assert.equal(m.kind, 'pruned'); continue; }
    assert.equal(m.kind, 'rewritten', `expected ${sha} to have a rewritten core commit`);
    const out = execFileSync('git', ['cat-file', '-t', m.core], { cwd: REPO_ROOT }).toString().trim();
    assert.equal(out, 'commit', `expected core commit ${m.core} (from ${sha}) to be reachable in this repo`);
  }
});

test('post18: the zero-Python DuckDB verdict quoted in this post matches the real commit message', () => {
  const { execFileSync } = require('node:child_process');
  const msg = execFileSync('git', ['log', '-1', '--format=%B', resolvePreSplitCommit(REPO_ROOT, '4f8fc95').core], { cwd: REPO_ROOT }).toString();
  assert.match(msg, /DuckDB verdict: ACCEPTED byte-exact on 5-quad, 6,780-quad,\s+and\s+888,949-quad corpora/);
  assert.match(msg, /0 missing, 0 extra vs source/);
});
