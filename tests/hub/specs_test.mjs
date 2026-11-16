// The Hub Data and documents page (docs/web/hub/specs/) rendered in Node with the sample data of
// tests/hub/specs-fixtures/sample (written by tests/browser-wpt/specs-data.py from runs-sample.csv).
// The HTML comes from the same functions the browser uses (specs.mjs). Also: the schema check,
// and the real mapping (tests/browser-wpt/spec-suites.json) is consistent.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {pageHTML, familyHTML, suiteChart, familyChart, partsHTML, specRows, headlineText, groups, attentionHTML, chips, bar} from '../../docs/web/hub/specs/specs.mjs';
import {checkDir, SCHEMA_PATH} from './specs_schema.mjs';
import {validate} from './conformance_schema.mjs';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const SAMPLE = path.join(HERE, 'specs-fixtures', 'sample');
const D = JSON.parse(fs.readFileSync(path.join(SAMPLE, 'data.json'), 'utf8'));
const H = JSON.parse(fs.readFileSync(path.join(SAMPLE, 'history.json'), 'utf8'));
const NOW = Date.parse('2026-11-16T06:00:00Z');

/** Tags opened and closed in order (a cheap check that the HTML strings nest). */
function balanced(html) {
  const VOID = new Set(['br', 'img', 'input', 'meta', 'link', 'hr']);
  const stack = [];
  for (const [, close, name, self] of html.matchAll(/<(\/?)([a-zA-Z][a-zA-Z0-9]*)\b[^>]*?(\/?)>/g)) {
    const n = name.toLowerCase();
    if (self || (VOID.has(n) && !close)) continue;
    if (!close) stack.push(n);
    else if (stack.pop() !== n) return false;
  }
  return stack.length === 0;
}

test('the sample files match the schema', () => {
  for (const [file, errs] of Object.entries(checkDir(SAMPLE))) assert.deepEqual(errs, [], file);
});

test('the schema finds a bad status, a negative count and a missing field', () => {
  const schema = JSON.parse(fs.readFileSync(SCHEMA_PATH, 'utf8'));
  const bad = structuredClone(D);
  bad.suites[0].status = 'great';
  bad.suites[1].passed = -1;
  delete bad.families[0].headline;
  const errs = validate(bad, schema['data.json'], schema.definitions);
  assert.ok(errs.some(e => e.includes('suites[0].status')), errs.join('\n'));
  assert.ok(errs.some(e => e.includes('suites[1].passed')), errs.join('\n'));
  assert.ok(errs.some(e => e.includes('families[0]: no headline')), errs.join('\n'));
});

test('every view renders, nests, and names each status', () => {
  for (const view of ['families', 'specs', 'attention']) {
    const html = pageHTML(D, H, {now: NOW, view, width: 700});
    assert.ok(balanced(html), view);
    assert.ok(html.includes(`data-view="${view}" aria-selected="true"`), view);
  }
  const fam = pageHTML(D, H, {now: NOW});
  assert.match(fam, /id="family-sparql"/);
  assert.doesNotMatch(fam, /id="family-csvw"/, 'a family with no records is left out');
  const att = pageHTML(D, H, {now: NOW, view: 'attention'});
  assert.match(att, /scoreboard status crashed/);                       // invalid, with its reason
  assert.match(att, /last valid: 42 of 43/);                            // and its last valid run
  assert.match(att, /no built-in OWL 2 EL\/QL\/RL profile recogniser/); // not run
  assert.match(att, /347 of 347 not decided/);                          // partial
  assert.match(att, /no row since 2026-11-13 10:00 UTC/);               // stale built-in suite
  assert.match(att, /l4-geosparql/);                                    // unmapped suite id
  assert.match(att, /XSLT 4\.0/);                                       // runner with no recorded rows
});

test('the top level is one row per family; suites are inside, F* rows apart', () => {
  const f = D.families.find(x => x.id === 'sparql');
  const html = familyHTML(f, D, H, {width: 600});
  assert.equal((html.match(/<details class="fam"/g) || []).length, 1);
  assert.match(html, /<details class="earlier"><summary>Earlier F\* rows \(1, stale\)/);
  const g = groups(D, 'sparql');
  assert.deepEqual(g.map(x => [x.spec, x.version, x.current.map(s => s.suite), x.earlier.map(s => s.suite)]),
    [['SPARQL 1.1', '1.1', ['l4w3c-sparql11'], ['sparql']]]);
  assert.match(headlineText(f), /<b>650<\/b> of 650 tests pass \(100%\)/);
  const owl = D.families.find(x => x.id === 'owl');
  assert.equal(owl.headline.total, null, 'OWL populations overlap: no summed count');
  assert.match(headlineText(owl), /populations all pass/);
});

test('SPARQL 1.1 is split by specification when its sub-manifests are recorded', () => {
  const s = D.suites.find(x => x.suite === 'l4w3c-sparql11');
  const specs = [...new Set(s.parts.map(p => p.spec))];
  for (const want of ['SPARQL 1.1 Query Language', 'SPARQL 1.1 Update', 'SPARQL 1.1 Query Results JSON Format',
    'SPARQL 1.1 Query Results CSV and TSV Formats', 'SPARQL 1.1 Federated Query', 'SPARQL 1.1 Entailment Regimes',
    'SPARQL 1.1 Protocol', 'SPARQL 1.1 Service Description']) assert.ok(specs.includes(want), want);
  assert.equal(s.parts.reduce((a, p) => a + p.total, 0), s.total);
  const upd = s.parts.filter(p => p.spec === 'SPARQL 1.1 Update').map(p => p.label).sort();
  assert.deepEqual(upd, ['add', 'basic-update', 'delete', 'drop', 'syntax-update-1']);
  const rows = specRows(D).filter(r => r.family === 'sparql');
  assert.ok(rows.find(r => r.spec === 'SPARQL 1.1 Update' && r.total === 109));
  const ent = rows.find(r => r.spec === 'SPARQL 1.1 Entailment Regimes');
  assert.equal(ent.total - ent.decided, 4);
  assert.ok(balanced(partsHTML(s.parts)));
});

test('history: a suite chart shows the F* suite it continues; invalid rows are left out', () => {
  const svg = suiteChart(D, H, 'l4-xslt', 600);
  assert.match(svg, /F\* \(xslt\)/);
  assert.equal((svg.match(/<svg /g) || []).length, 1);
  const rif = suiteChart(D, H, 'l4-rif_core', 600);
  assert.doesNotMatch(rif, /crashed/);
  assert.equal(familyChart(D.families.find(f => f.id === 'owl'), H, 600), '', 'no summed series for overlapping populations');
});

test('text from the data is escaped', () => {
  const bad = structuredClone(D);
  bad.suites[0].population = '<script>x</script>';
  bad.suites[0].reason = '"><img src=x>';
  const html = pageHTML(bad, H, {now: NOW, open: bad.suites[0].family});
  assert.doesNotMatch(html, /<script>x/);
  assert.doesNotMatch(html, /"><img src=x>/);
  assert.match(chips({status: 'invalid', reason: '<b>', stale: false}), /title="&lt;b&gt;"/);
  assert.match(bar(5, 7, 10), /width:50\.00%.*left:50\.00%;width:20\.00%/);
});

test('the real mapping is consistent', () => {
  const M = JSON.parse(fs.readFileSync(path.join(HERE, '..', 'browser-wpt', 'spec-suites.json'), 'utf8'));
  const fams = new Set(M.families.map(f => f.id));
  for (const [id, s] of Object.entries(M.suites)) {
    for (const k of ['family', 'spec', 'version', 'technology', 'testType', 'population', 'source', 'engine'])
      assert.ok(s[k], `${id}: no ${k}`);
    assert.ok(fams.has(s.family), `${id}: family ${s.family}`);
    assert.ok(M.sources[s.source], `${id}: source ${s.source}`);
    assert.ok(['lean', 'fstar'].includes(s.engine), id);
    if (s.parts) assert.ok(M.parts[s.parts], `${id}: parts ${s.parts}`);
    for (const k of ['continues', 'supersededBy', 'coveredBy']) if (s[k]) assert.ok(M.suites[s[k]], `${id}: ${k} ${s[k]}`);
    for (const r of s.replacedBy || []) assert.ok(M.suites[r], `${id}: replacedBy ${r}`);
    if (s.engine === 'fstar') assert.ok(s.supersededBy || s.coveredBy || s.replacedBy, `${id}: an F* suite says what took its place`);
    if (s.continues) assert.equal(M.suites[s.continues].supersededBy, id, `${id} continues ${s.continues}, which must name it`);
  }
  for (const u of M.unrecorded) assert.ok(fams.has(u.family) && M.sources[u.source], u.spec);
  for (const [k, rules] of Object.entries(M.parts)) {
    assert.equal(rules.at(-1)[0] === '.*' || k === 'rdf', true);
    for (const [re] of rules) new RegExp(re);
  }
});
