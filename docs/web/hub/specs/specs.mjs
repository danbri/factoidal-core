// The Hub Data and documents page: conformance of the built-in engine's RDF, SPARQL, OWL, SHACL,
// ShEx, JSON-LD, CSVW, RML, RIF, VC, XML, XSLT/XPath/XQuery, Schematron, JSON Schema and MathML
// implementations, from data.json and history.json (written by tests/browser-wpt/specs-data.py;
// schema data.schema.json; what each suite id measures: tests/browser-wpt/spec-suites.json).
//
// Top level: one row per technology family with its headline. Drill down: family -> specification
// and version -> suite (population, test type) -> sub-manifests and history. Two other views:
// every specification and version as one flat table (SPARQL Query, Update and result formats
// apart), and the suites that need attention (invalid, partial, stale, not yet recorded).
//
// Pure functions build HTML strings (no DOM at import), so tests/hub/specs_test.mjs renders the
// page in Node with sample data. mount() is the browser part. Charts reuse the Conformance page's
// SVG line chart; no library is loaded.
import {lineChart} from '../conformance/conformance.mjs';

export const VIEWS = [['families', 'Families'], ['specs', 'Specifications'], ['attention', 'Needs attention']];
export const STALE_HOURS = 36;

const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
const fmt = n => n == null ? 'n/a' : Number(n).toLocaleString('en-GB');
const pct = (a, b) => !b ? 'n/a' : (a === b ? '100%' : (Math.floor(a / b * 1000) / 10).toFixed(1) + '%');
const when = iso => iso ? iso.replace('T', ' ').slice(0, 16) + ' UTC' : 'n/a';
const day = iso => iso ? iso.slice(0, 10) : 'n/a';
const ageH = (iso, now) => (now - Date.parse(iso)) / 36e5;
const ageText = h => h < 48 ? Math.round(h) + ' hours' : Math.round(h / 24) + ' days';
const commitLink = c => c ? `<a href="https://github.com/danbri/factoidal-core/commit/${esc(c)}">${esc(String(c).slice(0, 9))}</a>` : 'n/a';
const ENGINE = {lean: 'built-in', fstar: 'F*'};
const KIND = {official: 'official suite', subset: 'subset of the official suite', authored: 'cases written by the project from the specification'};

/** The status chip of a record: valid, partial or invalid, and stale. */
export function chips(s) {
  const out = [];
  if (s.stale) out.push(`<span class="chip stale" title="${esc(s.staleReason)}">stale</span>`);
  if (s.status === 'invalid') out.push(`<span class="chip invalid" title="${esc(s.reason)}">invalid</span>`);
  else if (s.status === 'partial') out.push(`<span class="chip partial" title="${esc(s.reason)}">partial</span>`);
  else if (!s.stale && s.total && s.passed === s.total) out.push('<span class="chip full">all pass</span>');
  return out.join(' ');
}

/** A bar: passed (solid), decided but not passed (second colour), not decided (track). */
export function bar(passed, decided, total) {
  if (!total) return '<span class="track"></span>';
  const p = Math.max(0, Math.min(100, passed / total * 100)), f = Math.max(0, Math.min(100 - p, (decided - passed) / total * 100));
  return `<span class="track" role="img" aria-label="${fmt(passed)} passed, ${fmt(Math.max(0, decided - passed))} failed, ${fmt(Math.max(0, total - decided))} not decided, of ${fmt(total)}">` +
    `<span class="fill" style="width:${p.toFixed(2)}%"></span><span class="fail" style="left:${p.toFixed(2)}%;width:${f.toFixed(2)}%"></span></span>`;
}

const value = s => s.status === 'invalid' && !s.decided ? '<span class="v muted">not run</span>' :
  `<span class="v"><b>${fmt(s.passed)}</b> / ${fmt(s.total)}<small>${pct(s.passed, s.total)}</small></span>`;

/** The family headline in words. */
export function headlineText(f) {
  const h = f.headline, bits = [];
  if (f.additive && h.total) bits.push(`<b>${fmt(h.passed)}</b> of ${fmt(h.total)} tests pass (${pct(h.passed, h.total)})`);
  bits.push(`${h.complete} of ${h.suites} ${f.additive ? 'suites' : 'populations'} all pass`);
  if (h.partial) bits.push(`${h.partial} partial`);
  if (h.invalid) bits.push(`${h.invalid} not run or invalid`);
  if (h.unrecorded) bits.push(`${h.unrecorded} measured, not recorded`);
  return bits.join(' · ');
}

/** The records of a family grouped by specification and version, in mapping order. Current
built-in suites first; F* rows that a built-in suite supersedes or covers go in "earlier". */
export function groups(D, fid) {
  const out = new Map();
  for (const s of D.suites.filter(s => s.family === fid)) {
    const k = s.spec + '\u0000' + s.version;
    if (!out.has(k)) out.set(k, {spec: s.spec, version: s.version, specUrl: s.specUrl, current: [], earlier: []});
    (s.engine === 'fstar' && (s.supersededBy || s.coveredBy || s.replacedBy) ? out.get(k).earlier : out.get(k).current).push(s);
  }
  return [...out.values()];
}

function suiteLabel(s) {
  return `${esc(s.testType)}<small>${esc(s.technology)} · ${esc(s.suite)}${s.engine === 'fstar' ? ' · F*' : ''}</small>`;
}

/** One suite as a disclosure row: the summary line and, when open, its details. */
export function suiteHTML(s, D) {
  const id = 'suite-' + s.suite;
  return `<details class="suite" id="${esc(id)}" data-suite="${esc(s.suite)}"><summary class="srow">` +
    `<span class="lbl">${suiteLabel(s)}</span>${bar(s.passed, s.decided, s.total)}${value(s)}<span class="cs">${chips(s)}</span></summary>` +
    `<div class="sbody">${suiteDetailHTML(s, D)}<div class="hist" data-suite="${esc(s.suite)}"></div></div></details>`;
}

/** The facts of a record. */
export function suiteDetailHTML(s, D) {
  const src = D.sources[s.source] || {};
  const rows = [
    ['Population', esc(s.population)],
    ['Test type', esc(s.testType)],
    ['Specification', `${s.specUrl ? `<a href="${esc(s.specUrl)}">${esc(s.spec)}</a>` : esc(s.spec)}, version ${esc(s.version)}`],
    ['Source', `${src.url ? `<a href="${esc(src.url)}">${esc(src.name || s.source)}</a>` : esc(src.name || s.source)}${src.kind ? ` (${esc(KIND[src.kind] || src.kind)})` : ''}${src.licence ? ', ' + esc(src.licence) : ''}`],
  ];
  if (s.manifest) rows.push(['Manifest', `<code>${esc(s.manifest)}</code>`]);
  rows.push(['Run', s.run ? `${esc(when(s.finished))}, ${esc(ENGINE[s.engine] || s.engine)} engine at ${commitLink(s.commit)}, ${s.workflow ? `<a href="${esc(s.workflow)}">workflow run</a>` : 'no workflow link'}; ${fmt(s.runs)} recorded run${s.runs === 1 ? '' : 's'}` : 'never recorded']);
  rows.push(['Counts', `${fmt(s.passed)} passed, ${s.failed == null ? 'n/a' : fmt(s.failed)} failed, ${fmt(s.undecided)} not decided, of ${fmt(s.total)}`]);
  if (s.reason) rows.push(['Status', `${esc(s.status)}: ${esc(s.reason)}`]);
  if (s.lastValid) rows.push(['Last valid run', `${fmt(s.lastValid.passed)} of ${fmt(s.lastValid.total)}, ${esc(when(s.lastValid.finished))} at ${commitLink(s.lastValid.commit)}`]);
  if (s.stale) rows.push(['Stale', esc(s.staleReason)]);
  if (s.approved) rows.push(['Approved cases', `${fmt(s.approved.passed)} of ${fmt(s.approved.total)} pass`]);
  if (s.continues) rows.push(['Continues', `the F* suite <a href="#suite-${esc(s.continues)}">${esc(s.continues)}</a> (shown in the chart)`]);
  if (s.supersededBy) rows.push(['Superseded by', `<a href="#suite-${esc(s.supersededBy)}">${esc(s.supersededBy)}</a>`]);
  if (s.coveredBy) rows.push(['Covered by', `<a href="#suite-${esc(s.coveredBy)}">${esc(s.coveredBy)}</a>`]);
  if (s.replacedBy) rows.push(['Replaced by', s.replacedBy.map(r => `<a href="#suite-${esc(r)}">${esc(r)}</a>`).join(', ')]);
  if (s.note) rows.push(['Note', esc(s.note)]);
  let h = '<dl class="facts">' + rows.map(([k, v]) => `<dt>${k}</dt><dd>${v}</dd>`).join('') + '</dl>';
  if (s.parts?.length) h += partsHTML(s.parts);
  return h;
}

/** The sub-manifests of an l4w3c suite, grouped by the specification each one tests. */
export function partsHTML(parts) {
  const by = new Map();
  for (const p of parts) {
    if (!by.has(p.spec)) by.set(p.spec, {spec: p.spec, url: p.specUrl, technology: p.technology, rows: []});
    by.get(p.spec).rows.push(p);
  }
  return '<div class="tw"><table class="parts"><thead><tr><th>Specification and sub-manifest</th><th>Passed</th><th>Failed</th><th>Not decided</th><th>Total</th></tr></thead><tbody>' +
    [...by.values()].map(g => {
      const t = k => g.rows.reduce((a, r) => a + r[k], 0);
      return `<tr class="ph"><td>${g.url ? `<a href="${esc(g.url)}">${esc(g.spec)}</a>` : esc(g.spec)}</td><td><b>${fmt(t('passed'))}</b></td><td>${fmt(t('failed'))}</td><td>${fmt(t('skipped'))}</td><td>${fmt(t('total'))}</td></tr>` +
        g.rows.map(r => `<tr><td class="sub">${esc(r.label)}</td><td>${fmt(r.passed)}</td><td>${fmt(r.failed)}</td><td>${fmt(r.skipped)}</td><td>${fmt(r.total)}</td></tr>`).join('');
    }).join('') + '</tbody></table></div>';
}

/** The share history of a suite (and the F* suite it continues) as an SVG chart. Invalid rows are left out. */
export function suiteChart(D, H, sid, width) {
  const s = D.suites.find(x => x.suite === sid);
  if (!s) return '';
  const pts = id => (H.suites[id] || []).filter(r => r[5] !== 'i' && r[4] > 0)
    .map(r => ({t: Date.parse(r[0]), v: r[2] / r[4], tip: `${fmt(r[2])} of ${fmt(r[4])} (${pct(r[2], r[4])}), ${when(r[0])}, ${r[1]}${r[5] === 'p' ? ', partial' : ''}`}));
  const series = [{label: ENGINE[s.engine] === 'F*' ? 'F*' : 'built-in', cls: s.engine === 'fstar' ? 's2' : 's1', pts: pts(sid)}];
  if (s.continues && H.suites[s.continues]) series.push({label: `F* (${s.continues})`, cls: 's2', pts: pts(s.continues)});
  const totals = new Set(series.flatMap(x => (H.suites[x === series[0] ? sid : s.continues] || []).map(r => r[4])));
  return `<h5>History</h5>` + lineChart({width, height: 170, series: series.filter(x => x.pts.length), title: `Share of ${s.suite} over time`}) +
    (totals.size > 1 ? `<p class="muted">The population size changed over time (${[...totals].sort((a, b) => a - b).map(fmt).join(', ')} tests): the F* and built-in runners do not always run the same population.</p>` : '');
}

/** The family headline over recording runs (additive families). */
export function familyChart(f, H, width) {
  const rows = (H.families || {})[f.id] || [];
  if (rows.length < 2) return '';
  const pts = rows.filter(r => r[3] > 0).map(r => ({t: Date.parse(r[0]), v: r[2] / r[3], tip: `${fmt(r[2])} of ${fmt(r[3])} in ${r[4]} suites, ${when(r[0])}, ${r[1]}`}));
  return lineChart({width, height: 150, series: [{label: 'built-in', cls: 's1', pts}], title: `${f.name}: share of the headline suites per recording run`});
}

/** One family: the summary row and, open, its specifications and suites. */
export function familyHTML(f, D, H, {open = false, width = 700} = {}) {
  const h = f.headline;
  const gs = groups(D, f.id);
  const unrec = (D.unrecorded || []).filter(u => u.family === f.id);
  const flags = [h.partial ? `<span class="chip partial">${h.partial} partial</span>` : '', h.invalid ? `<span class="chip invalid">${h.invalid} invalid</span>` : '',
    h.stale ? `<span class="chip stale">${h.stale} stale</span>` : '', unrec.length ? `<span class="chip unrec">${unrec.length} not recorded</span>` : ''].filter(Boolean).join(' ');
  const barHTML = f.additive && h.total ? bar(h.passed, h.decided, h.total) : popStrip(D, f.id);
  let body = `<p class="muted">${esc(f.summary)}${f.additiveNote ? ' ' + esc(f.additiveNote) : ''}</p>`;
  if (f.additive) body += `<div class="fchart" data-family="${esc(f.id)}">${open ? familyChart(f, H, width) : ''}</div>`;
  for (const g of gs) {
    if (!g.current.length && !g.earlier.length) continue;
    body += `<div class="spec"><h4>${g.specUrl ? `<a href="${esc(g.specUrl)}">${esc(g.spec)}</a>` : esc(g.spec)} <span class="ver">${esc(g.version)}</span></h4>` +
      g.current.map(s => suiteHTML(s, D)).join('') +
      (g.earlier.length ? `<details class="earlier"><summary>Earlier F* rows (${g.earlier.length}, stale)</summary>${g.earlier.map(s => suiteHTML(s, D)).join('')}</details>` : '') + '</div>';
  }
  if (unrec.length) body += unrecordedHTML(unrec);
  return `<details class="fam" id="family-${esc(f.id)}" data-family="${esc(f.id)}"${open ? ' open' : ''}><summary class="frow">` +
    `<span class="fname">${esc(f.name)}</span><span class="fbar">${barHTML}</span><span class="fhead">${headlineText(f)}</span><span class="cs">${flags}</span></summary>` +
    `<div class="fbody">${body}</div></details>`;
}

/** For a family whose populations overlap (OWL 2): one small cell per headline population. */
export function popStrip(D, fid) {
  const ss = D.suites.filter(s => s.family === fid && s.headline && !s.stale);
  return '<span class="strip">' + ss.map(s => {
    const v = s.total && s.status !== 'invalid' ? s.passed / s.total : null;
    const lvl = v == null ? 'na' : v >= 1 ? 'l4' : v >= 0.9 ? 'l3' : v >= 0.5 ? 'l2' : v > 0 ? 'l1' : 'l0';
    return `<i class="pc ${lvl}" title="${esc(s.testType + ', ' + s.technology + ': ' + (v == null ? 'not run' : fmt(s.passed) + ' of ' + fmt(s.total)))}"></i>`;
  }).join('') + '</span>';
}

/** Measurements with a runner but no recorded row: shown apart, never as a score. */
export function unrecordedHTML(list) {
  return '<div class="unrec"><h4>Measured locally, not yet recorded by CI</h4><p class="muted">These runners exist but have no rows in runs.csv. The numbers are from the linked write-ups; they are not current scores.</p><ul>' +
    list.map(u => `<li><b>${u.specUrl ? `<a href="${esc(u.specUrl)}">${esc(u.spec)}</a>` : esc(u.spec)}</b> ${esc(u.version)}: ${fmt(u.passed)} of ${fmt(u.scored)} pass` +
      (u.failed != null ? `, ${fmt(u.failed)} fail` : '') + (u.unsupported != null ? `, ${fmt(u.unsupported)} unsupported` : '') +
      ` <span class="muted">(<code>${esc(u.runner)}</code>, ${esc(u.where)}, ${esc(u.measured)}; <a href="${esc(u.doc)}">write-up</a>)</span>${u.note ? `<br><small class="muted">${esc(u.note)}</small>` : ''}</li>`).join('') + '</ul></div>';
}

/** Every specification and version as one row: current built-in suites, and the sub-manifests of
the l4w3c suites in place of the suite when they are recorded (SPARQL Query, Update, ... apart). */
export function specRows(D) {
  const rows = new Map();
  const add = (fid, spec, url, version, technology, passed, decided, total, src) => {
    const k = [fid, spec, version, technology].join('\u0000');
    if (!rows.has(k)) rows.set(k, {family: fid, spec, url, version, technology, passed: 0, decided: 0, total: 0, from: []});
    const r = rows.get(k); r.passed += passed; r.decided += decided; r.total += total; if (!r.from.includes(src)) r.from.push(src);
  };
  for (const s of D.suites) {
    if (s.engine !== 'lean' || s.stale || s.status === 'invalid') continue;
    if (s.parts?.length) for (const p of s.parts) add(s.family, p.spec === 'unclassified' ? s.spec : p.spec, p.specUrl || s.specUrl, s.version, p.technology, p.passed, p.passed + p.failed, p.total, s.suite);
    else add(s.family, s.spec, s.specUrl, s.version, s.technology + ' — ' + s.testType, s.passed, s.decided, s.total, s.suite);
  }
  return [...rows.values()];
}

export function specsViewHTML(D) {
  const rows = specRows(D);
  const fams = D.families.filter(f => rows.some(r => r.family === f.id));
  return '<p class="muted">One row per specification, version and technology, from the current built-in suites. Where a suite runs several specifications (SPARQL 1.1: Query, Update, result formats, protocol, …) and its sub-manifests are recorded, each specification has its own row. OWL 2 populations overlap; each is its own row.</p>' +
    fams.map(f => `<h3 class="vh">${esc(f.name)}</h3><div class="tw"><table class="specs"><thead><tr><th>Specification</th><th>Version</th><th>Technology and test type</th><th>Passed</th><th>Total</th><th>Share</th><th>Suite</th></tr></thead><tbody>` +
      rows.filter(r => r.family === f.id).map(r => `<tr><td>${r.url ? `<a href="${esc(r.url)}">${esc(r.spec)}</a>` : esc(r.spec)}</td><td>${esc(r.version)}</td><td class="wrap">${esc(r.technology)}</td>` +
        `<td><b>${fmt(r.passed)}</b></td><td>${fmt(r.total)}</td><td>${pct(r.passed, r.total)}${r.decided < r.total ? `<small>${fmt(r.total - r.decided)} not decided</small>` : ''}</td>` +
        `<td class="wrap">${r.from.map(x => `<a href="#suite-${esc(x)}" data-go="${esc(x)}">${esc(x)}</a>`).join(', ')}</td></tr>`).join('') + '</tbody></table></div>').join('');
}

/** Invalid, partial and stale suites, and runners with no recorded rows, each with its reason. */
export function attentionHTML(D) {
  const cur = D.suites.filter(s => s.engine === 'lean');
  const sect = (title, list, why) => list.length ? `<h3 class="vh">${title} (${list.length})</h3><ul class="att">` + list.map(s =>
    `<li><a href="#suite-${esc(s.suite)}" data-go="${esc(s.suite)}">${esc(s.suite)}</a> <span class="muted">${esc(s.spec)} ${esc(s.version)}, ${esc(s.testType)}</span><br>${why(s)}</li>`).join('') + '</ul>' : '';
  const fonly = D.suites.filter(s => s.engine === 'fstar' && !s.supersededBy && !s.coveredBy && !s.replacedBy);
  return sect('Not run or invalid', cur.filter(s => s.status === 'invalid'), s => esc(s.reason) + (s.lastValid ? ` (last valid: ${fmt(s.lastValid.passed)} of ${fmt(s.lastValid.total)}, ${day(s.lastValid.finished)})` : '')) +
    sect('Partial: valid runs that do not decide every test', cur.filter(s => s.status === 'partial' && !s.stale), s => `${fmt(s.passed)} of ${fmt(s.total)} pass; ${esc(s.reason)}`) +
    sect('Built-in suites with no recent row', cur.filter(s => s.stale), s => esc(s.staleReason)) +
    sect('F* suites with no built-in successor', fonly, s => esc(s.staleReason)) +
    (D.unrecorded?.length ? '<h3 class="vh">Runners with no recorded rows</h3>' + unrecordedHTML(D.unrecorded) : '') +
    (D.unmapped?.length ? `<h3 class="vh">Suite ids not in the mapping</h3><p>${D.unmapped.map(esc).join(', ')} — add them to tests/browser-wpt/spec-suites.json.</p>` : '');
}

/** The whole page body below the title. view: families | specs | attention. */
export function pageHTML(D, H, {now = Date.now(), view = 'families', open = null, width = 700} = {}) {
  const hh = D.newestLean ? ageH(D.newestLean, now) : Infinity;
  const c = D.counts;
  let h = `<p class="asof">Newest recorded run <b>${when(D.newestLean)}</b>. Page data built ${when(D.generatedAt)} from ${fmt(D.source.rows)} recorded rows.</p>` +
    (hh > STALE_HOURS ? `<p class="stale">The newest recorded run is ${ageText(hh)} old. The suites run with every release of main; this data is regenerated when a run is recorded and every 3 hours.</p>` : '') +
    `<p class="counts"><span class="chip full">${fmt(c.valid)} valid</span> <span class="chip partial">${fmt(c.partial)} partial</span> <span class="chip invalid">${fmt(c.invalid)} invalid or not run</span> <span class="chip stale">${fmt(c.stale)} stale (mostly F* history)</span></p>` +
    `<div class="tabs" role="tablist">${VIEWS.map(([k, l]) => `<button type="button" role="tab" class="tab" data-view="${k}" aria-selected="${k === view}">${l}</button>`).join('')}</div>`;
  if (view === 'specs') h += `<section class="view">${specsViewHTML(D)}</section>`;
  else if (view === 'attention') h += `<section class="view">${attentionHTML(D)}</section>`;
  else h += `<section class="view fams">${D.families.filter(f => D.suites.some(s => s.family === f.id) || (D.unrecorded || []).some(u => u.family === f.id)).map(f => familyHTML(f, D, H, {open: open === f.id, width})).join('')}</section>`;
  h += '<section class="notes"><h2>About these numbers</h2>' +
    '<p><b>What runs.</b> release-tests (danbri/factoidal-builds) runs these suites on the built-in engine with every release of main, and records one row per suite in runs.csv on the wpt-scores branch. Each suite id is described in <a href="https://github.com/danbri/factoidal-core/blob/main/tests/browser-wpt/spec-suites.json">spec-suites.json</a>: family, specification, version, technology, test type and population. Suite ids are never renamed; the mapping says what they are.</p>' +
    '<p><b>Totals.</b> A total is the whole suite or population. Bars show passed (solid), decided but failed (second colour) and not decided (track). A valid run that does not decide every test is <i>partial</i>, with the count and why; an invalid run is shown with its reason and never as a score.</p>' +
    `<p><b>Stale.</b> The F* implementation's automatic runs stopped on ${esc(day(D.fstarStopped))}. Its rows stay as history (and in each built-in suite's chart where the built-in suite continues it), marked stale. A built-in suite with no row for ${D.staleLeanHours} hours before the newest recording is also stale.</p>` +
    '<p><b>XSLT, XPath, XQuery.</b> XSLT 1.0 is recorded (87 of 88). The QT4 work (XPath, XQuery and XSLT 4.0, XML Schema in qt4tests) has runners, measured locally in October; recording it with the other suites: <a href="https://github.com/danbri/factoidal-core/issues/511">issue 511</a>.</p>' +
    '<p><b>Data.</b> <a href="data.json">data.json</a> (current records), <a href="history.json">history.json</a> (every row as a time series) and <a href="records.csv">records.csv</a> (every row as a flat record, for any CSV tool) are written by tests/browser-wpt/specs-data.py and kept with their history on the <a href="https://github.com/danbri/factoidal-builds/commits/hub-data">hub-data</a> branch of danbri/factoidal-builds.</p></section>';
  return h;
}

/** Browser: fetch, render, wire the views, the disclosures and the hash (#family-ID, #suite-ID, #view-NAME). */
export async function mount(root, {base = './'} = {}) {
  let D, H;
  try {
    const get = async n => { const r = await fetch(base + n, {cache: 'no-cache'}); if (!r.ok) throw Error(`${n}: HTTP ${r.status}`); return r.json(); };
    [D, H] = await Promise.all([get('data.json'), get('history.json')]);
  } catch (e) {
    root.innerHTML = `<p class="stale">No data in this build of the site (${esc(e.message)}). The Pages build copies data.json, history.json and records.csv from the hub-data branch of danbri/factoidal-builds.</p>`;
    return;
  }
  const st = {view: 'families'};
  const width = el => Math.max(280, Math.min((el || root).clientWidth || 700, 1060) - 8);
  const draw = () => { root.innerHTML = pageHTML(D, H, {now: Date.now(), view: st.view, width: width()}); };
  const go = () => {
    const h = decodeURIComponent(location.hash.slice(1));
    if (h.startsWith('view-')) st.view = VIEWS.some(v => v[0] === h.slice(5)) ? h.slice(5) : 'families';
    else if (h.startsWith('suite-') || h.startsWith('family-')) st.view = 'families';
    draw();
    const el = h && document.getElementById(h);
    if (!el) return;
    for (let p = el; p && p !== root; p = p.parentElement) if (p.tagName === 'DETAILS') p.open = true;
    el.scrollIntoView({block: 'start'});
  };
  root.addEventListener('click', e => {
    const t = e.target.closest('button.tab');
    if (t) { history.replaceState(null, '', '#view-' + t.dataset.view); st.view = t.dataset.view; draw(); return; }
    const g = e.target.closest('a[data-go]');
    if (g) { e.preventDefault(); location.hash = 'suite-' + g.dataset.go; }
  });
  // Charts are drawn when a disclosure opens, so a closed family or suite costs nothing.
  root.addEventListener('toggle', e => {
    const d = e.target;
    if (!(d instanceof HTMLDetailsElement) || !d.open) return;
    if (d.classList.contains('suite')) {
      const box = d.querySelector(':scope > .sbody > .hist');
      if (box && !box.dataset.done) { box.innerHTML = suiteChart(D, H, d.dataset.suite, width(box)); box.dataset.done = '1'; }
    } else if (d.classList.contains('fam')) {
      const box = d.querySelector(':scope > .fbody > .fchart');
      const f = D.families.find(x => x.id === d.dataset.family);
      if (box && f && !box.dataset.done) { box.innerHTML = familyChart(f, H, width(box)); box.dataset.done = '1'; }
    }
  }, true);
  addEventListener('hashchange', go);
  go();
  return {D, H};
}
